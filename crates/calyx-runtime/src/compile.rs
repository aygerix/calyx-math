//! Compilation of the syntax tree into the resolved IR.
//!
//! Scoping follows Magma's rules: identifiers assigned anywhere in a
//! function body are local to it; other free identifiers are captured by
//! value when the function value is created; top-level identifiers are
//! global and looked up dynamically.

use std::rc::Rc;

use calyx_syntax::Span;
use calyx_syntax::ast::{self, AggBody, Arg, BinOp, Expr, ExprKind, FuncBody, FuncDef, LValue, Stmt, StmtKind, UnOp};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::ir::*;
use crate::sym::Sym;
use crate::value::Value;

#[derive(Debug)]
pub struct CompileError {
    pub message: String,
    pub span: Span,
}

type CResult<T> = Result<T, CompileError>;

fn cerr<T>(span: Span, msg: impl Into<String>) -> CResult<T> {
    Err(CompileError { message: msg.into(), span })
}

/// The kind of a literal constant: 0 for numbers, 1 for strings, 2 for
/// booleans.
fn literal_kind(e: &Expr) -> Option<u8> {
    match &e.kind {
        ExprKind::Int(_) | ExprKind::Real(_) => Some(0),
        ExprKind::Str(_) => Some(1),
        ExprKind::Bool(_) => Some(2),
        ExprKind::Paren(x) | ExprKind::Unary(ast::UnOp::Neg | ast::UnOp::Plus, x) => literal_kind(x).filter(|&k| k == 0),
        ExprKind::Binary(ast::BinOp::Div, a, b) => (literal_kind(a) == Some(0) && literal_kind(b) == Some(0)).then_some(0),
        _ => None,
    }
}

/// A sequence of literal constants of different kinds has no universe, which
/// Magma reports when the statement is read, at the first element that does
/// not fit.
fn check_literal_universe(es: &[Expr]) -> CResult<()> {
    let kinds: Option<Vec<u8>> = es.iter().map(literal_kind).collect();
    let Some(kinds) = kinds else { return Ok(()) };
    if let Some(i) = kinds.iter().position(|&k| k != kinds[0]) {
        return cerr(es[i].span, "Could not find a valid universe for the sequence");
    }
    Ok(())
}

#[derive(Default)]
struct Scope {
    top: bool,
    locals: FxHashMap<Sym, Slot>,
    bindings: Vec<(Sym, Slot)>,
    captures: Vec<(Sym, CapSrc)>,
    cap_index: FxHashMap<Sym, u32>,
    slot_names: Vec<Sym>,
    self_name: Option<Sym>,
    loops: Vec<Sym>,
    in_function: bool,
    /// The body of an intrinsic (where `require` is allowed).
    in_intrinsic: bool,
    /// Depth of sequence constructors whose head may use `Self`.
    seq_compr: u32,
    /// Names that `eval` code may read but not assign.
    readonly: FxHashSet<Sym>,
}

impl Scope {
    fn lookup(&self, name: Sym) -> Option<Slot> {
        self.bindings.iter().rev().find(|b| b.0 == name).map(|b| b.1).or_else(|| self.locals.get(&name).copied())
    }

    fn new_slot(&mut self, name: Sym) -> Slot {
        let s = self.slot_names.len() as Slot;
        self.slot_names.push(name);
        s
    }
}

/// Options for a compilation unit.
#[derive(Clone, Default)]
pub struct UnitOptions {
    /// Package code: unresolved identifiers are late-bound intrinsics.
    pub package: bool,
    /// `eval` code: may `return` at top level, and may not assign these names.
    pub eval_readonly: Option<FxHashSet<Sym>>,
}

pub struct Compiler<'a> {
    scopes: Vec<Scope>,
    forwards: &'a FxHashSet<Sym>,
    opts: UnitOptions,
    src: &'a str,
    /// The position of the identifier being resolved (for errors about
    /// captured globals).
    cur_span: Span,
}

impl<'a> Compiler<'a> {
    pub fn new(forwards: &'a FxHashSet<Sym>, src: &'a str, opts: UnitOptions) -> Compiler<'a> {
        let mut top = Scope { top: true, ..Scope::default() };
        if let Some(ro) = &opts.eval_readonly {
            top.readonly = ro.clone();
            top.in_function = true;
        }
        Compiler { scopes: vec![top], forwards, opts, src, cur_span: Span::default() }
    }

    fn cur(&mut self) -> &mut Scope {
        self.scopes.last_mut().unwrap()
    }

    /// Compile top-level statements into a unit executed with a fresh frame.
    pub fn compile_unit(mut self, stmts: &[Stmt], span: Span) -> CResult<Rc<FuncCode>> {
        let body = self.block(stmts)?;
        let sc = self.scopes.pop().unwrap();
        Ok(Rc::new(FuncCode {
            name: None,
            params: Vec::new(),
            variadic: false,
            opt_params: Vec::new(),
            body: Body::Block(body),
            is_procedure: true,
            n_slots: sc.slot_names.len() as u32,
            local_inits: Vec::new(),
            capture_names: Vec::new(),
            slot_names: sc.slot_names,
            span,
            source: None,
        }))
    }

    /// Compile a lone expression (for `eval`).
    pub fn compile_expr_unit(mut self, e: &Expr) -> CResult<Rc<FuncCode>> {
        let ex = self.expr(e)?;
        let sc = self.scopes.pop().unwrap();
        Ok(Rc::new(FuncCode {
            name: None,
            params: Vec::new(),
            variadic: false,
            opt_params: Vec::new(),
            body: Body::Expr(ex),
            is_procedure: false,
            n_slots: sc.slot_names.len() as u32,
            local_inits: Vec::new(),
            capture_names: Vec::new(),
            slot_names: sc.slot_names,
            span: e.span,
            source: None,
        }))
    }

    // ----- name resolution ------------------------------------------------

    fn resolve(&mut self, name: Sym) -> Ex {
        let si = self.scopes.len() - 1;
        let sc = &self.scopes[si];
        if let Some(slot) = sc.lookup(name) {
            return Ex::Local(slot, name);
        }
        if sc.self_name == Some(name) {
            return Ex::SelfFn;
        }
        if sc.top || self.forwards.contains(&name) {
            return Ex::Global(name);
        }
        if let Some(&i) = sc.cap_index.get(&name) {
            return Ex::Capture(i, name);
        }
        let late = self.opts.package;
        let src = self.capture_source(si - 1, name, if late { Mode::Late } else { Mode::Strict });
        Ex::Capture(self.add_capture(si, name, src), name)
    }

    fn add_capture(&mut self, si: usize, name: Sym, src: CapSrc) -> u32 {
        let sc = &mut self.scopes[si];
        let i = sc.captures.len() as u32;
        sc.captures.push((name, src));
        sc.cap_index.insert(name, i);
        i
    }

    fn capture_source(&mut self, si: usize, name: Sym, mode: Mode) -> CapSrc {
        let sc = &self.scopes[si];
        if let Some(slot) = sc.lookup(name) {
            return CapSrc::Local(slot);
        }
        if sc.self_name == Some(name) {
            return CapSrc::SelfFn;
        }
        if sc.top || self.forwards.contains(&name) {
            return match mode {
                Mode::Strict => CapSrc::Global(name, self.cur_span),
                Mode::Late => CapSrc::GlobalLate(name),
                Mode::Init => CapSrc::GlobalInit(name),
            };
        }
        if let Some(&i) = sc.cap_index.get(&name) {
            return CapSrc::Capture(i);
        }
        let src = self.capture_source(si - 1, name, mode);
        CapSrc::Capture(self.add_capture(si, name, src))
    }

    fn place(&mut self, name: Sym, span: Span) -> CResult<Place> {
        let sc = self.cur();
        if sc.readonly.contains(&name) {
            return cerr(span, format!("Imported environment value '{name}' cannot be used as a local"));
        }
        if let Some(slot) = sc.lookup(name) {
            return Ok(Place::Local(slot, name));
        }
        if sc.top {
            return Ok(Place::Global(name));
        }
        let slot = sc.new_slot(name);
        sc.locals.insert(name, slot);
        Ok(Place::Local(slot, name))
    }

    /// Bind a fresh slot for a block-scoped name (loop or `where` variable).
    fn bind(&mut self, name: Sym) -> Slot {
        let sc = self.cur();
        let slot = sc.new_slot(name);
        sc.bindings.push((name, slot));
        slot
    }

    fn unbind(&mut self, n: usize) {
        let sc = self.cur();
        let len = sc.bindings.len();
        sc.bindings.truncate(len - n);
    }

    // ----- statements -----------------------------------------------------

    fn block(&mut self, stmts: &[Stmt]) -> CResult<Vec<S>> {
        let mut out = Vec::with_capacity(stmts.len());
        for s in stmts {
            out.push(self.stmt(s)?);
        }
        Ok(out)
    }

    fn stmt(&mut self, s: &Stmt) -> CResult<S> {
        let span = s.span;
        let kind = match &s.kind {
            StmtKind::Empty => St::Nop,
            StmtKind::Expr(es, level) => {
                let level = level.as_deref().map(Sym::new);
                if es.len() == 1 {
                    if let ExprKind::Call(f, args, params) = &es[0].kind {
                        let c = self.call(f, args, params, true)?;
                        // Errors in the call are reported at its bracket.
                        return Ok(S { kind: St::CallStmt(Box::new(c), level), span: es[0].err_span() });
                    }
                }
                St::Print(self.expr_list(es)?, level)
            }
            StmtKind::Print(es, level) => St::Print(self.expr_list(es)?, level.as_deref().map(Sym::new)),
            StmtKind::Printf(es) => St::Printf(self.expr_list(es)?),
            StmtKind::Fprintf(f, es) => St::Fprintf(self.expr(f)?, self.expr_list(es)?),
            StmtKind::Vprint(flag, lvl, es) | StmtKind::Vprintf(flag, lvl, es) => {
                let is_printf = matches!(s.kind, StmtKind::Vprintf(..));
                let lvl = lvl.as_ref().map(|e| self.expr(e)).transpose()?;
                St::Vprint(Sym::new(flag), lvl, self.expr_list(es)?, is_printf)
            }
            StmtKind::Assign(lvs, value, at) => {
                let v = self.expr(value)?;
                let mut targets = Vec::new();
                for lv in lvs {
                    targets.push(self.lvalue(lv)?);
                }
                St::Assign(targets, v, *at)
            }
            StmtKind::OpAssign(lv, op, value, at) => {
                let v = self.expr(value)?;
                St::OpAssign(self.lvalue(lv)?, *op, v, *at)
            }
            StmtKind::GenAssign(lv, names, value) => {
                let v = self.expr(value)?;
                let target = self.lvalue(lv)?;
                let names = match names {
                    ast::GenNames::List(ns) => {
                        let mut out = Vec::new();
                        for (n, sp) in ns {
                            out.push((self.place(Sym::new(n), *sp)?, *sp));
                        }
                        GenNamesEx::List(out)
                    }
                    ast::GenNames::Seq(n, sp) => GenNamesEx::Seq(self.place(Sym::new(n), *sp)?, *sp),
                };
                St::GenAssign(target, names, v)
            }
            StmtKind::If(branches, else_) => {
                let mut bs = Vec::new();
                for (c, b) in branches {
                    bs.push((self.expr(c)?, self.block(b)?));
                }
                let e = else_.as_ref().map(|b| self.block(b)).transpose()?;
                St::If(bs, e)
            }
            StmtKind::Case(scrut, arms, else_) => {
                let sc = self.expr(scrut)?;
                let mut out = Vec::new();
                for (vals, b) in arms {
                    out.push((self.expr_list(vals)?, self.block(b)?));
                }
                let e = else_.as_ref().map(|b| self.block(b)).transpose()?;
                St::Case(sc, out, e)
            }
            StmtKind::For { index, var, kind, body } => return self.for_stmt(index, var, kind, body, span),
            StmtKind::While(c, b) => {
                let c = self.expr(c)?;
                self.cur().loops.push(Sym::new(""));
                let b = self.block(b);
                self.cur().loops.pop();
                St::While(c, b?)
            }
            StmtKind::Repeat(b, c) => {
                self.cur().loops.push(Sym::new(""));
                let b = self.block(b);
                self.cur().loops.pop();
                St::Repeat(b?, self.expr(c)?)
            }
            StmtKind::Break(label) | StmtKind::Continue(label) => {
                let is_break = matches!(s.kind, StmtKind::Break(_));
                let loops = &self.cur().loops;
                if loops.is_empty() {
                    return cerr(span, format!("'{}' is not inside a loop", if is_break { "break" } else { "continue" }));
                }
                let label = label.as_deref().map(Sym::new);
                if let Some(l) = label {
                    if !loops.contains(&l) {
                        return cerr(span, format!("There is no enclosing loop with variable '{l}'"));
                    }
                }
                if is_break { St::Break(label) } else { St::Continue(label) }
            }
            StmtKind::Return(es) => {
                if !self.cur().in_function {
                    return cerr(span, "'return' is not inside a function or procedure");
                }
                let mut v = Vec::new();
                for e in es {
                    v.push(self.expr(e)?);
                }
                St::Return(v)
            }
            StmtKind::FuncDef(name, def) => {
                let sym = Sym::new(name);
                let clo = self.function(def, Some(sym))?;
                let place = self.place(sym, span)?;
                St::Assign(vec![LV::Var(place, span)], clo, span)
            }
            StmtKind::Intrinsic(def) => St::Intrinsic(self.intrinsic(def)?),
            StmtKind::Forward(names) => {
                if !self.cur().top {
                    return cerr(span, "'forward' must be used at the top level");
                }
                St::Forward(names.iter().map(|n| Sym::new(&n.0)).collect())
            }
            StmtKind::Local(names) => {
                for (n, sp) in names {
                    let sym = Sym::new(n);
                    let sc = self.cur();
                    if sc.top {
                        return cerr(*sp, "'local' must be used inside a function or procedure");
                    }
                    if !sc.locals.contains_key(&sym) {
                        let slot = sc.new_slot(sym);
                        sc.locals.insert(sym, slot);
                    }
                }
                St::Nop
            }
            StmtKind::Delete(lv) => St::Delete(self.lvalue(lv)?),
            StmtKind::Error(cond, es) => {
                let c = cond.as_ref().map(|e| self.expr(e)).transpose()?;
                St::Error(c, self.expr_list(es)?)
            }
            StmtKind::Assert(level, e) => St::Assert(*level, self.expr(e)?),
            StmtKind::Require(..) | StmtKind::RequireRange(..) | StmtKind::RequireGe(..) if !self.cur().in_intrinsic => {
                return cerr(span, "Require statements only allowed in intrinsics".to_string());
            }
            StmtKind::Require(c, es) => St::Require(self.expr(c)?, self.expr_list(es)?),
            StmtKind::RequireRange(v, lo, hi) => {
                let sym = Sym::new(v);
                let ve = E { kind: self.resolve(sym), span };
                St::RequireRange(ve, self.expr(lo)?, self.expr(hi)?, sym)
            }
            StmtKind::RequireGe(v, lo) => {
                let sym = Sym::new(v);
                let ve = E { kind: self.resolve(sym), span };
                St::RequireGe(ve, self.expr(lo)?, sym)
            }
            StmtKind::Try(body, var, handler) => {
                let b = self.block(body)?;
                let p = var.as_ref().map(|(n, sp)| self.place(Sym::new(n), *sp)).transpose()?;
                St::Try(b, p, self.block(handler)?)
            }
            StmtKind::Time(s) => St::Time(Box::new(self.stmt(s)?)),
            StmtKind::Vtime(flag, lvl, s) => {
                let lvl = lvl.as_ref().map(|e| self.expr(e)).transpose()?;
                St::Vtime(Sym::new(flag), lvl, Box::new(self.stmt(s)?))
            }
            StmtKind::Load(e, i) => St::Load(self.expr(e)?, *i),
            StmtKind::Import(f, names) => {
                let fe = self.expr(f)?;
                let mut out = Vec::new();
                for (n, sp) in names {
                    let sym = Sym::new(n);
                    out.push((sym, self.place(sym, *sp)?));
                }
                St::Import(fe, out)
            }
            StmtKind::Freeze => St::Freeze,
            StmtKind::DeclareType(n, e, ps) => {
                St::DeclareType(Sym::new(n), e.as_deref().map(Sym::new), ps.iter().map(|p| Sym::new(p)).collect())
            }
            StmtKind::DeclareAttributes(c, ns) => St::DeclareAttributes(Sym::new(c), ns.iter().map(|n| Sym::new(n)).collect()),
            StmtKind::DeclareVerbose(n, e) => St::DeclareVerbose(Sym::new(n), self.expr(e)?),
            StmtKind::Read(lv, prompt, int) => {
                let p = prompt.as_ref().map(|e| self.expr(e)).transpose()?;
                St::Read(self.lvalue(lv)?, p, *int)
            }
            StmtKind::Quit(e) => St::Quit(e.as_ref().map(|e| self.expr(e)).transpose()?),
            StmtKind::Clear => St::Clear,
            StmtKind::Save(e) => St::Save(self.expr(e)?),
            StmtKind::Restore(e) => St::Restore(self.expr(e)?),
        };
        Ok(S { kind, span })
    }

    fn for_stmt(&mut self, index: &Option<(String, Span)>, var: &(String, Span), kind: &ast::ForKind, body: &[Stmt], span: Span) -> CResult<S> {
        let vsym = Sym::new(&var.0);
        match kind {
            ast::ForKind::Range(a, b, c) => {
                let from = self.expr(a)?;
                let to = self.expr(b)?;
                let by = c.as_ref().map(|c| self.expr(c)).transpose()?;
                let slot = self.bind(vsym);
                self.cur().loops.push(vsym);
                let body = self.block(body);
                self.cur().loops.pop();
                self.unbind(1);
                Ok(S { kind: St::ForRange { var: Place::Local(slot, vsym), from, to, by, body: body? }, span })
            }
            ast::ForKind::In(dom) | ast::ForKind::Random(dom) => {
                let random = matches!(kind, ast::ForKind::Random(_));
                let domain = self.domain(dom)?;
                let mut n = 0;
                let index = match index {
                    Some((i, _)) => {
                        let isym = Sym::new(i);
                        n += 1;
                        Some(Place::Local(self.bind(isym), isym))
                    }
                    None => None,
                };
                let slot = self.bind(vsym);
                n += 1;
                self.cur().loops.push(vsym);
                let body = self.block(body);
                self.cur().loops.pop();
                self.unbind(n);
                Ok(S { kind: St::ForIn { var: Place::Local(slot, vsym), index, domain, random, body: body?, var_span: var.1 }, span })
            }
        }
    }

    fn domain(&mut self, e: &Expr) -> CResult<DomainEx> {
        if let ExprKind::Aggregate(ast::AggKind::Seq, None, AggBody::Range(a, b, c)) = &e.kind {
            let a = self.expr(a)?;
            let b = self.expr(b)?;
            let c = c.as_ref().map(|c| self.expr(c)).transpose()?;
            return Ok(DomainEx::Range(a, b, c));
        }
        Ok(DomainEx::General(self.expr(e)?))
    }

    fn lvalue(&mut self, lv: &LValue) -> CResult<LV> {
        Ok(match lv {
            LValue::Ident(n, sp) => LV::Var(self.place(Sym::new(n), *sp)?, *sp),
            LValue::Underscore(_) => LV::Discard,
            LValue::Index(b, idx, sp) => {
                let base = self.lvalue(b)?;
                LV::Index(Box::new(base), self.expr_list(idx)?, *sp)
            }
            LValue::Attr(b, n, sp) => LV::Attr(Box::new(self.lvalue(b)?), Sym::new(n), *sp),
            LValue::AttrDyn(b, e, sp) => {
                let base = self.lvalue(b)?;
                LV::AttrDyn(Box::new(base), self.expr(e)?, *sp)
            }
        })
    }

    // ----- functions ------------------------------------------------------

    /// Compile a function or procedure expression into a closure constructor.
    fn function(&mut self, def: &FuncDef, self_name: Option<Sym>) -> CResult<E> {
        let (code, caps) = self.function_code(def, self_name, false)?;
        Ok(E { kind: Ex::Closure(code, caps), span: def.span })
    }

    fn function_code(&mut self, def: &FuncDef, self_name: Option<Sym>, intrinsic: bool) -> CResult<(Rc<FuncCode>, Rc<[CapSrc]>)> {
        let mut sc = Scope { in_function: true, in_intrinsic: intrinsic, self_name, ..Scope::default() };
        let mut params = Vec::new();
        for p in &def.params {
            let sym = Sym::new(&p.name);
            let slot = sc.new_slot(sym);
            sc.locals.insert(sym, slot);
            params.push(ParamSpec { slot, name: sym, is_ref: p.is_ref });
        }
        let mut opt_slots = Vec::new();
        for (n, _) in &def.opt_params {
            let sym = Sym::new(n);
            let slot = sc.new_slot(sym);
            sc.locals.insert(sym, slot);
            opt_slots.push((sym, slot));
        }
        // Identifiers assigned anywhere in the body are locals.
        let mut assigned = Vec::new();
        match &def.body {
            FuncBody::Block(b) => scan_block(b, &mut assigned),
            FuncBody::Expr(e) => scan_expr(e, &mut assigned),
        }
        let mut fresh_locals = Vec::new();
        for name in assigned {
            let sym = Sym::new(&name);
            if !sc.locals.contains_key(&sym) {
                let slot = sc.new_slot(sym);
                sc.locals.insert(sym, slot);
                fresh_locals.push((sym, slot));
            }
        }
        self.scopes.push(sc);
        let si = self.scopes.len() - 1;

        // Locals start with the value of the same name outside, if any.
        let mut local_inits = Vec::new();
        for (sym, slot) in fresh_locals {
            if self.scopes[si].self_name == Some(sym) {
                continue;
            }
            let src = self.capture_source(si - 1, sym, Mode::Init);
            let i = self.add_capture(si, sym, src);
            local_inits.push((slot, i));
        }

        let result = (|| -> CResult<_> {
            let mut opts = Vec::new();
            for ((sym, slot), (_, e)) in opt_slots.iter().zip(&def.opt_params) {
                opts.push((*sym, *slot, self.expr(e)?));
            }
            let body = match &def.body {
                FuncBody::Block(b) => Body::Block(self.block(b)?),
                FuncBody::Expr(e) => {
                    if def.is_procedure {
                        // proc< x | P(~x) >: the body is a single call.
                        let st = self.stmt(&Stmt { kind: StmtKind::Expr(vec![(**e).clone()], None), span: e.span })?;
                        Body::Block(vec![st])
                    } else {
                        Body::Expr(self.expr(e)?)
                    }
                }
            };
            Ok((opts, body))
        })();
        let sc = self.scopes.pop().unwrap();
        let (opt_params, body) = result?;
        let caps: Rc<[CapSrc]> = sc.captures.iter().map(|c| c.1.clone()).collect();
        let source = self.src.get(def.span.lo as usize..def.span.hi as usize).map(Rc::from);
        let code = FuncCode {
            name: def.name.as_deref().map(Sym::new),
            params,
            variadic: def.variadic,
            opt_params,
            body,
            is_procedure: def.is_procedure,
            n_slots: sc.slot_names.len() as u32,
            local_inits,
            capture_names: sc.captures.iter().map(|c| c.0).collect(),
            slot_names: sc.slot_names,
            span: def.span,
            source,
        };
        Ok((Rc::new(code), caps))
    }

    /// Compile `params | body` as a function (for map rules and predicates).
    fn lambda(&mut self, params: &[&str], body: &Expr) -> CResult<E> {
        let def = FuncDef {
            name: None,
            params: params.iter().map(|p| ast::Param { name: p.to_string(), is_ref: false, span: body.span }).collect(),
            variadic: false,
            opt_params: Vec::new(),
            body: FuncBody::Expr(Box::new(body.clone())),
            is_procedure: false,
            span: body.span,
        };
        self.function(&def, None)
    }

    fn intrinsic(&mut self, def: &ast::IntrinsicDef) -> CResult<Rc<IntrinsicDefIR>> {
        let fdef = FuncDef {
            name: Some(def.name.clone()),
            params: def.args.iter().map(|a| ast::Param { name: a.name.clone(), is_ref: a.is_ref, span: a.span }).collect(),
            variadic: def.variadic,
            opt_params: def.opt_params.clone(),
            body: FuncBody::Block(def.body.clone()),
            is_procedure: def.returns.is_none(),
            span: def.span,
        };
        // Free identifiers in intrinsics are late-bound.
        let saved = self.opts.package;
        self.opts.package = true;
        let r = self.function_code(&fdef, None, true);
        self.opts.package = saved;
        let (code, captures) = r?;
        Ok(Rc::new(IntrinsicDefIR {
            name: Sym::new(&def.name),
            arg_types: def.args.iter().map(|a| (a.ty.clone(), a.is_ref)).collect(),
            returns: def.returns.clone(),
            doc: Rc::from(def.doc.as_str()),
            code,
            captures,
            span: def.span,
        }))
    }

    // ----- expressions ----------------------------------------------------

    /// Compile an expression list, where a `where` clause also scopes over
    /// the expressions to its left.
    fn expr_list(&mut self, es: &[Expr]) -> CResult<Vec<E>> {
        let mut out = Vec::with_capacity(es.len());
        for (i, e) in es.iter().enumerate() {
            // Where-chains to the right of this element, nearest last.
            let mut chains: Vec<&Expr> = Vec::new();
            for later in es[i + 1..].iter().rev() {
                if matches!(later.kind, ExprKind::Where(..)) {
                    chains.push(later);
                }
            }
            let mut bindings: Vec<(&[String], &Expr)> = Vec::new();
            for c in &chains {
                let mut b = Vec::new();
                let mut cur = *c;
                while let ExprKind::Where(inner, n, v) = &cur.kind {
                    b.push((n.as_slice(), &**v));
                    cur = inner;
                }
                // Outermost binding first.
                bindings.extend(b);
            }
            if bindings.is_empty() {
                out.push(self.expr(e)?);
                continue;
            }
            let mut slots = Vec::new();
            let mut values = Vec::new();
            let mut nbound = 0;
            for (names, v) in &bindings {
                values.push(self.expr(v)?);
                slots.push(names.iter().map(|n| self.bind(Sym::new(n))).collect::<Vec<_>>());
                nbound += names.len();
            }
            let body = self.expr(e);
            self.unbind(nbound);
            let mut ex = body?;
            for (s, v) in slots.into_iter().zip(values).rev() {
                let span = ex.span;
                let kind = if s.len() == 1 { Ex::Let(s[0], Box::new(v), Box::new(ex)) } else { Ex::LetMulti(s, Box::new(v), Box::new(ex)) };
                ex = E { kind, span };
            }
            out.push(ex);
        }
        Ok(out)
    }

    fn bx(&mut self, e: &Expr) -> CResult<Box<E>> {
        Ok(Box::new(self.expr(e)?))
    }

    pub fn expr(&mut self, e: &Expr) -> CResult<E> {
        let span = e.err_span();
        let kind = match &e.kind {
            ExprKind::Int(s) => Ex::Const(parse_int_literal(s).ok_or_else(|| CompileError { message: format!("bad integer literal '{s}'"), span })?),
            ExprKind::Real(s) => Ex::Constructor(Sym::new("__real_literal"), vec![E { kind: Ex::Const(Value::str(s)), span }], None),
            ExprKind::Str(s) => Ex::Const(Value::str(s)),
            ExprKind::Bool(b) => Ex::Const(Value::Bool(*b)),
            ExprKind::Ident(n) => {
                self.cur_span = span;
                self.resolve(Sym::new(n))
            }
            ExprKind::Previous(n) => Ex::Previous(*n),
            ExprKind::SelfRef => {
                if !self.cur().in_function || self.cur().top {
                    return cerr(span, "'$$' is not inside a function");
                }
                Ex::SelfFn
            }
            ExprKind::Underscore => Ex::Undef,
            ExprKind::Paren(inner) => return self.expr(inner),
            ExprKind::Unary(op, a) => {
                let a = self.bx(a)?;
                match op {
                    UnOp::Neg => Ex::Neg(a),
                    UnOp::Plus => return Ok(*a),
                    UnOp::Not => Ex::Not(a),
                    UnOp::Card => Ex::Card(a),
                }
            }
            ExprKind::Binary(op, a, b) => {
                let a = self.bx(a)?;
                let b = self.bx(b)?;
                match op {
                    BinOp::And => Ex::And(a, b),
                    BinOp::Or => Ex::Or(a, b),
                    _ => Ex::Bin(*op, a, b),
                }
            }
            ExprKind::Select(c, a, b) => Ex::Select(self.bx(c)?, self.bx(a)?, self.bx(b)?),
            ExprKind::Call(f, args, params) => {
                // `Self(i)` inside a sequence constructor.
                if let ExprKind::Ident(n) = &f.kind {
                    if n == "Self" && self.cur().seq_compr > 0 && args.len() <= 1 && self.cur().lookup(Sym::new("Self")).is_none() {
                        match args.first() {
                            Some(Arg::Value(a)) => return Ok(E { kind: Ex::SelfSeq(self.bx(a)?), span }),
                            None => return Ok(E { kind: Ex::SelfSeq(Box::new(E { kind: Ex::Undef, span })), span }),
                            _ => {}
                        }
                    }
                }
                Ex::Call(Box::new(self.call(f, args, params, false)?))
            }
            ExprKind::Index(a, idx) => Ex::Index(self.bx(a)?, self.expr_list(idx)?),
            ExprKind::Dot(a, b) => {
                // `S.x` with x an identifier that is not a variable means the
                // generator named x; we only support integer expressions here.
                Ex::Dot(self.bx(a)?, self.bx(b)?)
            }
            ExprKind::Attr(a, n) => Ex::Attr(self.bx(a)?, Sym::new(n)),
            ExprKind::AttrDyn(a, n) => Ex::AttrDyn(self.bx(a)?, self.bx(n)?),
            ExprKind::Coerce(a, b, d) => Ex::Coerce(self.bx(a)?, self.bx(b)?, *d),
            ExprKind::Image(a, b) => Ex::Image(self.bx(a)?, self.bx(b)?),
            ExprKind::Preimage(a, b) => Ex::Preimage(self.bx(a)?, self.bx(b)?),
            ExprKind::Reduce(op, a) => Ex::Reduce(*op, self.bx(a)?),
            ExprKind::Assigned(a) => {
                let target = match &a.kind {
                    ExprKind::Ident(_) | ExprKind::Paren(_) => AssignedEx::Var(self.expr(a)?),
                    ExprKind::Attr(b, n) => AssignedEx::Attr(self.expr(b)?, Sym::new(n)),
                    ExprKind::AttrDyn(b, n) => AssignedEx::AttrDyn(self.expr(b)?, self.expr(n)?),
                    ExprKind::Index(b, idx) => AssignedEx::Index(self.expr(b)?, self.expr_list(idx)?),
                    _ => return cerr(span, "bad syntax: 'assigned' needs an identifier or attribute"),
                };
                Ex::Assigned(Box::new(target))
            }
            ExprKind::Eval(a) => Ex::Eval(self.bx(a)?),
            ExprKind::Where(body, names, v) => {
                let value = self.bx(v)?;
                let slots: Vec<Slot> = names.iter().map(|n| self.bind(Sym::new(n))).collect();
                let b = self.bx(body);
                self.unbind(slots.len());
                if slots.len() == 1 { Ex::Let(slots[0], value, b?) } else { Ex::LetMulti(slots, value, b?) }
            }
            ExprKind::Multiplicity(a, b) => Ex::Multiplicity(self.bx(a)?, self.bx(b)?),
            ExprKind::Tuple(es) => Ex::Tuple(self.expr_list(es)?),
            ExprKind::TupleCompr(c) => Ex::TupleCompr(Box::new(self.comprehension(c, false)?)),
            ExprKind::Aggregate(kind, universe, body) => {
                if let (ast::AggKind::Seq, None, AggBody::Enum(es)) = (kind, universe, body) {
                    check_literal_universe(es)?;
                }
                let universe = universe.as_ref().map(|u| self.expr(u)).transpose()?;
                let body = match body {
                    AggBody::Empty => AggBodyEx::Empty,
                    AggBody::Enum(es) => AggBodyEx::Enum(self.expr_list(es)?),
                    AggBody::Range(a, b, c) => {
                        let c = c.as_ref().map(|c| self.expr(c)).transpose()?;
                        AggBodyEx::Range(self.expr(a)?, self.expr(b)?, c)
                    }
                    AggBody::Compr(c) => AggBodyEx::Compr(self.comprehension(c, *kind == ast::AggKind::Seq)?),
                };
                Ex::Agg(Box::new(AggEx { kind: *kind, universe, body }))
            }
            ExprKind::List(es) => Ex::List(self.expr_list(es)?),
            ExprKind::Formal(kind, _universe, var, dom, pred) => {
                let d = self.bx(dom)?;
                let p = match pred {
                    Some(p) => Some(Box::new(self.lambda(&[var.as_str()], p)?)),
                    None => None,
                };
                Ex::Formal(*kind == ast::FormalKind::Seq, d, p)
            }
            ExprKind::Quantifier(q, witnesses, c) => {
                let compr = self.comprehension(c, false)?;
                let mut ws = Vec::new();
                for w in witnesses {
                    ws.push(LV::Var(self.place(Sym::new(w), span)?, span));
                }
                Ex::Quant(Box::new(QuantEx { kind: *q, witnesses: ws, compr }))
            }
            ExprKind::Function(def) => return self.function(def, None),
            ExprKind::Map(kind, dom, cod, body) => {
                let domain = self.expr(dom)?;
                let codomain = self.expr(cod)?;
                let body = match body {
                    ast::MapBody::Rule(x, img, inv) => {
                        let f = self.lambda(&[x.as_str()], img)?;
                        let g = match inv {
                            Some((y, e)) => Some(self.lambda(&[y.as_str()], e)?),
                            None => None,
                        };
                        MapBodyEx::Rule(f, g)
                    }
                    ast::MapBody::Exprs(es) => MapBodyEx::Exprs(self.expr_list(es)?),
                };
                Ex::Map(Box::new(MapEx { kind: *kind, domain, codomain, body }))
            }
            ExprKind::Rec(fmt, fields) => {
                let f = self.bx(fmt)?;
                let mut out = Vec::new();
                for (n, v) in fields {
                    out.push((Sym::new(n), self.expr(v)?));
                }
                Ex::Rec(f, out)
            }
            ExprKind::RecFormat(fields) => {
                let mut out = Vec::new();
                for (n, t) in fields {
                    out.push((Sym::new(n), t.as_ref().map(|t| self.expr(t)).transpose()?));
                }
                Ex::RecFormat(out)
            }
            ExprKind::Car(es) => Ex::Car(self.expr_list(es)?),
            ExprKind::Cop(es) => Ex::Cop(self.expr_list(es)?),
            ExprKind::Elt(p, es) => Ex::Elt(self.bx(p)?, self.expr_list(es)?),
            ExprKind::Case(s, arms, d) => {
                let s = self.bx(s)?;
                let mut out = Vec::new();
                for (l, r) in arms {
                    out.push((self.expr(l)?, self.expr(r)?));
                }
                Ex::Case(s, out, self.bx(d)?)
            }
            ExprKind::Constructor(n, l, r) => {
                let l = self.expr_list(l)?;
                let r = r.as_ref().map(|r| self.expr_list(r)).transpose()?;
                Ex::Constructor(Sym::new(n), l, r)
            }
        };
        Ok(E { kind, span })
    }

    fn call(&mut self, f: &Expr, args: &[Arg], params: &[ast::ParamArg], _stmt: bool) -> CResult<CallEx> {
        let func = self.expr(f)?;
        let mut cargs = Vec::with_capacity(args.len());
        let values: Vec<Expr> = args
            .iter()
            .filter_map(|a| match a {
                Arg::Value(e) => Some(e.clone()),
                Arg::Ref(..) => None,
            })
            .collect();
        let has_where = values.iter().any(|e| matches!(e.kind, ExprKind::Where(..)));
        let mut compiled_values = if has_where { self.expr_list(&values)?.into_iter() } else { Vec::new().into_iter() };
        for a in args {
            match a {
                Arg::Value(e) => {
                    let ce = if has_where { compiled_values.next().unwrap() } else { self.expr(e)? };
                    cargs.push(CArg::Val(ce));
                }
                Arg::Ref(lv, sp) => cargs.push(CArg::Ref(self.lvalue(lv)?, *sp)),
            }
        }
        let mut ps = Vec::new();
        for p in params {
            ps.push((Sym::new(&p.name), self.expr(&p.value)?));
        }
        Ok(CallEx { func, args: cargs, params: ps, site: Default::default() })
    }

    fn comprehension(&mut self, c: &ast::Comprehension, is_seq: bool) -> CResult<ComprEx> {
        let mut iters = Vec::new();
        let mut nbound = 0;
        let result = (|| -> CResult<ComprEx> {
            // The last iterator is the outermost loop, so the domain of an
            // iterator may use the variables of the iterators after it.
            for it in c.iters.iter().rev() {
                let domain = self.domain(&it.domain)?;
                let index = match &it.index {
                    Some(i) => {
                        nbound += 1;
                        Some(self.bind(Sym::new(i)))
                    }
                    None => None,
                };
                nbound += 1;
                let var = self.bind(Sym::new(&it.var));
                iters.push(IterEx { var, index, domain, span: it.span });
            }
            iters.reverse();
            // `where` clauses in an unparenthesised predicate scope over the head.
            let mut lets = Vec::new();
            let mut pred = None;
            if let Some(p) = &c.pred {
                let mut chain = Vec::new();
                let mut cur: &Expr = p;
                while let ExprKind::Where(inner, n, v) = &cur.kind {
                    chain.push((n, &**v));
                    cur = inner;
                }
                for (names, v) in chain {
                    let ve = self.expr(v)?;
                    nbound += names.len();
                    lets.push((names.iter().map(|n| self.bind(Sym::new(n))).collect(), ve));
                }
                pred = Some(self.expr(cur)?);
            }
            if is_seq {
                self.cur().seq_compr += 1;
            }
            let head = self.expr(&c.head);
            if is_seq {
                self.cur().seq_compr -= 1;
            }
            Ok(ComprEx { head: head?, iters: std::mem::take(&mut iters), lets, pred })
        })();
        self.unbind(nbound);
        result
    }
}

#[derive(Clone, Copy)]
enum Mode {
    Strict,
    Late,
    Init,
}

pub fn parse_int_literal(s: &str) -> Option<Value> {
    use calyx_flint::Integer;
    if let Some(h) = s.strip_prefix("0x") {
        return Integer::parse_radix(h, 16).map(Value::Int);
    }
    Integer::parse(s).map(Value::Int)
}

// ----- scanning for assigned identifiers ------------------------------------

fn push_unique(out: &mut Vec<String>, n: &str) {
    if !out.iter().any(|x| x == n) {
        out.push(n.to_string());
    }
}

fn scan_lvalue(lv: &LValue, out: &mut Vec<String>) {
    if let Some(r) = lv.root() {
        push_unique(out, r);
    }
    if let LValue::Index(b, idx, _) = lv {
        scan_lvalue(b, out);
        for e in idx {
            scan_expr(e, out);
        }
    }
}

fn scan_block(b: &[Stmt], out: &mut Vec<String>) {
    for s in b {
        scan_stmt(s, out);
    }
}

fn scan_stmt(s: &Stmt, out: &mut Vec<String>) {
    match &s.kind {
        StmtKind::Expr(es, _) | StmtKind::Print(es, _) | StmtKind::Printf(es) | StmtKind::Return(es) => es.iter().for_each(|e| scan_expr(e, out)),
        StmtKind::Fprintf(f, es) => {
            scan_expr(f, out);
            es.iter().for_each(|e| scan_expr(e, out));
        }
        StmtKind::Vprint(_, l, es) | StmtKind::Vprintf(_, l, es) => {
            l.iter().for_each(|e| scan_expr(e, out));
            es.iter().for_each(|e| scan_expr(e, out));
        }
        StmtKind::Assign(lvs, v, _) => {
            scan_expr(v, out);
            lvs.iter().for_each(|lv| scan_lvalue(lv, out));
        }
        StmtKind::OpAssign(lv, _, v, _) => {
            scan_expr(v, out);
            scan_lvalue(lv, out);
        }
        StmtKind::GenAssign(lv, names, v) => {
            scan_expr(v, out);
            scan_lvalue(lv, out);
            match names {
                ast::GenNames::List(ns) => ns.iter().for_each(|n| push_unique(out, &n.0)),
                ast::GenNames::Seq(n, _) => push_unique(out, n),
            }
        }
        StmtKind::If(bs, e) => {
            for (c, b) in bs {
                scan_expr(c, out);
                scan_block(b, out);
            }
            if let Some(e) = e {
                scan_block(e, out);
            }
        }
        StmtKind::Case(sc, arms, e) => {
            scan_expr(sc, out);
            for (vs, b) in arms {
                vs.iter().for_each(|v| scan_expr(v, out));
                scan_block(b, out);
            }
            if let Some(e) = e {
                scan_block(e, out);
            }
        }
        StmtKind::For { kind, body, .. } => {
            match kind {
                ast::ForKind::Range(a, b, c) => {
                    scan_expr(a, out);
                    scan_expr(b, out);
                    c.iter().for_each(|c| scan_expr(c, out));
                }
                ast::ForKind::In(d) | ast::ForKind::Random(d) => scan_expr(d, out),
            }
            scan_block(body, out);
        }
        StmtKind::While(c, b) | StmtKind::Repeat(b, c) => {
            scan_expr(c, out);
            scan_block(b, out);
        }
        StmtKind::FuncDef(name, _) => push_unique(out, name),
        StmtKind::Local(ns) => ns.iter().for_each(|n| push_unique(out, &n.0)),
        StmtKind::Delete(lv) => scan_lvalue(lv, out),
        StmtKind::Error(c, es) => {
            c.iter().for_each(|e| scan_expr(e, out));
            es.iter().for_each(|e| scan_expr(e, out));
        }
        StmtKind::Assert(_, e) => scan_expr(e, out),
        StmtKind::Require(c, es) => {
            scan_expr(c, out);
            es.iter().for_each(|e| scan_expr(e, out));
        }
        StmtKind::Try(b, v, h) => {
            scan_block(b, out);
            if let Some((n, _)) = v {
                push_unique(out, n);
            }
            scan_block(h, out);
        }
        StmtKind::Time(s) | StmtKind::Vtime(_, _, s) => scan_stmt(s, out),
        StmtKind::Import(_, ns) => ns.iter().for_each(|n| push_unique(out, &n.0)),
        StmtKind::Read(lv, _, _) => scan_lvalue(lv, out),
        _ => {}
    }
}

/// Find reference arguments and quantifier witnesses inside an expression
/// (not descending into nested function bodies).
fn scan_expr(e: &Expr, out: &mut Vec<String>) {
    match &e.kind {
        ExprKind::Call(f, args, params) => {
            scan_expr(f, out);
            for a in args {
                match a {
                    Arg::Value(v) => scan_expr(v, out),
                    Arg::Ref(lv, _) => scan_lvalue(lv, out),
                }
            }
            params.iter().for_each(|p| scan_expr(&p.value, out));
        }
        ExprKind::Quantifier(_, ws, c) => {
            ws.iter().for_each(|w| push_unique(out, w));
            scan_compr(c, out);
        }
        ExprKind::TupleCompr(c) => scan_compr(c, out),
        ExprKind::Paren(a)
        | ExprKind::Unary(_, a)
        | ExprKind::Attr(a, _)
        | ExprKind::Reduce(_, a)
        | ExprKind::Assigned(a)
        | ExprKind::Eval(a) => scan_expr(a, out),
        ExprKind::Binary(_, a, b)
        | ExprKind::Dot(a, b)
        | ExprKind::AttrDyn(a, b)
        | ExprKind::Coerce(a, b, _)
        | ExprKind::Image(a, b)
        | ExprKind::Preimage(a, b)
        | ExprKind::Multiplicity(a, b) => {
            scan_expr(a, out);
            scan_expr(b, out);
        }
        ExprKind::Where(a, _, b) => {
            scan_expr(a, out);
            scan_expr(b, out);
        }
        ExprKind::Select(a, b, c) => {
            scan_expr(a, out);
            scan_expr(b, out);
            scan_expr(c, out);
        }
        ExprKind::Index(a, es) => {
            scan_expr(a, out);
            es.iter().for_each(|e| scan_expr(e, out));
        }
        ExprKind::Tuple(es) | ExprKind::List(es) | ExprKind::Car(es) | ExprKind::Cop(es) => es.iter().for_each(|e| scan_expr(e, out)),
        ExprKind::Aggregate(_, u, body) => {
            u.iter().for_each(|u| scan_expr(u, out));
            match body {
                AggBody::Empty => {}
                AggBody::Enum(es) => es.iter().for_each(|e| scan_expr(e, out)),
                AggBody::Range(a, b, c) => {
                    scan_expr(a, out);
                    scan_expr(b, out);
                    c.iter().for_each(|c| scan_expr(c, out));
                }
                AggBody::Compr(c) => scan_compr(c, out),
            }
        }
        ExprKind::Formal(_, u, _, d, p) => {
            u.iter().for_each(|u| scan_expr(u, out));
            scan_expr(d, out);
            p.iter().for_each(|p| scan_expr(p, out));
        }
        ExprKind::Map(_, a, b, _) => {
            scan_expr(a, out);
            scan_expr(b, out);
        }
        ExprKind::Rec(f, fields) => {
            scan_expr(f, out);
            fields.iter().for_each(|(_, v)| scan_expr(v, out));
        }
        ExprKind::Elt(p, es) => {
            scan_expr(p, out);
            es.iter().for_each(|e| scan_expr(e, out));
        }
        ExprKind::Case(s, arms, d) => {
            scan_expr(s, out);
            for (l, r) in arms {
                scan_expr(l, out);
                scan_expr(r, out);
            }
            scan_expr(d, out);
        }
        ExprKind::Constructor(_, l, r) => {
            l.iter().for_each(|e| scan_expr(e, out));
            r.iter().flatten().for_each(|e| scan_expr(e, out));
        }
        _ => {}
    }
}

fn scan_compr(c: &ast::Comprehension, out: &mut Vec<String>) {
    scan_expr(&c.head, out);
    for it in &c.iters {
        scan_expr(&it.domain, out);
    }
    if let Some(p) = &c.pred {
        scan_expr(p, out);
    }
}
