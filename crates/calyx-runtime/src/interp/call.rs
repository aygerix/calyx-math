//! Calling user functions, procedures and intrinsics.

use std::rc::Rc;

use calyx_syntax::Span;

use super::{Flow, Frame, Interp};
use crate::error::{ErrKind, RResult, RuntimeError, TraceFrame};
use crate::intrinsics::{Imp, SigCache, Signature, SiteKey};
use crate::ir::*;
use crate::sym::Sym;
use crate::value::*;

/// Arguments to an intrinsic call.
pub struct CallArgs {
    pub args: Vec<Value>,
    /// Named parameters, with defaults filled in, in signature order.
    pub params: Vec<(Sym, Value)>,
    pub nresults: usize,
    pub name: Sym,
    pub span: Span,
}

impl CallArgs {
    pub fn param(&self, name: &str) -> Option<&Value> {
        let s = Sym::new(name);
        self.params.iter().find(|p| p.0 == s).map(|p| &p.1)
    }
}

/// The reference mask of `n` value arguments.
fn value_mask(n: usize) -> std::borrow::Cow<'static, [bool]> {
    const NONE: [bool; 32] = [false; 32];
    if n <= NONE.len() { std::borrow::Cow::Borrowed(&NONE[..n]) } else { std::borrow::Cow::Owned(vec![false; n]) }
}

impl Interp {
    /// Evaluate a call expression. Returns `None` if a procedure was called.
    /// With `stmt` set, a procedure call is allowed.
    pub fn call_expr(&mut self, c: &CallEx, f: &mut Frame, nres: usize, stmt: bool, span: Span) -> RResult<Option<Vals>> {
        let func = self.eval(&c.func, f)?;
        let mut args = self.spare_vecs.pop().unwrap_or_default();
        let has_refs = c.args.iter().any(|a| matches!(a, CArg::Ref(..)));
        let mut refs: smallvec::SmallVec<[Option<super::assign::RefTarget>; 3]> = smallvec::SmallVec::new();
        // Evaluate value arguments first; take references afterwards so a
        // referenced variable is not shared while the callee modifies it.
        for a in &c.args {
            match a {
                CArg::Val(e) => {
                    let v = self.eval(e, f)?;
                    if v.is_undef() {
                        return Err(RuntimeError::user("Argument has no value").at(e.span));
                    }
                    args.push(v);
                }
                CArg::Ref(..) => args.push(Value::Undef),
            }
        }
        if has_refs {
            refs.resize_with(c.args.len(), || None);
        }
        for (i, a) in c.args.iter().enumerate() {
            if let CArg::Ref(lv, sp) = a {
                match self.take_ref(lv, f) {
                    Ok((t, v)) => {
                        args[i] = v;
                        refs[i] = Some(t);
                    }
                    Err(e) => {
                        let _ = self.restore_refs(&mut refs, &mut args, f);
                        return Err(e.at(*sp));
                    }
                }
            }
        }
        let mut params = Vec::with_capacity(c.params.len());
        for (n, e) in &c.params {
            params.push((*n, self.eval(e, f)?));
        }
        let mut buf = [false; 32];
        let mask: Vec<bool>;
        let refmask = if c.args.len() <= buf.len() {
            for (b, a) in buf.iter_mut().zip(&c.args) {
                *b = matches!(a, CArg::Ref(..));
            }
            &buf[..c.args.len()]
        } else {
            mask = c.args.iter().map(|a| matches!(a, CArg::Ref(..))).collect();
            &mask[..]
        };
        if has_refs && !stmt {
            self.restore_refs(&mut refs, &mut args, f)?;
            return Err(RuntimeError::runtime("Reference arguments may only be used in procedure calls"));
        }
        // Anonymous functions are named after the identifier they are called
        // through (for error reports).
        self.pending_call_name = match &c.func.kind {
            Ex::Global(n) | Ex::Local(_, n) | Ex::Capture(_, n) => Some(*n),
            _ => None,
        };
        let result = self.call_value_full(&func, &mut args, refmask, params, nres, stmt, span, Some(&c.site));
        // Write back reference arguments, even if the call failed.
        let wb = self.restore_refs(&mut refs, &mut args, f);
        self.recycle(args);
        let r = result?;
        wb?;
        Ok(r)
    }

    fn restore_refs(&mut self, refs: &mut [Option<super::assign::RefTarget>], args: &mut [Value], f: &mut Frame) -> RResult<()> {
        let mut first_err = None;
        for (i, r) in refs.iter_mut().enumerate() {
            if let Some(t) = r.take() {
                let v = std::mem::take(&mut args[i]);
                if let Err(e) = self.put_ref(t, v, f) {
                    first_err.get_or_insert(e);
                }
            }
        }
        match first_err {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }

    /// Call any callable value. `stmt` allows procedures (returns `None`).
    #[allow(clippy::too_many_arguments)]
    pub fn call_value_full(
        &mut self,
        func: &Value,
        args: &mut Vec<Value>,
        refmask: &[bool],
        params: Vec<(Sym, Value)>,
        nres: usize,
        stmt: bool,
        span: Span,
        site: Option<&SigCache>,
    ) -> RResult<Option<Vals>> {
        self.check_interrupt()?;
        let call_name = self.pending_call_name.take();
        match func {
            Value::Func(clo) => {
                if clo.code.is_procedure {
                    if !stmt {
                        return Err(RuntimeError::runtime("A procedure cannot be used as a function (it returns no value)"));
                    }
                } else if refmask.iter().any(|&b| b) {
                    return Err(RuntimeError::runtime("Functions cannot take reference arguments"));
                }
                let clo = clo.clone();
                let r = self.call_closure(&clo, args, refmask, params, nres, span, call_name)?;
                Ok(if clo.code.is_procedure { None } else { Some(r) })
            }
            Value::Intr(name) => self.call_intrinsic(*name, args, refmask, params, nres, stmt, span, site),
            Value::Map(_) => {
                if args.len() != 1 || !params.is_empty() {
                    return Err(RuntimeError::runtime("A map takes exactly one argument"));
                }
                let x = args[0].clone();
                Ok(Some(vals![self.image(&x, func)?]))
            }
            Value::Obj(_) => {
                // Objects of user types may be made callable via '()'? Not supported.
                Err(RuntimeError::runtime(format!("An object of type {} is not callable", self.type_name(func))))
            }
            // Magma reads `f(x)` as `x @ f`.
            other if args.len() == 1 && params.is_empty() => {
                let e = RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}, {}", self.type_name_ext(&args[0]), self.type_name_ext(other)));
                Err(if stmt { e.in_context("@") } else { e })
            }
            _ => {
                let msg = "Attempting to call something that is not callable";
                Err(if stmt { RuntimeError::statement("procedure call", msg) } else { RuntimeError::runtime(msg) })
            }
        }
    }

    /// Call a value as a function returning its principal value.
    pub fn call_function(&mut self, func: &Value, mut args: Vec<Value>) -> RResult<Value> {
        let mask = value_mask(args.len());
        let span = Span::default();
        match self.call_value_full(func, &mut args, &mask, Vec::new(), 1, false, span, None)? {
            Some(v) if !v.is_empty() => Ok(v.into_iter().next().unwrap()),
            _ => Err(RuntimeError::runtime("Function returned no value")),
        }
    }

    /// Call a value, returning all results.
    pub fn call_function_multi(&mut self, func: &Value, mut args: Vec<Value>, nres: usize) -> RResult<Vec<Value>> {
        let mask = value_mask(args.len());
        Ok(self.call_value_full(func, &mut args, &mask, Vec::new(), nres, false, Span::default(), None)?.map(Vals::into_vec).unwrap_or_default())
    }

    #[allow(clippy::too_many_arguments)]
    pub fn call_closure(
        &mut self,
        clo: &Rc<Closure>,
        args: &mut [Value],
        refmask: &[bool],
        params: Vec<(Sym, Value)>,
        nres: usize,
        span: Span,
        trace_name: Option<Sym>,
    ) -> RResult<Vals> {
        let code = &clo.code;
        let np = code.params.len();
        let name = trace_name.or(code.name).unwrap_or_else(|| Sym::new("<function>"));
        if code.variadic {
            if args.len() + 1 < np {
                return Err(RuntimeError::statement("procedure call", format!("Number of arguments ({}) is less than the minimum number of arguments ({})", args.len(), np.saturating_sub(1))));
            }
        } else if args.len() != np {
            return Err(RuntimeError::statement("procedure call", format!("Number of arguments ({}) does not equal expected number of arguments ({np})", args.len())));
        }
        for (i, p) in code.params.iter().enumerate() {
            let is_ref = refmask.get(i).copied().unwrap_or(false);
            if i < args.len() && p.is_ref != is_ref && !(code.variadic && i == np - 1) {
                let msg = if p.is_ref { "must be a variable reference (use ~)" } else { "must not be a variable reference" };
                return Err(RuntimeError::statement("procedure call", format!("Argument {} {msg}", i + 1)));
            }
        }
        if self.depth >= self.max_depth {
            return Err(RuntimeError::runtime("Recursion depth exceeded"));
        }
        let mut frame = Frame {
            slots: {
                let mut slots = self.spare_vecs.pop().unwrap_or_default();
                slots.resize(code.n_slots as usize, Value::Undef);
                slots
            },
            captures: clo.captures.clone(),
            self_fn: Some(Value::Func(clo.clone())),
            code: Some(code.clone()),
            nresults: nres,
        };
        for (slot, ci) in &code.local_inits {
            frame.slots[*slot as usize] = clo.captures[*ci as usize].clone();
        }
        for (i, p) in code.params.iter().enumerate() {
            if code.variadic && i == np - 1 {
                let rest: Vec<Value> = args[i.min(args.len())..].to_vec();
                frame.slots[p.slot as usize] = Value::list(rest);
            } else {
                frame.slots[p.slot as usize] = std::mem::take(&mut args[i]);
            }
        }
        // Optional parameters: given values or defaults evaluated in the callee.
        for (pname, _) in &params {
            if !code.opt_params.iter().any(|(n, _, _)| n == pname) {
                // Restore arguments before failing.
                self.restore_args(code, &mut frame, args);
                return Err(RuntimeError::statement("procedure call", format!("Parameter '{pname}' is not defined for this function")));
            }
        }
        self.depth += 1;
        self.nresults_stack.push(nres);
        self.trace.push(TraceFrame { name, span: Some(span), args: Vec::new() });
        let result = (|| -> RResult<Vals> {
            for (pname, slot, default) in &code.opt_params {
                let v = match params.iter().find(|(n, _)| n == pname) {
                    Some((_, v)) => v.clone(),
                    None => self.eval(default, &mut frame)?,
                };
                frame.slots[*slot as usize] = v;
            }
            match &code.body {
                Body::Expr(e) => Ok(vals![self.eval(e, &mut frame)?]),
                Body::Block(stmts) => match self.exec_block(stmts, &mut frame)? {
                    Flow::Return(vals) => {
                        if code.is_procedure && !vals.is_empty() {
                            return Err(RuntimeError::runtime("A procedure cannot return values"));
                        }
                        Ok(vals)
                    }
                    Flow::Normal => {
                        if code.is_procedure {
                            Ok(Vals::new())
                        } else {
                            Err(RuntimeError::runtime("Function has no return value"))
                        }
                    }
                    Flow::Break(_) | Flow::Continue(_) => Err(RuntimeError::runtime("break/continue outside of a loop")),
                },
            }
        })();
        self.depth -= 1;
        self.nresults_stack.pop();
        let result = match result {
            Ok(v) => {
                self.trace.pop();
                Ok(v)
            }
            Err(mut e) => {
                if e.at_caller && e.span.is_none() {
                    e.at_caller = false;
                    if span != Span::default() {
                        e.span = Some(span);
                    }
                }
                if e.kind != ErrKind::Interrupt {
                    let mut targs = Vec::with_capacity(code.params.len());
                    for p in &code.params {
                        let v = frame.slots[p.slot as usize].clone();
                        let text = if v.is_undef() { "undef".to_string() } else { self.format_flat(&v, crate::print::Level::Default).unwrap_or_default() };
                        targs.push((p.name.to_string(), text));
                    }
                    e.trace.push(TraceFrame { name, span: Some(span), args: targs });
                }
                self.trace.pop();
                Err(e)
            }
        };
        self.restore_args(code, &mut frame, args);
        self.recycle(frame.slots);
        result
    }

    /// Keep an emptied vector for a later call.
    fn recycle(&mut self, mut v: Vec<Value>) {
        if self.spare_vecs.len() < 64 {
            v.clear();
            self.spare_vecs.push(v);
        }
    }

    fn restore_args(&self, code: &FuncCode, frame: &mut Frame, args: &mut [Value]) {
        let np = code.params.len();
        for (i, p) in code.params.iter().enumerate() {
            if code.variadic && i == np - 1 {
                break;
            }
            if i < args.len() && p.is_ref {
                args[i] = std::mem::take(&mut frame.slots[p.slot as usize]);
            }
        }
    }

    // ----- intrinsics -----------------------------------------------------

    /// Call an intrinsic by name with value arguments, returning the
    /// principal result.
    pub fn call_intrinsic_named(&mut self, name: Sym, mut args: Vec<Value>) -> RResult<Value> {
        let mask = value_mask(args.len());
        match self.call_intrinsic(name, &mut args, &mask, Vec::new(), 1, false, Span::default(), None)? {
            Some(v) if !v.is_empty() => Ok(v.into_iter().next().unwrap()),
            _ => Err(RuntimeError::runtime(format!("'{name}' returned no value"))),
        }
    }

    /// Find the best signature of `name` for these arguments.
    pub fn select_signature(&self, name: Sym, args: &[Value], refmask: &[bool], stmt: bool) -> Option<Rc<Signature>> {
        let sigs = self.intrinsics.get(name)?;
        // The first match is kept apart so that the usual single match
        // allocates nothing.
        let mut first = None;
        let mut candidates: Vec<&Rc<Signature>> = Vec::new();
        for sig in sigs {
            if self.signature_matches(sig, args, refmask) {
                if !stmt && sig.returns.is_none() && refmask.iter().all(|r| !r) && sigs.iter().any(|s| s.returns.is_some() && self.signature_matches(s, args, refmask)) {
                    // Prefer function forms in expression context.
                    continue;
                }
                if first.is_none() {
                    first = Some(sig);
                } else {
                    candidates.push(sig);
                }
            }
        }
        let first = first?;
        if candidates.is_empty() {
            return Some(first.clone());
        }
        candidates.insert(0, first);
        // Keep the candidates not dominated by a more specific one.
        let undominated: Vec<&Rc<Signature>> = candidates
            .iter()
            .filter(|s| !candidates.iter().any(|o| !Rc::ptr_eq(o, s) && self.strictly_more_specific(o, s)))
            .copied()
            .collect();
        let pool = if undominated.is_empty() { &candidates } else { &undominated };
        // Among equals, user definitions and later definitions win, except that
        // a null sequence or set, which fits every element type, goes to the
        // earliest built-in: CRT([], []) is the integer CRT.
        let null = |v: &Value| match v {
            Value::Seq(s) => s.universe.is_none(),
            Value::Set(s) => s.universe.is_none(),
            _ => false,
        };
        if args.iter().any(null) && pool.iter().all(|s| matches!(s.imp, Imp::Native(_))) {
            return pool.iter().min_by_key(|s| s.order).map(|s| (*s).clone());
        }
        pool.iter().max_by_key(|s| s.order).map(|s| (*s).clone())
    }

    fn strictly_more_specific(&self, a: &Signature, b: &Signature) -> bool {
        let n = a.args.len().min(b.args.len());
        let mut strict = false;
        for i in 0..n {
            let (pa, pb) = (&a.args[i].pat, &b.args[i].pat);
            if !pa.leq(pb, &self.types) {
                return false;
            }
            if !pb.leq(pa, &self.types) {
                strict = true;
            }
        }
        strict || (!a.variadic && b.variadic)
    }

    pub fn signature_matches(&self, sig: &Signature, args: &[Value], refmask: &[bool]) -> bool {
        if sig.variadic {
            if args.len() < sig.args.len() {
                return false;
            }
        } else if args.len() != sig.args.len() {
            return false;
        }
        for (i, a) in sig.args.iter().enumerate() {
            let is_ref = refmask.get(i).copied().unwrap_or(false);
            if a.is_ref != is_ref {
                return false;
            }
            let v = &args[i];
            if v.is_undef() {
                // An uninitialised reference argument matches only untyped refs.
                if !(a.is_ref && a.untyped) {
                    return false;
                }
                continue;
            }
            if !self.value_matches(v, &a.pat) {
                return false;
            }
        }
        if sig.variadic && refmask[sig.args.len()..].iter().any(|&r| r) {
            return false;
        }
        true
    }

    #[allow(clippy::too_many_arguments)]
    pub fn call_intrinsic(
        &mut self,
        name: Sym,
        args: &mut Vec<Value>,
        refmask: &[bool],
        params: Vec<(Sym, Value)>,
        nres: usize,
        stmt: bool,
        span: Span,
        site: Option<&SigCache>,
    ) -> RResult<Option<Vals>> {
        let site = site.filter(|s| !s.never(self, name));
        let key = site.and_then(|_| SiteKey::new(self, name, args, refmask, stmt));
        let known = match (site, &key) {
            (Some(site), Some(key)) => site.get(key),
            _ => None,
        };
        let chosen = known.or_else(|| {
            let sig = self.select_signature(name, args, refmask, stmt)?;
            if let (Some(site), Some(key)) = (site, key) {
                if self.intrinsics.plain(name, args.len()) {
                    site.put(key, sig.clone());
                } else {
                    site.put_never(key);
                }
            }
            Some(sig)
        });
        let Some(sig) = chosen else {
            if !self.intrinsics.contains(name) {
                return Err(self.unassigned_error(name));
            }
            let types: Vec<String> = args.iter().zip(refmask).map(|(a, r)| if a.is_undef() { "<unassigned>".to_string() } else if *r { format!("{} ~", self.type_name_ext(a)) } else { self.type_name_ext(a) }).collect();
            let mut msg = "Bad argument types".to_string();
            if !types.is_empty() {
                msg.push_str(&format!("\nArgument types given: {}", types.join(", ")));
            }
            return Err(RuntimeError::runtime(msg).in_context(name.to_string()));
        };
        if sig.returns.is_none() && !stmt {
            return Err(RuntimeError::runtime("Procedure has no return value (it may only be called as a statement)").in_context(name.to_string()));
        }
        // Fill named parameters.
        let mut full_params = Vec::with_capacity(sig.params.len());
        for (pname, _) in &params {
            if !sig.params.iter().any(|p| p.name == *pname) {
                return Err(RuntimeError::runtime(format!("Undefined parameter '{pname}'")).in_context(name.to_string()));
            }
        }
        let result = match &sig.imp {
            Imp::Native(fun) => {
                for p in &sig.params {
                    let v = match params.iter().find(|(n, _)| *n == p.name) {
                        Some((_, v)) => v.clone(),
                        None => p.default.clone(),
                    };
                    full_params.push((p.name, v));
                }
                // Move the arguments so referenced values stay uniquely owned.
                let n = args.len();
                let mut ca = CallArgs { args: std::mem::take(args), params: full_params, nresults: nres, name, span };
                let r = fun(self, &mut ca);
                *args = ca.args;
                args.resize_with(n, Value::default);
                r.map_err(|e| if e.span.is_none() && e.kind != ErrKind::Syntax { e.in_context(name.to_string()) } else { e })
            }
            Imp::User(clo) => {
                let clo = clo.clone();
                let user_params: Vec<(Sym, Value)> = params;
                self.call_closure(&clo, args, refmask, user_params, nres, span, Some(name))
            }
        };
        let vals = result?;
        Ok(if sig.returns.is_none() { None } else { Some(vals) })
    }

    /// Dispatch an operator to user-defined intrinsics (e.g. `'+'` on a
    /// user type). Returns `None` if no signature other than the generic
    /// built-in one matches.
    pub fn dispatch_user_operator(&mut self, name: &str, args: Vec<Value>) -> RResult<Option<Value>> {
        let sym = Sym::new(name);
        let mask = value_mask(args.len());
        let Some(sig) = self.select_signature(sym, &args, &mask, false) else {
            return Ok(None);
        };
        if sig.generic {
            return Ok(None);
        }
        let mut args = args;
        let r = self.call_intrinsic(sym, &mut args, &mask, Vec::new(), 1, false, Span::default(), None)?;
        Ok(r.and_then(|v| v.into_iter().next()))
    }

    pub fn type_name_ext(&self, v: &Value) -> String {
        match self.shown_extended_type(v) {
            Some(t) => t.display(&self.types).to_string(),
            None => self.type_name(v),
        }
    }
}
