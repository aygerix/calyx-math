//! Expression evaluation.

use std::rc::Rc;

use calyx_syntax::ast::{AggKind, MapKind as AstMapKind, QuantKind};

use super::{Frame, Interp};
use crate::error::{RResult, RuntimeError};
use crate::ir::*;
use crate::sym::Sym;
use crate::value::*;

impl Interp {
    #[inline]
    pub fn eval(&mut self, e: &E, f: &mut Frame) -> RResult<Value> {
        match &e.kind {
            Ex::Const(v) => Ok(v.clone()),
            Ex::Local(s, name) => {
                let v = f.get(*s);
                if v.is_undef() {
                    return Err(RuntimeError::runtime(format!("Variable '{name}' has not been initialized")).at(e.span));
                }
                Ok(v.clone())
            }
            _ => self.eval_slow(e, f).map_err(|err| err.at(e.span)),
        }
    }

    /// The condition of a statement such as `if` or `assert`.
    pub fn eval_cond(&mut self, e: &E, f: &mut Frame, stmt: &str) -> RResult<bool> {
        match self.eval(e, f)? {
            Value::Bool(b) => Ok(b),
            _ => Err(RuntimeError::statement(stmt, "Logical expected")),
        }
    }

    pub fn eval_bool(&mut self, e: &E, f: &mut Frame) -> RResult<bool> {
        match self.eval(e, f)? {
            Value::Bool(b) => Ok(b),
            other => Err(RuntimeError::runtime(format!("Expected a boolean, not an object of type {}", self.type_name(&other))).at(e.span)),
        }
    }

    /// Evaluate an expression that may produce several values (a call, or
    /// `$n`). `nres` is the number of values wanted (0 = all, for printing).
    pub fn eval_multi(&mut self, e: &E, f: &mut Frame, nres: usize) -> RResult<Vec<Value>> {
        match &e.kind {
            Ex::Call(c) => match self.call_expr(c, f, nres, false, e.span).map_err(|err| err.at(e.span))? {
                Some(v) if !v.is_empty() => Ok(v.into_vec()),
                _ => Err(RuntimeError::runtime("Procedure call has no return value").at(e.span)),
            },
            Ex::Previous(n) => self.previous_values(*n).ok_or_else(|| RuntimeError::user(format!("There is no previous value ${n}")).at(e.span)),
            Ex::Constructor(name, left, right) => {
                let mut l = Vec::new();
                for x in left {
                    l.push(self.eval(x, f)?);
                }
                let r = match right {
                    Some(r) => {
                        let mut v = Vec::new();
                        for x in r {
                            v.push(self.eval(x, f)?);
                        }
                        Some(v)
                    }
                    None => None,
                };
                self.constructor_multi(*name, l, r).map_err(|err| err.at(e.span))
            }
            Ex::Cop(_) => {
                let c = self.eval(e, f)?;
                let inj = self.call_intrinsic_named(Sym::new("Injections"), vec![c.clone()])?;
                Ok(vec![c, inj])
            }
            Ex::Let(slot, v, body) => {
                let val = self.eval(v, f)?;
                f.set(*slot, val);
                self.eval_multi(body, f, nres)
            }
            Ex::LetMulti(slots, v, body) => {
                self.bind_values(slots, v, f)?;
                self.eval_multi(body, f, nres)
            }
            _ => Ok(vec![self.eval(e, f)?]),
        }
    }

    /// Bind the values of `v` to the slots of a `where` clause.
    pub fn bind_values(&mut self, slots: &[Slot], v: &E, f: &mut Frame) -> RResult<()> {
        if let [slot] = slots {
            let val = self.eval(v, f)?;
            f.set(*slot, val);
            return Ok(());
        }
        let vals = self.eval_multi(v, f, slots.len())?;
        if vals.len() < slots.len() {
            let msg = format!("Expected to assign {} value(s) but only computed {} value(s)", slots.len(), vals.len());
            return Err(RuntimeError::runtime(msg).at(v.span));
        }
        for (slot, val) in slots.iter().zip(vals) {
            f.set(*slot, val);
        }
        Ok(())
    }

    fn previous_values(&self, n: u32) -> Option<Vec<Value>> {
        if n == 0 {
            return None;
        }
        self.previous.get(n as usize - 1).cloned()
    }

    fn eval_slow(&mut self, e: &E, f: &mut Frame) -> RResult<Value> {
        match &e.kind {
            Ex::Const(_) | Ex::Local(..) => self.eval(e, f),
            Ex::Capture(i, name) => {
                let v = &f.captures[*i as usize];
                if v.is_undef() {
                    return Err(RuntimeError::user(format!("Identifier '{name}' has not been assigned")));
                }
                Ok(v.clone())
            }
            Ex::Global(name) => self.lookup_global(*name).ok_or_else(|| self.unassigned_error(*name)),
            Ex::SelfFn => f.self_fn.clone().ok_or_else(|| RuntimeError::user("'$$' used outside of a function")),
            Ex::Previous(n) => {
                let vals = self.previous_values(*n).ok_or_else(|| RuntimeError::user(format!("There is no previous value ${n}")))?;
                Ok(vals.into_iter().next().unwrap_or(Value::Undef))
            }
            Ex::Undef => Ok(Value::Undef),
            Ex::Neg(a) => {
                let v = self.eval(a, f)?;
                self.negate(v)
            }
            Ex::Not(a) => match self.eval(a, f)? {
                Value::Bool(b) => Ok(Value::Bool(!b)),
                v => self.unary_intrinsic("not", v),
            },
            Ex::Card(a) => {
                let v = self.eval(a, f)?;
                self.cardinality(&v)
            }
            Ex::Bin(op, a, b) => {
                let x = self.eval(a, f)?;
                let y = self.eval(b, f)?;
                self.binop(*op, x, y)
            }
            Ex::And(a, b) => {
                if !self.bool_operand(a, f, "and")? {
                    return Ok(Value::Bool(false));
                }
                Ok(Value::Bool(self.bool_operand(b, f, "and")?))
            }
            Ex::Or(a, b) => {
                if self.bool_operand(a, f, "or")? {
                    return Ok(Value::Bool(true));
                }
                Ok(Value::Bool(self.bool_operand(b, f, "or")?))
            }
            Ex::Select(c, a, b) => {
                if self.eval_bool(c, f)? {
                    self.eval(a, f)
                } else {
                    self.eval(b, f)
                }
            }
            Ex::Call(c) => {
                let vals = self.call_expr(c, f, 1, false, e.span)?;
                match vals {
                    Some(v) if !v.is_empty() => Ok(v.into_iter().next().unwrap()),
                    _ => Err(RuntimeError::runtime("Procedure call has no return value")),
                }
            }
            Ex::Index(a, idx) => {
                let base = self.eval(a, f)?;
                let mut ids = Vec::with_capacity(idx.len());
                for i in idx {
                    ids.push(self.eval(i, f)?);
                }
                self.index_multi(base, &ids)
            }
            Ex::Dot(a, b) => {
                let s = self.eval(a, f)?;
                let i = self.eval(b, f)?;
                self.call_intrinsic_named(Sym::new("."), vec![s, i])
            }
            Ex::Attr(a, name) => {
                let v = self.eval(a, f)?;
                self.get_attr(&v, *name)
            }
            Ex::AttrDyn(a, n) => {
                let v = self.eval(a, f)?;
                let Value::Str(name) = self.eval(n, f)? else {
                    return Err(RuntimeError::runtime("Attribute name must be a string"));
                };
                self.get_attr(&v, Sym::new(&name)).map_err(|mut e| {
                    if e.message.ends_with("does not exist in this record") {
                        e.message = format!("Invalid attribute '{name}' for this object");
                    }
                    e
                })
            }
            Ex::Coerce(s, x, _) => {
                let s = self.eval(s, f)?;
                let x = self.eval(x, f)?;
                self.coerce(&s, &x).map_err(|e| e.in_context("!"))
            }
            Ex::Image(x, m) => {
                let x = self.eval(x, f)?;
                let m = self.eval(m, f)?;
                self.image(&x, &m)
            }
            Ex::Preimage(y, m) => {
                let y = self.eval(y, f)?;
                let m = self.eval(m, f)?;
                self.preimage(&y, &m)
            }
            Ex::Reduce(op, a) => {
                let v = self.eval(a, f)?;
                self.reduce(*op, &v)
            }
            Ex::Assigned(t) => self.eval_assigned(t, f),
            Ex::Eval(a) => {
                let v = self.eval(a, f)?;
                let Value::Str(src) = v else {
                    return Err(RuntimeError::runtime("eval requires a string"));
                };
                self.eval_string(&src, f).map_err(|mut err| {
                    if let Some((_, compile)) = err.eval_outer {
                        err.eval_outer = Some((e.span, compile));
                    }
                    err
                })
            }
            Ex::Let(slot, v, body) => {
                let val = self.eval(v, f)?;
                f.set(*slot, val);
                self.eval(body, f)
            }
            Ex::LetMulti(slots, v, body) => {
                self.bind_values(slots, v, f)?;
                self.eval(body, f)
            }
            Ex::Multiplicity(..) => Err(RuntimeError::runtime("'^^' may only be used in multiset constructors")),
            Ex::Tuple(es) => {
                let mut v = Vec::with_capacity(es.len());
                for x in es {
                    v.push(self.eval(x, f)?);
                }
                Ok(Value::tuple(v))
            }
            Ex::Agg(a) => self.eval_aggregate(a, f),
            Ex::TupleCompr(c) => {
                let mut vals = Vec::new();
                self.run_comprehension(c, f, &mut |_, v, _| {
                    vals.push(v);
                    Ok(true)
                })?;
                Ok(Value::tuple(vals))
            }
            Ex::List(es) => {
                let mut v = Vec::with_capacity(es.len());
                for x in es {
                    v.push(self.eval(x, f)?);
                }
                Ok(Value::list(v))
            }
            Ex::Formal(is_seq, dom, pred) => {
                let universe = self.eval(dom, f)?;
                let pred = match pred {
                    Some(p) => Some(self.eval(p, f)?),
                    None => None,
                };
                Ok(Value::Formal(Rc::new(Formal { is_seq: *is_seq, universe, pred })))
            }
            Ex::Quant(q) => self.eval_quantifier(q, f),
            Ex::Closure(code, caps) => self.make_closure(code, caps, f),
            Ex::Map(m) => self.eval_map(m, f),
            Ex::Rec(fmt, fields) => {
                let fv = self.eval(fmt, f)?;
                let mut vals = Vec::new();
                for (n, e) in fields {
                    vals.push((*n, self.eval(e, f)?));
                }
                self.make_record(&fv, vals)
            }
            Ex::RecFormat(fields) => {
                let mut names = Vec::new();
                let mut types = Vec::new();
                for (n, t) in fields {
                    if names.contains(n) {
                        return Err(RuntimeError::runtime(format!("Duplicate field name '{n}' in record format")));
                    }
                    names.push(*n);
                    types.push(match t {
                        Some(t) => Some(self.eval(t, f)?),
                        None => None,
                    });
                }
                Ok(Value::structure(StructKind::RecFormat(RecFormat { names, types })))
            }
            Ex::Car(es) => {
                let mut v = Vec::new();
                for x in es {
                    v.push(self.eval(x, f)?);
                }
                self.cartesian_product(v)
            }
            Ex::Cop(es) => {
                let mut v = Vec::new();
                for x in es {
                    v.push(self.eval(x, f)?);
                }
                // cop< [S1, ..., Sk] > takes the constituents from a sequence.
                if v.len() == 1 {
                    if let Value::Seq(s) = &v[0] {
                        v = s.elems.clone();
                    }
                }
                Ok(Value::structure(StructKind::Coproduct(v)))
            }
            Ex::Elt(p, es) => {
                let p = self.eval(p, f)?;
                let mut v = Vec::new();
                for x in es {
                    v.push(self.eval(x, f)?);
                }
                self.elt_constructor(&p, v).map_err(|e| e.in_context("elt< ... >"))
            }
            Ex::Case(s, arms, d) => {
                let v = self.eval(s, f)?;
                for (l, r) in arms {
                    let w = self.eval(l, f)?;
                    if self.values_equal(&v, &w)? {
                        return self.eval(r, f);
                    }
                }
                self.eval(d, f)
            }
            Ex::Constructor(name, left, right) => {
                let mut l = Vec::new();
                for x in left {
                    l.push(self.eval(x, f)?);
                }
                let r = match right {
                    Some(r) => {
                        let mut v = Vec::new();
                        for x in r {
                            v.push(self.eval(x, f)?);
                        }
                        Some(v)
                    }
                    None => None,
                };
                self.constructor(*name, l, r)
            }
            Ex::SelfSeq(i) if matches!(i.kind, Ex::Undef) => {
                let Some(cur) = self.self_seqs.last() else {
                    return Err(RuntimeError::runtime("Self may only be used in a sequence constructor"));
                };
                Ok(Value::seq(None, cur.clone()))
            }
            Ex::SelfSeq(i) => {
                let iv = self.eval(i, f)?;
                let Value::Int(i) = iv else {
                    return Err(RuntimeError::runtime("Self requires an integer index"));
                };
                let Some(cur) = self.self_seqs.last() else {
                    return Err(RuntimeError::runtime("Self may only be used in a sequence constructor"));
                };
                match i.to_i64() {
                    Some(k) if k >= 1 && (k as usize) <= cur.len() => Ok(cur[k as usize - 1].clone()),
                    _ => Err(RuntimeError::runtime(format!("Self({i}) refers to an element not yet defined")).in_context("Self")),
                }
            }
        }
    }

    fn bool_operand(&mut self, e: &E, f: &mut Frame, op: &str) -> RResult<bool> {
        match self.eval(e, f)? {
            Value::Bool(b) => Ok(b),
            other => {
                let t = self.type_name(&other);
                Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {t}")).in_context(op))
            }
        }
    }

    fn make_closure(&mut self, code: &Rc<FuncCode>, caps: &Rc<[CapSrc]>, f: &mut Frame) -> RResult<Value> {
        let mut vals = Vec::with_capacity(caps.len());
        for (i, c) in caps.iter().enumerate() {
            let v = match c {
                CapSrc::Local(s, span) => {
                    let v = f.get(*s).clone();
                    if v.is_undef() && !code.local_inits.iter().any(|&(_, j)| j as usize == i) {
                        let msg = format!("Variable '{}' in enclosing environment has not been assigned to", code.capture_names[i]);
                        return Err(RuntimeError::runtime(msg).at(*span));
                    }
                    v
                }
                CapSrc::Capture(j) => f.captures[*j as usize].clone(),
                CapSrc::SelfFn => f.self_fn.clone().unwrap_or(Value::Undef),
                CapSrc::Global(name, span) => match self.lookup_global(*name) {
                    Some(v) => v,
                    None => return Err(self.unassigned_error(*name).at(*span)),
                },
                CapSrc::GlobalLate(name) => self.lookup_global(*name).unwrap_or(Value::Intr(*name)),
                CapSrc::GlobalInit(name) => self.lookup_variable(*name).unwrap_or(Value::Undef),
            };
            vals.push(v);
        }
        Ok(Value::Func(Rc::new(Closure { code: code.clone(), captures: vals.into() })))
    }

    /// A user variable (not an intrinsic or type) visible at top level.
    pub fn lookup_variable(&self, name: Sym) -> Option<Value> {
        for env in self.eval_env.iter().rev() {
            if let Some(v) = env.get(&name) {
                return Some(v.clone());
            }
        }
        if let Some(pkg) = self.package_stack.last() {
            if let Some(v) = pkg.get(&name) {
                return Some(v.clone());
            }
        }
        self.globals.get(&name).filter(|v| !v.is_undef()).cloned()
    }

    fn eval_assigned(&mut self, t: &AssignedEx, f: &mut Frame) -> RResult<Value> {
        Ok(Value::Bool(match t {
            AssignedEx::Var(e) => match &e.kind {
                Ex::Local(s, _) => !f.get(*s).is_undef(),
                Ex::Capture(i, _) => !f.captures[*i as usize].is_undef(),
                Ex::Global(n) => self.lookup_variable(*n).is_some(),
                Ex::SelfFn => true,
                _ => true,
            },
            AssignedEx::Attr(b, name, span) => {
                let v = self.eval(b, f)?;
                self.attr_assigned(&v, *name).map_err(|e| e.at(*span))?
            }
            AssignedEx::AttrDyn(b, n, span) => {
                let v = self.eval(b, f)?;
                let Value::Str(name) = self.eval(n, f)? else {
                    return Err(RuntimeError::runtime("Attribute name must be a string"));
                };
                self.attr_assigned(&v, Sym::new(&name)).map_err(|e| e.at(*span))?
            }
            AssignedEx::Index(b, idx) => {
                let v = self.eval(b, f)?;
                let mut ids = Vec::new();
                for i in idx {
                    ids.push(self.eval(i, f)?);
                }
                self.index_multi(v, &ids).is_ok_and(|v| !v.is_undef())
            }
        }))
    }

    // ----- aggregates -----------------------------------------------------

    fn eval_aggregate(&mut self, a: &AggEx, f: &mut Frame) -> RResult<Value> {
        let universe = match &a.universe {
            Some(u) => {
                let u = self.eval(u, f)?;
                if !u.is_structure_like() {
                    return Err(RuntimeError::runtime(format!("Illegal universe: an object of type {}", self.type_name(&u))));
                }
                Some(u)
            }
            None => None,
        };
        let ctx = agg_context(a.kind);
        match &a.body {
            AggBodyEx::Empty => Ok(self.build_aggregate(a.kind, universe.or_else(|| None), Vec::new(), true)?),
            AggBodyEx::Enum(es) => {
                let mut vals = Vec::with_capacity(es.len());
                let mut mults = Vec::new();
                for x in es {
                    if a.kind == AggKind::Seq {
                        // In a sequence, x^^n means x repeated n times.
                        if let Ex::Multiplicity(v, n) = &x.kind {
                            let v = self.eval(v, f)?;
                            let Value::Int(n) = self.eval(n, f)? else {
                                return Err(RuntimeError::runtime("Multiplicity must be an integer").in_context("^^"));
                            };
                            let n = n.to_u64().ok_or_else(|| RuntimeError::runtime("Multiplicity must be non-negative").in_context("^^"))?;
                            for _ in 0..n {
                                vals.push(v.clone());
                            }
                            continue;
                        }
                    }
                    if a.kind == AggKind::MSet {
                        if let Ex::Multiplicity(v, n) = &x.kind {
                            let v = self.eval(v, f)?;
                            let n = self.eval(n, f)?;
                            let Value::Int(n) = n else {
                                return Err(RuntimeError::runtime("Multiplicity must be an integer").in_context("^^"));
                            };
                            let n = n.to_u64().ok_or_else(|| RuntimeError::runtime("Multiplicity must be non-negative").in_context("^^"))?;
                            vals.push(v);
                            mults.push(n);
                            continue;
                        }
                        mults.push(1);
                    }
                    vals.push(self.eval(x, f)?);
                }
                if a.kind == AggKind::MSet {
                    // Magma reports this failure from its sub< > constructor.
                    return self.build_multiset(universe, vals, mults).map_err(|e| if e.message.starts_with("Cannot coerce argument") { e.in_context("sub< ... >") } else { e });
                }
                let explicit = universe.is_some();
                self.build_aggregate(a.kind, universe, vals, false).map_err(|mut e| {
                    // Magma words the failure differently for sequences.
                    if a.kind == AggKind::Seq && !explicit && e.message.starts_with("Cannot coerce argument") {
                        e.message = "No valid universe containing all elements".into();
                    }
                    e.in_context(ctx)
                })
            }
            AggBodyEx::Range(lo, hi, by) => {
                let (lo, hi, step) = self.range_bounds(lo, hi, by.as_ref(), f)?;
                if let Some(u) = &universe {
                    if !u.is_integers() {
                        return Err(RuntimeError::runtime("Invalid set universe").in_context(format!("{} .. {}", ctx_open(a.kind), ctx_close(a.kind))));
                    }
                }
                if a.kind == AggKind::Set {
                    return Ok(Value::Set(Rc::new(SetEnum::range(lo, &hi, step))));
                }
                let mut it = super::iter::ValueIter::range(lo, &hi, step);
                let mut vals = Vec::new();
                while let Some((_, v)) = it.next_item() {
                    vals.push(v);
                }
                if a.kind == AggKind::Seq {
                    let mut s = SeqEnum::new(Some(Value::integers()), vals);
                    s.range_hint = true;
                    return Ok(Value::Seq(Rc::new(s)));
                }
                self.build_aggregate(a.kind, Some(Value::integers()), vals, true)
            }
            AggBodyEx::Compr(c) => {
                if a.kind == AggKind::Seq {
                    self.self_seqs.push(Vec::new());
                    let r = self.run_comprehension(c, f, &mut |it, v, _f| {
                        it.self_seqs.last_mut().unwrap().push(v);
                        Ok(true)
                    });
                    let vals = self.self_seqs.pop().unwrap();
                    r?;
                    let explicit = universe.is_some();
                    return self.build_aggregate(a.kind, universe, vals, false).map_err(|mut e| {
                        if explicit && e.message.starts_with("Cannot coerce argument") {
                            e.message = "Cannot coerce element into the universe".into();
                            e.context = Some("sequence construction".into());
                        } else if !explicit && e.message.starts_with("Cannot coerce argument") {
                            e.message = "No valid universe containing all elements".into();
                        }
                        e.in_context(ctx)
                    });
                }
                let mut vals = Vec::new();
                let is_mset = a.kind == AggKind::MSet;
                let multiplicity_head = matches!(c.head.kind, Ex::Multiplicity(..));
                if is_mset && multiplicity_head {
                    let Ex::Multiplicity(hv, hn) = &c.head.kind else { unreachable!() };
                    let mut pairs = Vec::new();
                    self.run_comprehension_with_head(c, hv, hn, f, &mut pairs)?;
                    let (vals, mults) = pairs.into_iter().unzip();
                    return self.build_multiset(universe, vals, mults);
                }
                self.run_comprehension(c, f, &mut |_, v, _| {
                    vals.push(v);
                    Ok(true)
                })?;
                if is_mset {
                    let n = vals.len();
                    return self.build_multiset(universe, vals, vec![1; n]);
                }
                self.build_aggregate(a.kind, universe, vals, false).map_err(|e| e.in_context(ctx))
            }
        }
    }

    fn run_comprehension_with_head(&mut self, c: &ComprEx, hv: &E, hn: &E, f: &mut Frame, out: &mut Vec<(Value, u64)>) -> RResult<()> {
        fn level(it: &mut Interp, c: &ComprEx, k: usize, hv: &E, hn: &E, f: &mut Frame, out: &mut Vec<(Value, u64)>) -> RResult<()> {
            if k == 0 {
                for (slots, e) in &c.lets {
                    it.bind_values(slots, e, f)?;
                }
                if let Some(p) = &c.pred {
                    if !it.eval_bool(p, f)? {
                        return Ok(());
                    }
                }
                let v = it.eval(hv, f)?;
                let Value::Int(n) = it.eval(hn, f)? else {
                    return Err(RuntimeError::runtime("Multiplicity must be an integer").in_context("^^"));
                };
                out.push((v, n.to_u64().unwrap_or(0)));
                return Ok(());
            }
            let ie = &c.iters[k - 1];
            let mut iter = it.loop_domain(&ie.domain, f, ie.index.is_some(), ie.span)?;
            while let Some((i, x)) = iter.next_item() {
                if let Some(s) = ie.index {
                    f.set(s, i);
                }
                f.set(ie.var, x);
                level(it, c, k - 1, hv, hn, f, out)?;
            }
            Ok(())
        }
        level(self, c, c.iters.len(), hv, hn, f, out)
    }

    fn eval_quantifier(&mut self, q: &QuantEx, f: &mut Frame) -> RResult<Value> {
        match q.kind {
            QuantKind::Exists | QuantKind::Forall => {
                let is_exists = q.kind == QuantKind::Exists;
                let mut witness = None;
                // For exists, the predicate must hold; for forall it must fail.
                let c = &q.compr;
                let found = !self.quant_level(c, c.iters.len(), f, is_exists, &mut witness)?;
                if found {
                    if let Some(w) = witness {
                        self.assign_witnesses(&q.witnesses, w, f)?;
                    }
                }
                Ok(Value::Bool(if is_exists { found } else { !found }))
            }
            QuantKind::Rep => {
                let mut result = None;
                self.run_comprehension(&q.compr, f, &mut |_, v, _| {
                    result = Some(v);
                    Ok(false)
                })?;
                result.ok_or_else(|| RuntimeError::runtime("Could not find a representative").in_context("{ ... }"))
            }
            QuantKind::Random => {
                let mut vals = Vec::new();
                self.run_comprehension(&q.compr, f, &mut |_, v, _| {
                    vals.push(v);
                    Ok(true)
                })?;
                if vals.is_empty() {
                    return Err(RuntimeError::runtime("No element satisfies the predicate").in_context("random"));
                }
                let k = self.rng.below_u64(vals.len() as u64) as usize;
                Ok(vals.swap_remove(k))
            }
        }
    }

    /// Returns `Ok(false)` if the search stopped (a witness was found).
    fn quant_level(&mut self, c: &ComprEx, k: usize, f: &mut Frame, want: bool, witness: &mut Option<Value>) -> RResult<bool> {
        if k == 0 {
            for (slots, e) in &c.lets {
                self.bind_values(slots, e, f)?;
            }
            let holds = match &c.pred {
                Some(p) => self.eval_bool(p, f)?,
                None => true,
            };
            if holds == want {
                *witness = Some(self.eval(&c.head, f)?);
                return Ok(false);
            }
            return Ok(true);
        }
        let ie = &c.iters[k - 1];
        let mut it = self.loop_domain(&ie.domain, f, ie.index.is_some(), ie.span)?;
        while let Some((i, x)) = it.next_item() {
            self.check_interrupt()?;
            if let Some(s) = ie.index {
                f.set(s, i);
            }
            f.set(ie.var, x);
            if !self.quant_level(c, k - 1, f, want, witness)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn assign_witnesses(&mut self, ws: &[LV], w: Value, f: &mut Frame) -> RResult<()> {
        match ws.len() {
            0 => Ok(()),
            1 => self.assign(&ws[0], w, f),
            n => {
                let Value::Tuple(t) = &w else {
                    return Err(RuntimeError::runtime("Several witnesses require a tuple-valued expression"));
                };
                if t.elems.len() != n {
                    return Err(RuntimeError::runtime(format!("Expected a tuple of length {n} for the witnesses")));
                }
                for (lv, v) in ws.iter().zip(t.elems.iter()) {
                    self.assign(lv, v.clone(), f)?;
                }
                Ok(())
            }
        }
    }

    fn eval_map(&mut self, m: &MapEx, f: &mut Frame) -> RResult<Value> {
        let domain = self.eval(&m.domain, f)?;
        let codomain = self.eval(&m.codomain, f)?;
        let kind = match m.kind {
            AstMapKind::Map => MapKind::Map,
            AstMapKind::PMap => MapKind::PMap,
            AstMapKind::Hom => MapKind::Hom,
            AstMapKind::Iso => MapKind::Iso,
        };
        let imp = match &m.body {
            MapBodyEx::Rule(fe, inv) => {
                let fv = self.eval(fe, f)?;
                let inv = match inv {
                    Some(g) => Some(self.eval(g, f)?),
                    None => None,
                };
                MapImpl::Rule { f: fv, inv }
            }
            // The natural homomorphism from the integers, a prime field, or a
            // real or complex field: a coercion, which prints as a plain mapping.
            MapBodyEx::Exprs(es) if es.is_empty() && kind == MapKind::Hom && is_coercion_domain(&domain) => {
                return Ok(Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain, codomain, imp: MapImpl::Coercion })));
            }
            // The natural homomorphism from Q, which takes no images.
            MapBodyEx::Exprs(es) if kind == MapKind::Hom && domain.is_rationals() => {
                return crate::intrinsics::rationals::rational_hom(&codomain, es.len()).map_err(|e| e.in_context("hom< ... >"));
            }
            // The natural homomorphism from a residue class ring.
            MapBodyEx::Exprs(es) if es.is_empty() && kind == MapKind::Hom && crate::intrinsics::abgroups::residue_hom(&domain, &codomain).is_some() => {
                return Ok(crate::intrinsics::abgroups::residue_hom(&domain, &codomain).unwrap());
            }
            MapBodyEx::Exprs(es) => {
                let mut vals = Vec::new();
                for x in es {
                    vals.push(self.eval(x, f)?);
                }
                // hom< D -> C | images >: the images of the generators of D, for
                // the structures whose homomorphisms are given that way. No
                // images at all is theirs to reject too.
                if matches!(kind, MapKind::Hom | MapKind::Iso) && (vals.is_empty() || !is_graph(&vals)) {
                    let images = match &vals[..] {
                        [Value::Seq(s)] => s.elems.iter().cloned().collect(),
                        _ => vals.clone(),
                    };
                    if let Some(m) = self.hom_images(kind, &domain, &codomain, &images)? {
                        return Ok(m);
                    }
                }
                self.map_from_values(kind, &domain, &codomain, vals)?
            }
        };
        Ok(Value::Map(Rc::new(MapObj { kind, domain, codomain, imp })))
    }

    fn map_from_values(&mut self, kind: MapKind, domain: &Value, codomain: &Value, vals: Vec<Value>) -> RResult<MapImpl> {
        if vals.len() == 1 && matches!(vals[0], Value::Func(_) | Value::Intr(_)) {
            return Ok(MapImpl::Rule { f: vals.into_iter().next().unwrap(), inv: None });
        }
        let pairs: Vec<Value> = if vals.len() == 1 && matches!(vals[0], Value::Seq(_) | Value::Set(_) | Value::ISet(_) | Value::List(_)) {
            let mut it = self.iter_value(&vals[0], false)?;
            let mut v = Vec::new();
            while let Some((_, x)) = it.next_item() {
                v.push(x);
            }
            v
        } else {
            vals
        };
        let mut graph = VMap::default();
        for p in pairs {
            let Value::Tuple(t) = &p else {
                return Err(RuntimeError::runtime("A map graph must consist of pairs <x, y>").in_context("map< >"));
            };
            if t.elems.len() != 2 {
                return Err(RuntimeError::runtime("A map graph must consist of pairs <x, y>").in_context("map< >"));
            }
            let x = self.coerce(domain, &t.elems[0]).map_err(|e| e.in_context("map< >"))?;
            let y = self.coerce(codomain, &t.elems[1]).map_err(|e| e.in_context("map< >"))?;
            if let Some(old) = graph.get(&x) {
                if old != &y {
                    return Err(RuntimeError::runtime("More than one image is given for a single element of the domain").in_context("map< >"));
                }
            }
            graph.insert(x, y);
        }
        if kind != MapKind::PMap {
            // A total map must be defined on its whole (finite) domain.
            if let Ok(mut it) = self.iter_value(domain, false) {
                let mut n = 0usize;
                while let Some((_, x)) = it.next_item() {
                    if !graph.contains_key(&x) {
                        return Err(RuntimeError::runtime("Not enough images given to constructor").in_context("map< >"));
                    }
                    n += 1;
                    if n > 1_000_000 {
                        break;
                    }
                }
            }
        }
        Ok(MapImpl::Graph(graph))
    }

    pub fn eval_string(&mut self, src: &str, f: &mut Frame) -> RResult<Value> {
        // Make the caller's local variables visible (read-only) to the code.
        let mut env = rustc_hash::FxHashMap::default();
        if let Some(code) = &f.code {
            for (i, name) in code.slot_names.iter().enumerate() {
                if let Some(v) = f.slots.get(i) {
                    if !v.is_undef() {
                        env.insert(*name, v.clone());
                    }
                }
            }
            for (i, name) in code.capture_names.iter().enumerate() {
                if let Some(v) = f.captures.get(i) {
                    if !v.is_undef() {
                        env.entry(*name).or_insert_with(|| v.clone());
                    }
                }
            }
        }
        let readonly: rustc_hash::FxHashSet<Sym> = env.keys().copied().collect();
        self.eval_env.push(env);
        let r = self.run_eval_source(src, readonly);
        self.eval_env.pop();
        r
    }
}

fn agg_context(k: AggKind) -> &'static str {
    match k {
        AggKind::Seq => "[ ... ]",
        AggKind::Set => "{ ... }",
        AggKind::ISet => "{@ @}",
        AggKind::MSet => "{* *}",
    }
}

fn ctx_open(k: AggKind) -> &'static str {
    match k {
        AggKind::Seq => "[",
        AggKind::Set => "{",
        AggKind::ISet => "{@",
        AggKind::MSet => "{*",
    }
}

fn ctx_close(k: AggKind) -> &'static str {
    match k {
        AggKind::Seq => "]",
        AggKind::Set => "}",
        AggKind::ISet => "@}",
        AggKind::MSet => "*}",
    }
}

/// Whether the values of `hom< D -> C | ... >` give a map by its graph: pairs
/// `<x, y>`, as values or in one aggregate.
fn is_graph(vals: &[Value]) -> bool {
    let pair = |v: &Value| matches!(v, Value::Tuple(t) if t.elems.len() == 2);
    match vals {
        [Value::Seq(s)] => s.elems.iter().all(pair),
        [Value::Set(_) | Value::ISet(_) | Value::List(_)] => true,
        _ => vals.iter().all(pair),
    }
}

/// Domains whose natural homomorphism, `hom< D -> R | >`, is the coercion.
fn is_coercion_domain(d: &Value) -> bool {
    match d.as_struct() {
        Some(StructKind::Integers | StructKind::Reals(_)) => true,
        Some(StructKind::Ring(r)) => match &r.kind {
            crate::rings::RingKind::Complex(_) => true,
            crate::rings::RingKind::Finite(f) => f.degree == 1,
            _ => false,
        },
        _ => false,
    }
}
