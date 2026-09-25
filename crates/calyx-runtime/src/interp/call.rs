//! Calling user functions, procedures and intrinsics.

use std::rc::Rc;

use calyx_syntax::Span;

use super::{Flow, Frame, Interp};
use crate::error::{ErrKind, RResult, RuntimeError, TraceFrame};
use crate::intrinsics::{Imp, Signature};
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

impl Interp {
    /// Evaluate a call expression. Returns `None` if a procedure was called.
    /// With `stmt` set, a procedure call is allowed.
    pub fn call_expr(&mut self, c: &CallEx, f: &mut Frame, nres: usize, stmt: bool, span: Span) -> RResult<Option<Vec<Value>>> {
        let func = self.eval(&c.func, f)?;
        let mut args = Vec::with_capacity(c.args.len());
        let mut refs: Vec<Option<super::assign::RefTarget>> = Vec::with_capacity(c.args.len());
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
            refs.push(None);
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
        let refmask: Vec<bool> = c.args.iter().map(|a| matches!(a, CArg::Ref(..))).collect();
        let has_refs = refmask.iter().any(|&b| b);
        if has_refs && !stmt {
            self.restore_refs(&mut refs, &mut args, f)?;
            return Err(RuntimeError::runtime("Reference arguments may only be used in procedure calls"));
        }
        // Anonymous functions are named after the identifier they are called
        // through (for error reports).
        self.pending_call_name = match &c.func.kind {
            Ex::Global(n) | Ex::Local(_, n) | Ex::Capture(_, n) => Some(n.to_string()),
            _ => None,
        };
        let result = self.call_value_full(&func, &mut args, &refmask, params, nres, stmt, span);
        // Write back reference arguments, even if the call failed.
        let wb = self.restore_refs(&mut refs, &mut args, f);
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
        args: &mut [Value],
        refmask: &[bool],
        params: Vec<(Sym, Value)>,
        nres: usize,
        stmt: bool,
        span: Span,
    ) -> RResult<Option<Vec<Value>>> {
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
            Value::Intr(name) => self.call_intrinsic(*name, args, refmask, params, nres, stmt, span),
            Value::Map(_) => {
                if args.len() != 1 || !params.is_empty() {
                    return Err(RuntimeError::runtime("A map takes exactly one argument"));
                }
                let x = args[0].clone();
                Ok(Some(vec![self.image(&x, func)?]))
            }
            Value::Obj(_) => {
                // Objects of user types may be made callable via '()'? Not supported.
                Err(RuntimeError::runtime(format!("An object of type {} is not callable", self.type_name(func))))
            }
            other => Err(RuntimeError::runtime(format!("An object of type {} is not callable", self.type_name(other)))),
        }
    }

    /// Call a value as a function returning its principal value.
    pub fn call_function(&mut self, func: &Value, mut args: Vec<Value>) -> RResult<Value> {
        let mask = vec![false; args.len()];
        let span = Span::default();
        match self.call_value_full(func, &mut args, &mask, Vec::new(), 1, false, span)? {
            Some(v) if !v.is_empty() => Ok(v.into_iter().next().unwrap()),
            _ => Err(RuntimeError::runtime("Function returned no value")),
        }
    }

    /// Call a value, returning all results.
    pub fn call_function_multi(&mut self, func: &Value, mut args: Vec<Value>, nres: usize) -> RResult<Vec<Value>> {
        let mask = vec![false; args.len()];
        Ok(self.call_value_full(func, &mut args, &mask, Vec::new(), nres, false, Span::default())?.unwrap_or_default())
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
        trace_name: Option<String>,
    ) -> RResult<Vec<Value>> {
        let code = &clo.code;
        let np = code.params.len();
        let name = trace_name.unwrap_or_else(|| code.name.map(|n| n.to_string()).unwrap_or_else(|| "<function>".to_string()));
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
        let mut frame = Frame::new(code.n_slots);
        frame.captures = Rc::from(clo.captures.as_ref());
        frame.self_fn = Some(Value::Func(clo.clone()));
        frame.code = Some(code.clone());
        frame.nresults = nres;
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
        self.trace.push(TraceFrame { name: name.clone(), span: Some(span), args: Vec::new() });
        let result = (|| -> RResult<Vec<Value>> {
            for (pname, slot, default) in &code.opt_params {
                let v = match params.iter().find(|(n, _)| n == pname) {
                    Some((_, v)) => v.clone(),
                    None => self.eval(default, &mut frame)?,
                };
                frame.slots[*slot as usize] = v;
            }
            match &code.body {
                Body::Expr(e) => Ok(vec![self.eval(e, &mut frame)?]),
                Body::Block(stmts) => match self.exec_block(stmts, &mut frame)? {
                    Flow::Return(vals) => {
                        if code.is_procedure && !vals.is_empty() {
                            return Err(RuntimeError::runtime("A procedure cannot return values"));
                        }
                        Ok(vals)
                    }
                    Flow::Normal => {
                        if code.is_procedure {
                            Ok(Vec::new())
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
                    e.trace.push(TraceFrame { name: name.clone(), span: Some(span), args: targs });
                }
                self.trace.pop();
                Err(e)
            }
        };
        self.restore_args(code, &mut frame, args);
        result
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
        let mask = vec![false; args.len()];
        match self.call_intrinsic(name, &mut args, &mask, Vec::new(), 1, false, Span::default())? {
            Some(v) if !v.is_empty() => Ok(v.into_iter().next().unwrap()),
            _ => Err(RuntimeError::runtime(format!("'{name}' returned no value"))),
        }
    }

    /// Find the best signature of `name` for these arguments.
    pub fn select_signature(&self, name: Sym, args: &[Value], refmask: &[bool], stmt: bool) -> Option<Rc<Signature>> {
        let sigs = self.intrinsics.get(name)?;
        let mut candidates: Vec<&Rc<Signature>> = Vec::new();
        for sig in sigs {
            if self.signature_matches(sig, args, refmask) {
                if !stmt && sig.returns.is_none() && refmask.iter().all(|r| !r) && sigs.iter().any(|s| s.returns.is_some() && self.signature_matches(s, args, refmask)) {
                    // Prefer function forms in expression context.
                    continue;
                }
                candidates.push(sig);
            }
        }
        if candidates.is_empty() {
            return None;
        }
        // Keep the candidates not dominated by a more specific one.
        let undominated: Vec<&Rc<Signature>> = candidates
            .iter()
            .filter(|s| !candidates.iter().any(|o| !Rc::ptr_eq(o, s) && self.strictly_more_specific(o, s)))
            .copied()
            .collect();
        let pool = if undominated.is_empty() { &candidates } else { &undominated };
        // Among equals, user definitions and later definitions win.
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
    pub fn call_intrinsic(&mut self, name: Sym, args: &mut [Value], refmask: &[bool], params: Vec<(Sym, Value)>, nres: usize, stmt: bool, span: Span) -> RResult<Option<Vec<Value>>> {
        let Some(sig) = self.select_signature(name, args, refmask, stmt) else {
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
                let owned: Vec<Value> = args.iter_mut().map(std::mem::take).collect();
                let mut ca = CallArgs { args: owned, params: full_params, nresults: nres, name, span };
                let r = fun(self, &mut ca);
                for (i, v) in ca.args.into_iter().enumerate() {
                    if i < args.len() {
                        args[i] = v;
                    }
                }
                r.map_err(|e| if e.span.is_none() && e.kind != ErrKind::Syntax { e.in_context(name.to_string()) } else { e })
            }
            Imp::User(clo) => {
                let clo = clo.clone();
                let user_params: Vec<(Sym, Value)> = params;
                self.call_closure(&clo, args, refmask, user_params, nres, span, Some(name.to_string()))
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
        let mask = vec![false; args.len()];
        let Some(sig) = self.select_signature(sym, &args, &mask, false) else {
            return Ok(None);
        };
        if sig.generic {
            return Ok(None);
        }
        let mut args = args;
        let r = self.call_intrinsic(sym, &mut args, &mask, Vec::new(), 1, false, Span::default())?;
        Ok(r.and_then(|v| v.into_iter().next()))
    }

    pub fn type_name_ext(&self, v: &Value) -> String {
        match self.extended_type(v) {
            Some(t) => t.display(&self.types).to_string(),
            None => self.type_name(v),
        }
    }
}
