//! Iteration: `for` loops, domains, and constructor comprehensions.

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_syntax::Span;

use super::{Flow, Frame, Interp};
use crate::error::{NOT_ITERABLE, RResult, RuntimeError};
use crate::ir::*;
use crate::value::*;

/// An iterator over the elements of an enumerable value. Each item is
/// `(index, element)`, where the index is what dual iteration binds first.
pub enum ValueIter {
    Small { cur: i64, step: i64, remaining: u64 },
    Big { cur: Integer, step: Integer, remaining: u64 },
    Seq(Rc<SeqEnum>, usize),
    List(Rc<Vec<Value>>, usize),
    Set(Rc<SetEnum>, usize),
    ISet(Rc<SetIndx>, usize),
    MSet { set: Rc<SetMulti>, pos: usize, rep: u64, dual: bool },
    Assoc(Rc<Assoc>, usize),
    Values(Vec<Value>, usize),
}

impl ValueIter {
    pub fn range(lo: Integer, hi: &Integer, step: Integer) -> ValueIter {
        let n = range_len(&lo, hi, &step);
        match (lo.to_i64(), step.to_i64(), hi.to_i64()) {
            (Some(a), Some(s), Some(_)) if a.checked_add(s.saturating_mul(n.min(i64::MAX as u64) as i64)).is_some() => {
                ValueIter::Small { cur: a, step: s, remaining: n }
            }
            _ => ValueIter::Big { cur: lo, step, remaining: n },
        }
    }

    pub fn next_item(&mut self) -> Option<(Value, Value)> {
        match self {
            ValueIter::Small { cur, step, remaining } => {
                if *remaining == 0 {
                    return None;
                }
                *remaining -= 1;
                let v = *cur;
                *cur = cur.wrapping_add(*step);
                Some((Value::Undef, Value::int(v)))
            }
            ValueIter::Big { cur, step, remaining } => {
                if *remaining == 0 {
                    return None;
                }
                *remaining -= 1;
                let v = cur.clone();
                *cur = &*cur + &*step;
                Some((Value::Undef, Value::Int(v)))
            }
            ValueIter::Seq(s, i) => loop {
                let v = s.elems.get(*i)?.clone();
                *i += 1;
                if !v.is_undef() {
                    return Some((Value::int(*i as i64), v));
                }
            },
            ValueIter::List(s, i) => {
                let v = s.get(*i)?.clone();
                *i += 1;
                Some((Value::int(*i as i64), v))
            }
            ValueIter::Set(s, i) => {
                let v = match &s.repr {
                    SetRepr::Range { lo, step, len } => {
                        if *i as u64 >= *len {
                            return None;
                        }
                        Value::Int(lo + &(step * &Integer::from_u64(*i as u64)))
                    }
                    SetRepr::Elems(e) => e.get_index(*i)?.clone(),
                };
                *i += 1;
                Some((Value::int(*i as i64), v))
            }
            ValueIter::ISet(s, i) => {
                let v = s.elems.get_index(*i)?.clone();
                *i += 1;
                Some((Value::int(*i as i64), v))
            }
            ValueIter::MSet { set, pos, rep, dual } => {
                let (v, n) = set.elems.get_index(*pos)?;
                if *dual {
                    *pos += 1;
                    return Some((v.clone(), Value::Int(Integer::from_u64(*n))));
                }
                let v = v.clone();
                *rep += 1;
                if *rep >= *n {
                    *rep = 0;
                    *pos += 1;
                }
                Some((Value::Undef, v))
            }
            ValueIter::Assoc(a, i) => {
                let (k, v) = a.map.get_index(*i)?;
                *i += 1;
                Some((k.clone(), v.clone()))
            }
            ValueIter::Values(v, i) => {
                let x = v.get(*i)?.clone();
                *i += 1;
                Some((Value::int(*i as i64), x))
            }
        }
    }
}

impl Interp {
    /// Start iterating over `dom`. `dual` selects the `i -> x` form.
    pub fn iter_value(&mut self, dom: &Value, dual: bool) -> RResult<ValueIter> {
        Ok(match dom {
            Value::Seq(s) => ValueIter::Seq(s.clone(), 0),
            Value::List(l) => ValueIter::List(l.clone(), 0),
            Value::Set(s) => ValueIter::Set(s.clone(), 0),
            Value::ISet(s) => ValueIter::ISet(s.clone(), 0),
            Value::MSet(s) => ValueIter::MSet { set: s.clone(), pos: 0, rep: 0, dual },
            Value::Tuple(t) => ValueIter::Values(t.elems.clone(), 0),
            Value::Assoc(a) => {
                if dual {
                    ValueIter::Assoc(a.clone(), 0)
                } else {
                    // Plain iteration over an associative array gives its values.
                    ValueIter::Values(a.map.values().cloned().collect(), 0)
                }
            }
            _ => ValueIter::Values(self.enumerate_structure(dom)?, 0),
        })
    }

    /// All elements of a finite structure that is not itself an aggregate.
    pub fn enumerate_structure(&mut self, s: &Value) -> RResult<Vec<Value>> {
        match s {
            Value::Struct(st) => match &st.kind {
                StructKind::Booleans => Ok(vec![Value::Bool(false), Value::Bool(true)]),
                StructKind::Cartesian(parts) => {
                    let mut lists = Vec::new();
                    for p in parts {
                        let mut it = self.iter_value(p, false)?;
                        let mut v = Vec::new();
                        while let Some((_, x)) = it.next_item() {
                            v.push(x);
                        }
                        lists.push(v);
                    }
                    let mut out = vec![Vec::new()];
                    for l in &lists {
                        let mut next = Vec::with_capacity(out.len() * l.len());
                        for prefix in &out {
                            for x in l {
                                let mut p = prefix.clone();
                                p.push(x.clone());
                                next.push(p);
                            }
                        }
                        out = next;
                    }
                    Ok(out.into_iter().map(|elems| Value::Tuple(Rc::new(Tuple { elems, parent: Some(s.clone()) }))).collect())
                }
                StructKind::Coproduct(_) => Err(RuntimeError::runtime(NOT_ITERABLE)),
                StructKind::Ring(_) => self.enumerate_ring(st),
                StructKind::ResIdeal(..) => self.enumerate_res_ideal(st),
                StructKind::AbGroup(_) => self.enumerate_abgroup(st),
                _ => Err(RuntimeError::runtime(NOT_ITERABLE)),
            },
            _ => Err(RuntimeError::runtime(NOT_ITERABLE)),
        }
    }

    pub fn type_name(&self, v: &Value) -> String {
        self.types.name(v.type_id()).to_string()
    }

    /// The domain of a loop or comprehension: one that cannot be iterated
    /// over is reported at the loop variable, as an error in `for`.
    pub fn loop_domain(&mut self, d: &DomainEx, f: &mut Frame, dual: bool, var_span: Span) -> RResult<ValueIter> {
        self.domain_iter(d, f, dual).map_err(|e| if e.message == NOT_ITERABLE && e.context.is_none() { e.in_context("for").at(var_span) } else { e })
    }

    pub fn domain_iter(&mut self, d: &DomainEx, f: &mut Frame, dual: bool) -> RResult<ValueIter> {
        match d {
            DomainEx::Range(a, b, c) => {
                let (lo, hi, step) = self.range_bounds(a, b, c.as_ref(), f)?;
                Ok(ValueIter::range(lo, &hi, step))
            }
            DomainEx::General(e) => {
                let v = self.eval(e, f)?;
                self.iter_value(&v, dual)
            }
        }
    }

    pub fn range_bounds(&mut self, a: &E, b: &E, c: Option<&E>, f: &mut Frame) -> RResult<(Integer, Integer, Integer)> {
        let lo = self.eval(a, f)?;
        let hi = self.eval(b, f)?;
        let step = match c {
            Some(c) => self.eval(c, f)?,
            None => Value::int(1),
        };
        let as_int = |v: Value| -> RResult<Integer> {
            match v {
                Value::Int(i) => Ok(i),
                Value::Rat(q) if q.is_integral() => Ok(q.numerator()),
                _ => Err(RuntimeError::runtime("Arithmetic progression bounds must be integers").in_context("..")),
            }
        };
        let (lo, hi, step) = (as_int(lo)?, as_int(hi)?, as_int(step)?);
        if step.is_zero() {
            return Err(RuntimeError::runtime("Step size must be non-zero").in_context(".."));
        }
        Ok((lo, hi, step))
    }

    fn loop_body(&mut self, body: &[S], f: &mut Frame, var: &Place) -> RResult<Option<Flow>> {
        match self.exec_block(body, f)? {
            Flow::Normal | Flow::Continue(None) => Ok(None),
            Flow::Continue(Some(l)) if l == var.name() => Ok(None),
            Flow::Break(None) => Ok(Some(Flow::Normal)),
            Flow::Break(Some(l)) if l == var.name() => Ok(Some(Flow::Normal)),
            other => Ok(Some(other)),
        }
    }

    pub(super) fn for_range(&mut self, var: &Place, from: &E, to: &E, by: Option<&E>, body: &[S], f: &mut Frame) -> RResult<Flow> {
        let (lo, hi, step) = self.range_bounds(from, to, by, f).map_err(|e| e.in_context("for"))?;
        let mut it = ValueIter::range(lo, &hi, step);
        while let Some((_, v)) = it.next_item() {
            self.check_interrupt()?;
            self.assign_place(*var, v, f)?;
            if let Some(flow) = self.loop_body(body, f, var)? {
                return Ok(flow);
            }
        }
        Ok(Flow::Normal)
    }

    /// Bind a loop variable. A structure without a name is known by the
    /// loop variable only while the variable holds it; `named` tracks the
    /// structure named this way so the name can be taken back.
    fn bind_loop_var(&mut self, var: Place, v: Value, f: &mut Frame, named: &mut Option<Value>) {
        if let Some(cell) = named.take().as_ref().and_then(|n| n.name_cell()) {
            *cell.borrow_mut() = None;
        }
        if let Some(cell) = v.name_cell() {
            if cell.borrow().is_none() {
                *cell.borrow_mut() = Some(var.name());
                *named = Some(v.clone());
            }
        }
        self.store_place(var, v, f);
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn for_in(&mut self, var: &Place, index: Option<&Place>, domain: &DomainEx, random: bool, body: &[S], f: &mut Frame, var_span: Span) -> RResult<Flow> {
        let mut named = None;
        let r = self.for_in_named(var, index, domain, random, body, f, &mut named, var_span);
        if let Some(cell) = named.as_ref().and_then(|n| n.name_cell()) {
            *cell.borrow_mut() = None;
        }
        r
    }

    #[allow(clippy::too_many_arguments)]
    fn for_in_named(&mut self, var: &Place, index: Option<&Place>, domain: &DomainEx, random: bool, body: &[S], f: &mut Frame, named: &mut Option<Value>, var_span: Span) -> RResult<Flow> {
        if random {
            let dom = match domain {
                DomainEx::General(e) => self.eval(e, f)?,
                DomainEx::Range(a, b, c) => {
                    let (lo, hi, step) = self.range_bounds(a, b, c.as_ref(), f)?;
                    Value::Set(Rc::new(SetEnum::range(lo, &hi, step)))
                }
            };
            loop {
                self.check_interrupt()?;
                let (i, x) = self.random_element_indexed(&dom)?;
                if let Some(ip) = index {
                    self.assign_place(*ip, i, f)?;
                }
                self.bind_loop_var(*var, x, f, named);
                if let Some(flow) = self.loop_body(body, f, var)? {
                    return Ok(flow);
                }
            }
        }
        let mut it = self.loop_domain(domain, f, index.is_some(), var_span)?;
        while let Some((i, x)) = it.next_item() {
            self.check_interrupt()?;
            if let Some(ip) = index {
                self.assign_place(*ip, i, f)?;
            }
            self.bind_loop_var(*var, x, f, named);
            if let Some(flow) = self.loop_body(body, f, var)? {
                return Ok(flow);
            }
        }
        Ok(Flow::Normal)
    }

    /// Run a comprehension, calling `sink` with each head value.
    /// `sink` returns `false` to stop early.
    pub fn run_comprehension(&mut self, c: &ComprEx, f: &mut Frame, sink: &mut dyn FnMut(&mut Interp, Value, &mut Frame) -> RResult<bool>) -> RResult<bool> {
        self.compr_level(c, c.iters.len(), f, sink)
    }

    /// `k` iterators remain; the last one is the outermost loop.
    fn compr_level(&mut self, c: &ComprEx, k: usize, f: &mut Frame, sink: &mut dyn FnMut(&mut Interp, Value, &mut Frame) -> RResult<bool>) -> RResult<bool> {
        if k == 0 {
            for (slots, e) in &c.lets {
                self.bind_values(slots, e, f)?;
            }
            if let Some(p) = &c.pred {
                if !self.eval_bool(p, f)? {
                    return Ok(true);
                }
            }
            let v = self.eval(&c.head, f)?;
            return sink(self, v, f);
        }
        let it_ex = &c.iters[k - 1];
        let mut it = self.loop_domain(&it_ex.domain, f, it_ex.index.is_some(), it_ex.span)?;
        while let Some((i, x)) = it.next_item() {
            self.check_interrupt()?;
            if let Some(islot) = it_ex.index {
                f.set(islot, i);
            }
            f.set(it_ex.var, x);
            if !self.compr_level(c, k - 1, f, sink)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Choose a random element of an enumerable value, with its index.
    pub fn random_element_indexed(&mut self, dom: &Value) -> RResult<(Value, Value)> {
        let items: Vec<(Value, Value)> = {
            let mut it = self.iter_value(dom, true)?;
            // Fast paths for large ranges and sequences.
            match &it {
                ValueIter::Set(s, _) if s.is_range() => {
                    if let SetRepr::Range { lo, step, len } = &s.repr {
                        if *len == 0 {
                            return Err(RuntimeError::runtime("Cannot choose a random element of an empty set"));
                        }
                        let k = self.rng.below_u64(*len);
                        return Ok((Value::int(k as i64 + 1), Value::Int(lo + &(step * &Integer::from_u64(k)))));
                    }
                    unreachable!()
                }
                ValueIter::Seq(s, _) => {
                    if s.elems.is_empty() {
                        return Err(RuntimeError::runtime("Cannot choose a random element of an empty sequence"));
                    }
                    let k = self.rng.below_u64(s.elems.len() as u64) as usize;
                    return Ok((Value::int(k as i64 + 1), s.elems[k].clone()));
                }
                _ => {}
            }
            let mut v = Vec::new();
            while let Some(p) = it.next_item() {
                v.push(p);
            }
            v
        };
        if items.is_empty() {
            return Err(RuntimeError::runtime("Cannot choose a random element of an empty structure"));
        }
        let k = self.rng.below_u64(items.len() as u64) as usize;
        Ok(items[k].clone())
    }
}
