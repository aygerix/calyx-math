//! Parents, coercion, universes of aggregates, and type matching.

use std::rc::Rc;

use calyx_flint::{Rational, Real, bits_for_digits};
use calyx_syntax::ast::AggKind;

use crate::error::{RResult, RuntimeError};
use crate::interp::Interp;
use crate::sym::Sym;
use crate::types::{TypeArg, TypeId, TypePat, TypeVal, t};
use crate::value::*;

impl Interp {
    // ----- parents --------------------------------------------------------

    pub fn parent_of(&mut self, v: &Value) -> RResult<Value> {
        Ok(match v {
            Value::Undef => return Err(RuntimeError::runtime("An undefined value has no parent")),
            Value::Bool(_) => Value::booleans(),
            Value::Int(_) => Value::integers(),
            Value::Rat(_) => Value::rationals(),
            Value::Real(r) => Value::reals(r.digits),
            Value::Str(_) => Value::strings(),
            Value::Seq(s) => Value::structure(StructKind::PowerSeq(s.universe.clone())),
            Value::Set(s) => Value::structure(StructKind::PowerSet(s.universe.clone())),
            Value::ISet(s) => Value::structure(StructKind::PowerISet(s.universe.clone())),
            Value::MSet(s) => Value::structure(StructKind::PowerMSet(s.universe.clone())),
            Value::Tuple(tp) => match &tp.parent {
                Some(p) => p.clone(),
                None => {
                    let mut parts = Vec::with_capacity(tp.elems.len());
                    for e in &tp.elems {
                        parts.push(self.parent_of(e)?);
                    }
                    Value::structure(StructKind::Cartesian(parts))
                }
            },
            Value::Rec(r) => Value::Struct(r.format.clone()),
            Value::Map(m) => Value::structure(StructKind::Maps(m.domain.clone(), m.codomain.clone())),
            Value::CopElt(c) => Value::Struct(c.cop.clone()),
            Value::Elt(e) => e.parent_value(),
            Value::Obj(o) => {
                let sym = Sym::new("Parent");
                if self.select_signature(sym, std::slice::from_ref(v), &[false], false).is_some_and(|s| !s.generic) {
                    return self.call_intrinsic_named(sym, vec![v.clone()]);
                }
                Value::structure(StructKind::PowerStructure(o.ty))
            }
            Value::Struct(_) => Value::structure(StructKind::PowerStructure(v.type_id())),
            other => Value::structure(StructKind::PowerStructure(other.type_id())),
        })
    }

    // ----- coercion -------------------------------------------------------

    /// `S ! x`
    pub fn coerce(&mut self, s: &Value, x: &Value) -> RResult<Value> {
        match self.try_coerce(s, x)? {
            Ok(v) => Ok(v),
            Err(msg) => {
                let reason = msg.unwrap_or_else(|| "Illegal coercion".to_string());
                // Magma shows a tuple's type as <>.
                let rhs = if matches!(x, Value::Tuple(_)) { "<>".to_string() } else { self.type_name(x) };
                let text = format!("{reason}\nLHS: {}\nRHS: {rhs}", self.type_name(s));
                Err(RuntimeError { style: crate::error::ErrStyle::Plain, ..RuntimeError::runtime(text) })
            }
        }
    }

    /// Attempt a coercion. The inner `Err` carries an optional reason.
    pub fn try_coerce(&mut self, s: &Value, x: &Value) -> RResult<Result<Value, Option<String>>> {
        if x.is_undef() {
            return Ok(Err(Some("Cannot coerce an undefined value".into())));
        }
        let fail = || Ok(Err(None));
        match s {
            Value::Struct(st) => match &st.kind {
                StructKind::Ring(_) => self.coerce_into_ring(st, x),
                StructKind::Integers | StructKind::Rationals | StructKind::Reals(_) if matches!(x, Value::Elt(_)) => {
                    let Value::Elt(e) = x else { unreachable!() };
                    match self.coerce_ring_elt_down(&st.kind, e) {
                        Some(v) => Ok(Ok(v)),
                        None => fail(),
                    }
                }
                StructKind::Integers => match x {
                    Value::Int(_) => Ok(Ok(x.clone())),
                    Value::Rat(q) if q.is_integral() => Ok(Ok(Value::Int(q.numerator()))),
                    Value::Rat(_) => Ok(Err(Some("Rational argument is not a whole integer".into()))),
                    Value::Str(s) => match calyx_flint::Integer::parse(s.trim()) {
                        Some(i) => Ok(Ok(Value::Int(i))),
                        None => Ok(Err(Some("String does not represent an integer".into()))),
                    },
                    Value::Seq(q) if q.elems.len() == 1 => {
                        let e = q.elems[0].clone();
                        self.try_coerce(s, &e)
                    }
                    _ => fail(),
                },
                StructKind::Rationals => match x {
                    Value::Int(i) => Ok(Ok(Value::rat(Rational::from_integer(i)))),
                    Value::Rat(_) => Ok(Ok(x.clone())),
                    _ => fail(),
                },
                StructKind::Reals(d) => {
                    let bits = bits_for_digits(*d as u64);
                    let r = match x {
                        Value::Int(i) => Real::from_integer(i, bits),
                        Value::Rat(q) => Real::from_rational(q, bits),
                        Value::Real(r) => r.x.round_to(bits),
                        _ => return fail(),
                    };
                    Ok(Ok(Value::real(r, *d)))
                }
                StructKind::Booleans => match x {
                    Value::Bool(_) => Ok(Ok(x.clone())),
                    _ => fail(),
                },
                StructKind::Strings => match x {
                    Value::Str(_) => Ok(Ok(x.clone())),
                    _ => fail(),
                },
                StructKind::PowerSet(u) => match x {
                    Value::Set(set) => {
                        let Some(u) = u else { return Ok(Ok(x.clone())) };
                        let mut out = VSet::default();
                        for e in set.iter() {
                            match self.try_coerce(u, &e)? {
                                Ok(v) => {
                                    out.insert(v);
                                }
                                Err(m) => return Ok(Err(m)),
                            }
                        }
                        let mut elems: Vec<Value> = out.into_iter().collect();
                        sort_values(&mut elems);
                        Ok(Ok(Value::Set(Rc::new(SetEnum::new(Some(u.clone()), elems.into_iter().collect())))))
                    }
                    _ => fail(),
                },
                StructKind::PowerISet(u) => match x {
                    Value::ISet(set) => {
                        let Some(u) = u else { return Ok(Ok(x.clone())) };
                        let mut out = VSet::default();
                        for e in set.elems.iter() {
                            match self.try_coerce(u, e)? {
                                Ok(v) => {
                                    out.insert(v);
                                }
                                Err(m) => return Ok(Err(m)),
                            }
                        }
                        Ok(Ok(Value::ISet(Rc::new(SetIndx { universe: Some(u.clone()), elems: out }))))
                    }
                    _ => fail(),
                },
                StructKind::PowerMSet(u) => match x {
                    Value::MSet(set) => {
                        let Some(u) = u else { return Ok(Ok(x.clone())) };
                        let mut out = SetMulti { universe: Some(u.clone()), elems: VMap::default() };
                        for (e, n) in set.elems.iter() {
                            match self.try_coerce(u, e)? {
                                Ok(v) => out.insert(v, *n),
                                Err(m) => return Ok(Err(m)),
                            }
                        }
                        Ok(Ok(Value::MSet(Rc::new(out))))
                    }
                    _ => fail(),
                },
                StructKind::PowerSeq(u) => match x {
                    Value::Seq(seq) => {
                        let Some(u) = u else { return Ok(Ok(x.clone())) };
                        let mut out = Vec::with_capacity(seq.elems.len());
                        for e in &seq.elems {
                            if e.is_undef() {
                                out.push(Value::Undef);
                                continue;
                            }
                            match self.try_coerce(u, e)? {
                                Ok(v) => out.push(v),
                                Err(m) => return Ok(Err(m)),
                            }
                        }
                        Ok(Ok(Value::seq(Some(u.clone()), out)))
                    }
                    _ => fail(),
                },
                StructKind::Cartesian(parts) => match x {
                    Value::Tuple(tp) if tp.elems.len() == parts.len() => {
                        let mut out = Vec::with_capacity(parts.len());
                        for (p, e) in parts.iter().zip(&tp.elems) {
                            match self.try_coerce(p, e)? {
                                Ok(v) => out.push(v),
                                Err(_) => return fail(),
                            }
                        }
                        Ok(Ok(Value::Tuple(Rc::new(Tuple { elems: out, parent: Some(s.clone()) }))))
                    }
                    _ => fail(),
                },
                StructKind::Coproduct(parts) => {
                    if let Value::CopElt(c) = x {
                        if struct_eq(&c.cop, st) {
                            return Ok(Ok(x.clone()));
                        }
                    }
                    for (i, p) in parts.iter().enumerate() {
                        if let Ok(v) = self.try_coerce(p, x)? {
                            return Ok(Ok(Value::CopElt(Rc::new(CopElt { cop: st.clone(), index: i, value: v }))));
                        }
                    }
                    Ok(Err(Some("No constituent (with unique type) to coerce into".into())))
                }
                StructKind::PowerStructure(ty) => {
                    let xt = self.effective_type(x);
                    if self.types.isa(xt, *ty) { Ok(Ok(x.clone())) } else { fail() }
                }
                StructKind::RecFormat(_) => match x {
                    Value::Rec(r) if Rc::ptr_eq(&r.format, st) => Ok(Ok(x.clone())),
                    _ => fail(),
                },
                StructKind::Maps(..) => match x {
                    Value::Map(_) => Ok(Ok(x.clone())),
                    _ => fail(),
                },
            },
            // An aggregate used as a universe: coerce into its universe and
            // check membership.
            Value::Seq(_) | Value::Set(_) | Value::ISet(_) | Value::MSet(_) => {
                let u = match s {
                    Value::Seq(a) => a.universe.clone(),
                    Value::Set(a) => a.universe.clone(),
                    Value::ISet(a) => a.universe.clone(),
                    Value::MSet(a) => a.universe.clone(),
                    _ => unreachable!(),
                };
                let v = match u {
                    Some(u) => match self.try_coerce(&u, x)? {
                        Ok(v) => v,
                        Err(m) => return Ok(Err(m)),
                    },
                    None => x.clone(),
                };
                if self.contains(s, &v)? { Ok(Ok(v)) } else { Ok(Err(Some("Element is not in the given set".into()))) }
            }
            Value::Formal(fs) => {
                let fs = fs.clone();
                let v = match self.try_coerce(&fs.universe, x)? {
                    Ok(v) => v,
                    Err(m) => return Ok(Err(m)),
                };
                if self.formal_contains(&fs, &v)? { Ok(Ok(v)) } else { fail() }
            }
            Value::Obj(_) => {
                let sym = Sym::new("IsCoercible");
                if self.select_signature(sym, &[s.clone(), x.clone()], &[false, false], false).is_some_and(|sig| !sig.generic) {
                    let r = self.call_function_multi(&Value::Intr(sym), vec![s.clone(), x.clone()], 2)?;
                    return match r.as_slice() {
                        [Value::Bool(true), v, ..] => Ok(Ok(v.clone())),
                        [Value::Bool(false), Value::Str(m), ..] => Ok(Err(Some(m.to_string()))),
                        _ => fail(),
                    };
                }
                let p = self.parent_of(x)?;
                if &p == s { Ok(Ok(x.clone())) } else { fail() }
            }
            _ => Err(RuntimeError::runtime(format!("Cannot coerce into an object of type {}", self.type_name(s)))),
        }
    }

    pub fn coerce_into_universe(&mut self, u: &Value, x: &Value) -> RResult<Value> {
        match self.try_coerce(u, x)? {
            Ok(v) => Ok(v),
            Err(m) => Err(RuntimeError::runtime(m.unwrap_or_else(|| "Could not coerce the element into the universe".to_string()))),
        }
    }

    pub fn try_coerce_into_universe(&mut self, u: &Value, x: &Value) -> RResult<Option<Value>> {
        Ok(self.try_coerce(u, x)?.ok())
    }

    /// The type used for signature matching (user objects report their type).
    pub fn effective_type(&self, v: &Value) -> TypeId {
        v.type_id()
    }

    // ----- common universes ----------------------------------------------

    /// A structure containing both `a` and `b` (automatic coercion only).
    pub fn common_universe(&self, a: &Value, b: &Value) -> Option<Value> {
        if a == b {
            return Some(a.clone());
        }
        // An aggregate used as a universe behaves like its own universe.
        let agg_universe = |v: &Value| -> Option<Option<Value>> {
            match v {
                Value::Seq(s) => Some(s.universe.clone()),
                Value::Set(s) => Some(s.universe.clone()),
                Value::ISet(s) => Some(s.universe.clone()),
                Value::MSet(s) => Some(s.universe.clone()),
                _ => None,
            }
        };
        if let Some(u) = agg_universe(a) {
            return match u {
                Some(u) => self.common_universe(&u, b),
                None => Some(b.clone()),
            };
        }
        if let Some(u) = agg_universe(b) {
            return match u {
                Some(u) => self.common_universe(a, &u),
                None => Some(a.clone()),
            };
        }
        let (Value::Struct(x), Value::Struct(y)) = (a, b) else {
            return None;
        };
        if matches!(x.kind, StructKind::Ring(_)) || matches!(y.kind, StructKind::Ring(_)) {
            return self.common_ring_existing(a, b);
        }
        use StructKind::*;
        let opt = |p: &Option<Value>, q: &Option<Value>| -> Option<Option<Value>> {
            match (p, q) {
                (None, None) => Some(None),
                (Some(p), None) | (None, Some(p)) => Some(Some(p.clone())),
                (Some(p), Some(q)) => self.common_universe(p, q).map(Some),
            }
        };
        match (&x.kind, &y.kind) {
            (Integers, Rationals) | (Rationals, Integers) => Some(Value::rationals()),
            (Integers | Rationals, Reals(_)) => Some(b.clone()),
            (Reals(_), Integers | Rationals) => Some(a.clone()),
            (Reals(p), Reals(q)) => Some(Value::reals(*p.min(q))),
            (PowerSeq(p), PowerSeq(q)) => opt(p, q).map(|u| Value::structure(PowerSeq(u))),
            (PowerSet(p), PowerSet(q)) => opt(p, q).map(|u| Value::structure(PowerSet(u))),
            (PowerISet(p), PowerISet(q)) => opt(p, q).map(|u| Value::structure(PowerISet(u))),
            (PowerMSet(p), PowerMSet(q)) => opt(p, q).map(|u| Value::structure(PowerMSet(u))),
            (Cartesian(p), Cartesian(q)) if p.len() == q.len() => {
                let mut parts = Vec::with_capacity(p.len());
                for (u, v) in p.iter().zip(q) {
                    parts.push(self.common_universe(u, v)?);
                }
                Some(Value::structure(Cartesian(parts)))
            }
            (PowerStructure(s), PowerStructure(t)) => {
                // Structures of different kinds cannot share a universe.
                if self.types.isa(*s, *t) {
                    Some(b.clone())
                } else if self.types.isa(*t, *s) {
                    Some(a.clone())
                } else if self.types.info(*s).user || self.types.info(*t).user {
                    Some(Value::structure(PowerStructure(self.common_ancestor(*s, *t))))
                } else {
                    None
                }
            }
            (Maps(..), Maps(..)) => Some(Value::structure(PowerStructure(t::MAP))),
            _ => None,
        }
    }

    fn common_ancestor(&self, a: TypeId, b: TypeId) -> TypeId {
        let mut queue = vec![a];
        let mut i = 0;
        while i < queue.len() {
            let x = queue[i];
            if self.types.isa(b, x) {
                return x;
            }
            for p in &self.types.info(x).parents {
                if !queue.contains(p) {
                    queue.push(*p);
                }
            }
            i += 1;
        }
        t::ANY
    }

    /// Find the universe for the given elements and coerce them into it.
    pub fn unify_universe(&mut self, vals: &mut [Value], universe: Option<Value>) -> RResult<Option<Value>> {
        if let Some(u) = universe {
            for (i, v) in vals.iter_mut().enumerate() {
                if v.is_undef() {
                    return Err(RuntimeError::runtime("Undefined element in constructor"));
                }
                match self.try_coerce(&u, v)? {
                    Ok(c) => *v = c,
                    Err(_) => return Err(RuntimeError::runtime(format!("Cannot coerce argument {} into the universe", i + 1))),
                }
            }
            return Ok(Some(u));
        }
        if vals.is_empty() {
            return Ok(None);
        }
        let mut parents = Vec::with_capacity(vals.len());
        let mut u: Option<Value> = None;
        for (i, v) in vals.iter().enumerate() {
            if v.is_undef() {
                return Err(RuntimeError::runtime("Undefined element in constructor"));
            }
            let p = self.parent_of(v)?;
            u = Some(match u {
                None => p.clone(),
                Some(cur) => {
                    if cur == p {
                        cur
                    } else {
                        match self.common_universe(&cur, &p) {
                            Some(c) => c,
                            None => return Err(RuntimeError::runtime(format!("Cannot coerce argument {} into the universe", i + 1))),
                        }
                    }
                }
            });
            parents.push(p);
        }
        let u = u.unwrap();
        for (v, p) in vals.iter_mut().zip(parents) {
            if p != u {
                let c = self.coerce_into_universe(&u, v)?;
                *v = c;
            } else if let Value::Tuple(tp) = v {
                if tp.parent.is_none() {
                    Rc::make_mut(tp).parent = Some(u.clone());
                }
            }
        }
        Ok(Some(u))
    }

    /// Build an enumerated sequence, set or indexed set from values.
    pub fn build_aggregate(&mut self, kind: AggKind, universe: Option<Value>, mut vals: Vec<Value>, trusted: bool) -> RResult<Value> {
        let u = if trusted { universe } else { self.unify_universe(&mut vals, universe)? };
        Ok(match kind {
            AggKind::Seq => Value::seq(u, vals),
            AggKind::Set => {
                let mut set: VSet = VSet::with_capacity_and_hasher(vals.len(), Default::default());
                for v in vals {
                    set.insert(v);
                }
                let mut elems: Vec<Value> = set.into_iter().collect();
                sort_values(&mut elems);
                Value::Set(Rc::new(SetEnum::new(u, elems.into_iter().collect())))
            }
            AggKind::ISet => {
                let mut set: VSet = VSet::with_capacity_and_hasher(vals.len(), Default::default());
                for v in vals {
                    set.insert(v);
                }
                Value::ISet(Rc::new(SetIndx { universe: u, elems: set }))
            }
            AggKind::MSet => {
                let n = vals.len();
                return self.build_multiset(u, vals, vec![1; n]);
            }
        })
    }

    pub fn build_multiset(&mut self, universe: Option<Value>, mut vals: Vec<Value>, mults: Vec<u64>) -> RResult<Value> {
        let u = self.unify_universe(&mut vals, universe)?;
        let mut m = SetMulti { universe: u, elems: VMap::default() };
        for (v, n) in vals.into_iter().zip(mults) {
            m.insert(v, n);
        }
        Ok(Value::MSet(Rc::new(m)))
    }

    /// Coerce a record field value into its declared structure, or check it
    /// against its declared category.
    pub fn coerce_field(&mut self, t: &Value, v: Value) -> RResult<Value> {
        match t {
            Value::Cat(c) => {
                if self.types.isa(self.effective_type(&v), *c) {
                    Ok(v)
                } else {
                    Err(RuntimeError::runtime(format!("Field value must be of type {}", self.types.name(*c))))
                }
            }
            _ => self.coerce(t, &v),
        }
    }

    pub fn cartesian_product(&mut self, parts: Vec<Value>) -> RResult<Value> {
        for p in &parts {
            if !p.is_structure_like() {
                return Err(RuntimeError::runtime(format!("Cartesian product components must be structures, not {}", self.type_name(p))).in_context("car< >"));
            }
        }
        Ok(Value::structure(StructKind::Cartesian(parts)))
    }

    pub fn make_record(&mut self, fmt: &Value, fields: Vec<(Sym, Value)>) -> RResult<Value> {
        let Value::Struct(st) = fmt else {
            return Err(RuntimeError::runtime("rec< > requires a record format").in_context("rec< >"));
        };
        let StructKind::RecFormat(rf) = &st.kind else {
            return Err(RuntimeError::runtime("rec< > requires a record format").in_context("rec< >"));
        };
        let mut vals = vec![Value::Undef; rf.names.len()];
        for (n, v) in fields {
            let Some(k) = rf.names.iter().position(|x| *x == n) else {
                return Err(RuntimeError::runtime(format!("Field '{n}' is not in the format")).in_context("rec< >"));
            };
            vals[k] = match &rf.types[k] {
                Some(t) => match self.coerce_field(t, v) {
                    Ok(x) => x,
                    Err(_) => {
                        let msg = match t {
                            Value::Cat(c) => format!("Value for field '{n}' should have category {}", self.types.name(*c)),
                            _ => format!("Value for field '{n}' not in structure given by format"),
                        };
                        return Err(RuntimeError::runtime(msg).in_context("rec< >"));
                    }
                },
                None => v,
            };
        }
        Ok(Value::Rec(Rc::new(Record { format: st.clone(), fields: vals })))
    }

    // ----- membership -----------------------------------------------------

    /// `x in S` for aggregates and structures.
    pub fn contains(&mut self, s: &Value, x: &Value) -> RResult<bool> {
        match s {
            Value::Set(set) => {
                if set.contains(x) {
                    return Ok(true);
                }
                match &set.universe {
                    Some(u) => {
                        let u = u.clone();
                        match self.try_coerce(&u, x)? {
                            Ok(v) => Ok(set.contains(&v)),
                            Err(_) => Err(RuntimeError::runtime("Element is not coercible into the universe of the set").in_context("in")),
                        }
                    }
                    None => Ok(false),
                }
            }
            Value::ISet(set) => {
                if set.elems.contains(x) {
                    return Ok(true);
                }
                match &set.universe {
                    Some(u) => {
                        let u = u.clone();
                        match self.try_coerce(&u, x)? {
                            Ok(v) => Ok(set.elems.contains(&v)),
                            Err(_) => Err(RuntimeError::runtime("Element is not coercible into the universe of the set").in_context("in")),
                        }
                    }
                    None => Ok(false),
                }
            }
            Value::MSet(set) => {
                if set.elems.contains_key(x) {
                    return Ok(true);
                }
                match &set.universe {
                    Some(u) => {
                        let u = u.clone();
                        match self.try_coerce(&u, x)? {
                            Ok(v) => Ok(set.elems.contains_key(&v)),
                            Err(_) => Err(RuntimeError::runtime("Element is not coercible into the universe of the set").in_context("in")),
                        }
                    }
                    None => Ok(false),
                }
            }
            Value::Seq(seq) => {
                for e in &seq.elems {
                    if !e.is_undef() && self.values_equal(e, x)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Value::List(l) => {
                for e in l.iter() {
                    if self.values_equal_weak(e, x)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Value::Tuple(tp) => {
                for e in &tp.elems {
                    if self.values_equal_weak(e, x)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Value::Str(hay) => match x {
                Value::Str(needle) => Ok(hay.contains(&**needle)),
                _ => Err(RuntimeError::runtime("Bad argument types").in_context("in")),
            },
            Value::Formal(fs) => {
                let fs = fs.clone();
                match self.try_coerce(&fs.universe, x)? {
                    Ok(v) => self.formal_contains(&fs, &v),
                    Err(_) => Ok(false),
                }
            }
            Value::Assoc(_) => Err(RuntimeError::runtime("Use IsDefined to test membership in an associative array").in_context("in")),
            Value::Struct(_) | Value::Obj(_) => {
                if let Value::Obj(_) = s {
                    if let Some(v) = self.dispatch_user_operator("in", vec![x.clone(), s.clone()])? {
                        return match v {
                            Value::Bool(b) => Ok(b),
                            _ => Err(RuntimeError::runtime("'in' must return a boolean")),
                        };
                    }
                }
                match self.try_coerce(s, x)? {
                    Ok(v) => Ok(self.values_equal_weak(&v, x)?),
                    Err(_) => Ok(false),
                }
            }
            other => Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}, {}", self.type_name(x), self.type_name(other))).in_context("in")),
        }
    }

    pub fn formal_contains(&mut self, fs: &Formal, x: &Value) -> RResult<bool> {
        if !self.contains_structure_or_agg(&fs.universe, x)? {
            return Ok(false);
        }
        match &fs.pred {
            None => Ok(true),
            Some(p) => match self.call_function(p, vec![x.clone()])? {
                Value::Bool(b) => Ok(b),
                _ => Err(RuntimeError::runtime("The predicate of a formal set must return a boolean")),
            },
        }
    }

    fn contains_structure_or_agg(&mut self, s: &Value, x: &Value) -> RResult<bool> {
        match s {
            Value::Struct(_) => Ok(self.try_coerce(s, x)?.is_ok()),
            _ => self.contains(s, x),
        }
    }

    // ----- types ----------------------------------------------------------

    /// The type of the elements of a structure, as an extended type.
    pub fn element_type_of(&mut self, u: &Value) -> TypeVal {
        match u {
            Value::Struct(s) => match &s.kind {
                StructKind::Integers => TypeVal::Cat(t::RNG_INT_ELT),
                StructKind::Rationals => TypeVal::Cat(t::FLD_RAT_ELT),
                StructKind::Reals(_) => TypeVal::Cat(t::FLD_RE_ELT),
                StructKind::Booleans => TypeVal::Cat(t::BOOL_ELT),
                StructKind::Strings => TypeVal::Cat(t::MON_STG_ELT),
                StructKind::PowerSeq(v) => self.agg_type(t::SEQ_ENUM, v),
                StructKind::PowerSet(v) => self.agg_type(t::SET_ENUM, v),
                StructKind::PowerISet(v) => self.agg_type(t::SET_INDX, v),
                StructKind::PowerMSet(v) => self.agg_type(t::SET_MULTI, v),
                StructKind::Cartesian(_) => TypeVal::Cat(t::TUP),
                StructKind::RecFormat(_) => TypeVal::Cat(t::REC),
                StructKind::Maps(..) => TypeVal::Cat(t::MAP),
                StructKind::Coproduct(_) => TypeVal::Cat(t::COP_ELT),
                StructKind::PowerStructure(ty) => TypeVal::Cat(*ty),
                StructKind::Ring(r) => TypeVal::Cat(r.elt_type()),
            },
            Value::Seq(s) => match s.universe.clone() {
                Some(u) => self.element_type_of(&u),
                None => TypeVal::Cat(t::ANY),
            },
            Value::Set(s) => match s.universe.clone() {
                Some(u) => self.element_type_of(&u),
                None => TypeVal::Cat(t::ANY),
            },
            Value::Obj(o) => match self.types.info(o.ty).elt_type {
                Some(e) => TypeVal::Cat(e),
                None => TypeVal::Cat(t::ANY),
            },
            _ => TypeVal::Cat(t::ANY),
        }
    }

    fn agg_type(&mut self, base: TypeId, u: &Option<Value>) -> TypeVal {
        match u {
            Some(u) => {
                let e = self.element_type_of(u);
                TypeVal::Ext(base, Rc::from(vec![TypeArg::Type(e)]))
            }
            None => TypeVal::Cat(base),
        }
    }

    pub fn extended_type(&self, v: &Value) -> Option<TypeVal> {
        // Extended types need `&mut self` for element types of user
        // structures; compute a conservative version here.
        let tmp = |u: &Option<Value>, base: TypeId| -> TypeVal {
            match u {
                Some(u) => TypeVal::Ext(base, Rc::from(vec![TypeArg::Type(self.static_element_type(u))])),
                None => TypeVal::Cat(base),
            }
        };
        Some(match v {
            Value::Seq(s) => tmp(&s.universe, t::SEQ_ENUM),
            Value::Set(s) => tmp(&s.universe, t::SET_ENUM),
            Value::ISet(s) => tmp(&s.universe, t::SET_INDX),
            Value::MSet(s) => tmp(&s.universe, t::SET_MULTI),
            Value::Map(m) => TypeVal::Ext(t::MAP, Rc::from(vec![TypeArg::Type(TypeVal::Cat(self.static_type_of_structure(&m.domain))), TypeArg::Type(TypeVal::Cat(self.static_type_of_structure(&m.codomain)))])),
            Value::Elt(e) => match e.ring().base() {
                Some(b) => TypeVal::Ext(v.type_id(), Rc::from(vec![TypeArg::Type(TypeVal::Cat(b.type_id()))])),
                None => TypeVal::Cat(v.type_id()),
            },
            Value::Struct(s) => match &s.kind {
                StructKind::PowerSeq(u) => tmp(u, t::POW_SEQ_ENUM),
                StructKind::PowerSet(u) => tmp(u, t::POW_SET_ENUM),
                StructKind::Ring(r) if r.base().is_some() => TypeVal::Ext(v.type_id(), Rc::from(vec![TypeArg::Type(TypeVal::Cat(r.base().unwrap().type_id()))])),
                _ => TypeVal::Cat(v.type_id()),
            },
            _ => TypeVal::Cat(v.type_id()),
        })
    }

    fn static_type_of_structure(&self, v: &Value) -> TypeId {
        v.type_id()
    }

    fn static_element_type(&self, u: &Value) -> TypeVal {
        match u {
            Value::Struct(s) => match &s.kind {
                StructKind::Integers => TypeVal::Cat(t::RNG_INT_ELT),
                StructKind::Rationals => TypeVal::Cat(t::FLD_RAT_ELT),
                StructKind::Reals(_) => TypeVal::Cat(t::FLD_RE_ELT),
                StructKind::Booleans => TypeVal::Cat(t::BOOL_ELT),
                StructKind::Strings => TypeVal::Cat(t::MON_STG_ELT),
                StructKind::PowerSeq(Some(w)) => TypeVal::Ext(t::SEQ_ENUM, Rc::from(vec![TypeArg::Type(self.static_element_type(w))])),
                StructKind::PowerSet(Some(w)) => TypeVal::Ext(t::SET_ENUM, Rc::from(vec![TypeArg::Type(self.static_element_type(w))])),
                StructKind::PowerSeq(None) => TypeVal::Cat(t::SEQ_ENUM),
                StructKind::PowerSet(None) => TypeVal::Cat(t::SET_ENUM),
                StructKind::PowerISet(_) => TypeVal::Cat(t::SET_INDX),
                StructKind::PowerMSet(_) => TypeVal::Cat(t::SET_MULTI),
                StructKind::Cartesian(_) => TypeVal::Cat(t::TUP),
                StructKind::RecFormat(_) => TypeVal::Cat(t::REC),
                StructKind::Maps(..) => TypeVal::Cat(t::MAP),
                StructKind::Coproduct(_) => TypeVal::Cat(t::COP_ELT),
                StructKind::PowerStructure(ty) => TypeVal::Cat(*ty),
                StructKind::Ring(r) => TypeVal::Cat(r.elt_type()),
            },
            Value::Seq(s) => s.universe.as_ref().map(|u| self.static_element_type(u)).unwrap_or(TypeVal::Cat(t::ANY)),
            Value::Set(s) => s.universe.as_ref().map(|u| self.static_element_type(u)).unwrap_or(TypeVal::Cat(t::ANY)),
            Value::Obj(o) => TypeVal::Cat(self.types.info(o.ty).elt_type.unwrap_or(t::ANY)),
            _ => TypeVal::Cat(t::ANY),
        }
    }

    /// Whether a value matches a signature pattern.
    pub fn value_matches(&self, v: &Value, pat: &TypePat) -> bool {
        match pat {
            TypePat::Any => true,
            TypePat::Is(ty) => self.types.isa(self.effective_type(v), *ty),
            TypePat::Tuple => matches!(v, Value::Tuple(_)),
            TypePat::Seq(inner) => match v {
                Value::Seq(s) => self.elements_match(&s.universe, s.elems.iter().find(|e| !e.is_undef()), inner),
                _ => false,
            },
            TypePat::Set(inner) => match v {
                Value::Set(s) => {
                    let first = s.iter().next();
                    self.elements_match(&s.universe, first.as_ref(), inner)
                }
                _ => false,
            },
            TypePat::SetOrSeq(inner) => self.value_matches(v, &TypePat::Seq(inner.clone())) || self.value_matches(v, &TypePat::Set(inner.clone())),
            TypePat::ISet(inner) => match v {
                Value::ISet(s) => self.elements_match(&s.universe, s.elems.first(), inner),
                _ => false,
            },
            TypePat::MSet(inner) => match v {
                Value::MSet(s) => self.elements_match(&s.universe, s.elems.keys().next(), inner),
                _ => false,
            },
            TypePat::Ext(base, params) => {
                if !self.types.isa(self.effective_type(v), *base) {
                    return false;
                }
                match self.extended_type(v) {
                    Some(tv) => {
                        let args = tv.args();
                        if args.len() < params.len() {
                            // Null aggregates have no element type; accept them.
                            return args.is_empty();
                        }
                        params.iter().zip(args).all(|(p, a)| match a {
                            TypeArg::Type(tv) => self.typeval_matches(tv, p),
                            TypeArg::Str(_) => matches!(p, TypePat::Any),
                        })
                    }
                    None => false,
                }
            }
        }
    }

    fn elements_match(&self, universe: &Option<Value>, first: Option<&Value>, inner: &Option<Box<TypePat>>) -> bool {
        let Some(inner) = inner else { return true };
        if universe.is_none() {
            return true;
        }
        if let Some(e) = first {
            return self.value_matches(e, inner);
        }
        let et = self.static_element_type(universe.as_ref().unwrap());
        self.typeval_matches(&et, inner)
    }

    pub fn typeval_matches(&self, tv: &TypeVal, pat: &TypePat) -> bool {
        match pat {
            TypePat::Any => true,
            TypePat::Is(ty) => self.types.isa(tv.base(), *ty),
            TypePat::Ext(ty, ps) => {
                self.types.isa(tv.base(), *ty)
                    && tv.args().len() >= ps.len()
                    && ps.iter().zip(tv.args()).all(|(p, a)| match a {
                        TypeArg::Type(x) => self.typeval_matches(x, p),
                        TypeArg::Str(_) => false,
                    })
            }
            TypePat::Seq(inner) => tv.base() == t::SEQ_ENUM && inner.as_ref().is_none_or(|i| tv.args().first().is_some_and(|a| matches!(a, TypeArg::Type(x) if self.typeval_matches(x, i)))),
            TypePat::Set(inner) => tv.base() == t::SET_ENUM && inner.as_ref().is_none_or(|i| tv.args().first().is_some_and(|a| matches!(a, TypeArg::Type(x) if self.typeval_matches(x, i)))),
            TypePat::SetOrSeq(_) => tv.base() == t::SET_ENUM || tv.base() == t::SEQ_ENUM,
            TypePat::ISet(_) => tv.base() == t::SET_INDX,
            TypePat::MSet(_) => tv.base() == t::SET_MULTI,
            TypePat::Tuple => tv.base() == t::TUP,
        }
    }
}
