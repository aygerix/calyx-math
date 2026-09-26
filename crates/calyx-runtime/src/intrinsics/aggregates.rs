//! Intrinsics for sets, sequences, tuples, lists, associative arrays,
//! records and coproducts (handbook Part II).

use std::cmp::Ordering;
use std::rc::Rc;

use calyx_flint::Integer;
use calyx_syntax::ast::AggKind;

use super::{boolv, none, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp, seq_index};
use crate::sym::Sym;
use crate::value::*;

/// Generate the procedure (`F(~S, ...)`) and function (`F(S, ...)`) forms
/// of an operation that modifies its first argument in place.
macro_rules! both_forms {
    ($proc:ident, $func:ident, $imp:ident) => {
        fn $proc(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
            $imp(it, a)?;
            none()
        }
        fn $func(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
            $imp(it, a)?;
            one(std::mem::take(&mut a.args[0]))
        }
    };
}

fn universe_of(v: &Value) -> Option<Option<Value>> {
    match v {
        Value::Seq(s) => Some(s.universe.clone()),
        Value::Set(s) => Some(s.universe.clone()),
        Value::ISet(s) => Some(s.universe.clone()),
        Value::MSet(s) => Some(s.universe.clone()),
        Value::Assoc(a) => Some(a.universe.clone()),
        _ => None,
    }
}

fn elements(it: &mut Interp, v: &Value) -> RResult<Vec<Value>> {
    let mut it2 = it.iter_value(v, false)?;
    let mut out = Vec::new();
    while let Some((_, x)) = it2.next_item() {
        out.push(x);
    }
    Ok(out)
}

/// Coerce `x` into the universe of an aggregate, setting the universe of a
/// null aggregate from `x`.
fn fit(it: &mut Interp, universe: &mut Option<Value>, x: Value) -> RResult<Value> {
    match universe {
        Some(u) => {
            let u = u.clone();
            it.coerce_into_universe(&u, &x)
        }
        None => {
            *universe = Some(it.parent_of(&x)?);
            Ok(x)
        }
    }
}

fn set_value(universe: Option<Value>, mut elems: Vec<Value>) -> Value {
    sort_values(&mut elems);
    let s: VSet = elems.into_iter().collect();
    Value::Set(Rc::new(SetEnum::new(universe, s)))
}

// ----- power structures ------------------------------------------------------

fn power_set(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::structure(StructKind::PowerSet(Some(a.args[0].clone()))))
}

fn power_iset(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::structure(StructKind::PowerISet(Some(a.args[0].clone()))))
}

fn power_mset(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::structure(StructKind::PowerMSet(Some(a.args[0].clone()))))
}

fn power_seq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::structure(StructKind::PowerSeq(Some(a.args[0].clone()))))
}

fn set_of(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let v = a.args[0].clone();
    let u = match universe_of(&v) {
        Some(u) => u,
        None => Some(v.clone()),
    };
    let elems = elements(it, &v)?;
    let mut uniq = VSet::default();
    for e in elems {
        uniq.insert(e);
    }
    one(set_value(u, uniq.into_iter().collect()))
}

fn universe(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match universe_of(&a.args[0]) {
        Some(Some(u)) => one(u),
        Some(None) => Err(RuntimeError::runtime("The null sequence or set has no universe")),
        None => Err(RuntimeError::runtime("Argument has no universe")),
    }
}

// ----- predicates ------------------------------------------------------------

fn is_null(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(matches!(universe_of(&a.args[0]), Some(None)))
}

fn is_empty(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let v = a.args[0].clone();
    let n = it.cardinality(&v)?;
    boolv(matches!(n, Value::Int(i) if i.is_zero()))
}

fn is_complete(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(a.seq(0)?.is_complete())
}

fn is_defined(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match &a.args[0] {
        Value::Seq(s) => {
            let k = seq_index(&a.args[1], "Sequence")?;
            boolv(s.elems.get(k - 1).is_some_and(|v| !v.is_undef()))
        }
        Value::List(l) => {
            let k = seq_index(&a.args[1], "List")?;
            boolv(k <= l.len())
        }
        Value::Assoc(m) => {
            let key = match &m.universe {
                Some(u) => {
                    let u = u.clone();
                    match it.try_coerce_into_universe(&u, &a.args[1])? {
                        Some(k) => k,
                        None => return Ok(vals![Value::Bool(false), Value::Undef]),
                    }
                }
                None => a.args[1].clone(),
            };
            match m.map.get(&key).or(m.default.as_ref()) {
                Some(v) => Ok(vals![Value::Bool(true), v.clone()]),
                None => Ok(vals![Value::Bool(false), Value::Undef]),
            }
        }
        other => Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}", it.type_name(other)))),
    }
}

fn is_disjoint(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (x, y) = (a.args[0].clone(), a.args[1].clone());
    for e in elements(it, &x)? {
        if it.contains(&y, &e)? {
            return boolv(false);
        }
    }
    boolv(true)
}

fn is_subsequence(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = a.seq(0)?.clone();
    let t = a.seq(1)?.clone();
    let kind = match a.param("Kind") {
        Some(Value::Str(k)) => k.to_string(),
        _ => "Consecutive".to_string(),
    };
    let (s, t) = (&s.elems, &t.elems);
    match kind.as_str() {
        "Consecutive" => {
            if s.is_empty() {
                return boolv(true);
            }
            if s.len() > t.len() {
                return boolv(false);
            }
            for start in 0..=(t.len() - s.len()) {
                let mut ok = true;
                for (i, x) in s.iter().enumerate() {
                    if !it.values_equal(x, &t[start + i])? {
                        ok = false;
                        break;
                    }
                }
                if ok {
                    return boolv(true);
                }
            }
            boolv(false)
        }
        "Sequential" => {
            let mut j = 0;
            for x in s {
                loop {
                    if j >= t.len() {
                        return boolv(false);
                    }
                    j += 1;
                    if it.values_equal(x, &t[j - 1])? {
                        break;
                    }
                }
            }
            boolv(true)
        }
        "Setwise" => {
            let tv = Value::seq(None, t.clone());
            for x in s {
                if !it.contains(&tv, x)? {
                    return boolv(false);
                }
            }
            boolv(true)
        }
        other => Err(RuntimeError::runtime(format!("Unknown Kind \"{other}\""))),
    }
}

// ----- selection ---------------------------------------------------------------

fn rep(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let v = a.args[0].clone();
    if let Value::Struct(st) = &v {
        if matches!(st.kind, StructKind::Booleans) {
            return one(Value::Bool(true));
        }
        // The zero of a ring, otherwise the first element.
        if let Ok(Ok(z)) = it.try_coerce(&v, &Value::int(0)) {
            return one(z);
        }
        let mut iter = it.iter_value(&v, false).map_err(|_| RuntimeError::runtime("Cannot choose a representative"))?;
        return match iter.next_item() {
            Some((_, x)) => one(x),
            None => Err(RuntimeError::runtime("Argument is empty")),
        };
    }
    // For a sequence, the last element.
    if let Value::Seq(s) = &v {
        return match s.elems.iter().rev().find(|x| !x.is_undef()) {
            Some(x) => one(x.clone()),
            None => Err(RuntimeError::runtime("Argument is empty")),
        };
    }
    let mut iter = it.iter_value(&v, false)?;
    match iter.next_item() {
        Some((_, x)) => one(x),
        None => Err(RuntimeError::runtime("Argument is empty")),
    }
}

fn extract_rep(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Set(s) = &mut a.args[0] else {
        return Err(RuntimeError::runtime("Argument 1 must be a set"));
    };
    let s = Rc::make_mut(s);
    let elems = s.elems_mut();
    let Some(x) = elems.shift_remove_index(0) else {
        return Err(RuntimeError::runtime("The set is empty"));
    };
    a.args[1] = x;
    none()
}

fn min_max(it: &mut Interp, a: &mut CallArgs, want: Ordering) -> RResult<Vals> {
    let v = a.args[0].clone();
    let with_index = matches!(v, Value::Seq(_) | Value::ISet(_));
    let mut iter = it.iter_value(&v, false)?;
    let Some((_, mut best)) = iter.next_item() else {
        return Err(super::arg_not(1, "non-empty"));
    };
    // Magma asks the universe for an order before looking at the elements.
    if it.compare_ord(&best, &best)?.is_none() {
        let seq = matches!(v, Value::Seq(_)) && matches!(best, Value::Nfd(_));
        return Err(RuntimeError::runtime(if seq { NO_ORDER } else { "Universe has no comparison algorithm" }));
    }
    let mut best_i = 1;
    let mut i = 1;
    while let Some((_, x)) = iter.next_item() {
        i += 1;
        if it.compare_for_sort(&x, &best)? == want {
            best = x;
            best_i = i;
        }
    }
    if with_index { Ok(vals![best, Value::int(best_i)]) } else { one(best) }
}

fn minimum(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    min_max(it, a, Ordering::Less)
}

fn maximum(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    min_max(it, a, Ordering::Greater)
}

fn index_of(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = a.args[1].clone();
    match &a.args[0] {
        Value::Seq(s) => {
            let s = s.clone();
            let start = if a.args.len() > 2 { seq_index(&a.args[2], "Start")? } else { 1 };
            for (i, e) in s.elems.iter().enumerate().skip(start - 1) {
                if !e.is_undef() && it.values_equal_weak(e, &x)? {
                    return one(Value::int(i as i64 + 1));
                }
            }
            one(Value::int(0))
        }
        Value::ISet(s) => {
            let s = s.clone();
            let x = match &s.universe {
                Some(u) => match it.try_coerce_into_universe(u, &x)? {
                    Some(v) => v,
                    None => return Err(RuntimeError::runtime("Element is not coercible into the universe of the set")),
                },
                None => x,
            };
            one(Value::int(s.elems.get_index_of(&x).map(|i| i as i64 + 1).unwrap_or(0)))
        }
        Value::List(l) => {
            let l = l.clone();
            for (i, e) in l.iter().enumerate() {
                if it.values_equal_weak(e, &x)? {
                    return one(Value::int(i as i64 + 1));
                }
            }
            one(Value::int(0))
        }
        Value::CopElt(c) => one(Value::int(c.index as i64 + 1)),
        other => Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}", it.type_name(other)))),
    }
}

fn cop_index(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match &a.args[0] {
        Value::CopElt(c) => one(Value::int(c.index as i64 + 1)),
        _ => unreachable!(),
    }
}

fn explode(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match &a.args[0] {
        Value::Seq(s) => Ok(s.elems.iter().cloned().collect()),
        Value::Tuple(t) => Ok(t.elems.iter().cloned().collect()),
        Value::List(l) => Ok(l.iter().cloned().collect()),
        _ => unreachable!(),
    }
}

fn eltseq_seq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(a.args[0].clone())
}

// ----- modification ---------------------------------------------------------------

fn append_imp(it: &mut Interp, a: &mut CallArgs) -> RResult<()> {
    let x = std::mem::take(&mut a.args[1]);
    match &mut a.args[0] {
        Value::Seq(s) => {
            let s = Rc::make_mut(s);
            let x = fit(it, &mut s.universe, x)?;
            s.elems.push(x);
        }
        Value::List(l) => Rc::make_mut(l).push(x),
        Value::Tuple(t) => {
            let t = Rc::make_mut(t);
            t.elems.push(x);
            t.parent = None;
        }
        Value::ISet(s) => {
            let s = Rc::make_mut(s);
            let x = fit(it, &mut s.universe, x)?;
            s.elems.insert(x);
        }
        _ => unreachable!(),
    }
    Ok(())
}
both_forms!(append_proc, append_func, append_imp);

fn include_imp(it: &mut Interp, a: &mut CallArgs) -> RResult<()> {
    let x = std::mem::take(&mut a.args[1]);
    match &mut a.args[0] {
        Value::Set(s) => {
            let s = Rc::make_mut(s);
            let x = fit(it, &mut s.universe, x)?;
            if !s.contains(&x) {
                s.elems_mut().insert(x);
            }
        }
        Value::ISet(s) => {
            let s = Rc::make_mut(s);
            let x = fit(it, &mut s.universe, x)?;
            s.elems.insert(x);
        }
        Value::MSet(s) => {
            let s = Rc::make_mut(s);
            let x = fit(it, &mut s.universe, x)?;
            s.insert(x, 1);
        }
        Value::Seq(s) => {
            let present = {
                let snapshot = Value::Seq(s.clone());
                it.contains(&snapshot, &x)?
            };
            if !present {
                let s = Rc::make_mut(s);
                let x = fit(it, &mut s.universe, x)?;
                s.elems.push(x);
            }
        }
        _ => unreachable!(),
    }
    Ok(())
}
both_forms!(include_proc, include_func, include_imp);

fn exclude_imp(it: &mut Interp, a: &mut CallArgs) -> RResult<()> {
    let x = std::mem::take(&mut a.args[1]);
    match &mut a.args[0] {
        Value::Set(s) => {
            let s = Rc::make_mut(s);
            let x = match &s.universe {
                Some(u) => {
                    let u = u.clone();
                    it.coerce_into_universe(&u, &x)?
                }
                None => x,
            };
            if s.contains(&x) {
                s.elems_mut().shift_remove(&x);
            }
        }
        Value::MSet(s) => {
            let s = Rc::make_mut(s);
            let x = match &s.universe {
                Some(u) => {
                    let u = u.clone();
                    it.coerce_into_universe(&u, &x)?
                }
                None => x,
            };
            if let Some(n) = s.elems.get_mut(&x) {
                *n -= 1;
                if *n == 0 {
                    s.elems.shift_remove(&x);
                }
            }
        }
        Value::Seq(s) => {
            let pos = {
                let mut found = None;
                for (i, e) in s.elems.iter().enumerate() {
                    if !e.is_undef() && it.values_equal_weak(e, &x)? {
                        found = Some(i);
                        break;
                    }
                }
                found
            };
            if let Some(i) = pos {
                Rc::make_mut(s).elems.remove(i);
            }
        }
        Value::ISet(s) => {
            Rc::make_mut(s).elems.shift_remove(&x);
        }
        _ => unreachable!(),
    }
    Ok(())
}
both_forms!(exclude_proc, exclude_func, exclude_imp);

fn insert_imp(it: &mut Interp, a: &mut CallArgs) -> RResult<()> {
    let i = seq_index(&a.args[1], "Insert position")?;
    if a.args.len() == 4 {
        // Insert(~S, k, m, T): replace S[k..m] by T.
        let m = match &a.args[2] {
            Value::Int(m) => m.to_i64().unwrap_or(0),
            _ => return Err(RuntimeError::runtime("Argument 3 must be an integer")),
        };
        let t = std::mem::take(&mut a.args[3]);
        let Value::Seq(t) = t else { unreachable!() };
        let Value::Seq(s) = &mut a.args[0] else { unreachable!() };
        let s = Rc::make_mut(s);
        let k = i - 1;
        if m < k as i64 {
            return Err(RuntimeError::runtime("Argument 2 must not exceed argument 3 plus one"));
        }
        if k > s.elems.len() {
            s.elems.resize(k, Value::Undef);
        }
        let m = (m as usize).min(s.elems.len());
        let mut items = Vec::new();
        for x in &t.elems {
            items.push(fit(it, &mut s.universe, x.clone())?);
        }
        s.elems.splice(k..m, items);
        return Ok(());
    }
    let x = std::mem::take(&mut a.args[2]);
    match &mut a.args[0] {
        Value::Seq(s) => {
            let s = Rc::make_mut(s);
            let x = fit(it, &mut s.universe, x)?;
            if i > s.elems.len() + 1 {
                s.elems.resize(i - 1, Value::Undef);
            }
            s.elems.insert(i - 1, x);
        }
        Value::List(l) => {
            let l = Rc::make_mut(l);
            if i > l.len() + 1 {
                return Err(RuntimeError::runtime(format!("Insert position {i} is beyond the end of the list")));
            }
            l.insert(i - 1, x);
        }
        Value::ISet(s) => {
            let s = Rc::make_mut(s);
            if i > s.elems.len() + 1 {
                return Err(RuntimeError::runtime(format!("Insert position {i} is beyond the end of the set")));
            }
            let x = fit(it, &mut s.universe, x)?;
            if !s.elems.contains(&x) {
                s.elems.shift_insert(i - 1, x);
            }
        }
        _ => unreachable!(),
    }
    Ok(())
}
both_forms!(insert_proc, insert_func, insert_imp);

/// A sequence's length is the index of its last defined entry.
fn trim_undef(s: &mut SeqEnum) {
    while s.elems.last().is_some_and(|v| v.is_undef()) {
        s.elems.pop();
    }
}

fn prune_imp(_it: &mut Interp, a: &mut CallArgs) -> RResult<()> {
    let empty = || RuntimeError::runtime("Cannot prune an empty aggregate");
    match &mut a.args[0] {
        Value::Seq(s) => {
            let s = Rc::make_mut(s);
            s.elems.pop().ok_or_else(empty)?;
            trim_undef(s);
        }
        Value::List(l) => {
            Rc::make_mut(l).pop().ok_or_else(empty)?;
        }
        Value::Tuple(t) => {
            let t = Rc::make_mut(t);
            t.elems.pop().ok_or_else(empty)?;
            t.parent = None;
        }
        Value::ISet(s) => {
            Rc::make_mut(s).elems.pop().ok_or_else(empty)?;
        }
        _ => unreachable!(),
    }
    Ok(())
}
both_forms!(prune_proc, prune_func, prune_imp);

fn remove_imp(it: &mut Interp, a: &mut CallArgs) -> RResult<()> {
    if matches!(a.args[0], Value::Assoc(_)) {
        let key = std::mem::take(&mut a.args[1]);
        let Value::Assoc(m) = &mut a.args[0] else { unreachable!() };
        let m = Rc::make_mut(m);
        let key = match &m.universe {
            Some(u) => {
                let u = u.clone();
                it.try_coerce_into_universe(&u, &key)?.unwrap_or(key)
            }
            None => key,
        };
        m.map.shift_remove(&key);
        return Ok(());
    }
    let i = seq_index(&a.args[1], "Position")?;
    match &mut a.args[0] {
        Value::Seq(s) => {
            if i > s.elems.len() {
                return Err(RuntimeError::runtime("Illegal sequence position"));
            }
            let s = Rc::make_mut(s);
            s.elems.remove(i - 1);
            trim_undef(s);
        }
        Value::List(l) => {
            if i > l.len() {
                return Err(RuntimeError::runtime("Illegal sequence position"));
            }
            Rc::make_mut(l).remove(i - 1);
        }
        _ => unreachable!(),
    }
    Ok(())
}
both_forms!(remove_proc, remove_func, remove_imp);

fn reverse_imp(_it: &mut Interp, a: &mut CallArgs) -> RResult<()> {
    match &mut a.args[0] {
        Value::Seq(s) => {
            let s = Rc::make_mut(s);
            s.elems.reverse();
            // A reversed factorization is no longer one.
            s.fact = false;
        }
        Value::List(l) => Rc::make_mut(l).reverse(),
        _ => unreachable!(),
    }
    Ok(())
}
both_forms!(reverse_proc, reverse_func, reverse_imp);

fn rotate_imp(_it: &mut Interp, a: &mut CallArgs) -> RResult<()> {
    let p = a.i64(1)?;
    let Value::Seq(s) = &mut a.args[0] else { unreachable!() };
    let s = Rc::make_mut(s);
    let n = s.elems.len() as i64;
    if n > 0 {
        let k = p.rem_euclid(n) as usize;
        s.elems.rotate_right(k);
    }
    Ok(())
}
both_forms!(rotate_proc, rotate_func, rotate_imp);

fn undefine_imp(_it: &mut Interp, a: &mut CallArgs) -> RResult<()> {
    let i = seq_index(&a.args[1], "Position")?;
    let Value::Seq(s) = &mut a.args[0] else { unreachable!() };
    let s = Rc::make_mut(s);
    if i <= s.elems.len() {
        s.elems[i - 1] = Value::Undef;
        while s.elems.last().is_some_and(|v| v.is_undef()) {
            s.elems.pop();
        }
    }
    Ok(())
}
both_forms!(undefine_proc, undefine_func, undefine_imp);

/// Magma's error for ordering nearfield elements.
const NO_ORDER: &str = "No comparison algorithm for this sequence universe";

/// Sort values, optionally with a comparison function; returns the
/// original position of each sorted value.
fn sort_with(it: &mut Interp, vals: &mut Vec<Value>, cmp: Option<&Value>) -> RResult<Vec<usize>> {
    let mut idx: Vec<usize> = (0..vals.len()).collect();
    // Without a comparison function the elements must have an order, even
    // when there is nothing to compare.
    if cmp.is_none() {
        if let Some(v) = vals.first() {
            if it.compare_ord(v, v)?.is_none() {
                return Err(RuntimeError::runtime(if matches!(v, Value::Nfd(_)) { NO_ORDER } else { "No comparison algorithm for sequence elts" }));
            }
        }
    }
    // Merge sort with a fallible comparator (stable).
    let mut err = None;
    let snapshot = vals.clone();
    let mut compare = |it: &mut Interp, a: usize, b: usize| -> Ordering {
        if err.is_some() {
            return Ordering::Equal;
        }
        let r = match cmp {
            None => it.compare_for_sort(&snapshot[a], &snapshot[b]),
            Some(f) => match it.call_function(f, vec![snapshot[a].clone(), snapshot[b].clone()]) {
                Ok(Value::Int(n)) => Ok(n.sign().cmp(&0)),
                Ok(Value::Rat(q)) => Ok(q.sign().cmp(&0)),
                Ok(Value::Real(r)) => Ok(r.x.sign().cmp(&0)),
                Ok(_) => Err(RuntimeError::runtime("The comparison function must return a number")),
                Err(e) => Err(e),
            },
        };
        match r {
            Ok(o) => o,
            Err(e) => {
                err = Some(e);
                Ordering::Equal
            }
        }
    };
    merge_sort(&mut idx, &mut |a, b| compare(it, a, b));
    if let Some(e) = err {
        return Err(e);
    }
    *vals = idx.iter().map(|&i| snapshot[i].clone()).collect();
    Ok(idx)
}

fn merge_sort(v: &mut [usize], cmp: &mut dyn FnMut(usize, usize) -> Ordering) {
    let n = v.len();
    if n <= 1 {
        return;
    }
    let mid = n / 2;
    merge_sort(&mut v[..mid], cmp);
    merge_sort(&mut v[mid..], cmp);
    let mut merged = Vec::with_capacity(n);
    let (mut i, mut j) = (0, mid);
    while i < mid && j < n {
        if cmp(v[j], v[i]) == Ordering::Less {
            merged.push(v[j]);
            j += 1;
        } else {
            merged.push(v[i]);
            i += 1;
        }
    }
    merged.extend_from_slice(&v[i..mid]);
    merged.extend_from_slice(&v[j..n]);
    v.copy_from_slice(&merged);
}

/// The sorting permutation, in `Sym(n)`: it maps `i` to the original
/// position of the i-th sorted value.
fn perm_value(it: &mut Interp, idx: &[usize]) -> Value {
    it.perm(idx.iter().map(|&i| i as u32).collect())
}

fn sort_proc(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let cmp = if a.args.len() > 1 && !matches!(a.args[1], Value::Undef) && matches!(a.args[1], Value::Func(_) | Value::Intr(_)) { Some(a.args[1].clone()) } else { None };
    let Value::Seq(s) = &mut a.args[0] else { unreachable!() };
    let s = Rc::make_mut(s);
    if !s.is_complete() {
        return Err(RuntimeError::runtime("Cannot sort a sequence with undefined entries"));
    }
    let idx = sort_with(it, &mut s.elems, cmp.as_ref())?;
    // Sort(~S, ~p) also returns the permutation.
    if a.args.len() > 1 && !matches!(a.args[1], Value::Func(_) | Value::Intr(_)) {
        a.args[1] = perm_value(it, &idx);
    }
    if a.args.len() > 2 {
        a.args[2] = perm_value(it, &idx);
    }
    none()
}

fn sort_func(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let cmp = a.args.get(1).cloned();
    match &a.args[0] {
        Value::Seq(s) => {
            let mut s2 = (**s).clone();
            if !s2.is_complete() {
                return Err(RuntimeError::runtime("Cannot sort a sequence with undefined entries"));
            }
            let idx = sort_with(it, &mut s2.elems, cmp.as_ref())?;
            // Only the form with a comparison function returns the permutation.
            let sorted = Value::Seq(Rc::new(s2));
            if cmp.is_none() {
                return one(sorted);
            }
            Ok(vals![sorted, perm_value(it, &idx)])
        }
        Value::Set(s) => {
            let mut v: Vec<Value> = s.iter().collect();
            sort_with(it, &mut v, cmp.as_ref())?;
            one(Value::seq(s.universe.clone(), v))
        }
        Value::List(l) => {
            let mut v = (**l).clone();
            sort_with(it, &mut v, cmp.as_ref())?;
            one(Value::list(v))
        }
        _ => unreachable!(),
    }
}

fn parallel_sort(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (Value::Seq(s), Value::Seq(t)) = (&a.args[0], &a.args[1]) else { unreachable!() };
    if s.elems.len() != t.elems.len() {
        return Err(RuntimeError::runtime("Sequences must have the same length"));
    }
    let mut sv = s.elems.clone();
    let idx = sort_with(it, &mut sv, None)?;
    let tv: Vec<Value> = idx.iter().map(|&i| t.elems[i].clone()).collect();
    let (su, tu) = (s.universe.clone(), t.universe.clone());
    a.args[0] = Value::seq(su, sv);
    a.args[1] = Value::seq(tu, tv);
    none()
}

fn change_universe_imp(it: &mut Interp, a: &mut CallArgs) -> RResult<()> {
    let v = a.args[1].clone();
    let x = std::mem::take(&mut a.args[0]);
    let target = match &x {
        Value::Seq(_) => StructKind::PowerSeq(Some(v)),
        Value::Set(_) => StructKind::PowerSet(Some(v)),
        Value::ISet(_) => StructKind::PowerISet(Some(v)),
        Value::MSet(_) => StructKind::PowerMSet(Some(v)),
        _ => unreachable!(),
    };
    let p = Value::structure(target);
    match it.coerce(&p, &x) {
        Ok(y) => {
            a.args[0] = y;
            Ok(())
        }
        Err(e) => {
            a.args[0] = x;
            Err(e)
        }
    }
}
both_forms!(change_universe_proc, change_universe_func, change_universe_imp);

fn can_change_universe(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match change_universe_imp(it, a) {
        Ok(()) => Ok(vals![Value::Bool(true), std::mem::take(&mut a.args[0])]),
        Err(_) => Ok(vals![Value::Bool(false), Value::Undef]),
    }
}

// ----- conversions -------------------------------------------------------------------

fn to_kind(it: &mut Interp, a: &mut CallArgs, kind: AggKind) -> RResult<Vals> {
    let v = a.args[0].clone();
    let u = universe_of(&v).flatten();
    let elems = elements(it, &v)?;
    one(it.build_aggregate(kind, u, elems, true)?)
}

fn to_seq(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    to_kind(it, a, AggKind::Seq)
}

fn to_set(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    to_kind(it, a, AggKind::Set)
}

fn to_iset(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    to_kind(it, a, AggKind::ISet)
}

fn to_mset(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    to_kind(it, a, AggKind::MSet)
}

fn multiset_to_set(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::MSet(m) = &a.args[0] else { unreachable!() };
    let u = m.universe.clone();
    let elems: Vec<Value> = m.elems.keys().cloned().collect();
    one(it.build_aggregate(AggKind::Set, u, elems, true)?)
}

fn to_list(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match &a.args[0] {
        Value::Seq(s) => one(Value::list(s.elems.clone())),
        Value::Tuple(t) => one(Value::list(t.elems.clone())),
        Value::List(l) => one(Value::List(l.clone())),
        _ => unreachable!(),
    }
}

// ----- set operations ------------------------------------------------------------------

fn multiplicity(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::MSet(m) = &a.args[0] else { unreachable!() };
    let m = m.clone();
    let x = match &m.universe {
        Some(u) => it.try_coerce_into_universe(u, &a.args[1])?.unwrap_or(a.args[1].clone()),
        None => a.args[1].clone(),
    };
    one(Value::Int(Integer::from_u64(m.elems.get(&x).copied().unwrap_or(0))))
}

fn multiplicities(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::MSet(m) = &a.args[0] else { unreachable!() };
    let mut pairs: Vec<(Value, u64)> = m.elems.iter().map(|(k, v)| (k.clone(), *v)).collect();
    let mut keys: Vec<Value> = pairs.iter().map(|p| p.0.clone()).collect();
    if sort_values(&mut keys) {
        let map: VMap<u64> = pairs.drain(..).collect();
        pairs = keys.into_iter().map(|k| (k.clone(), map[&k])).collect();
    }
    one(Value::int_seq(pairs.into_iter().map(|p| Integer::from_u64(p.1))))
}

fn subsets_of(elems: &[Value], k: Option<usize>) -> Vec<Vec<Value>> {
    let n = elems.len();
    let mut out = Vec::new();
    match k {
        None => {
            for mask in 0u64..(1u64 << n) {
                out.push((0..n).filter(|i| mask >> i & 1 == 1).map(|i| elems[i].clone()).collect());
            }
        }
        Some(k) => {
            if k > n {
                return out;
            }
            let mut idx: Vec<usize> = (0..k).collect();
            loop {
                out.push(idx.iter().map(|&i| elems[i].clone()).collect());
                let mut i = k;
                loop {
                    if i == 0 {
                        return out;
                    }
                    i -= 1;
                    if idx[i] != i + n - k {
                        break;
                    }
                    if i == 0 && idx[0] == n - k {
                        return out;
                    }
                }
                idx[i] += 1;
                for j in i + 1..k {
                    idx[j] = idx[j - 1] + 1;
                }
            }
        }
    }
    out
}

fn set_elements_sorted(s: &SetEnum) -> Vec<Value> {
    let mut v: Vec<Value> = s.iter().collect();
    sort_values(&mut v);
    v
}

fn subsets(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Set(s) = &a.args[0] else { unreachable!() };
    let k = if a.args.len() > 1 { Some(a.usize(1)?) } else { None };
    if k.is_none() && s.len() > 24 {
        return Err(RuntimeError::runtime("The set is too large to form all its subsets"));
    }
    let elems = set_elements_sorted(s);
    let u = s.universe.clone();
    let subs: Vec<Value> = subsets_of(&elems, k).into_iter().map(|v| set_value(u.clone(), v)).collect();
    let pu = Some(Value::structure(StructKind::PowerSet(u)));
    one(set_value(pu, subs))
}

fn random_subset(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Set(s) = &a.args[0] else { unreachable!() };
    let k = a.usize(1)?;
    let mut elems: Vec<Value> = s.iter().collect();
    if k > elems.len() {
        return Err(RuntimeError::runtime("The subset size exceeds the size of the set"));
    }
    for i in 0..k {
        let j = i + it.rng.below_u64((elems.len() - i) as u64) as usize;
        elems.swap(i, j);
    }
    elems.truncate(k);
    one(set_value(s.universe.clone(), elems))
}

fn multisets(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Set(s) = &a.args[0] else { unreachable!() };
    let k = a.usize(1)?;
    let elems = set_elements_sorted(s);
    let n = elems.len();
    let mut out = Vec::new();
    // Combinations with repetition as non-decreasing index sequences.
    let mut idx = vec![0usize; k];
    if n > 0 || k == 0 {
        loop {
            let mut m = SetMulti { universe: s.universe.clone(), elems: VMap::default(), name: Default::default() };
            for &i in &idx {
                m.insert(elems[i].clone(), 1);
            }
            out.push(Value::MSet(Rc::new(m)));
            let mut i = k;
            loop {
                if i == 0 {
                    break;
                }
                i -= 1;
                if idx[i] + 1 < n {
                    break;
                }
                if i == 0 {
                    i = usize::MAX;
                    break;
                }
            }
            if i == usize::MAX || k == 0 || (i == 0 && idx[0] + 1 >= n) {
                break;
            }
            idx[i] += 1;
            for j in i + 1..k {
                idx[j] = idx[i];
            }
        }
    }
    let pu = Some(Value::structure(StructKind::PowerMSet(s.universe.clone())));
    let set: VSet = out.into_iter().collect();
    one(Value::Set(Rc::new(SetEnum::new(pu, set))))
}

fn subsequences(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Set(s) = &a.args[0] else { unreachable!() };
    let k = a.usize(1)?;
    let elems = set_elements_sorted(s);
    let n = elems.len();
    let mut out = Vec::new();
    if n > 0 || k == 0 {
        let total = (n as u64).checked_pow(k as u32).ok_or_else(|| RuntimeError::runtime("Too many subsequences"))?;
        if total > 10_000_000 {
            return Err(RuntimeError::runtime("Too many subsequences"));
        }
        for mut code in 0..total {
            let mut v = Vec::with_capacity(k);
            for _ in 0..k {
                v.push(elems[(code % n as u64) as usize].clone());
                code /= n as u64;
            }
            v.reverse();
            out.push(Value::seq(s.universe.clone(), v));
        }
    }
    let pu = Some(Value::structure(StructKind::PowerSeq(s.universe.clone())));
    one(set_value(pu, out))
}

fn permutations_of(elems: &[Value], k: usize, out: &mut Vec<Vec<Value>>, cur: &mut Vec<Value>, used: &mut Vec<bool>) {
    if cur.len() == k {
        out.push(cur.clone());
        return;
    }
    for i in 0..elems.len() {
        if !used[i] {
            used[i] = true;
            cur.push(elems[i].clone());
            permutations_of(elems, k, out, cur, used);
            cur.pop();
            used[i] = false;
        }
    }
}

fn permutations(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Set(s) = &a.args[0] else { unreachable!() };
    let elems = set_elements_sorted(s);
    let k = if a.args.len() > 1 { a.usize(1)? } else { elems.len() };
    if k > elems.len() {
        return one(set_value(Some(Value::structure(StructKind::PowerSeq(s.universe.clone()))), Vec::new()));
    }
    if elems.len() > 10 {
        return Err(RuntimeError::runtime("Too many permutations"));
    }
    let mut out = Vec::new();
    permutations_of(&elems, k, &mut out, &mut Vec::new(), &mut vec![false; elems.len()]);
    let u = s.universe.clone();
    let pu = Some(Value::structure(StructKind::PowerSeq(u.clone())));
    one(set_value(pu, out.into_iter().map(|v| Value::seq(u.clone(), v)).collect()))
}

// ----- sequences of booleans ----------------------------------------------------------

fn bool_seq_op(a: &mut CallArgs, f: fn(bool, bool) -> bool) -> RResult<Vals> {
    let (Value::Seq(s), Value::Seq(t)) = (&a.args[0], &a.args[1]) else { unreachable!() };
    if s.elems.len() != t.elems.len() {
        return Err(RuntimeError::runtime("Sequences must have the same length"));
    }
    let mut out = Vec::with_capacity(s.elems.len());
    for (x, y) in s.elems.iter().zip(&t.elems) {
        let (Value::Bool(x), Value::Bool(y)) = (x, y) else {
            return Err(RuntimeError::runtime("Sequences must contain booleans"));
        };
        out.push(Value::Bool(f(*x, *y)));
    }
    one(Value::seq(Some(Value::booleans()), out))
}

fn seq_and(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    bool_seq_op(a, |x, y| x && y)
}

fn seq_or(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    bool_seq_op(a, |x, y| x || y)
}

fn seq_xor(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    bool_seq_op(a, |x, y| x != y)
}

fn seq_not(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Seq(s) = &a.args[0] else { unreachable!() };
    let mut out = Vec::new();
    for x in &s.elems {
        let Value::Bool(b) = x else {
            return Err(RuntimeError::runtime("Sequence must contain booleans"));
        };
        out.push(Value::Bool(!b));
    }
    one(Value::seq(Some(Value::booleans()), out))
}

fn seq_and_proc(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    a.args[0] = seq_and(it, a)?.remove(0);
    none()
}

fn seq_or_proc(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    a.args[0] = seq_or(it, a)?.remove(0);
    none()
}

fn seq_xor_proc(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    a.args[0] = seq_xor(it, a)?.remove(0);
    none()
}

fn seq_not_proc(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    a.args[0] = seq_not(it, a)?.remove(0);
    none()
}

fn partition(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Seq(s) = &a.args[0] else { unreachable!() };
    let sizes: Vec<usize> = match &a.args[1] {
        Value::Int(p) => {
            let p = p.to_u64().filter(|&p| p > 0).ok_or_else(|| RuntimeError::runtime("Part size must be positive"))? as usize;
            if s.elems.len() % p != 0 {
                return Err(RuntimeError::runtime("Argument 2 must be a divisor of sequence length"));
            }
            vec![p; s.elems.len() / p]
        }
        Value::Seq(ps) => {
            let mut v = Vec::new();
            for x in &ps.elems {
                let Value::Int(n) = x else {
                    return Err(RuntimeError::runtime("Part sizes must be integers"));
                };
                v.push(n.to_u64().ok_or_else(|| RuntimeError::runtime("Part sizes must be non-negative"))? as usize);
            }
            if v.iter().sum::<usize>() != s.elems.len() {
                return Err(RuntimeError::runtime("The part sizes must add up to the length of the sequence"));
            }
            v
        }
        _ => unreachable!(),
    };
    let mut out = Vec::new();
    let mut pos = 0;
    for n in sizes {
        // Parts of a range still print as ranges.
        out.push(Value::Seq(Rc::new(SeqEnum {
            universe: s.universe.clone(),
            elems: s.elems[pos..pos + n].to_vec(),
            range_hint: s.range_hint,
            name: Default::default(),
            fact: false,
        })));
        pos += n;
    }
    one(Value::seq(Some(Value::structure(StructKind::PowerSeq(s.universe.clone()))), out))
}

// ----- tuples and Cartesian products ---------------------------------------------------

fn cartesian_product(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let parts: Vec<Value> = if a.args.len() == 1 {
        match &a.args[0] {
            Value::Seq(s) => s.elems.clone(),
            Value::List(l) => (**l).clone(),
            Value::Tuple(t) => t.elems.clone(),
            other => vec![other.clone()],
        }
    } else {
        a.args.clone()
    };
    one(it.cartesian_product(parts)?)
}

fn cartesian_power(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = a.usize(1)?;
    one(it.cartesian_product(vec![a.args[0].clone(); k])?)
}

fn car_parts(v: &Value) -> Option<&Vec<Value>> {
    match v {
        Value::Struct(s) => match &s.kind {
            StructKind::Cartesian(p) => Some(p),
            _ => None,
        },
        _ => None,
    }
}

fn cop_parts(v: &Value) -> Option<&Vec<Value>> {
    match v {
        Value::Struct(s) => match &s.kind {
            StructKind::Coproduct(p) => Some(p),
            _ => None,
        },
        _ => None,
    }
}

fn flat_values(v: &[Value], out: &mut Vec<Value>, tuples: bool) {
    for x in v {
        match x {
            Value::Tuple(t) if tuples => flat_values(&t.elems, out, true),
            Value::Struct(s) if !tuples && matches!(s.kind, StructKind::Cartesian(_)) => flat_values(car_parts(x).unwrap(), out, false),
            _ => out.push(x.clone()),
        }
    }
}

fn flat(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match &a.args[0] {
        Value::Tuple(t) => {
            let mut out = Vec::new();
            flat_values(&t.elems, &mut out, true);
            one(Value::tuple(out))
        }
        v if car_parts(v).is_some() => {
            let mut out = Vec::new();
            flat_values(car_parts(v).unwrap(), &mut out, false);
            one(Value::structure(StructKind::Cartesian(out)))
        }
        v if cop_parts(v).is_some() => {
            let mut out = Vec::new();
            for p in cop_parts(v).unwrap() {
                match cop_parts(p) {
                    Some(inner) => out.extend(inner.iter().cloned()),
                    None => out.push(p.clone()),
                }
            }
            let c = Value::structure(StructKind::Coproduct(out));
            let inj = _it.call_intrinsic_named(crate::sym::Sym::new("Injections"), vec![c.clone()])?;
            Ok(vals![c, inj])
        }
        Value::Seq(s) => {
            let mut out = Vec::new();
            fn go(v: &[Value], out: &mut Vec<Value>) {
                for x in v {
                    match x {
                        Value::Seq(s) => go(&s.elems, out),
                        _ => out.push(x.clone()),
                    }
                }
            }
            go(&s.elems, &mut out);
            one(Value::seq(None, out))
        }
        _ => Err(RuntimeError::runtime("Bad argument type")),
    }
}

fn number_of_components(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match car_parts(&a.args[0]).or_else(|| cop_parts(&a.args[0])) {
        Some(p) => one(Value::int(p.len() as i64)),
        None => Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}", it.type_name(&a.args[0])))),
    }
}

fn component(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let i = seq_index(&a.args[1], "Component")?;
    let parts = car_parts(&a.args[0]).or_else(|| cop_parts(&a.args[0])).ok_or_else(|| RuntimeError::runtime("Argument 1 must be a Cartesian product or coproduct"))?;
    parts.get(i - 1).cloned().map(|v| vals![v]).ok_or_else(|| RuntimeError::runtime(format!("Component {i} is out of range")))
}

fn components(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let parts = car_parts(&a.args[0]).ok_or_else(|| RuntimeError::runtime("Argument must be a Cartesian product"))?;
    one(Value::list(parts.clone()))
}

fn car_random(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let parts = car_parts(&a.args[0]).cloned().unwrap();
    let mut elems = Vec::new();
    for p in &parts {
        let (_, x) = it.random_element_indexed(p)?;
        elems.push(x);
    }
    one(Value::Tuple(Rc::new(Tuple { elems, parent: Some(a.args[0].clone()) })))
}

fn car_rep(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let parts = car_parts(&a.args[0]).cloned().unwrap();
    let mut elems = Vec::new();
    for p in &parts {
        let mut iter = it.iter_value(p, false)?;
        match iter.next_item() {
            Some((_, x)) => elems.push(x),
            None => return Err(RuntimeError::runtime("A component of the product is empty")),
        }
    }
    one(Value::Tuple(Rc::new(Tuple { elems, parent: Some(a.args[0].clone()) })))
}

// ----- associative arrays --------------------------------------------------------------

fn assoc_new(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let universe = a.args.first().cloned();
    let default = a.param("Default").filter(|v| !v.is_undef()).cloned();
    one(Value::Assoc(Rc::new(Assoc { universe, map: VMap::default(), default })))
}

fn assoc_keys(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Assoc(m) = &a.args[0] else { unreachable!() };
    let keys: Vec<Value> = m.map.keys().cloned().collect();
    let u = m.universe.clone();
    if u.is_none() && keys.is_empty() {
        return one(Value::Set(Rc::new(SetEnum::new(None, VSet::default()))));
    }
    one(it.build_aggregate(AggKind::Set, u, keys, true)?)
}

fn assoc_values(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Assoc(m) = &a.args[0] else { unreachable!() };
    one(Value::list(m.map.values().cloned().collect()))
}

fn is_in_keys(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Assoc(m) = &a.args[0] else { unreachable!() };
    let m = m.clone();
    let key = match &m.universe {
        Some(u) => match it.try_coerce_into_universe(u, &a.args[1])? {
            Some(k) => k,
            None => return Ok(vals![Value::Bool(false), Value::Undef]),
        },
        None => a.args[1].clone(),
    };
    match m.map.get(&key) {
        Some(v) => Ok(vals![Value::Bool(true), v.clone()]),
        None => Ok(vals![Value::Bool(false), Value::Undef]),
    }
}

// ----- records -----------------------------------------------------------------------

fn record_format(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Rec(r) = &a.args[0] else { unreachable!() };
    one(Value::Struct(r.format.clone()))
}

fn record_names(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let fmt = match &a.args[0] {
        Value::Rec(r) => r.format.clone(),
        Value::Struct(s) if matches!(s.kind, StructKind::RecFormat(_)) => s.clone(),
        _ => return Err(RuntimeError::runtime("Argument must be a record or record format")),
    };
    let StructKind::RecFormat(rf) = &fmt.kind else { unreachable!() };
    one(Value::seq(Some(Value::strings()), rf.names.iter().map(|n| Value::str(&n.as_rc())).collect()))
}

// ----- coproducts --------------------------------------------------------------------

fn injections(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let c = a.args[0].clone();
    let parts = cop_parts(&c).ok_or_else(|| RuntimeError::runtime("Argument must be a coproduct"))?;
    let maps: Vec<Value> = parts.iter().enumerate().map(|(i, p)| Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain: p.clone(), codomain: c.clone(), imp: MapImpl::Injection(i) }))).collect();
    one(Value::seq(None, maps))
}

fn constituent(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    component(it, a)
}

fn retrieve(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::CopElt(c) = &a.args[0] else { unreachable!() };
    one(c.value.clone())
}

fn universal_map(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let c = a.args[0].clone();
    let s = a.args[1].clone();
    let Value::Seq(ms) = &a.args[2] else { unreachable!() };
    let parts = cop_parts(&c).ok_or_else(|| RuntimeError::runtime("Argument 1 must be a coproduct"))?.clone();
    if ms.elems.len() != parts.len() {
        return Err(RuntimeError::runtime("One map per constituent is required"));
    }
    // Build a rule: x :-> maps[Index(x)](Retrieve(x)).
    let mut graph = VMap::default();
    for (i, p) in parts.iter().enumerate() {
        let mut iter = it.iter_value(p, false)?;
        let m = ms.elems[i].clone();
        while let Some((_, x)) = iter.next_item() {
            let y = it.image(&x, &m)?;
            let key = Value::CopElt(Rc::new(CopElt { cop: match &c { Value::Struct(st) => st.clone(), _ => unreachable!() }, index: i, value: x }));
            graph.insert(key, y);
        }
    }
    one(Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain: c, codomain: s, imp: MapImpl::Graph(graph) })))
}

pub fn register(it: &mut Interp) {
    it.def("PowerSet", "R::. -> PowSetEnum", "The structure of all enumerated subsets of R.", power_set);
    it.def("PowerIndexedSet", "R::. -> PowSetIndx", "The structure of all indexed subsets of R.", power_iset);
    it.def("PowerMultiset", "R::. -> PowSetMulti", "The structure of all multisets over R.", power_mset);
    it.def("PowerSequence", "R::. -> PowSeqEnum", "The structure of all sequences over R.", power_seq);
    it.def("Set", "M::. -> SetEnum", "The set of elements of the finite structure or aggregate M.", set_of);
    for t in ["SeqEnum", "SetEnum", "SetIndx", "SetMulti", "Assoc"] {
        it.def("Universe", &format!("S::{t} -> ."), "The universe of S.", universe);
    }
    for t in ["SeqEnum", "SetEnum", "SetIndx", "SetMulti"] {
        it.def("IsNull", &format!("S::{t} -> BoolElt"), "Whether S is empty with no universe.", is_null);
    }
    for t in ["SeqEnum", "SetEnum", "SetIndx", "SetMulti", "List", "Tup", "Assoc"] {
        it.def("IsEmpty", &format!("S::{t} -> BoolElt"), "Whether S is empty.", is_empty);
    }
    it.def("IsComplete", "S::SeqEnum -> BoolElt", "Whether S has no undefined entries.", is_complete);
    it.def("IsDefined", "S::SeqEnum, i::RngIntElt -> BoolElt", "Whether S[i] is defined.", is_defined);
    it.def("IsDefined", "L::List, i::RngIntElt -> BoolElt", "Whether L[i] is defined.", is_defined);
    it.def("IsDefined", "A::Assoc, x::. -> BoolElt, .", "Whether A[x] is defined, and its value.", is_defined);
    it.def("IsInKeys", "A::Assoc, x::. -> BoolElt, .", "Whether x is explicitly a key of A, and the value A[x].", is_in_keys);
    for t in ["SetEnum", "SetIndx", "SetMulti"] {
        it.def("IsDisjoint", &format!("R::{t}, S::{t} -> BoolElt"), "Whether R and S have no common element.", is_disjoint);
    }
    it.def_params("IsSubsequence", "S::SeqEnum, T::SeqEnum -> BoolElt", &[("Kind", Value::str("Consecutive"))], "Whether S occurs in T (consecutively by default).", is_subsequence);

    for name in ["Representative", "Rep"] {
        it.def(name, "S::. -> .", "An element of S.", rep);
    }
    it.def("ExtractRep", "~R::SetEnum, ~r", "Remove an element from R and assign it to r.", extract_rep);
    for (name, f) in [("Minimum", minimum as super::NativeFn), ("Min", minimum), ("Maximum", maximum), ("Max", maximum)] {
        for t in ["SeqEnum", "SetIndx"] {
            it.def(name, &format!("S::{t} -> ., RngIntElt"), "The extreme element of S and its position.", f);
        }
        for t in ["SetEnum", "SetMulti", "List"] {
            it.def(name, &format!("S::{t} -> ."), "The extreme element of S.", f);
        }
    }
    for name in ["Index", "Position"] {
        it.def(name, "S::SeqEnum, x::. -> RngIntElt", "The first position of x in S, or 0.", index_of);
        it.def(name, "S::SeqEnum, x::., f::RngIntElt -> RngIntElt", "The first position of x in S from position f, or 0.", index_of);
        it.def(name, "S::SetIndx, x::. -> RngIntElt", "The index of x in S, or 0.", index_of);
        it.def(name, "S::List, x::. -> RngIntElt", "The first position of x in S, or 0.", index_of);
    }
    it.def("Index", "x::CopElt -> RngIntElt", "The index of the constituent of x.", cop_index);
    for t in ["SeqEnum", "Tup", "List"] {
        it.def("Explode", &format!("S::{t} -> ."), "The elements of S as separate return values.", explode);
    }
    it.def("ElementToSequence", "S::SeqEnum -> SeqEnum", "S itself.", eltseq_seq);
    it.def("Eltseq", "S::SeqEnum -> SeqEnum", "S itself.", eltseq_seq);

    for t in ["SeqEnum", "List", "Tup", "SetIndx"] {
        it.def("Append", &format!("~S::{t}, x::."), "Append x to S.", append_proc);
        it.def("Append", &format!("S::{t}, x::. -> {t}"), "S with x appended.", append_func);
    }
    for t in ["SetEnum", "SetIndx", "SetMulti", "SeqEnum"] {
        it.def("Include", &format!("~S::{t}, x::."), "Include x in S.", include_proc);
        it.def("Include", &format!("S::{t}, x::. -> {t}"), "S with x included.", include_func);
    }
    for t in ["SetEnum", "SetMulti", "SeqEnum", "SetIndx"] {
        it.def("Exclude", &format!("~S::{t}, x::."), "Remove (one copy of) x from S.", exclude_proc);
        it.def("Exclude", &format!("S::{t}, x::. -> {t}"), "S with (one copy of) x removed.", exclude_func);
    }
    for t in ["SeqEnum", "List", "SetIndx"] {
        it.def("Insert", &format!("~S::{t}, i::RngIntElt, x::."), "Insert x at position i of S.", insert_proc);
        it.def("Insert", &format!("S::{t}, i::RngIntElt, x::. -> {t}"), "S with x inserted at position i.", insert_func);
    }
    it.def("Insert", "~S::SeqEnum, k::RngIntElt, m::RngIntElt, T::SeqEnum", "Replace S[k..m] by the elements of T.", insert_proc);
    it.def("Insert", "S::SeqEnum, k::RngIntElt, m::RngIntElt, T::SeqEnum -> SeqEnum", "S with S[k..m] replaced by the elements of T.", insert_func);
    for t in ["SeqEnum", "List", "Tup", "SetIndx"] {
        it.def("Prune", &format!("~S::{t}"), "Remove the last element of S.", prune_proc);
        it.def("Prune", &format!("S::{t} -> {t}"), "S without its last element.", prune_func);
    }
    for t in ["SeqEnum", "List"] {
        it.def("Remove", &format!("~S::{t}, i::RngIntElt"), "Remove the i-th element of S.", remove_proc);
        it.def("Remove", &format!("S::{t}, i::RngIntElt -> {t}"), "S without its i-th element.", remove_func);
        it.def("Reverse", &format!("~S::{t}"), "Reverse S.", reverse_proc);
        it.def("Reverse", &format!("S::{t} -> {t}"), "S reversed.", reverse_func);
    }
    it.def("Remove", "~A::Assoc, x::.", "Remove the key x from A.", remove_proc);
    it.def("Remove", "A::Assoc, x::. -> Assoc", "A without the key x.", remove_func);
    it.def("Rotate", "~S::SeqEnum, p::RngIntElt", "Rotate S right by p positions.", rotate_proc);
    it.def("Rotate", "S::SeqEnum, p::RngIntElt -> SeqEnum", "S rotated right by p positions.", rotate_func);
    it.def("Undefine", "~S::SeqEnum, i::RngIntElt", "Make S[i] undefined.", undefine_proc);
    it.def("Undefine", "S::SeqEnum, i::RngIntElt -> SeqEnum", "S with S[i] undefined.", undefine_func);
    it.def("Sort", "~S::SeqEnum", "Sort S into increasing order.", sort_proc);
    it.def("Sort", "~S::SeqEnum, ~p", "Sort S and set p to the sorting permutation, which maps i to the original position of the i-th element.", sort_proc);
    it.def("Sort", "~S::SeqEnum, C::Program", "Sort S using the comparison function C.", sort_proc);
    it.def("Sort", "~S::SeqEnum, C::Program, ~p", "Sort S using C and set p to the sorting permutation.", sort_proc);
    it.def("Sort", "S::SeqEnum -> SeqEnum", "S sorted into increasing order.", sort_func);
    it.def("Sort", "S::SeqEnum, C::Program -> SeqEnum, GrpPermElt", "S sorted using the comparison function C, and the sorting permutation.", sort_func);
    it.def("Sort", "S::SetEnum -> SeqEnum", "The elements of S in increasing order.", sort_func);
    it.def("Sort", "S::SetEnum, C::Program -> SeqEnum", "The elements of S sorted using C.", sort_func);
    it.def("Sort", "L::List, C::Program -> List", "L sorted using the comparison function C.", sort_func);
    it.def("ParallelSort", "~S::SeqEnum, ~T::SeqEnum", "Sort S, applying the same permutation to T.", parallel_sort);
    for t in ["SeqEnum", "SetEnum", "SetIndx", "SetMulti"] {
        it.def("ChangeUniverse", &format!("~S::{t}, V::Str"), "Coerce the elements of S into V.", change_universe_proc);
        it.def("ChangeUniverse", &format!("S::{t}, V::Str -> {t}"), "S with its elements coerced into V.", change_universe_func);
        it.def("CanChangeUniverse", &format!("S::{t}, V::. -> BoolElt, {t}"), "Whether the elements of S can be coerced into V, and the result.", can_change_universe);
    }

    for name in ["Setseq", "SetToSequence"] {
        it.def(name, "S::SetEnum -> SeqEnum", "The elements of S as a sequence.", to_seq);
    }
    for name in ["Seqset", "SequenceToSet"] {
        it.def(name, "S::SeqEnum -> SetEnum", "The set of elements of S.", to_set);
    }
    it.def("SetToIndexedSet", "S::SetEnum -> SetIndx", "The elements of S as an indexed set.", to_iset);
    it.def("SequenceToIndexedSet", "S::SeqEnum -> SetIndx", "The elements of S as an indexed set.", to_iset);
    for name in ["IndexedSetToSet", "Isetset"] {
        it.def(name, "S::SetIndx -> SetEnum", "The elements of S as an enumerated set.", to_set);
    }
    for name in ["IndexedSetToSequence", "Isetseq"] {
        it.def(name, "S::SetIndx -> SeqEnum", "The elements of S as a sequence.", to_seq);
    }
    it.def("MultisetToSet", "S::SetMulti -> SetEnum", "The distinct elements of S.", multiset_to_set);
    it.def("SetToMultiset", "S::SetEnum -> SetMulti", "The multiset of elements of S.", to_mset);
    it.def("SequenceToMultiset", "S::SeqEnum -> SetMulti", "The multiset of elements of S.", to_mset);
    it.def("Multiset", "S::SeqEnum -> SetMulti", "The multiset of elements of S.", to_mset);
    it.def("Multiset", "S::SetEnum -> SetMulti", "The multiset of elements of S.", to_mset);
    it.def("SequenceToList", "S::SeqEnum -> List", "The elements of S as a list.", to_list);
    it.def("Seqlist", "S::SeqEnum -> List", "The elements of S as a list.", to_list);
    it.def("TupleToList", "T::Tup -> List", "The components of T as a list.", to_list);
    it.def("Tuplist", "T::Tup -> List", "The components of T as a list.", to_list);

    it.def("Multiplicity", "S::SetMulti, x::. -> RngIntElt", "The multiplicity of x in S.", multiplicity);
    it.def("Multiplicities", "S::SetMulti -> [RngIntElt]", "The multiplicities of the distinct elements of S.", multiplicities);
    it.def("Subsets", "S::SetEnum -> SetEnum", "The set of all subsets of S.", subsets);
    it.def("Subsets", "S::SetEnum, k::RngIntElt -> SetEnum", "The set of subsets of S of size k.", subsets);
    it.def("RandomSubset", "S::SetEnum, k::RngIntElt -> SetEnum", "A random subset of S of size k.", random_subset);
    it.def("Multisets", "S::SetEnum, k::RngIntElt -> SetEnum", "The set of multisets of k elements of S.", multisets);
    it.def("Subsequences", "S::SetEnum, k::RngIntElt -> SetEnum", "The set of sequences of length k over S.", subsequences);
    it.def("Permutations", "S::SetEnum -> SetEnum", "The set of permutations of S (as sequences).", permutations);
    it.def("Permutations", "S::SetEnum, k::RngIntElt -> SetEnum", "The set of arrangements of k elements of S (as sequences).", permutations);

    it.def("And", "S::[BoolElt], T::[BoolElt] -> [BoolElt]", "The componentwise conjunction of S and T.", seq_and);
    it.def("And", "~S::[BoolElt], T::[BoolElt]", "Replace S by the componentwise conjunction of S and T.", seq_and_proc);
    it.def("Or", "~S::[BoolElt], T::[BoolElt]", "Replace S by the componentwise disjunction of S and T.", seq_or_proc);
    it.def("Xor", "~S::[BoolElt], T::[BoolElt]", "Replace S by the componentwise exclusive or of S and T.", seq_xor_proc);
    it.def("Not", "~S::[BoolElt]", "Replace S by its componentwise negation.", seq_not_proc);
    it.def("Or", "S::[BoolElt], T::[BoolElt] -> [BoolElt]", "The componentwise disjunction of S and T.", seq_or);
    it.def("Xor", "S::[BoolElt], T::[BoolElt] -> [BoolElt]", "The componentwise exclusive or of S and T.", seq_xor);
    it.def("Not", "S::[BoolElt] -> [BoolElt]", "The componentwise negation of S.", seq_not);
    it.def("Partition", "S::SeqEnum, p::RngIntElt -> SeqEnum", "S cut into consecutive parts of length p.", partition);
    it.def("Partition", "S::SeqEnum, P::[RngIntElt] -> SeqEnum", "S cut into consecutive parts of the given lengths.", partition);

    it.def("CartesianProduct", "R::., S::., ... -> SetCart", "The Cartesian product of the given structures.", cartesian_product);
    it.def("CartesianProduct", "L::. -> SetCart", "The Cartesian product of the structures in L.", cartesian_product);
    it.def("CartesianPower", "R::., k::RngIntElt -> SetCart", "The k-th Cartesian power of R.", cartesian_power);
    it.def("Flat", "T::Tup -> Tup", "T with nested tuples expanded.", flat);
    it.def("Flat", "C::SetCart -> SetCart", "C with nested products expanded.", flat);
    it.def("Flat", "C::Cop -> Cop", "C with nested coproducts expanded.", flat);
    it.def("Flat", "S::SeqEnum -> SeqEnum", "S with nested sequences expanded.", flat);
    it.def("NumberOfComponents", "C::SetCart -> RngIntElt", "The number of components of C.", number_of_components);
    it.def("NumberOfComponents", "C::Cop -> RngIntElt", "The number of constituents of C.", number_of_components);
    it.def("Component", "C::SetCart, i::RngIntElt -> .", "The i-th component of C.", component);
    it.def("Components", "C::SetCart -> List", "The components of C.", components);
    it.def("Random", "C::SetCart -> Tup", "A random element of C.", car_random);
    it.def("Rep", "C::SetCart -> Tup", "An element of C.", car_rep);
    it.def("Representative", "C::SetCart -> Tup", "An element of C.", car_rep);

    it.def_params("AssociativeArray", "-> Assoc", &[("Default", Value::Undef)], "A new empty associative array.", assoc_new);
    it.def_params("AssociativeArray", "I::. -> Assoc", &[("Default", Value::Undef)], "A new empty associative array with index universe I.", assoc_new);
    it.def("Keys", "A::Assoc -> SetEnum", "The set of keys of A.", assoc_keys);
    it.def("Values", "A::Assoc -> List", "The values stored in A.", assoc_values);

    it.def("Format", "r::Rec -> RecFrmt", "The record format of r.", record_format);
    it.def("Names", "r::Rec -> [MonStgElt]", "The field names of r.", record_names);
    it.def("Names", "F::RecFrmt -> [MonStgElt]", "The field names of F.", record_names);

    it.def("Injections", "C::Cop -> SeqEnum", "The injections into C.", injections);
    it.def("Constituent", "C::Cop, i::RngIntElt -> .", "The i-th constituent of C.", constituent);
    it.def("Retrieve", "x::CopElt -> .", "The element of a constituent represented by x.", retrieve);
    it.def("UniversalMap", "C::Cop, S::., M::SeqEnum -> Map", "The map from C to S defined by the maps in M.", universal_map);
    let _ = Sym::new("");
}
