//! Multivariate polynomial rings (the handbook chapter of that name):
//! creating rings and polynomials, structure operations, the functions of
//! polynomials, greatest common divisors, factorization, resultants and
//! the functions for integer polynomials.
//!
//! Polynomials are `gr_mpoly`s, whose generic arithmetic is fast enough
//! (it beats Magma on Fateman's benchmark). The algorithms beyond it run
//! on FLINT's specialised types through `calyx_flint::mpoly`.

use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{Elem, GrError, MonomialOrder, Truth};
use calyx_flint::mpoly as fm;
use calyx_syntax::ast::BinOp;

use super::{arg_ge, boolv, intv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::ops::div_by_zero;
use crate::rings::props::ring_props;
use crate::rings::{Elt, Ring, RingKind, make_elt, ring_of};
use crate::value::*;

// ----- helpers ---------------------------------------------------------------

/// Argument `i`, which the signature makes a multivariate polynomial.
fn mpol(a: &CallArgs, i: usize) -> Rc<Elt> {
    match &a.args[i] {
        Value::Elt(e) => e.clone(),
        _ => unreachable!("a polynomial argument"),
    }
}

/// Argument `i`, a multivariate polynomial ring.
fn ring_arg(a: &CallArgs, i: usize) -> (Rc<Struct>, Rc<Ring>) {
    match &a.args[i] {
        Value::Struct(s) => match &s.kind {
            StructKind::Ring(r) => (s.clone(), r.clone()),
            _ => unreachable!("a polynomial ring argument"),
        },
        _ => unreachable!("a polynomial ring argument"),
    }
}

/// The rank of a multivariate polynomial ring.
fn rank(r: &Ring) -> usize {
    match &r.kind {
        RingKind::MPoly { rank, .. } => *rank,
        _ => unreachable!("a multivariate polynomial ring"),
    }
}

/// The index of `v` among the variables of the ring of `f` (from 0), if
/// it is one of them.
fn var_index(f: &Elt, v: &Value) -> Option<usize> {
    let Value::Elt(v) = v else { return None };
    if v.ring().id != f.ring().id || v.x.mpoly_len() != 1 {
        return None;
    }
    let (c, exps) = v.x.mpoly_term(0);
    if c.is_one() != Truth::True || exps.iter().sum::<u64>() != 1 {
        return None;
    }
    exps.iter().position(|&e| e == 1)
}

/// Argument `i` naming a variable of `P` of rank `n`, by number (1 to n) or
/// as the variable itself, as an index from 0. `what` words the error for a
/// number out of range ("variable number", "name index").
fn var_arg(a: &CallArgs, i: usize, f: &Elt, what: &str) -> RResult<usize> {
    let n = rank(f.ring());
    match &a.args[i] {
        Value::Int(k) => match k.to_i64() {
            Some(k) if k >= 1 && k as usize <= n => Ok(k as usize - 1),
            _ => Err(RuntimeError::runtime(format!("Value for {what} ({k}) should be in the range [1..{n}]"))),
        },
        v => var_index(f, v).ok_or_else(|| RuntimeError::runtime(format!("Argument {} is not a variable", i + 1))),
    }
}

/// An element of the ring of `f`.
fn like(f: &Elt, x: Elem) -> Value {
    make_elt(&f.parent, x)
}

/// The coefficient ring of the ring of `f`.
fn base_of(f: &Elt) -> Value {
    f.ring().base().expect("a polynomial ring").clone()
}

/// A coefficient of `f` as an element of its coefficient ring.
fn cval(it: &Interp, f: &Elt, c: Elem) -> Value {
    it.elem_to_value(&base_of(f), c)
}

/// The zero of the coefficient ring of `f`.
fn czero(f: &Elt) -> Elem {
    Elem::zero(f.x.ctx().base().expect("a polynomial ring"))
}

/// The terms of a polynomial, largest first.
fn terms(f: &Elem) -> Vec<(Elem, Vec<u64>)> {
    (0..f.mpoly_len()).map(|i| f.mpoly_term(i)).collect()
}

/// The polynomial of the ring of `f` with the given terms.
fn build(f: &Elt, ts: &[(Elem, Vec<u64>)]) -> RResult<Value> {
    Ok(like(f, Elem::mpoly_from_terms(f.x.ctx(), ts)?))
}

/// The monomial with exponents `e` in the ring of `f`.
fn monomial(f: &Elt, e: Vec<u64>) -> RResult<Value> {
    let c = Elem::one(f.x.ctx().base().expect("a polynomial ring"))?;
    build(f, &[(c, e)])
}

/// The terms of `f` by their power of variable `i`, ascending.
fn by_power(f: &Elem, i: usize) -> BTreeMap<u64, Vec<(Elem, Vec<u64>)>> {
    let mut m: BTreeMap<u64, Vec<(Elem, Vec<u64>)>> = BTreeMap::new();
    for (c, e) in terms(f) {
        m.entry(e[i]).or_default().push((c, e));
    }
    m
}

/// Terms without their power of variable `i`.
fn without(ts: &[(Elem, Vec<u64>)], i: usize) -> Vec<(Elem, Vec<u64>)> {
    ts.iter().map(|(c, e)| (c.clone(), e.iter().enumerate().map(|(j, &k)| if j == i { 0 } else { k }).collect())).collect()
}

/// A sequence of polynomials of the ring of `f`.
fn pseq(f: &Elt, xs: Vec<Value>) -> Value {
    Value::seq(Some(f.parent_value()), xs)
}

// ----- creation --------------------------------------------------------------

/// The monomial order named `s`.
fn parse_order(s: &str) -> RResult<MonomialOrder> {
    Ok(match s {
        "lex" => MonomialOrder::Lex,
        "glex" => MonomialOrder::DegLex,
        "grevlex" => MonomialOrder::DegRevLex,
        _ => return Err(RuntimeError::runtime(format!("Bad order \"{s}\""))),
    })
}

/// `PolynomialRing(R, n)` (global with the parameter Global) and
/// `PolynomialRing(R, n, order)`.
fn polynomial_ring(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let base = a.args[0].clone();
    let n = a.int(1)?;
    let Some(n) = n.to_i64().filter(|n| (0..1 << 29).contains(n)) else {
        return Err(RuntimeError::runtime(format!("Argument 2 ({n}) should be in the range [0 .. 536870911]")));
    };
    let order = if a.args.len() > 2 { parse_order(&a.str(2)?)? } else { MonomialOrder::Lex };
    let global = a.args.len() == 2 && a.param_bool("Global")?;
    one(it.mpoly_ring(&base, n as usize, order, global)?)
}

fn identity(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, r) = ring_arg(a, 0);
    one(make_elt(&st, Elem::one(&r.ctx)?))
}

/// `MultivariatePolynomial(P, f, v)`: the univariate `f` in the variable v
/// of P (given by number or as the variable).
fn multivariate_polynomial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, r) = ring_arg(a, 0);
    let Value::Elt(f) = &a.args[1] else { unreachable!("a polynomial argument") };
    let base = r.base().expect("a polynomial ring");
    if f.ring().base() != Some(base) {
        return Err(RuntimeError::runtime("Arguments have incompatible coefficient rings"));
    }
    let n = rank(&r);
    let i = match &a.args[2] {
        Value::Int(k) => match k.to_i64() {
            Some(k) if k >= 1 && k as usize <= n => k as usize - 1,
            _ => return Err(RuntimeError::runtime(format!("Value for variable number ({k}) should be in the range [1..{n}]"))),
        },
        v => {
            let p = Elt { parent: st.clone(), x: Elem::zero(&r.ctx) };
            var_index(&p, v).ok_or_else(|| RuntimeError::runtime("Argument 3 is not a variable"))?
        }
    };
    let mut terms = Vec::with_capacity(f.x.poly_len());
    for k in 0..f.x.poly_len() {
        let c = f.x.poly_coeff(k);
        if c.is_zero() != Truth::True {
            let mut exps = vec![0u64; n];
            exps[i] = k as u64;
            terms.push((c, exps));
        }
    }
    one(make_elt(&st, Elem::mpoly_from_terms(&r.ctx, &terms)?))
}

// ----- predicates ------------------------------------------------------------------

/// Whether `f` is not a zero divisor: Magma answers only over domains.
fn is_regular(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    boolv(ring_props(&base_of(&f)).is_some_and(|p| p.domain) && f.x.mpoly_len() > 0)
}

// ----- coefficients, monomials and terms -------------------------------------

/// `Coefficients(f)`, and the coefficients of the powers of a variable (from
/// the 0-th) with one given.
fn coefficients(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    if a.args.len() == 1 {
        let cs = terms(&f.x).into_iter().map(|(c, _)| cval(it, &f, c)).collect();
        return one(Value::seq(Some(base_of(&f)), cs));
    }
    let i = var_arg(a, 1, &f, "variable number")?;
    let m = by_power(&f.x, i);
    let n = m.keys().next_back().map_or(0, |&d| d + 1);
    let mut cs = Vec::new();
    for k in 0..n {
        cs.push(build(&f, &m.get(&k).map_or_else(Vec::new, |ts| without(ts, i)))?);
    }
    one(pseq(&f, cs))
}

/// The coefficient of the k-th power of a variable.
fn coefficient(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let i = var_arg(a, 1, &f, "variable number")?;
    let k = a.int(2)?;
    if k.sign() < 0 {
        return Err(arg_ge(3, &k, 0));
    }
    let ts = k.to_u64().and_then(|k| by_power(&f.x, i).remove(&k)).unwrap_or_default();
    one(build(&f, &without(&ts, i))?)
}

/// The coefficient of the leading term, or of the largest power of a
/// variable.
fn leading_coefficient(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    if a.args.len() == 1 {
        let c = if f.x.mpoly_len() == 0 { czero(&f) } else { f.x.mpoly_term(0).0 };
        return one(cval(it, &f, c));
    }
    let i = var_arg(a, 1, &f, "variable number")?;
    let ts = by_power(&f.x, i).pop_last().map(|(_, ts)| ts).unwrap_or_default();
    one(build(&f, &without(&ts, i))?)
}

/// The coefficient of the trailing term, or of the least power of a
/// variable.
fn trailing_coefficient(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let n = f.x.mpoly_len();
    if a.args.len() == 1 {
        let c = if n == 0 { czero(&f) } else { f.x.mpoly_term(n - 1).0 };
        return one(cval(it, &f, c));
    }
    let i = var_arg(a, 1, &f, "variable number")?;
    let ts = by_power(&f.x, i).pop_first().map(|(_, ts)| ts).unwrap_or_default();
    one(build(&f, &without(&ts, i))?)
}

fn length(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(mpol(a, 0).x.mpoly_len() as u64))
}

/// The terms of `f`, or its terms by ascending powers of a variable.
fn terms_of(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let ts: Vec<Vec<(Elem, Vec<u64>)>> = if a.args.len() == 1 {
        terms(&f.x).into_iter().map(|t| vec![t]).collect()
    } else {
        let i = var_arg(a, 1, &f, "variable number")?;
        by_power(&f.x, i).into_values().collect()
    };
    let ts = ts.iter().map(|t| build(&f, t)).collect::<RResult<Vec<_>>>()?;
    one(pseq(&f, ts))
}

/// The term of `f` in the k-th power of a variable.
fn term(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let i = var_arg(a, 1, &f, "variable number")?;
    let k = a.int(2)?;
    if k.sign() < 0 {
        return Err(arg_ge(3, &k, 0));
    }
    let ts = k.to_u64().and_then(|k| by_power(&f.x, i).remove(&k)).unwrap_or_default();
    one(build(&f, &ts)?)
}

/// The leading term of `f`, or its term in the largest power of a variable.
fn leading_term(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let ts = if a.args.len() == 1 {
        terms(&f.x).into_iter().take(1).collect()
    } else {
        let i = var_arg(a, 1, &f, "variable number")?;
        by_power(&f.x, i).pop_last().map(|(_, ts)| ts).unwrap_or_default()
    };
    one(build(&f, &ts)?)
}

/// The trailing term of `f`, or its term in the least power of a variable.
fn trailing_term(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let ts = if a.args.len() == 1 {
        let n = f.x.mpoly_len();
        if n == 0 { Vec::new() } else { vec![f.x.mpoly_term(n - 1)] }
    } else {
        let i = var_arg(a, 1, &f, "variable number")?;
        by_power(&f.x, i).pop_first().map(|(_, ts)| ts).unwrap_or_default()
    };
    one(build(&f, &ts)?)
}

fn monomials(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let ms = terms(&f.x).into_iter().map(|(_, e)| monomial(&f, e)).collect::<RResult<Vec<_>>>()?;
    one(pseq(&f, ms))
}

fn coefficients_and_monomials(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let (mut cs, mut ms) = (Vec::new(), Vec::new());
    for (c, e) in terms(&f.x) {
        cs.push(cval(it, &f, c));
        ms.push(monomial(&f, e)?);
    }
    Ok(vals![Value::seq(Some(base_of(&f)), cs), pseq(&f, ms)])
}

fn leading_monomial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    if f.x.mpoly_len() == 0 {
        return one(like(&f, Elem::zero(f.x.ctx())));
    }
    one(monomial(&f, f.x.mpoly_term(0).1)?)
}

/// The coefficient in `f` of the monomial `m`.
fn monomial_coefficient(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, m) = (mpol(a, 0), mpol(a, 1));
    if f.ring().id != m.ring().id {
        return Err(RuntimeError::runtime("Arguments are not compatible"));
    }
    let e = match m.x.mpoly_len() {
        1 => match m.x.mpoly_term(0) {
            (c, e) if c.is_one() == Truth::True => e,
            _ => return Err(RuntimeError::runtime("Argument 2 must be a monomial")),
        },
        _ => return Err(RuntimeError::runtime("Argument 2 must be a monomial")),
    };
    let c = terms(&f.x).into_iter().find(|(_, x)| *x == e).map_or_else(|| czero(&f), |(c, _)| c);
    one(cval(it, &f, c))
}

/// The exponents of the monomial of a term.
fn exponents(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    if f.x.mpoly_len() != 1 {
        return Err(RuntimeError::runtime("Argument 1 must be a term"));
    }
    one(Value::int_seq(f.x.mpoly_term(0).1.into_iter().map(Integer::from_u64)))
}

/// `Monomial(P, E)`: the product of the variables to the powers E.
fn monomial_from(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, r) = ring_arg(a, 0);
    let n = rank(&r);
    let es = a.seq(1)?.elems.clone();
    if es.len() != n {
        return Err(RuntimeError::runtime(format!("Argument 2 should have length {n}")));
    }
    let mut e = Vec::with_capacity(n);
    for v in &es {
        match v {
            Value::Int(k) if k.sign() >= 0 => e.push(k.to_u64().ok_or_else(|| RuntimeError::runtime("Exponent too large"))?),
            _ => return Err(RuntimeError::runtime("Argument 2 must contain non-negative integers")),
        }
    }
    let c = Elem::one(r.ctx.base().expect("a polynomial ring"))?;
    one(make_elt(&st, Elem::mpoly_from_terms(&r.ctx, &[(c, e)])?))
}

/// `Polynomial(C, M)`: the sum of the products of the coefficients C and
/// the monomials M.
fn polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (cs, ms) = (a.seq(0)?.clone(), a.seq(1)?.clone());
    let Some((st, r)) = ms.universe.as_ref().and_then(ring_of).filter(|(_, r)| matches!(r.kind, RingKind::MPoly { .. })) else {
        return Err(RuntimeError::runtime("Argument 2 must be a sequence of polynomials"));
    };
    let (st, ctx, base) = (st.clone(), r.ctx.clone(), r.base().expect("a polynomial ring").clone());
    if cs.elems.len() != ms.elems.len() {
        return Err(RuntimeError::runtime("Arguments have different lengths"));
    }
    let (mut ts, mut acc) = (Vec::new(), Elem::zero(&ctx));
    for (c, m) in cs.elems.iter().zip(&ms.elems) {
        let Some(c) = it.to_structure_elem(&base, c, false)? else {
            return Err(RuntimeError::runtime("Coefficients are not in the coefficient ring"));
        };
        let Value::Elt(m) = m else { unreachable!("a polynomial") };
        match m.x.mpoly_len() {
            0 => {}
            1 if m.x.mpoly_term(0).0.is_one() == Truth::True => ts.push((c, m.x.mpoly_term(0).1)),
            _ => acc = acc.add(&m.x.mpoly_mul_scalar(&c)?)?,
        }
    }
    one(make_elt(&st, acc.add(&Elem::mpoly_from_terms(&ctx, &ts)?)?))
}

/// The least common multiple of the denominators of the coefficients.
fn denominator(f: &Elt) -> RResult<Integer> {
    let mut l = Integer::one();
    match ring_props(&base_of(f)) {
        Some(_) if matches!(base_of(f).as_struct(), Some(StructKind::Rationals)) => {
            for (c, _) in terms(&f.x) {
                l = l.lcm(&c.to_rational()?.denominator());
            }
        }
        Some(_) if matches!(base_of(f).as_struct(), Some(StructKind::Integers)) => {}
        _ => return Err(RuntimeError::runtime("Coefficient ring must be the integers or the rationals")),
    }
    Ok(l)
}

fn coefficient_denominator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(denominator(&mpol(a, 0))?)
}

fn coefficient_numerator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let l = Elem::from_integer(f.x.ctx().base().expect("a polynomial ring"), &denominator(&f)?)?;
    one(like(&f, f.x.mpoly_mul_scalar(&l)?))
}

// ----- degrees ----------------------------------------------------------------

/// The degree of `f` in a variable (-1 for zero).
fn degree(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let i = var_arg(a, 1, &f, "variable number")?;
    let d = terms(&f.x).iter().map(|(_, e)| e[i] as i64).max().unwrap_or(-1);
    intv(Integer::from_i64(d))
}

fn total_degree(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let d = terms(&f.x).iter().map(|(_, e)| e.iter().sum::<u64>() as i64).max().unwrap_or(-1);
    intv(Integer::from_i64(d))
}

fn leading_total_degree(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let d = if f.x.mpoly_len() == 0 { -1 } else { f.x.mpoly_term(0).1.iter().sum::<u64>() as i64 };
    intv(Integer::from_i64(d))
}

// ----- univariate polynomials ------------------------------------------------------

/// The variables occurring in `f` (from 0).
fn occurring(f: &Elem) -> Vec<usize> {
    let mut seen: Vec<bool> = Vec::new();
    for (_, e) in terms(f) {
        seen.resize(e.len(), false);
        for (j, &k) in e.iter().enumerate() {
            seen[j] |= k > 0;
        }
    }
    (0..seen.len()).filter(|&j| seen[j]).collect()
}

/// `f`, a polynomial in variable `i` alone, in the univariate polynomial ring
/// over its coefficient ring.
fn univariate(it: &mut Interp, f: &Elt, i: usize) -> RResult<Value> {
    let u = it.poly_ring(&base_of(f), true)?;
    let Some((st, r)) = ring_of(&u) else { unreachable!("a polynomial ring") };
    let (st, ctx) = (st.clone(), r.ctx.clone());
    let ts = terms(&f.x);
    let power = |e: &Vec<u64>| e.get(i).copied().unwrap_or(0) as usize;
    let n = ts.iter().map(|(_, e)| power(e) + 1).max().unwrap_or(0);
    let mut cs = vec![czero(f); n];
    for (c, e) in ts {
        cs[power(&e)] = c;
    }
    Ok(make_elt(&st, Elem::poly_from_coeffs(&ctx, &cs)?))
}

/// Whether `f` is univariate (in the given variable), with its univariate
/// version (and the number of its variable, the first for a constant).
fn is_univariate(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let vs = occurring(&f.x);
    if a.args.len() > 1 {
        let i = var_arg(a, 1, &f, "variable number")?;
        if vs.iter().any(|&j| j != i) {
            return boolv(false);
        }
        return Ok(vals![Value::Bool(true), univariate(it, &f, i)?]);
    }
    match vs.as_slice() {
        [] => Ok(vals![Value::Bool(true), univariate(it, &f, 0)?, Value::int(1)]),
        [i] => Ok(vals![Value::Bool(true), univariate(it, &f, *i)?, Value::int(*i as i64 + 1)]),
        _ => boolv(false),
    }
}

fn univariate_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    match occurring(&f.x).as_slice() {
        [] => one(univariate(it, &f, 0)?),
        [i] => one(univariate(it, &f, *i)?),
        _ => Err(RuntimeError::runtime("Argument 1 is not univariate")),
    }
}

// ----- derivative, integral ----------------------------------------------------------

/// The (k-th) derivative with respect to a variable.
fn derivative(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let (k, v) = if a.args.len() == 3 { (a.int(1)?.clone(), 2) } else { (Integer::one(), 1) };
    let i = var_arg(a, v, &f, "variable number")?;
    if k.sign() < 0 {
        return Err(arg_ge(2, &k, 0));
    }
    let Some(k) = k.to_u64() else { return one(like(&f, Elem::zero(f.x.ctx()))) };
    let mut out = Vec::new();
    for (c, mut e) in terms(&f.x) {
        if e[i] < k {
            continue;
        }
        // c times the falling factorial e (e - 1) ... (e - k + 1).
        let mut m = Integer::one();
        for j in 0..k {
            m = &m * &Integer::from_u64(e[i] - j);
        }
        e[i] -= k;
        out.push((c.mul_integer(&m)?, e));
    }
    one(build(&f, &out)?)
}

/// The integral with respect to a variable, over a field of characteristic 0.
fn integral(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let i = var_arg(a, 1, &f, "variable number")?;
    let p = ring_props(&base_of(&f));
    if !p.as_ref().is_some_and(|p| p.field) {
        return Err(RuntimeError::runtime("Coefficient ring of argument 1 is not a field"));
    }
    if !p.is_some_and(|p| p.characteristic.is_zero()) {
        return Err(RuntimeError::runtime("Coefficient ring must have characteristic 0"));
    }
    let base = f.x.ctx().base().expect("a polynomial ring").clone();
    let mut out = Vec::new();
    for (c, mut e) in terms(&f.x) {
        e[i] += 1;
        out.push((c.div(&Elem::from_integer(&base, &Integer::from_u64(e[i]))?)?, e));
    }
    one(build(&f, &out)?)
}

// ----- evaluation, interpolation --------------------------------------------------------

/// The sum of the terms of `f` with the variables replaced by `xs`, values
/// of any structure, computed with the interpreter's arithmetic.
fn evaluate_generic(it: &mut Interp, f: &Elt, xs: &[Value]) -> RResult<Value> {
    let mut acc: Option<Value> = None;
    for (c, e) in terms(&f.x) {
        let mut t = cval(it, f, c);
        for (j, &k) in e.iter().enumerate() {
            if k > 0 {
                let p = it.binop(BinOp::Pow, xs[j].clone(), Value::Int(Integer::from_u64(k)))?;
                t = it.binop(BinOp::Mul, t, p)?;
            }
        }
        acc = Some(match acc {
            Some(s) => it.binop(BinOp::Add, s, t)?,
            None => t,
        });
    }
    match (acc, xs.first()) {
        (Some(v), _) => Ok(v),
        (None, Some(x)) => it.binop(BinOp::Mul, x.clone(), Value::int(0)),
        (None, None) => Ok(cval(it, f, czero(f))),
    }
}

/// `Evaluate(f, s)`: the value of `f` at the sequence or tuple `s`, in the
/// coefficient ring if the values lift to it.
fn evaluate(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let n = rank(f.ring());
    let xs = match &a.args[1] {
        Value::Seq(s) => s.elems.clone(),
        Value::Tuple(t) => t.elems.clone(),
        _ => unreachable!("a sequence or tuple"),
    };
    if xs.len() != n {
        return Err(RuntimeError::runtime(format!("Argument 2 should have length {n}")));
    }
    let base = base_of(&f);
    let mut lifted = Vec::with_capacity(n);
    for x in &xs {
        let px = it.parent_of(x)?;
        match it.auto_coerces(&px, &base).then(|| it.to_structure_elem(&base, x, false)).transpose()?.flatten() {
            Some(y) => lifted.push(y),
            None => break,
        }
    }
    if lifted.len() < n {
        return one(evaluate_generic(it, &f, &xs)?);
    }
    let mut pows: HashMap<(usize, u64), Elem> = HashMap::new();
    let mut acc = czero(&f);
    for (c, e) in terms(&f.x) {
        let mut t = c;
        for (j, &k) in e.iter().enumerate() {
            if k > 0 {
                if !pows.contains_key(&(j, k)) {
                    pows.insert((j, k), lifted[j].pow(&Integer::from_u64(k))?);
                }
                t = t.mul(&pows[&(j, k)])?;
            }
        }
        acc = acc.add(&t)?;
    }
    one(it.elem_to_value(&base, acc))
}

/// `Evaluate(f, i, r)`: `f` with a variable replaced by `r`, in the ring of
/// `f` if r lifts to its coefficient ring or is in it, otherwise in the
/// structure of r (into which the other variables must coerce).
fn evaluate_at(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let i = var_arg(a, 1, &f, "variable number")?;
    let r = a.args[2].clone();
    let base = base_of(&f);
    let pr = it.parent_of(&r)?;
    if it.auto_coerces(&pr, &base) {
        if let Some(x) = it.to_structure_elem(&base, &r, false)? {
            let mut pows: HashMap<u64, Elem> = HashMap::new();
            let mut out = Vec::new();
            for (c, mut e) in terms(&f.x) {
                let k = std::mem::replace(&mut e[i], 0);
                if !pows.contains_key(&k) {
                    pows.insert(k, x.pow(&Integer::from_u64(k))?);
                }
                out.push((c.mul(&pows[&k])?, e));
            }
            return one(build(&f, &out)?);
        }
    }
    // A polynomial of the same ring: Horner's rule on the powers present.
    if let Value::Elt(re) = &r {
        if re.ring().id == f.ring().id {
            let ctx = f.x.ctx().clone();
            let mut acc = Elem::zero(&ctx);
            let mut last: Option<u64> = None;
            for (k, ts) in by_power(&f.x, i).into_iter().rev() {
                if let Some(l) = last {
                    acc = acc.mul(&re.x.pow(&Integer::from_u64(l - k))?)?;
                }
                acc = acc.add(&Elem::mpoly_from_terms(&ctx, &without(&ts, i))?)?;
                last = Some(k);
            }
            if let Some(l) = last.filter(|&l| l > 0) {
                acc = acc.mul(&re.x.pow(&Integer::from_u64(l))?)?;
            }
            return one(like(&f, acc));
        }
    }
    let n = rank(f.ring());
    let mut xs = Vec::with_capacity(n);
    for j in 0..n {
        xs.push(if j == i { r.clone() } else { it.coerce(&pr, &like(&f, f.x.ctx().mpoly_gen(j)?))? });
    }
    one(evaluate_generic(it, &f, &xs)?)
}

/// `Interpolation(I, V, i)`: the polynomial of degree less than #I in the
/// i-th variable taking the values V (free of that variable) at the points
/// I of the coefficient field.
fn interpolation(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (xs, vs) = (a.seq(0)?.clone(), a.seq(1)?.clone());
    let Some(Value::Elt(f)) = vs.elems.first().cloned() else {
        return Err(RuntimeError::runtime("Argument 2 must be a non-empty sequence of polynomials"));
    };
    let i = var_arg(a, 2, &f, "variable number")?;
    let n = xs.elems.len();
    if vs.elems.len() != n {
        return Err(RuntimeError::runtime("Arguments have different lengths"));
    }
    let base = base_of(&f);
    if !ring_props(&base).is_some_and(|p| p.field) {
        return Err(RuntimeError::runtime("Ring is not a field"));
    }
    let mut pts = Vec::with_capacity(n);
    for x in &xs.elems {
        match it.to_structure_elem(&base, x, false)? {
            Some(y) => pts.push(y),
            None => return Err(RuntimeError::runtime("Arguments have different rings")),
        }
    }
    let mut cs = Vec::with_capacity(n);
    for v in &vs.elems {
        let Value::Elt(v) = v else { unreachable!("a polynomial") };
        if v.ring().id != f.ring().id {
            return Err(RuntimeError::runtime("Arguments have different rings"));
        }
        if occurring(&v.x).contains(&i) {
            return Err(RuntimeError::runtime("Interpolation variable occurs in the values"));
        }
        cs.push(v.x.clone());
    }
    // Newton's divided differences, then Horner's rule.
    for k in 1..n {
        for j in (k..n).rev() {
            let d = pts[j].sub(&pts[j - k])?;
            if d.is_zero() == Truth::True {
                return Err(RuntimeError::runtime("Elements of argument 1 are not distinct"));
            }
            cs[j] = cs[j].sub(&cs[j - 1])?.mpoly_mul_scalar(&d.inv()?)?;
        }
    }
    let ctx = f.x.ctx().clone();
    let x = ctx.mpoly_gen(i)?;
    let mut acc = cs[n - 1].clone();
    for j in (0..n - 1).rev() {
        let mut shift = Elem::zero(&ctx);
        Elem::mpoly_set_scalar(&mut shift, &pts[j])?;
        acc = acc.mul(&x.sub(&shift)?)?.add(&cs[j])?;
    }
    one(like(&f, acc))
}

// ----- quotient and reductum ----------------------------------------------------------

/// `f / g` if g (non-zero) divides f exactly: on FLINT's specialised types
/// where they apply, otherwise by long division by leading terms.
pub fn exact_div(f: &Elem, g: &Elem) -> RResult<Option<Elem>> {
    match fm::divides(f, g) {
        Err(GrError::Unable) => {}
        r => return Ok(r?),
    }
    let ctx = f.ctx().clone();
    let (lc, le) = g.mpoly_term(0);
    let mut q = Vec::new();
    let mut r = f.clone();
    while r.mpoly_len() > 0 {
        let (c, e) = r.mpoly_term(0);
        if e.iter().zip(&le).any(|(x, y)| x < y) {
            return Ok(None);
        }
        let Ok(c) = c.div(&lc) else { return Ok(None) };
        let t = (c, e.iter().zip(&le).map(|(x, y)| x - y).collect::<Vec<_>>());
        r = r.sub(&Elem::mpoly_from_terms(&ctx, std::slice::from_ref(&t))?.mul(g)?)?;
        // Inexact coefficient arithmetic may leave the leading term.
        if r.mpoly_len() > 0 && r.mpoly_term(0).1 == e {
            r = Elem::mpoly_from_terms(&ctx, &terms(&r)[1..])?;
        }
        q.push(t);
    }
    Ok(Some(Elem::mpoly_from_terms(&ctx, &q)?))
}

/// The two polynomial arguments, of the same ring, the second non-zero.
fn quotient_args(a: &CallArgs) -> RResult<(Rc<Elt>, Rc<Elt>)> {
    let (f, g) = (mpol(a, 0), mpol(a, 1));
    if f.ring().id != g.ring().id {
        return Err(RuntimeError::runtime("Arguments are not compatible"));
    }
    if g.x.mpoly_len() == 0 {
        return Err(div_by_zero());
    }
    Ok((f, g))
}

fn exact_quotient(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = quotient_args(a)?;
    match exact_div(&f.x, &g.x)? {
        Some(q) => one(like(&f, q)),
        None => Err(RuntimeError::runtime("Argument 1 is not exactly divisible by argument 2")),
    }
}

fn is_divisible_by(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = quotient_args(a)?;
    match exact_div(&f.x, &g.x)? {
        Some(q) => Ok(vals![Value::Bool(true), like(&f, q)]),
        None => boolv(false),
    }
}

/// `f` without its leading term, or without its term in the largest power
/// of a variable.
fn reductum(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let ts = if a.args.len() == 1 {
        terms(&f.x).into_iter().skip(1).collect()
    } else {
        let i = var_arg(a, 1, &f, "variable number")?;
        let mut m = by_power(&f.x, i);
        m.pop_last();
        m.into_values().flatten().collect::<Vec<_>>()
    };
    one(build(&f, &ts)?)
}

// ----- greatest common divisors ---------------------------------------------------------

fn not_available() -> RuntimeError {
    RuntimeError::runtime("Algorithm is not available for this kind of coefficient ring")
}

/// A result of `calyx_flint::mpoly`, whose `Unable` means the coefficient
/// ring is not supported.
fn flint<T>(r: Result<T, GrError>) -> RResult<T> {
    r.map_err(|e| if e == GrError::Unable { not_available() } else { e.into() })
}

/// The two polynomial arguments, of the same ring.
fn same_ring(a: &CallArgs) -> RResult<(Rc<Elt>, Rc<Elt>)> {
    let (f, g) = (mpol(a, 0), mpol(a, 1));
    if f.ring().id != g.ring().id {
        return Err(RuntimeError::runtime("Arguments are not compatible"));
    }
    Ok((f, g))
}

/// The associate of `f` whose leading coefficient is normalized (monic over
/// a field, positive over the integers).
fn normalized(it: &mut Interp, f: &Elt) -> RResult<Elem> {
    if f.x.mpoly_len() == 0 {
        return Ok(f.x.clone());
    }
    let u = super::upoly::norm_unit(it, &base_of(f), &f.x.mpoly_term(0).0)?;
    Ok(f.x.mpoly_mul_scalar(&u)?)
}

fn normalize(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    one(like(&f, normalized(it, &f)?))
}

/// The normalized greatest common divisor.
fn gcd_of(it: &mut Interp, f: &Elt, g: &Elem) -> RResult<Elem> {
    let d = flint(fm::gcd(&f.x, g))?;
    normalized(it, &Elt { parent: f.parent.clone(), x: d })
}

/// The normalized least common multiple (zero if either is zero).
fn lcm_of(it: &mut Interp, f: &Elt, g: &Elem) -> RResult<Elem> {
    if f.x.mpoly_len() == 0 || g.mpoly_len() == 0 {
        return Ok(Elem::zero(f.x.ctx()));
    }
    let d = flint(fm::gcd(&f.x, g))?;
    let q = exact_div(&f.x, &d)?.expect("the gcd divides");
    normalized(it, &Elt { parent: f.parent.clone(), x: q.mul(g)? })
}

fn gcd(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = same_ring(a)?;
    one(like(&f, gcd_of(it, &f, &g.x)?))
}

fn lcm(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = same_ring(a)?;
    one(like(&f, lcm_of(it, &f, &g.x)?))
}

/// The gcd or lcm of a sequence: 0 or 1 of its universe if it is empty.
fn fold_seq(it: &mut Interp, a: &mut CallArgs, lcm: bool) -> RResult<Vals> {
    let q = a.seq(0)?.clone();
    let Some(Value::Elt(first)) = q.elems.first() else {
        let Some((st, r)) = q.universe.as_ref().and_then(ring_of) else { return Err(RuntimeError::runtime("Illegal null sequence")) };
        return one(make_elt(st, if lcm { Elem::one(&r.ctx)? } else { Elem::zero(&r.ctx) }));
    };
    let mut acc = Elt { parent: first.parent.clone(), x: first.x.clone() };
    for v in &q.elems {
        let Value::Elt(g) = v else { unreachable!("a polynomial") };
        acc.x = if lcm { lcm_of(it, &acc, &g.x)? } else { gcd_of(it, &acc, &g.x)? };
    }
    let x = normalized(it, &acc)?;
    one(like(&acc, x))
}

fn gcd_seq(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    fold_seq(it, a, false)
}

fn lcm_seq(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    fold_seq(it, a, true)
}

/// The content of `f` (the gcd of its coefficients over the integers, 1 over
/// a field; 0 for zero) and its primitive part.
fn contpp(it: &Interp, f: &Elt) -> RResult<(Value, Value)> {
    let b = f.x.ctx().base().expect("a polynomial ring").clone();
    match b.kind() {
        calyx_flint::gr::CtxKind::Integers => {
            let ts = terms(&f.x);
            let mut c = Integer::zero();
            for (x, _) in &ts {
                c = c.gcd(&x.to_integer()?);
            }
            if c.is_zero() || c.is_one() {
                return Ok((Value::Int(c), like(f, f.x.clone())));
            }
            let pp = ts.into_iter().map(|(x, e)| Ok((Elem::from_integer(&b, &x.to_integer()?.divexact(&c))?, e))).collect::<RResult<Vec<_>>>()?;
            Ok((Value::Int(c), like(f, Elem::mpoly_from_terms(f.x.ctx(), &pp)?)))
        }
        _ if ring_props(&base_of(f)).is_some_and(|p| p.field) => {
            let c = if f.x.mpoly_len() == 0 { Elem::zero(&b) } else { Elem::one(&b)? };
            Ok((cval(it, f, c), like(f, f.x.clone())))
        }
        _ => Err(not_available()),
    }
}

/// The constant `c` in the ring of `f`.
fn like_const(f: &Elt, c: &Elem) -> RResult<Elem> {
    let mut e = Elem::zero(f.x.ctx());
    e.mpoly_set_scalar(c)?;
    Ok(e)
}

fn content(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(contpp(it, &mpol(a, 0))?.0)
}

fn primitive_part(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(contpp(it, &mpol(a, 0))?.1)
}

fn content_and_primitive_part(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (c, pp) = contpp(it, &mpol(a, 0))?;
    Ok(vals![c, pp])
}

/// `f` times the least common multiple L of the denominators of its
/// coefficients, and L.
fn clear_denominators(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    if let Value::Seq(q) = &a.args[0] {
        let q = q.clone();
        let mut out = Vec::with_capacity(q.elems.len());
        for v in &q.elems {
            let Value::Elt(f) = v else { unreachable!("a polynomial") };
            let l = Elem::from_integer(f.x.ctx().base().expect("a polynomial ring"), &denominator(f)?)?;
            out.push(like(f, f.x.mpoly_mul_scalar(&l)?));
        }
        return one(Value::seq(q.universe.clone(), out));
    }
    let f = mpol(a, 0);
    let d = denominator(&f)?;
    let l = Elem::from_integer(f.x.ctx().base().expect("a polynomial ring"), &d)?;
    Ok(vals![like(&f, f.x.mpoly_mul_scalar(&l)?), Value::Int(d)])
}

// ----- factorization -------------------------------------------------------------------

fn nonzero(f: &Elt) -> RResult<()> {
    if f.x.mpoly_len() == 0 { Err(super::arg_not(1, "non-zero")) } else { Ok(()) }
}

fn is_integers(f: &Elt) -> bool {
    matches!(f.x.ctx().base().map(|b| b.kind()), Some(calyx_flint::gr::CtxKind::Integers))
}

/// Constant polynomials `<p, e>` for the prime powers of an integer.
fn prime_factors(f: &Elt, c: &Integer) -> RResult<Vec<(Elem, u64)>> {
    let zz = f.x.ctx().base().expect("a polynomial ring").clone();
    let Some(fz) = c.abs().factor() else { return Ok(Vec::new()) };
    fz.factors.iter().map(|(p, e)| Ok((like_const(f, &Elem::from_integer(&zz, p)?)?, *e))).collect()
}

/// A factorization sequence `[<q, k>, ...]` in Magma's order: by
/// multiplicity first if `by_mult`, then by the polynomials, compared term by
/// term from the leading one.
fn factorization_seq(it: &mut Interp, f: &Elt, mut v: Vec<(Elem, u64)>, by_mult: bool) -> Value {
    let ring = f.ring_rc();
    v.sort_by(|a, b| {
        let m = if by_mult { a.1.cmp(&b.1) } else { std::cmp::Ordering::Equal };
        m.then_with(|| it.ring_elt_cmp(&ring, &a.0, &b.0).ok().flatten().unwrap_or(std::cmp::Ordering::Equal))
    });
    Value::seq(None, v.into_iter().map(|(q, k)| Value::tuple(vec![like(f, q), Value::int(k as i64)])).collect())
}

/// The normalized factors of `f` (squarefree ones, merged by multiplicity,
/// with `squarefree`) and the unit: over the integers the prime powers of
/// the content come first as constant factors and the unit is the sign.
fn factors(it: &mut Interp, f: &Elt, squarefree: bool) -> RResult<(Vec<(Elem, u64)>, Value)> {
    nonzero(f)?;
    let (k, fs) = flint(fm::factor(&f.x, squarefree))?;
    let mut v: Vec<(Elem, u64)> = Vec::with_capacity(fs.len());
    for (q, e) in fs {
        let q = normalized(it, &Elt { parent: f.parent.clone(), x: q })?;
        match v.iter_mut().find(|(_, m)| squarefree && *m == e) {
            Some(p) => p.0 = normalized(it, &Elt { parent: f.parent.clone(), x: p.0.mul(&q)? })?,
            None => v.push((q, e)),
        }
    }
    if is_integers(f) {
        let c = k.to_integer()?;
        v.extend(prime_factors(f, &c)?);
        return Ok((v, Value::int(if c.sign() < 0 { -1 } else { 1 })));
    }
    // The unit is the leading coefficient of f over that of the product of
    // the (normalized) factors.
    let mut lead = Elem::one(k.ctx())?;
    for (q, e) in &v {
        lead = lead.mul(&q.mpoly_term(0).0.pow(&Integer::from_u64(*e))?)?;
    }
    let u = f.x.mpoly_term(0).0.div(&lead)?;
    Ok((v, cval(it, f, u)))
}

fn factorization(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let (v, unit) = factors(it, &f, false)?;
    let seq = factorization_seq(it, &f, v, false);
    if a.nresults >= 2 { Ok(vals![seq, unit]) } else { one(seq) }
}

fn squarefree_factorization(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let (v, _) = factors(it, &f, true)?;
    one(factorization_seq(it, &f, v, true))
}

/// The product of the distinct irreducible factors of positive degree,
/// normalized.
fn squarefree_part(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let (v, _) = factors(it, &f, true)?;
    let mut p = Elem::one(f.x.ctx())?;
    for (q, _) in v.iter().filter(|(q, _)| !q.mpoly_term(0).1.iter().all(|&e| e == 0)) {
        p = p.mul(q)?;
    }
    one(like(&f, normalized(it, &Elt { parent: f.parent.clone(), x: p })?))
}

/// Whether `f` is irreducible: it has one factor, of multiplicity 1 (over
/// the integers a prime constant is irreducible).
fn is_irreducible(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let (v, _) = factors(it, &f, false)?;
    boolv(matches!(v.as_slice(), [(_, 1)]))
}

// ----- resultants and discriminants ------------------------------------------------------

fn resultant(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = same_ring(a)?;
    let i = var_arg(a, 2, &f, "variable number")?;
    one(like(&f, flint(fm::resultant(&f.x, &g.x, i))?))
}

fn discriminant(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let i = var_arg(a, 1, &f, "variable number")?;
    one(like(&f, flint(fm::discriminant(&f.x, i))?))
}

// ----- polynomials over the integers ---------------------------------------------------------

/// The coefficients of `f`, which must be over the integers.
fn int_coeffs(f: &Elt) -> RResult<Vec<Integer>> {
    if !is_integers(f) {
        return Err(RuntimeError::runtime("Coefficient ring of argument must be Z"));
    }
    terms(&f.x).into_iter().map(|(c, _)| Ok(c.to_integer()?)).collect()
}

fn sign(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let cs = int_coeffs(&mpol(a, 0))?;
    intv(Integer::from_i64(cs.first().map_or(0, |c| c.sign() as i64)))
}

fn abs(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let cs = int_coeffs(&f)?;
    one(like(&f, if cs.first().is_some_and(|c| c.sign() < 0) { f.x.neg()? } else { f.x.clone() }))
}

fn max_norm(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let cs = int_coeffs(&mpol(a, 0))?;
    intv(cs.iter().map(|c| c.abs()).max().unwrap_or_default())
}

fn sum_norm(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let cs = int_coeffs(&mpol(a, 0))?;
    intv(cs.iter().fold(Integer::zero(), |s, c| &s + &c.abs()))
}

// ----- structure operations -------------------------------------------------

/// The map of `ChangeRing` between multivariate polynomial rings: coercion
/// of the coefficients, or a map applied to them.
struct CoefficientMap(Option<Rc<MapObj>>);

impl NativeMap for CoefficientMap {
    fn apply(&self, it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        let x = it.coerce(&m.domain, x).map_err(|_| RuntimeError::runtime("Element is not in the domain of the map").in_context("map application"))?;
        let Value::Elt(f) = &x else { unreachable!("a polynomial") };
        let Some((cst, cod)) = ring_of(&m.codomain) else { unreachable!("a polynomial ring") };
        let (cst, target, ctx) = (cst.clone(), cod.base().expect("a polynomial ring").clone(), cod.ctx.clone());
        let source = f.ring().base().expect("a polynomial ring").clone();
        let mut terms = Vec::with_capacity(f.x.mpoly_len());
        for i in 0..f.x.mpoly_len() {
            let (c, exps) = f.x.mpoly_term(i);
            let mut c = it.elem_to_value(&source, c);
            if let Some(g) = &self.0 {
                c = it.apply_map(g, &c)?;
            }
            match it.to_structure_elem(&target, &c, true)? {
                Some(c) => terms.push((c, exps)),
                None => {
                    let msg = "Cannot coerce element from source coefficent ring into the destination coefficient ring";
                    return Err(RuntimeError::runtime(msg).in_context("map application"));
                }
            }
        }
        Ok(make_elt(&cst, Elem::mpoly_from_terms(&ctx, &terms)?))
    }

    fn preimage(&self, _it: &mut Interp, _m: &MapObj, _y: &Value) -> RResult<Value> {
        Err(RuntimeError::runtime("No inverse is known for the map").in_context("@@"))
    }
}

/// A homomorphism from a polynomial ring given by the images of its
/// variables, applying a map to the coefficients or coercing them.
struct PolyHom {
    coeff: Option<Rc<MapObj>>,
    images: Vec<Value>,
}

impl NativeMap for PolyHom {
    fn apply(&self, it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        let x = it.coerce(&m.domain, x).map_err(|_| RuntimeError::runtime("Element is not in the domain of the map").in_context("map application"))?;
        let Value::Elt(f) = &x else { unreachable!("a polynomial") };
        let base = base_of(f);
        let image = |it: &mut Interp, c: Elem| -> RResult<Value> {
            let c = it.elem_to_value(&base, c);
            match &self.coeff {
                Some(g) => it.apply_map(g, &c),
                None => it.coerce(&m.codomain, &c),
            }
        };
        // Horner's rule for a univariate polynomial, a sum of terms otherwise.
        let mut acc = it.coerce(&m.codomain, &Value::int(0))?;
        if let RingKind::UPoly { .. } = f.ring().kind {
            for k in (0..f.x.poly_len()).rev() {
                acc = it.binop(BinOp::Mul, acc, self.images[0].clone())?;
                let c = image(it, f.x.poly_coeff(k))?;
                acc = it.binop(BinOp::Add, acc, c)?;
            }
            return Ok(acc);
        }
        for (c, e) in terms(&f.x) {
            let mut t = image(it, c)?;
            for (j, &k) in e.iter().enumerate() {
                if k > 0 {
                    let p = it.binop(BinOp::Pow, self.images[j].clone(), Value::Int(Integer::from_u64(k)))?;
                    t = it.binop(BinOp::Mul, t, p)?;
                }
            }
            acc = it.binop(BinOp::Add, acc, t)?;
        }
        Ok(acc)
    }

    fn preimage(&self, _it: &mut Interp, _m: &MapObj, _y: &Value) -> RResult<Value> {
        Err(RuntimeError::runtime("No inverse is known for the map").in_context("@@"))
    }
}

/// `hom< P -> S | y1, ..., yn >` and `hom< P -> S | f, y1, ..., yn >` for a
/// polynomial ring P: the images of the variables in S, after a map f of the
/// coefficients. `None` if P is not a polynomial ring.
pub fn polynomial_hom(it: &mut Interp, domain: &Value, codomain: &Value, images: &[Value]) -> RResult<Option<Value>> {
    let Some((_, r)) = ring_of(domain).filter(|(_, r)| matches!(r.kind, RingKind::UPoly { .. } | RingKind::MPoly { .. })) else { return Ok(None) };
    let n = r.ngens();
    let (coeff, ys) = match images {
        [Value::Map(g), ys @ ..] => (Some(g.clone()), ys),
        ys => (None, ys),
    };
    if ys.len() != n {
        return Err(RuntimeError::runtime(format!("Number of images ({}) does not equal the number of variables ({n})", ys.len())).in_context("hom< ... >"));
    }
    let mut out = Vec::with_capacity(n);
    for y in ys {
        out.push(it.coerce(codomain, y).map_err(|e| e.in_context("hom< ... >"))?);
    }
    let h = PolyHom { coeff, images: out };
    Ok(Some(Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain: domain.clone(), codomain: codomain.clone(), imp: MapImpl::Native(Rc::new(h)) }))))
}

/// `ChangeRing(P, S)`: the polynomial ring over S with the rank, order and
/// names of P, and the map from P (applying f to the coefficients if
/// given).
fn change_ring(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, r) = ring_arg(a, 0);
    let RingKind::MPoly { rank, order, .. } = r.kind else { unreachable!("a multivariate polynomial ring") };
    let q = it.mpoly_ring(&a.args[1], rank, order, false)?;
    if let Some((_, qr)) = ring_of(&q) {
        *qr.names.borrow_mut() = r.names.borrow().clone();
    }
    let f = match a.args.get(2) {
        Some(Value::Map(m)) => Some(m.clone()),
        _ => None,
    };
    let h = MapObj { kind: MapKind::Map, domain: a.args[0].clone(), codomain: q.clone(), imp: MapImpl::Native(Rc::new(CoefficientMap(f))) };
    Ok(vals![q, Value::Map(Rc::new(h))])
}

pub fn register(it: &mut Interp) {
    for name in ["PolynomialRing", "PolynomialAlgebra"] {
        it.def_params(name, "R::Rng, n::RngIntElt -> RngMPol", &[("Global", Value::Bool(false))], "The polynomial ring in n variables over R (the global one with Global).", polynomial_ring);
        it.def(name, "R::Rng, n::RngIntElt, order::MonStgElt -> RngMPol", "The polynomial ring in n variables over R with the given monomial order.", polynomial_ring);
    }
    it.def("Identity", "P::RngMPol -> RngMPolElt", "The identity of P.", identity);
    it.def("ChangeRing", "P::RngMPol, S::Rng -> RngMPol, Map", "The polynomial ring over S with the rank, order and names of P, with the map from P coercing coefficients.", change_ring);
    it.def("ChangeRing", "P::RngMPol, S::Rng, f::Map -> RngMPol, Map", "The polynomial ring over S with the rank, order and names of P, with the map from P applying f to the coefficients.", change_ring);
    it.def("MultivariatePolynomial", "P::RngMPol, f::RngUPolElt, i::RngIntElt -> RngMPolElt", "The univariate polynomial f in the i-th variable of P.", multivariate_polynomial);
    it.def("IsRegular", "f::RngMPolElt -> BoolElt", "Whether f is not a zero divisor.", is_regular);
    // A variable is given by its number or as itself.
    for v in ["i::RngIntElt", "v::RngMPolElt"] {
        it.def("Coefficients", &format!("f::RngMPolElt, {v} -> [RngMPolElt]"), "The coefficients of the powers of the variable in f, from the 0-th.", coefficients);
        it.def("Coefficient", &format!("f::RngMPolElt, {v}, k::RngIntElt -> RngMPolElt"), "The coefficient of the k-th power of the variable in f.", coefficient);
        it.def("LeadingCoefficient", &format!("f::RngMPolElt, {v} -> RngMPolElt"), "The coefficient of the largest power of the variable in f.", leading_coefficient);
        it.def("TrailingCoefficient", &format!("f::RngMPolElt, {v} -> RngMPolElt"), "The coefficient of the least power of the variable in f.", trailing_coefficient);
        it.def("Terms", &format!("f::RngMPolElt, {v} -> [RngMPolElt]"), "The terms of f in the powers of the variable, ascending.", terms_of);
        it.def("Term", &format!("f::RngMPolElt, {v}, k::RngIntElt -> RngMPolElt"), "The term of f in the k-th power of the variable.", term);
        it.def("LeadingTerm", &format!("f::RngMPolElt, {v} -> RngMPolElt"), "The term of f in the largest power of the variable.", leading_term);
        it.def("TrailingTerm", &format!("f::RngMPolElt, {v} -> RngMPolElt"), "The term of f in the least power of the variable.", trailing_term);
        it.def("Degree", &format!("f::RngMPolElt, {v} -> RngIntElt"), "The degree of f in the variable (-1 for zero).", degree);
        it.def("IsUnivariate", &format!("f::RngMPolElt, {v} -> BoolElt, RngUPolElt"), "Whether f is a polynomial in the variable alone, and if so as a univariate polynomial.", is_univariate);
        it.def("Derivative", &format!("f::RngMPolElt, {v} -> RngMPolElt"), "The derivative of f with respect to the variable.", derivative);
        it.def("Derivative", &format!("f::RngMPolElt, k::RngIntElt, {v} -> RngMPolElt"), "The k-th derivative of f with respect to the variable.", derivative);
        it.def("Integral", &format!("f::RngMPolElt, {v} -> RngMPolElt"), "The integral of f with respect to the variable.", integral);
        it.def("Evaluate", &format!("f::RngMPolElt, {v}, r::RngElt -> RngElt"), "f with the variable replaced by r.", evaluate_at);
        it.def("Interpolation", &format!("I::[RngElt], V::[RngMPolElt], {v} -> RngMPolElt"), "The polynomial of least degree in the variable taking the values V at the points I.", interpolation);
        it.def("Reductum", &format!("f::RngMPolElt, {v} -> RngMPolElt"), "f without its term in the largest power of the variable.", reductum);
    }
    it.def("Coefficients", "f::RngMPolElt -> [RngElt]", "The coefficients of the terms of f, largest first.", coefficients);
    it.def("LeadingCoefficient", "f::RngMPolElt -> RngElt", "The coefficient of the leading term of f.", leading_coefficient);
    it.def("TrailingCoefficient", "f::RngMPolElt -> RngElt", "The coefficient of the trailing term of f.", trailing_coefficient);
    it.def("Length", "f::RngMPolElt -> RngIntElt", "The number of terms of f.", length);
    it.def("CoefficientDenominator", "f::RngMPolElt -> RngIntElt", "The least common multiple of the denominators of the coefficients of f.", coefficient_denominator);
    it.def("CoefficientNumerator", "f::RngMPolElt -> RngMPolElt", "f times the denominator of its coefficients.", coefficient_numerator);
    it.def("MonomialCoefficient", "f::RngMPolElt, m::RngMPolElt -> RngElt", "The coefficient of the monomial m in f.", monomial_coefficient);
    it.def("Monomials", "f::RngMPolElt -> [RngMPolElt]", "The monomials of f, largest first.", monomials);
    it.def("CoefficientsAndMonomials", "f::RngMPolElt -> [RngElt], [RngMPolElt]", "The coefficients and the monomials of f.", coefficients_and_monomials);
    it.def("LeadingMonomial", "f::RngMPolElt -> RngMPolElt", "The monomial of the leading term of f.", leading_monomial);
    it.def("Terms", "f::RngMPolElt -> [RngMPolElt]", "The terms of f, largest first.", terms_of);
    it.def("LeadingTerm", "f::RngMPolElt -> RngMPolElt", "The leading term of f.", leading_term);
    it.def("TrailingTerm", "f::RngMPolElt -> RngMPolElt", "The trailing term of f.", trailing_term);
    it.def("Exponents", "f::RngMPolElt -> [RngIntElt]", "The exponents of the monomial of the term f.", exponents);
    it.def("Monomial", "P::RngMPol, E::[RngIntElt] -> RngMPolElt", "The product of the variables of P to the powers E.", monomial_from);
    it.def("Polynomial", "C::[RngElt], M::[RngMPolElt] -> RngMPolElt", "The sum of the products of the coefficients C and the monomials M.", polynomial);
    it.def("TotalDegree", "f::RngMPolElt -> RngIntElt", "The largest total degree of a monomial of f (-1 for zero).", total_degree);
    it.def("LeadingTotalDegree", "f::RngMPolElt -> RngIntElt", "The total degree of the leading monomial of f (-1 for zero).", leading_total_degree);
    it.def("IsUnivariate", "f::RngMPolElt -> BoolElt, RngUPolElt, RngIntElt", "Whether f is a polynomial in one variable, with its univariate version and the variable's number.", is_univariate);
    it.def("UnivariatePolynomial", "f::RngMPolElt -> RngUPolElt", "f, a polynomial in one variable, as a univariate polynomial.", univariate_polynomial);
    it.def("Evaluate", "f::RngMPolElt, s::[RngElt] -> RngElt", "The value of f at the sequence s.", evaluate);
    it.def("Evaluate", "f::RngMPolElt, s::Tup -> RngElt", "The value of f at the tuple s.", evaluate);
    it.def("ExactQuotient", "f::RngMPolElt, g::RngMPolElt -> RngMPolElt", "f / g for g dividing f.", exact_quotient);
    it.def("IsDivisibleBy", "f::RngMPolElt, g::RngMPolElt -> BoolElt, RngMPolElt", "Whether g divides f, and the quotient.", is_divisible_by);
    it.def("Reductum", "f::RngMPolElt -> RngMPolElt", "f without its leading term.", reductum);

    // Greatest common divisors, factorization, resultants.
    for name in ["GreatestCommonDivisor", "Gcd", "GCD"] {
        it.def(name, "f::RngMPolElt, g::RngMPolElt -> RngMPolElt", "The normalized greatest common divisor of f and g.", gcd);
        it.def(name, "Q::[RngMPolElt] -> RngMPolElt", "The normalized greatest common divisor of the polynomials of Q (0 for none).", gcd_seq);
    }
    for name in ["LeastCommonMultiple", "Lcm", "LCM"] {
        it.def(name, "f::RngMPolElt, g::RngMPolElt -> RngMPolElt", "The normalized least common multiple of f and g.", lcm);
        it.def(name, "Q::[RngMPolElt] -> RngMPolElt", "The normalized least common multiple of the polynomials of Q (1 for none).", lcm_seq);
    }
    for name in ["Normalize", "Normalise"] {
        it.def(name, "f::RngMPolElt -> RngMPolElt", "The normalized associate of f.", normalize);
    }
    it.def("ClearDenominators", "f::RngMPolElt -> RngMPolElt, RngIntElt", "f times the least common multiple L of the denominators of its coefficients, and L.", clear_denominators);
    it.def("ClearDenominators", "Q::[RngMPolElt] -> [RngMPolElt]", "The polynomials of Q with their denominators cleared.", clear_denominators);
    it.def("Content", "f::RngMPolElt -> RngElt", "The gcd of the coefficients of f.", content);
    it.def("PrimitivePart", "f::RngMPolElt -> RngMPolElt", "f divided by its content.", primitive_part);
    for name in ["ContentAndPrimitivePart", "Contpp"] {
        it.def(name, "f::RngMPolElt -> RngElt, RngMPolElt", "The content and the primitive part of f.", content_and_primitive_part);
    }
    for name in ["Factorization", "Factorisation"] {
        it.def(name, "f::RngMPolElt -> SeqEnum, RngElt", "The factorization of f into normalized irreducibles, and the unit.", factorization);
    }
    for name in ["SquarefreeFactorization", "SquarefreeFactorisation"] {
        it.def(name, "f::RngMPolElt -> SeqEnum", "The squarefree factorization of f.", squarefree_factorization);
    }
    it.def("SquarefreePart", "f::RngMPolElt -> RngMPolElt", "The product of the distinct irreducible factors of f, normalized.", squarefree_part);
    for name in ["IsIrreducible", "IsPrime"] {
        it.def(name, "f::RngMPolElt -> BoolElt", "Whether f is irreducible.", is_irreducible);
    }
    for v in ["i::RngIntElt", "v::RngMPolElt"] {
        it.def("Resultant", &format!("f::RngMPolElt, g::RngMPolElt, {v} -> RngMPolElt"), "The resultant of f and g with respect to the variable.", resultant);
        it.def("Discriminant", &format!("f::RngMPolElt, {v} -> RngMPolElt"), "The discriminant of f with respect to the variable.", discriminant);
    }

    // Polynomials over the integers.
    it.def("Sign", "f::RngMPolElt -> RngIntElt", "The sign of the leading coefficient of f.", sign);
    for name in ["AbsoluteValue", "Abs"] {
        it.def(name, "f::RngMPolElt -> RngMPolElt", "f or -f, whichever has a non-negative leading coefficient.", abs);
    }
    it.def("MaxNorm", "f::RngMPolElt -> RngIntElt", "The largest absolute value of a coefficient of f.", max_norm);
    it.def("SumNorm", "f::RngMPolElt -> RngIntElt", "The sum of the absolute values of the coefficients of f.", sum_norm);
    it.def("MultivariatePolynomial", "P::RngMPol, f::RngUPolElt, v::RngMPolElt -> RngMPolElt", "The univariate polynomial f in the variable v of P.", multivariate_polynomial);
}
