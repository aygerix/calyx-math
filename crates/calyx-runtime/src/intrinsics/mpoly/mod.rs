//! Multivariate polynomial rings (the handbook chapter of that name):
//! creating rings and polynomials, structure operations, the functions of
//! polynomials and their matrices (`matrices`), greatest common divisors,
//! factorization, resultants and the functions for integer polynomials.
//!
//! Polynomials are `gr_mpoly`s, whose generic arithmetic is fast enough
//! (it beats Magma on Fateman's benchmark). The algorithms beyond it run
//! on FLINT's specialised types through `calyx_flint::mpoly`, over
//! polynomial rings flattened (`upoly::Tower`).

use std::collections::{BTreeMap, HashMap, hash_map::Entry};
use std::rc::Rc;

use calyx_flint::gr::{Ctx, CtxKind, Elem, GrError, Truth};
use calyx_flint::mpoly as fm;
use calyx_flint::{Integer, Rational, Real};
use calyx_groebner::{Order, OrderArg};
use calyx_syntax::ast::{AggKind, BinOp};

use super::upoly::{Tower, norm_unit, over_ground, poly_divides, poly_gcd};
use super::{arg_ge, boolv, intv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::ops::div_by_zero;
use crate::rings::props::ring_props;
use crate::rings::{Elt, Ring, RingKind, make_elt, ring_of};
use crate::value::*;

mod matrices;

use matrices::*;

// ----- helpers ---------------------------------------------------------------

/// Argument `i`, which the signature makes a multivariate polynomial.
fn mpol(a: &CallArgs, i: usize) -> Rc<Elt> {
    match &a.args[i] {
        Value::Elt(e) => e.clone(),
        _ => unreachable!("a polynomial argument"),
    }
}

/// Argument `i`, a multivariate polynomial ring (or an ideal, which
/// answers for its ring).
fn ring_arg(a: &CallArgs, i: usize) -> (Rc<Struct>, Rc<Ring>) {
    match &a.args[i] {
        Value::Struct(s) => match &s.kind {
            StructKind::Ring(r) => (s.clone(), r.clone()),
            StructKind::MPolIdeal(id) => (id.ring.clone(), id.poly_ring().clone()),
            _ => unreachable!("a polynomial ring argument"),
        },
        _ => unreachable!("a polynomial ring argument"),
    }
}

/// The rank of a multivariate polynomial ring (or of an affine algebra).
fn rank(r: &Ring) -> usize {
    match &r.kind {
        RingKind::MPoly { rank, .. } | RingKind::MPolyRes { rank, .. } => *rank,
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

/// The terms of a polynomial in FLINT's order (the ring's own for lex,
/// glex and grevlex, lex for the other orders).
fn terms(f: &Elem) -> Vec<(Elem, Vec<u64>)> {
    (0..f.mpoly_len()).map(|i| f.mpoly_term(i)).collect()
}

/// The monomial order of a multivariate polynomial ring (or of the ring of
/// an affine algebra).
pub fn order_of(r: &Ring) -> &Order {
    match &r.kind {
        RingKind::MPoly { order, .. } => order,
        RingKind::MPolyRes { affine, .. } => order_of(affine.poly_ring()),
        _ => unreachable!("a multivariate polynomial ring"),
    }
}

/// The terms of `x`, an element of the multivariate ring `r`, from the
/// greatest in the ring's monomial order.
pub fn ordered_terms(r: &Ring, x: &Elem) -> Vec<(Elem, Vec<u64>)> {
    let mut ts = terms(x);
    let order = order_of(r);
    if !order.is_native() {
        ts.sort_by(|a, b| order.cmp(&b.1, &a.1));
    }
    ts
}

/// The greatest term of `x` in the monomial order of its ring `r`.
pub fn leading(r: &Ring, x: &Elem) -> Option<(Elem, Vec<u64>)> {
    let order = order_of(r);
    match x.mpoly_len() {
        0 => None,
        _ if order.is_native() => Some(x.mpoly_term(0)),
        _ => terms(x).into_iter().max_by(|a, b| order.cmp(&a.1, &b.1)),
    }
}

/// The least term of `x` in the monomial order of its ring `r`.
fn trailing(r: &Ring, x: &Elem) -> Option<(Elem, Vec<u64>)> {
    let order = order_of(r);
    match x.mpoly_len() {
        0 => None,
        n if order.is_native() => Some(x.mpoly_term(n - 1)),
        _ => terms(x).into_iter().min_by(|a, b| order.cmp(&a.1, &b.1)),
    }
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

/// An argument of a monomial order: an integer, a sequence of integers or
/// rationals, or anything else.
fn order_arg(v: &Value) -> OrderArg {
    let num = |x: &Value| match x {
        Value::Int(k) => Some(Rational::from_integer(k)),
        Value::Rat(q) => Some((**q).clone()),
        _ => None,
    };
    match v {
        Value::Int(k) => OrderArg::Int(k.clone()),
        Value::Seq(s) => s.elems.iter().map(num).collect::<Option<Vec<_>>>().map_or(OrderArg::Other, OrderArg::Seq),
        _ => OrderArg::Other,
    }
}

/// The order named `name` with the arguments `args` on `n` variables; Magma
/// numbers the arguments from `first` in its errors.
pub(super) fn parse_order(n: usize, name: &str, args: &[Value], first: usize) -> RResult<Order> {
    let args: Vec<OrderArg> = args.iter().map(order_arg).collect();
    Order::parse(n, name, &args).map_err(|e| RuntimeError::runtime(e.message(first)))
}

/// `PolynomialRing(R, n)` (global with the parameter Global), and with a
/// monomial order: `PolynomialRing(R, n, name, ...)` or `PolynomialRing(R,
/// n, <name, ...>)` with the name of the order and its arguments.
fn polynomial_ring(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let base = a.args[0].clone();
    let n = a.int(1)?;
    let Some(n) = n.to_i64().filter(|n| (0..1 << 29).contains(n)).map(|n| n as usize) else {
        return Err(RuntimeError::runtime(format!("Argument 2 ({n}) should be in the range [0 .. 536870911]")));
    };
    let order = match a.args.get(2) {
        None => Order::Lex,
        Some(Value::Str(s)) => parse_order(n, s.as_str(), &a.args[3..], 4)?,
        Some(Value::Tuple(t)) => match t.elems.split_first() {
            Some((Value::Str(s), rest)) => parse_order(n, s.as_str(), rest, 2)?,
            _ => return Err(RuntimeError::runtime("First component of tuple must be a string")),
        },
        Some(_) => unreachable!("an order"),
    };
    let global = a.args.len() == 2 && a.param_bool("Global")?;
    one(it.mpoly_ring(&base, n, order, None, global)?)
}

/// `PolynomialRing(R, Q)`: the graded ring whose variables have the weights
/// Q, ordered by grevlex with the weights max(w, 1).
fn graded_polynomial_ring(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let base = a.args[0].clone();
    let q = a.seq(1)?;
    if q.elems.is_empty() {
        return Err(super::arg_not(2, "non-empty"));
    }
    let mut ws = Vec::with_capacity(q.elems.len());
    for (i, w) in q.elems.iter().enumerate() {
        let w = match w {
            Value::Int(k) => k.to_u64().filter(|&k| k < 1 << 30),
            _ => None,
        };
        ws.push(w.ok_or_else(|| RuntimeError::runtime(format!("Weight number {} is not a small non-negative integer", i + 1)))?);
    }
    if ws.iter().any(|&w| w > Order::max_grevlexw_weight(ws.len())) {
        return Err(RuntimeError::runtime("Weight is too large"));
    }
    let order = Order::GRevLexW(ws.iter().map(|&w| w.max(1)).collect());
    one(it.mpoly_ring(&base, ws.len(), order, Some(ws.into()), false)?)
}

/// `MonomialOrder(P)`: the name of the order of P and its arguments.
fn monomial_order(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (name, args) = order_of(&ring_arg(a, 0).1).tuple();
    let mut t = vec![Value::str(name)];
    for arg in args {
        t.push(match arg {
            OrderArg::Int(k) => Value::Int(k),
            OrderArg::Seq(q) => Value::int_seq(q.iter().map(|x| x.numerator())),
            OrderArg::Other => unreachable!("an order argument"),
        });
    }
    one(Value::tuple(t))
}

/// The weight vectors of the order of P, whose dot products with exponent
/// vectors the order compares in turn.
fn monomial_order_weight_vectors(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let r = ring_arg(a, 0).1;
    let rat = |x: &Integer| Value::rat(Rational::from_integer(x));
    let rows = order_of(&r).weight_vectors(rank(&r)).iter().map(|row| Value::seq(Some(Value::rationals()), row.iter().map(rat).collect())).collect();
    one(it.build_aggregate(AggKind::Seq, None, rows, false)?)
}

fn identity(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    // Ideals have no identity.
    if let Some(StructKind::MPolIdeal(_)) = a.args[0].as_struct() {
        return Err(RuntimeError::runtime("Bad argument types"));
    }
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
        let cs = ordered_terms(f.ring(), &f.x).into_iter().map(|(c, _)| cval(it, &f, c)).collect();
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
        return Err(arg_ge(3, k, 0));
    }
    let ts = k.to_u64().and_then(|k| by_power(&f.x, i).remove(&k)).unwrap_or_default();
    one(build(&f, &without(&ts, i))?)
}

/// The coefficient of the leading term, or of the largest power of a
/// variable.
fn leading_coefficient(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    if a.args.len() == 1 {
        let c = leading(f.ring(), &f.x).map_or_else(|| czero(&f), |t| t.0);
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
    if a.args.len() == 1 {
        let c = trailing(f.ring(), &f.x).map_or_else(|| czero(&f), |t| t.0);
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
        ordered_terms(f.ring(), &f.x).into_iter().map(|t| vec![t]).collect()
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
        return Err(arg_ge(3, k, 0));
    }
    let ts = k.to_u64().and_then(|k| by_power(&f.x, i).remove(&k)).unwrap_or_default();
    one(build(&f, &ts)?)
}

/// The leading term of `f`, or its term in the largest power of a variable.
fn leading_term(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let ts = if a.args.len() == 1 {
        leading(f.ring(), &f.x).into_iter().collect()
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
        trailing(f.ring(), &f.x).into_iter().collect()
    } else {
        let i = var_arg(a, 1, &f, "variable number")?;
        by_power(&f.x, i).pop_first().map(|(_, ts)| ts).unwrap_or_default()
    };
    one(build(&f, &ts)?)
}

fn monomials(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let ms = ordered_terms(f.ring(), &f.x).into_iter().map(|(_, e)| monomial(&f, e)).collect::<RResult<Vec<_>>>()?;
    one(pseq(&f, ms))
}

fn coefficients_and_monomials(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let (mut cs, mut ms) = (Vec::new(), Vec::new());
    for (c, e) in ordered_terms(f.ring(), &f.x) {
        cs.push(cval(it, &f, c));
        ms.push(monomial(&f, e)?);
    }
    Ok(vals![Value::seq(Some(base_of(&f)), cs), pseq(&f, ms)])
}

fn leading_monomial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    nonzero(&f)?;
    one(monomial(&f, leading(f.ring(), &f.x).expect("a non-zero polynomial").1)?)
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
            _ => return Err(RuntimeError::runtime("Argument 2 is not a monomial")),
        },
        _ => return Err(RuntimeError::runtime("Argument 2 is not a monomial")),
    };
    let c = terms(&f.x).into_iter().find(|(_, x)| *x == e).map_or_else(|| czero(&f), |(c, _)| c);
    one(cval(it, &f, c))
}

/// The exponents of the monomial of a term.
fn exponents(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    if f.x.mpoly_len() != 1 {
        return Err(RuntimeError::runtime("Argument must be a term (polynomial with one term)"));
    }
    one(Value::int_seq(f.x.mpoly_term(0).1.into_iter().map(Integer::from_u64)))
}

/// `Monomial(P, E)`: the product of the variables to the powers E.
fn monomial_from(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, r) = ring_arg(a, 0);
    let n = rank(&r);
    let es = a.seq(1)?.elems.clone();
    if es.len() != n {
        return Err(RuntimeError::runtime(format!("Sequence should have length {n}")));
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
    let d = leading(f.ring(), &f.x).map_or(-1, |(_, e)| e.iter().sum::<u64>() as i64);
    intv(Integer::from_i64(d))
}

// ----- gradings -------------------------------------------------------------------
//
// The weighted degree of a monomial is the sum of its exponents times the
// weights of the variables: those of a graded ring, and 1 otherwise. The
// weights may be 0, so the monomial order of a graded ring (grevlex with the
// weights max(w, 1)) need not refine the weighted degree.

/// The weights of the variables of a multivariate polynomial ring.
pub(super) fn weights(r: &Ring) -> Vec<u64> {
    match &r.kind {
        RingKind::MPoly { grading: Some(w), .. } => w.to_vec(),
        RingKind::MPoly { rank, .. } => vec![1; *rank],
        RingKind::MPolyRes { affine, .. } => weights(affine.poly_ring()),
        _ => unreachable!("a multivariate polynomial ring"),
    }
}

/// The weighted degree of the monomial with exponents `e`.
fn wdeg(w: &[u64], e: &[u64]) -> i128 {
    w.iter().zip(e).map(|(&w, &k)| w as i128 * k as i128).sum()
}

/// `Grading(P)`: the weights of the variables.
fn grading(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int_seq(weights(&ring_arg(a, 0).1).into_iter().map(Integer::from_u64)))
}

/// `Degree(f)`, `WeightedDegree(f)`: the largest weighted degree of a term of
/// `f` (0 for zero).
fn weighted_degree(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let w = weights(f.ring());
    intv(Integer::from_i128(terms(&f.x).iter().map(|(_, e)| wdeg(&w, e)).max().unwrap_or(0)))
}

/// The weighted degree of the leading term of `f` (-1 for zero).
fn leading_weighted_degree(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let w = weights(f.ring());
    intv(Integer::from_i128(leading(f.ring(), &f.x).map_or(-1, |(_, e)| wdeg(&w, &e))))
}

/// Whether the terms of `x`, an element of `r`, have one weighted degree.
pub(super) fn homogeneous(r: &Ring, x: &Elem) -> bool {
    let w = weights(r);
    let mut ds = terms(x).into_iter().map(|(_, e)| wdeg(&w, &e));
    let d = ds.next();
    ds.all(|x| Some(x) == d)
}

fn is_homogeneous(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    boolv(homogeneous(f.ring(), &f.x))
}

/// The terms of `f` of weighted degree `d`.
fn homogeneous_component(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let d = a.int(1)?;
    if d.sign() < 0 {
        return Err(arg_ge(2, d, 0));
    }
    let w = weights(f.ring());
    let ts: Vec<_> = terms(&f.x).into_iter().filter(|(_, e)| Integer::from_i128(wdeg(&w, e)) == *d).collect();
    one(build(&f, &ts)?)
}

/// The homogeneous components of `f` of weighted degrees 0 to that of `f`.
fn homogeneous_components(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let w = weights(f.ring());
    let mut parts: Vec<Vec<(Elem, Vec<u64>)>> = vec![Vec::new()];
    for (c, e) in terms(&f.x) {
        let d = wdeg(&w, &e) as usize;
        if parts.len() <= d {
            parts.resize(d + 1, Vec::new());
        }
        parts[d].push((c, e));
    }
    let cs = parts.iter().map(|ts| build(&f, ts)).collect::<RResult<Vec<_>>>()?;
    one(pseq(&f, cs))
}

/// The exponent vectors of the monomials of weighted degree `d` for the
/// weights `w`, in which the variables of weight 0 do not occur, in
/// descending lexicographical order.
fn exponents_of_degree(w: &[u64], d: u64) -> Vec<Vec<u64>> {
    fn fill(w: &[u64], d: u64, e: &mut Vec<u64>, out: &mut Vec<Vec<u64>>) {
        let i = e.len();
        match w.len() - i {
            0 if d == 0 => out.push(e.clone()),
            0 => {}
            // The last variable takes what is left, if it can.
            1 => {
                let k = if w[i] == 0 { (d == 0).then_some(0) } else { (d % w[i] == 0).then_some(d / w[i]) };
                if let Some(k) = k {
                    out.push([&e[..], &[k]].concat());
                }
            }
            _ => {
                let top = if w[i] == 0 { 0 } else { d / w[i] };
                for k in (0..=top).rev() {
                    e.push(k);
                    fill(w, d - k * w[i], e, out);
                    e.pop();
                }
            }
        }
    }
    let mut out = Vec::new();
    fill(w, d, &mut Vec::with_capacity(w.len()), &mut out);
    out
}

/// The monomials of weighted degree `d` (argument 2) for the weights `w`,
/// as an indexed set in descending lexicographical order.
fn monomials_of(a: &CallArgs, w: &[u64]) -> RResult<Vals> {
    let (st, r) = ring_arg(a, 0);
    let d = a.int(1)?;
    if d.sign() < 0 {
        return Err(arg_ge(2, d, 0));
    }
    let d = d.to_u64().ok_or_else(|| RuntimeError::runtime(format!("Argument 2 ({d}) is too large")))?;
    let c = Elem::one(r.ctx.base().expect("a polynomial ring"))?;
    let mut elems = VSet::default();
    for e in exponents_of_degree(w, d) {
        elems.insert(make_elt(&st, Elem::mpoly_from_terms(&r.ctx, &[(c.clone(), e)])?));
    }
    one(Value::ISet(Rc::new(SetIndx { universe: Some(Value::Struct(st)), elems, name: Default::default() })))
}

/// `MonomialsOfDegree(P, d)`: the monomials of total degree `d`.
fn monomials_of_degree(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = rank(&ring_arg(a, 0).1);
    monomials_of(a, &vec![1; n])
}

/// `MonomialsOfWeightedDegree(P, d)`: the monomials of weighted degree `d`
/// in the variables of positive weight.
fn monomials_of_weighted_degree(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let w = weights(&ring_arg(a, 0).1);
    monomials_of(a, &w)
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

/// `f` as a univariate polynomial, and the number of its variable (1 for a
/// constant).
fn univariate_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let i = match occurring(&f.x).as_slice() {
        [] => 0,
        [i] => *i,
        _ => return Err(RuntimeError::runtime("Argument 1 is not univariate")),
    };
    Ok(vals![univariate(it, &f, i)?, Value::int(i as i64 + 1)])
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
    one(like(&f, partial(&f.x, i, k)?))
}

/// The k-th derivative of `x` with respect to variable i (from 0).
fn partial(x: &Elem, i: usize, k: u64) -> RResult<Elem> {
    let mut out = Vec::new();
    for (c, mut e) in terms(x) {
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
    Ok(Elem::mpoly_from_terms(x.ctx(), &out)?)
}

/// The integral with respect to a variable. Magma integrates over any
/// coefficient ring, dividing each coefficient by its new exponent, and where
/// that division is impossible (x over Z, x^(p-1) over GF(p)) returns a
/// malformed polynomial; calyx gives an error instead.
fn integral(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let i = var_arg(a, 1, &f, "variable number")?;
    let field = ring_props(&base_of(&f)).is_some_and(|p| p.field);
    let base = f.x.ctx().base().expect("a polynomial ring").clone();
    let mut out = Vec::new();
    for (c, mut e) in terms(&f.x) {
        e[i] += 1;
        match c.div(&Elem::from_integer(&base, &Integer::from_u64(e[i]))?) {
            Ok(q) => out.push((q, e)),
            Err(_) if field => return Err(div_by_zero()),
            Err(_) => return Err(RuntimeError::runtime("Coefficient ring of argument 1 is not a field")),
        }
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
        return Err(RuntimeError::runtime(format!("Argument 2 must have length {n}")));
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
                if let Entry::Vacant(v) = pows.entry((j, k)) {
                    v.insert(lifted[j].pow(&Integer::from_u64(k))?);
                }
                t = t.mul(&pows[&(j, k)])?;
            }
        }
        acc = acc.add(&t)?;
    }
    one(it.elem_to_value(&base, acc))
}

/// `g` with variable `i` replaced by `r` of the same ring, by Horner's rule on
/// the powers of the variable present.
fn substitute(g: &Elem, i: usize, r: &Elem) -> RResult<Elem> {
    let ctx = g.ctx().clone();
    let mut acc = Elem::zero(&ctx);
    let mut last: Option<u64> = None;
    for (k, ts) in by_power(g, i).into_iter().rev() {
        if let Some(l) = last {
            acc = acc.mul(&r.pow(&Integer::from_u64(l - k))?)?;
        }
        acc = acc.add(&Elem::mpoly_from_terms(&ctx, &without(&ts, i))?)?;
        last = Some(k);
    }
    if let Some(l) = last.filter(|&l| l > 0) {
        acc = acc.mul(&r.pow(&Integer::from_u64(l))?)?;
    }
    Ok(acc)
}

/// `Evaluate(f, i, r)`: `f` with a variable replaced by `r`. For r in a
/// multivariate ring of the same rank (that of f, or another into which f is
/// coerced as by `!`) the result lies in that ring; otherwise r must coerce
/// into the coefficient ring and the result lies in the ring of f.
fn evaluate_at(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let i = var_arg(a, 1, &f, "variable number")?;
    let r = a.args[2].clone();
    let not_coercible = || RuntimeError::runtime("Argument 3 not coercible into coefficient ring");
    if let Value::Elt(re) = &r {
        if let RingKind::MPoly { rank: m, .. } = re.ring().kind {
            if m != rank(f.ring()) {
                return Err(not_coercible());
            }
            let g = if re.ring().id == f.ring().id {
                f.x.clone()
            } else {
                let s = it.parent_of(&r)?;
                it.to_structure_elem(&s, &Value::Elt(f.clone()), true)?.ok_or_else(|| RuntimeError::runtime("Illegal coercion"))?
            };
            return one(like(re, substitute(&g, i, &re.x)?));
        }
    }
    let base = base_of(&f);
    let pr = it.parent_of(&r)?;
    let x = if it.auto_coerces(&pr, &base) { it.to_structure_elem(&base, &r, false)? } else { None };
    let x = x.ok_or_else(not_coercible)?;
    let mut pows: HashMap<u64, Elem> = HashMap::new();
    let mut out = Vec::new();
    for (c, mut e) in terms(&f.x) {
        let k = std::mem::replace(&mut e[i], 0);
        if let Entry::Vacant(v) = pows.entry(k) {
            v.insert(x.pow(&Integer::from_u64(k))?);
        }
        out.push((c.mul(&pows[&k])?, e));
    }
    one(build(&f, &out)?)
}

/// `Interpolation(I, V, i)`: the polynomial of degree less than #I in the
/// i-th variable taking the values V (free of that variable) at the points
/// I, a sequence over the coefficient field; 0 if the points are not
/// distinct, as in Magma.
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
    let u = xs.universe.clone().unwrap_or_else(|| base.clone());
    if !ring_props(&u).is_some_and(|p| p.field) {
        return Err(RuntimeError::runtime("Ring is not a field"));
    }
    if !it.auto_coerces(&u, &base) || !it.auto_coerces(&base, &u) {
        return Err(RuntimeError::runtime("Arguments have different rings"));
    }
    let mut cs = Vec::with_capacity(n);
    for (j, v) in vs.elems.iter().enumerate() {
        let Value::Elt(v) = v else { unreachable!("a polynomial") };
        if v.ring().id != f.ring().id {
            return Err(RuntimeError::runtime("Arguments have different rings"));
        }
        if occurring(&v.x).contains(&i) {
            return Err(RuntimeError::runtime(format!("Value {} contains variable {}", j + 1, i + 1)));
        }
        cs.push(v.x.clone());
    }
    let mut pts = Vec::with_capacity(n);
    for x in &xs.elems {
        pts.push(it.to_structure_elem(&base, x, false)?.ok_or_else(|| RuntimeError::runtime("Arguments have different rings"))?);
    }
    // Newton's divided differences, then Horner's rule.
    for k in 1..n {
        for j in (k..n).rev() {
            let d = pts[j].sub(&pts[j - k])?;
            if d.is_zero() == Truth::True {
                return one(like(&f, Elem::zero(f.x.ctx())));
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
    if let Some(t) = Tower::of(f.ctx()) {
        return Ok(t.divides(f, g)?);
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
        ordered_terms(f.ring(), &f.x).into_iter().skip(1).collect()
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
pub(super) fn normalized(it: &mut Interp, f: &Elt) -> RResult<Elem> {
    let Some((lc, _)) = leading(f.ring(), &f.x) else { return Ok(f.x.clone()) };
    let u = norm_unit(it, &base_of(f), &lc)?;
    Ok(f.x.mpoly_mul_scalar(&u)?)
}

fn normalize(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    one(like(&f, normalized(it, &f)?))
}

/// The gcd on FLINT's types, over a polynomial ring flattened.
fn flint_gcd(f: &Elem, g: &Elem) -> RResult<Elem> {
    match Tower::of(f.ctx()) {
        Some(t) => Ok(t.gcd(f, g)?),
        None => flint(fm::gcd(f, g)),
    }
}

/// The normalized greatest common divisor.
fn gcd_of(it: &mut Interp, f: &Elt, g: &Elem) -> RResult<Elem> {
    let d = flint_gcd(&f.x, g)?;
    normalized(it, &Elt { parent: f.parent.clone(), x: d })
}

/// The normalized least common multiple (zero if either is zero).
fn lcm_of(it: &mut Interp, f: &Elt, g: &Elem) -> RResult<Elem> {
    if f.x.mpoly_len() == 0 || g.mpoly_len() == 0 {
        return Ok(Elem::zero(f.x.ctx()));
    }
    let d = flint_gcd(&f.x, g)?;
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
/// a field, the gcd of the coefficients and n over Z/nZ, the normalized gcd
/// of the coefficients over a polynomial ring; 0 for zero) and its
/// primitive part, the quotient by it.
fn contpp(it: &mut Interp, f: &Elt) -> RResult<(Value, Value)> {
    let b = f.x.ctx().base().expect("a polynomial ring").clone();
    let ts = terms(&f.x);
    match b.kind() {
        CtxKind::Integers => {
            let mut c = Integer::zero();
            for (x, _) in &ts {
                c = c.gcd(&x.to_integer()?);
            }
            if c.is_zero() || c.is_one() {
                return Ok((Value::Int(c), like(f, f.x.clone())));
            }
            let pp = ts.into_iter().map(|(x, e)| Ok((Elem::from_integer(&b, &x.to_integer()?.divexact(&c))?, e))).collect::<RResult<Vec<_>>>()?;
            return Ok((Value::Int(c), like(f, Elem::mpoly_from_terms(f.x.ctx(), &pp)?)));
        }
        _ if ring_props(&base_of(f)).is_some_and(|p| p.field) => {
            let c = if f.x.mpoly_len() == 0 { Elem::zero(&b) } else { Elem::one(&b)? };
            return Ok((cval(it, f, c), like(f, f.x.clone())));
        }
        _ => {}
    }
    let pp = |c: &Elem, div: &dyn Fn(&Elem) -> RResult<Elem>| -> RResult<Value> {
        let ts = ts.iter().map(|(x, e)| Ok((div(x)?, e.clone()))).collect::<RResult<Vec<_>>>()?;
        Ok(like(f, if c.is_zero() == Truth::True { f.x.clone() } else { Elem::mpoly_from_terms(f.x.ctx(), &ts)? }))
    };
    let base = base_of(f);
    let kind = ring_of(&base).map(|(_, r)| &r.kind);
    match kind {
        Some(RingKind::Residue(m)) => {
            let mut c = m.clone();
            for (x, _) in &ts {
                c = c.gcd(&x.to_integer()?);
            }
            let q = pp(&Elem::from_integer(&b, &c)?, &|x| Ok(Elem::from_integer(&b, &x.to_integer()?.divexact(&c))?))?;
            Ok((cval(it, f, Elem::from_integer(&b, &c)?), q))
        }
        Some(RingKind::UPoly { .. } | RingKind::MPoly { .. }) if over_ground(&b) => {
            let mut c = Elem::zero(&b);
            for (x, _) in &ts {
                c = poly_gcd(&c, x)?;
            }
            let c = c.mul(&norm_unit(it, &base_of(f), &c)?)?;
            let q = pp(&c, &|x| Ok(poly_divides(x, &c)?.expect("the content divides")))?;
            Ok((cval(it, f, c), q))
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
    if c.is_zero() {
        return Ok(Vec::new());
    }
    super::factseq::factor(&c.abs()).iter().map(|(p, e)| Ok((like_const(f, &Elem::from_integer(&zz, p)?)?, *e))).collect()
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

fn no_factorization() -> RuntimeError {
    RuntimeError::runtime("Coefficient ring of argument 1 does not have a polynomial factorization algorithm")
}

fn is_constant(q: &Elem) -> bool {
    (0..q.mpoly_len()).all(|i| q.mpoly_term(i).1.iter().all(|&e| e == 0))
}

/// The normalized factors of `f` (squarefree ones, merged by multiplicity,
/// with `squarefree`) and the unit: over the integers the prime powers of
/// the content come first as constant factors and the unit is the sign.
/// Over a polynomial ring (flattened) the factors of the content come as
/// constants, merged apart from the others, and as in Magma they are left
/// out of the unit.
fn factors(it: &mut Interp, f: &Elt, squarefree: bool) -> RResult<(Vec<(Elem, u64)>, Value)> {
    nonzero(f)?;
    let tower = Tower::of(f.x.ctx());
    let (k, fs) = match &tower {
        Some(t) => {
            let (k, fs) = fm::factor(&t.flatten(&f.x)?, squarefree)?;
            (k, fs.into_iter().map(|(q, e)| Ok((t.unflatten(&q)?, e))).collect::<RResult<Vec<_>>>()?)
        }
        None => fm::factor(&f.x, squarefree).map_err(|e| if e == GrError::Unable { no_factorization() } else { e.into() })?,
    };
    let mut v: Vec<(Elem, u64)> = Vec::with_capacity(fs.len());
    for (q, e) in fs {
        let q = normalized(it, &Elt { parent: f.parent.clone(), x: q })?;
        match v.iter_mut().find(|(p, m)| squarefree && *m == e && is_constant(p) == is_constant(&q)) {
            Some(p) => p.0 = normalized(it, &Elt { parent: f.parent.clone(), x: p.0.mul(&q)? })?,
            None => v.push((q, e)),
        }
    }
    if matches!(k.ctx().kind(), CtxKind::Integers) {
        let c = k.to_integer()?;
        v.extend(prime_factors(f, &c)?);
        if tower.is_none() {
            return Ok((v, Value::int(if c.sign() < 0 { -1 } else { 1 })));
        }
    }
    // The unit is the leading coefficient of f over that of the product of
    // the (normalized) factors of positive degree: in Magma it keeps the
    // constant factors.
    let mut lead = Elem::one(&czero(f).ctx().clone())?;
    for (q, e) in v.iter().filter(|(q, _)| !is_constant(q)) {
        lead = lead.mul(&q.mpoly_term(0).0.pow(&Integer::from_u64(*e))?)?;
    }
    let lf = f.x.mpoly_term(0).0;
    let u = match lf.div(&lead) {
        Ok(u) => u,
        Err(_) => poly_divides(&lf, &lead)?.expect("the leading coefficients divide"),
    };
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

/// Whether `f` is irreducible: it has one factor, of multiplicity 1. Unlike
/// univariate polynomials in Magma, a prime constant over Z is irreducible.
fn is_irreducible(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let (v, _) = factors(it, &f, false)?;
    boolv(matches!(v.as_slice(), [(_, 1)]))
}

// ----- resultants and discriminants ------------------------------------------------------

/// The resultant of `f` and `g` in the variable `i`, or with no `g` the
/// discriminant of `f`: on FLINT's types, over polynomial rings flattened,
/// and over Z/nZ through the integers (it is a polynomial in the
/// coefficients).
/// The resultant (or discriminant) over the real or complex field, computed
/// exactly and rounded once: the coefficients are dyadic rationals, with
/// i a last variable reduced by i^2 = -1 at the end. None over other rings.
fn float_res_disc(f: &Elem, g: Option<&Elem>, i: usize) -> RResult<Option<Elem>> {
    let ctx = f.ctx();
    let b = ctx.base().expect("a polynomial ring");
    let (complex, prec) = match *b.kind() {
        CtxKind::RealFloat(p) => (false, p),
        CtxKind::ComplexFloat(p) => (true, p),
        _ => return Ok(None),
    };
    let CtxKind::MPoly { nvars, order } = *ctx.kind() else { unreachable!("a multivariate polynomial ring") };
    let qq = Ctx::rationals();
    let qx = Ctx::mpoly(&qq, nvars + complex as usize, order);
    let lift = |x: &Elem| -> RResult<Elem> {
        let mut ts = Vec::new();
        for (c, e) in terms(x) {
            let parts = match c.to_complex_parts() {
                Some((re, im)) => vec![(re, 0), (im, 1)],
                None => vec![(c.to_real().expect("a real number"), 0)],
            };
            for (r, k) in parts {
                let q = r.to_rational().ok_or_else(|| RuntimeError::runtime("Coefficients must be finite"))?;
                if !q.is_zero() {
                    let mut e = e.clone();
                    if complex {
                        e.push(k);
                    }
                    ts.push((Elem::from_rational(&qq, &q)?, e));
                }
            }
        }
        Ok(Elem::mpoly_from_terms(&qx, &ts)?)
    };
    let y = g.map(lift).transpose()?;
    let x = lift(f)?;
    let r = match &y {
        Some(y) => fm::resultant(&x, y, i)?,
        None => fm::discriminant(&x, i)?,
    };
    // The real and imaginary parts of each monomial, with i^k = ±1 or ±i.
    let mut parts: BTreeMap<Vec<u64>, (Rational, Rational)> = BTreeMap::new();
    for (c, mut e) in terms(&r) {
        let mut q = c.to_rational()?;
        let k = if complex { e.pop().expect("the variable i") } else { 0 };
        if k % 4 >= 2 {
            q = -&q;
        }
        let p = parts.entry(e).or_insert_with(|| (Rational::zero(), Rational::zero()));
        if k % 2 == 0 { p.0 = &p.0 + &q } else { p.1 = &p.1 + &q }
    }
    let mut ts = Vec::new();
    for (e, (re, im)) in parts {
        if re.is_zero() && im.is_zero() {
            continue;
        }
        let (re, im) = (Real::from_rational(&re, prec), Real::from_rational(&im, prec));
        ts.push((if complex { Elem::from_complex_parts(b, &re, &im)? } else { Elem::from_real(b, &re)? }, e));
    }
    Ok(Some(Elem::mpoly_from_terms(ctx, &ts)?))
}

fn res_disc(f: &Elem, g: Option<&Elem>, i: usize) -> RResult<Elem> {
    // As in Magma, the discriminant in a variable of degree 1 is 1, and of
    // degree 0 (or of zero) it is 0.
    if g.is_none() {
        match terms(f).iter().map(|(_, e)| e[i]).max() {
            None | Some(0) => return Ok(Elem::zero(f.ctx())),
            Some(1) => return Ok(Elem::one(f.ctx())?),
            _ => {}
        }
    }
    let run = |x: &Elem, y: Option<&Elem>| match y {
        Some(y) => fm::resultant(x, y, i),
        None => fm::discriminant(x, i),
    };
    if let Some(t) = Tower::of(f.ctx()) {
        let y = g.map(|g| t.flatten(g)).transpose()?;
        return Ok(t.unflatten(&run(&t.flatten(f)?, y.as_ref())?)?);
    }
    if let Some(r) = float_res_disc(f, g, i)? {
        return Ok(r);
    }
    match run(f, g) {
        Err(GrError::Unable) => {}
        r => return Ok(r?),
    }
    let b = f.ctx().base().expect("a polynomial ring").clone();
    let (CtxKind::Nmod(_) | CtxKind::FmpzMod(_), CtxKind::MPoly { nvars, order }) = (b.kind(), f.ctx().kind()) else { return Err(not_available()) };
    let zz = Ctx::integers();
    let zx = Ctx::mpoly(&zz, *nvars, *order);
    let lift = |x: &Elem| -> RResult<Elem> {
        let ts = terms(x).into_iter().map(|(c, e)| Ok((Elem::from_integer(&zz, &c.to_integer()?)?, e))).collect::<RResult<Vec<_>>>()?;
        Ok(Elem::mpoly_from_terms(&zx, &ts)?)
    };
    let y = g.map(lift).transpose()?;
    let r = flint(run(&lift(f)?, y.as_ref()))?;
    let ts = terms(&r).into_iter().map(|(c, e)| Ok((Elem::from_integer(&b, &c.to_integer()?)?, e))).collect::<RResult<Vec<_>>>()?;
    Ok(Elem::mpoly_from_terms(f.ctx(), &ts)?)
}

fn resultant(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = same_ring(a)?;
    let i = var_arg(a, 2, &f, "variable number")?;
    one(like(&f, res_disc(&f.x, Some(&g.x), i)?))
}

fn discriminant(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let i = var_arg(a, 1, &f, "variable number")?;
    one(like(&f, res_disc(&f.x, None, i)?))
}

// ----- polynomials over the integers ---------------------------------------------------------

/// The coefficients of `f`, which must be over the integers.
fn int_coeffs(f: &Elt) -> RResult<Vec<Integer>> {
    if !is_integers(f) {
        return Err(not_available());
    }
    terms(&f.x).into_iter().map(|(c, _)| Ok(c.to_integer()?)).collect()
}

/// The sign of the leading coefficient of `f` over Z.
fn lead_sign(f: &Elt) -> RResult<i32> {
    int_coeffs(f)?;
    Ok(leading(f.ring(), &f.x).map_or(0, |(c, _)| c.to_integer().map_or(0, |c| c.sign())))
}

fn sign(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_i64(lead_sign(&mpol(a, 0))? as i64))
}

fn abs(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    one(like(&f, if lead_sign(&f)? < 0 { f.x.neg()? } else { f.x.clone() }))
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
            let c = match &self.coeff {
                Some(g) => it.apply_map(g, &c)?,
                None => c,
            };
            it.coerce(&m.codomain, &c)
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
/// coefficients (from the coefficient ring into a ring that coerces into S).
/// Sequences among the images are flattened. `None` if P is not a polynomial
/// ring.
pub fn polynomial_hom(it: &mut Interp, domain: &Value, codomain: &Value, images: &[Value]) -> RResult<Option<Value>> {
    let Some((_, r)) = ring_of(domain).filter(|(_, r)| matches!(r.kind, RingKind::UPoly { .. } | RingKind::MPoly { .. })) else { return Ok(None) };
    let (n, univariate) = (r.ngens(), matches!(r.kind, RingKind::UPoly { .. }));
    let err = |s: String| RuntimeError::runtime(s).in_context("hom< ... >");
    let mut items = Vec::with_capacity(images.len());
    for v in images {
        match v {
            Value::Seq(s) => items.extend(s.elems.iter().cloned()),
            v => items.push(v.clone()),
        }
    }
    if univariate && !(1..=2).contains(&items.len()) {
        return Err(err("Wrong number of arguments to polynomial homomorphism element constructor (should be 1 or 2)".into()));
    }
    if items.is_empty() {
        return Err(err("No images given".into()));
    }
    let (coeff, ys) = match &items[..] {
        [Value::Map(g), ys @ ..] => (Some(g.clone()), ys),
        [_, _] if univariate => return Err(err("Illegal coefficient map".into())),
        ys => (None, ys),
    };
    if let Some(g) = &coeff {
        let base = r.base().expect("a polynomial ring").clone();
        if !it.auto_coerces(&base, &g.domain) || !it.auto_coerces(&g.codomain, codomain) {
            return Err(err("Illegal coefficient map".into()));
        }
    }
    // The univariate constructor and the multivariate one word their errors
    // differently; a multivariate image that does not coerce counts as a
    // wrong arity.
    let arity = || err(format!("RHS has arity {} but should have length {n}", ys.len()));
    if ys.len() != n {
        return Err(arity());
    }
    let mut out = Vec::with_capacity(n);
    for y in ys {
        match it.coerce(codomain, y) {
            Ok(y) => out.push(y),
            Err(_) if univariate => return Err(err("Element is not in the codomain of the map".into())),
            Err(_) => return Err(arity()),
        }
    }
    let h = PolyHom { coeff, images: out };
    Ok(Some(Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain: domain.clone(), codomain: codomain.clone(), imp: MapImpl::Native(Rc::new(h)) }))))
}

/// `ChangeRing(P, S)`: the polynomial ring over S with the rank, order and
/// names of P (unlike the univariate one, without a map).
fn change_ring(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, r) = ring_arg(a, 0);
    let RingKind::MPoly { rank, order, grading, .. } = &r.kind else { unreachable!("a multivariate polynomial ring") };
    let q = it.mpoly_ring(&a.args[1], *rank, order.clone(), grading.clone(), false)?;
    if let Some((_, qr)) = ring_of(&q) {
        *qr.names.borrow_mut() = r.names.borrow().clone();
    }
    if let Some(StructKind::MPolIdeal(id)) = a.args[0].as_struct() {
        return one(super::poly_ideals::change_ring(it, id, &q)?);
    }
    one(q)
}

pub fn register(it: &mut Interp) {
    for name in ["PolynomialRing", "PolynomialAlgebra"] {
        it.def_params(name, "R::Rng, n::RngIntElt -> RngMPol", &[("Global", Value::Bool(false))], "The polynomial ring in n variables over R (the global one with Global).", polynomial_ring);
        it.def(name, "R::Rng, n::RngIntElt, order::MonStgElt, ... -> RngMPol", "The polynomial ring in n variables over R with the named monomial order (and its arguments).", polynomial_ring);
        it.def(name, "R::Rng, n::RngIntElt, T::Tup -> RngMPol", "The polynomial ring in n variables over R with the monomial order <name, arguments> of T.", polynomial_ring);
        it.def(name, "R::Rng, Q::[RngIntElt] -> RngMPol", "The graded polynomial ring over R whose variables have the weights Q.", graded_polynomial_ring);
    }
    it.def("MonomialOrder", "P::RngMPol -> Tup", "The name of the monomial order of P and its arguments.", monomial_order);
    it.def("MonomialOrderWeightVectors", "P::RngMPol -> [[FldRatElt]]", "The weight vectors of the monomial order of P.", monomial_order_weight_vectors);
    for name in ["Grading", "VariableWeights"] {
        it.def(name, "P::RngMPol -> [RngIntElt]", "The weights of the variables of P.", grading);
    }
    it.def("Identity", "P::RngMPol -> RngMPolElt", "The identity of P.", identity);
    it.def("ChangeRing", "P::RngMPol, S::Rng -> RngMPol", "The polynomial ring over S with the rank, order and names of P.", change_ring);
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
    it.def("JacobianMatrix", "S::[RngMPolElt] -> Mtrx", "The matrix of the partial derivatives of the polynomials of S (rows) by the variables (columns).", jacobian_matrix);
    let doc = "The symmetric matrix B with f = v B v^T for f of total degree 2, v the variables (and 1 after them unless f is homogeneous).";
    it.def("SymmetricBilinearForm", "f::RngMPolElt -> ModMatRngElt", doc, symmetric_bilinear_form);
    let doc = "The diagonal form of f of total degree 2 over a field, and the matrix T with T B T^t diagonal for the symmetric bilinear form B of f.";
    it.def("DiagonalForm", "f::RngMPolElt -> RngMPolElt, ModMatRngElt", doc, diagonal_form);
    // Elements of affine algebras are their normal forms, whose terms these
    // functions see.
    it.def("Coefficients", "f::RngMPolResElt -> [RngElt]", "The coefficients of the terms of the normal form of f, largest first.", coefficients);
    it.def("LeadingCoefficient", "f::RngMPolResElt -> RngElt", "The coefficient of the leading term of the normal form of f.", leading_coefficient);
    it.def("Length", "f::RngMPolResElt -> RngIntElt", "The number of terms of the normal form of f.", length);
    it.def("Monomials", "f::RngMPolResElt -> [RngMPolResElt]", "The monomials of the normal form of f, largest first.", monomials);
    it.def("LeadingMonomial", "f::RngMPolResElt -> RngMPolResElt", "The monomial of the leading term of the normal form of f.", leading_monomial);
    it.def("Terms", "f::RngMPolResElt -> [RngMPolResElt]", "The terms of the normal form of f, largest first.", terms_of);
    it.def("LeadingTerm", "f::RngMPolResElt -> RngMPolResElt", "The leading term of the normal form of f.", leading_term);
    it.def("TotalDegree", "f::RngMPolResElt -> RngIntElt", "The largest total degree of a monomial of the normal form of f (-1 for zero).", total_degree);
    it.def("Degree", "f::RngMPolResElt -> RngIntElt", "The largest weighted degree of a term of the normal form of f.", weighted_degree);
    it.def("Degree", "f::RngMPolResElt, i::RngIntElt -> RngIntElt", "The degree of the normal form of f in the i-th variable (-1 for zero).", degree);
    it.def("Evaluate", "f::RngMPolResElt, s::[RngElt] -> RngElt", "The value of the normal form of f at the sequence s.", evaluate);
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
    for name in ["Degree", "WeightedDegree"] {
        it.def(name, "f::RngMPolElt -> RngIntElt", "The largest weighted degree of a term of f (0 for zero).", weighted_degree);
    }
    it.def("LeadingWeightedDegree", "f::RngMPolElt -> RngIntElt", "The weighted degree of the leading term of f (-1 for zero).", leading_weighted_degree);
    it.def("IsHomogeneous", "f::RngMPolElt -> BoolElt", "Whether the terms of f have one weighted degree.", is_homogeneous);
    it.def("HomogeneousComponent", "f::RngMPolElt, d::RngIntElt -> RngMPolElt", "The terms of f of weighted degree d.", homogeneous_component);
    it.def("HomogeneousComponents", "f::RngMPolElt -> [RngMPolElt]", "The homogeneous components of f, of weighted degrees 0 up to that of f.", homogeneous_components);
    it.def("MonomialsOfDegree", "P::RngMPol, d::RngIntElt -> SetIndx", "The monomials of P of total degree d.", monomials_of_degree);
    it.def("MonomialsOfWeightedDegree", "P::RngMPol, d::RngIntElt -> SetIndx", "The monomials of P of weighted degree d in its variables of positive weight.", monomials_of_weighted_degree);
    it.def("IsUnivariate", "f::RngMPolElt -> BoolElt, RngUPolElt, RngIntElt", "Whether f is a polynomial in one variable, with its univariate version and the variable's number.", is_univariate);
    it.def("UnivariatePolynomial", "f::RngMPolElt -> RngUPolElt, RngIntElt", "f, a polynomial in one variable, as a univariate polynomial, and the number of that variable.", univariate_polynomial);
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
