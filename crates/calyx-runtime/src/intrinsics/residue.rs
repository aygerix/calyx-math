//! The functions of residue class rings `Z/mZ` and their elements: square
//! roots, linear congruences, gcds and lcms, normalisation, primitivity and
//! the factored modulus. Dirichlet characters are in `dirichlet`.

pub mod dirichlet;

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::Elem;

use super::factseq::{fact_int, fact_of, fact_value, pairs_of};
use super::numtheory::{all_sqrts_factored, is_square_mod_factored, linear_congruence, modp, modsqrt_factored};
use super::{boolv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::rings::ideals::res_ideal_parts;
use crate::rings::{Ring, RingKind, gr_error, make_elt, ring_of};
use crate::value::*;

/// An element of a residue class ring: the ring, its modulus and the
/// representative in `[0, m)`.
pub(super) struct Res {
    pub st: Rc<Struct>,
    pub ring: Rc<Ring>,
    pub m: Integer,
    pub x: Integer,
}

impl Res {
    pub fn of(v: &Value) -> Option<Res> {
        let (st, x) = match v {
            Value::Small(r, x) => (r.parent(), Integer::from_u64(*x)),
            Value::Elt(e) => (e.parent.clone(), e.residue()?),
            _ => return None,
        };
        let StructKind::Ring(ring) = &st.kind else { return None };
        let RingKind::Residue(m) = &ring.kind else { return None };
        let (ring, m) = (ring.clone(), m.clone());
        Some(Res { st, ring, m, x })
    }

    /// The element of the same ring with representative `x mod m`.
    fn elt(&self, x: &Integer) -> RResult<Value> {
        residue_value(&self.st, &self.ring, x)
    }
}

fn bad() -> RuntimeError {
    RuntimeError::runtime("Bad argument types")
}

fn res_arg(a: &CallArgs, i: usize) -> RResult<Res> {
    Res::of(&a.args[i]).ok_or_else(bad)
}

/// Two elements of the same residue class ring.
fn res_pair(a: &CallArgs) -> RResult<(Res, Res)> {
    let (x, y) = (res_arg(a, 0)?, res_arg(a, 1)?);
    if x.ring.id != y.ring.id {
        return Err(RuntimeError::runtime("Arguments are not compatible\nArgument types given: RngIntResElt, RngIntResElt"));
    }
    Ok((x, y))
}

/// The element `x mod m` of the residue class ring `R = Z/mZ`.
pub fn residue_value(st: &Rc<Struct>, ring: &Ring, x: &Integer) -> RResult<Value> {
    if let Some(s) = ring.small {
        return Ok(Value::Small(s, s.modulus().reduce_integer(x)));
    }
    Ok(make_elt(st, Elem::from_integer(&ring.ctx, x).map_err(|e| gr_error(e, "Arithmetic error"))?))
}

/// The extended Euclidean algorithm as in the textbook, on `a, b ≥ 0`:
/// `(g, s)` with `s a = g (mod b)`. Magma's `Normalize` and `div` depend on
/// the exact cofactor this produces.
pub fn classic_xgcd(a: &Integer, b: &Integer) -> (Integer, Integer) {
    let (mut r0, mut r1) = (a.clone(), b.clone());
    let (mut s0, mut s1) = (Integer::one(), Integer::zero());
    while !r1.is_zero() {
        let (q, r) = r0.fdiv_qr(&r1).unwrap();
        (r0, r1) = (r1, r);
        let s = &s0 - &(&q * &s1);
        (s0, s1) = (s1, s);
    }
    (r0, s0)
}

/// `x div y` in `Z/mZ` as Magma computes it: with `s y = g (mod m)` from
/// `classic_xgcd(y, m)`, the quotient is `floor(x / g) * s`. For a unit `y`
/// this is `x / y`. `None` when `y` is zero.
pub fn residue_div(x: &Integer, y: &Integer, m: &Integer) -> Option<Integer> {
    if y.is_zero() {
        return None;
    }
    let (g, s) = classic_xgcd(y, m);
    Some(modp(&(&x.fdiv_qr(&g).unwrap().0 * &s), m))
}

/// The factorization of the modulus: the `Factorization` parameter when it
/// stands for the modulus, and otherwise the ring's own.
fn modulus_factors(it: &mut Interp, a: &CallArgs, r: &Res) -> Rc<[(Integer, u64)]> {
    if let Some(pairs) = a.param("Factorization").and_then(pairs_of) {
        let f: Vec<(Integer, u64)> = pairs.into_iter().filter_map(|(p, k)| Some((p, k.to_u64().filter(|&k| k > 0)?))).collect();
        if !f.is_empty() && fact_int(&f) == r.m {
            return f.into();
        }
    }
    r.ring.modulus_factors_by(|m| it.factor_int(m)).expect("a residue class ring")
}

fn is_square(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let r = res_arg(a, 0)?;
    let f = modulus_factors(it, a, &r);
    if !is_square_mod_factored(&r.x, &f) {
        return Ok(vals![Value::Bool(false), Value::Undef]);
    }
    match modsqrt_factored(&r.x, &f) {
        Some(s) => Ok(vals![Value::Bool(true), r.elt(&s)?]),
        None => Ok(vals![Value::Bool(false), Value::Undef]),
    }
}

fn sqrt(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let r = res_arg(a, 0)?;
    let f = modulus_factors(it, a, &r);
    match modsqrt_factored(&r.x, &f) {
        Some(s) => one(r.elt(&s)?),
        None => Err(RuntimeError::runtime("Argument has no square root")),
    }
}

fn all_square_roots(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let r = res_arg(a, 0)?;
    let f = modulus_factors(it, a, &r);
    let roots = all_sqrts_factored(&r.x, &f, 1 << 26).ok_or_else(|| RuntimeError::runtime("Too many square roots"))?;
    let elems = roots.iter().map(|x| r.elt(x)).collect::<RResult<Vec<_>>>()?;
    one(Value::seq(Some(Value::Struct(r.st.clone())), elems))
}

/// The least `x` with `a x = b`.
fn solution(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (x, y) = res_pair(a)?;
    match linear_congruence(&x.x, &y.x, &x.m) {
        Some((s, _)) => one(x.elt(&s)?),
        None => Err(RuntimeError::runtime("No solution to linear congruence")),
    }
}

/// The elements of a sequence argument, all in the ring of its universe
/// (which is the ring for an empty sequence).
fn res_seq(a: &CallArgs) -> RResult<(Rc<Struct>, Rc<Ring>, Integer, Vec<Integer>)> {
    let s = a.seq(0)?;
    let Some(Value::Struct(st)) = &s.universe else { return Err(bad()) };
    let StructKind::Ring(ring) = &st.kind else { return Err(bad()) };
    let RingKind::Residue(m) = &ring.kind else { return Err(bad()) };
    let mut xs = Vec::with_capacity(s.elems.len());
    for e in &s.elems {
        let r = Res::of(e).filter(|r| r.ring.id == ring.id).ok_or_else(bad)?;
        xs.push(r.x);
    }
    Ok((st.clone(), ring.clone(), m.clone(), xs))
}

/// A generator of the ideal `(a) + (b)`: `gcd(a, b, m)`.
fn gcd(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (x, y) = res_pair(a)?;
    one(x.elt(&x.x.gcd(&y.x).gcd(&x.m))?)
}

fn gcd_seq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, ring, m, xs) = res_seq(a)?;
    let g = xs.iter().fold(m.clone(), |g, x| g.gcd(x));
    one(residue_value(&st, &ring, &g)?)
}

/// A generator of the ideal `(a) ∩ (b)`: `lcm(gcd(a, m), gcd(b, m))`.
fn lcm(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (x, y) = res_pair(a)?;
    one(x.elt(&x.x.gcd(&x.m).lcm(&y.x.gcd(&x.m)))?)
}

fn lcm_seq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, ring, m, xs) = res_seq(a)?;
    let l = xs.iter().fold(Integer::one(), |l, x| l.lcm(&x.gcd(&m)));
    one(residue_value(&st, &ring, &l)?)
}

/// Euler's totient from a factorization.
fn phi(f: &[(Integer, u64)]) -> Integer {
    f.iter().fold(Integer::one(), |acc, (p, k)| &(&acc * &p.pow(k - 1)) * &(p - 1))
}

/// Whether `n` generates the unit group.
fn is_primitive(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let r = res_arg(a, 0)?;
    let order = super::ints::modorder(&r.x, &r.m);
    boolv(!order.is_zero() && order == phi(&r.ring.modulus_factors_by(|m| it.factor_int(m)).unwrap()))
}

/// The canonical associate `y = gcd(x, m)` (0 for x = 0) of `x`, and a
/// unit `u` with `u x = y`: the cofactor of the extended Euclidean
/// algorithm when it is a unit, and otherwise the least unit congruent to
/// it modulo `m / y`.
fn normalize(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let r = res_arg(a, 0)?;
    let (g, s) = classic_xgcd(&r.x, &r.m);
    let mut u = modp(&s, &r.m);
    if !u.gcd(&r.m).is_one() {
        let step = r.m.divexact(&g);
        u = modp(&s, &step);
        while !u.gcd(&r.m).is_one() {
            u = &u + &step;
        }
    }
    let y = if r.x.is_zero() { Integer::zero() } else { g };
    Ok(vals![r.elt(&y)?, r.elt(&u)?])
}

/// Whether `n` is not a zero divisor (a unit, in `Z/mZ`).
fn is_regular(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let r = res_arg(a, 0)?;
    boolv(r.x.gcd(&r.m).is_one())
}

fn factored_modulus(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, ring) = ring_of(&a.args[0]).ok_or_else(bad)?;
    let f = ring.modulus_factors_by(|m| it.factor_int(m)).ok_or_else(bad)?;
    one(fact_value(&f))
}

/// `Z/mZ` for the integer `m` a factorization sequence stands for, which
/// the ring keeps.
fn residue_ring_fact(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let mut f = fact_of(&a.args[0])?;
    f.retain(|(_, k)| *k > 0);
    f.sort_by(|x, y| x.0.cmp(&y.0));
    let mut merged: Vec<(Integer, u64)> = Vec::with_capacity(f.len());
    for (p, k) in f {
        match merged.last_mut() {
            Some((q, e)) if *q == p => *e += k,
            _ => merged.push((p, k)),
        }
    }
    let r = it.residue_ring(&fact_int(&merged));
    if let Some((_, ring)) = ring_of(&r) {
        let _ = ring.factored.set(merged.into());
    }
    one(r)
}

/// The generator `d` of the ideal `dR` (1 for `R` itself, 0 for the zero
/// ideal).
fn ideal_generator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (r, d) = res_ideal_parts(&a.args[0]).ok_or_else(bad)?;
    let StructKind::Ring(ring) = &r.kind else { unreachable!() };
    one(residue_value(&r, ring, &d)?)
}

fn ideal_is_principal(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    boolv(true)
}

fn identity(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, ring) = ring_of(&a.args[0]).ok_or_else(bad)?;
    one(residue_value(st, ring, &Integer::one())?)
}

pub fn register(it: &mut Interp) {
    const E: &str = "RngIntResElt";
    let fact = || [("Factorization", Value::seq(None, Vec::new()))];
    it.def_params("IsSquare", &format!("x::{E} -> BoolElt, {E}"), &fact(), "Whether x is a square, and a square root.", is_square);
    for name in ["Sqrt", "SquareRoot"] {
        it.def_params(name, &format!("x::{E} -> {E}"), &fact(), "A square root of x (the one Magma chooses).", sqrt);
    }
    for name in ["AllSquareRoots", "AllSqrts"] {
        it.def_params(name, &format!("x::{E} -> [{E}]"), &fact(), "All square roots of x, in increasing order.", all_square_roots);
    }
    it.def("Solution", &format!("a::{E}, b::{E} -> {E}"), "The least solution x of a x = b.", solution);
    for name in ["Gcd", "GCD", "GreatestCommonDivisor"] {
        it.def(name, &format!("a::{E}, b::{E} -> {E}"), "A generator of the ideal (a) + (b).", gcd);
        it.def(name, &format!("Q::[{E}] -> {E}"), "A generator of the ideal generated by the elements of Q.", gcd_seq);
    }
    for name in ["Lcm", "LCM", "LeastCommonMultiple"] {
        it.def(name, &format!("a::{E}, b::{E} -> {E}"), "A generator of the ideal (a) meet (b).", lcm);
        it.def(name, &format!("Q::[{E}] -> {E}"), "A generator of the intersection of the ideals generated by the elements of Q.", lcm_seq);
    }
    it.def("IsPrimitive", &format!("x::{E} -> BoolElt"), "Whether x generates the unit group.", is_primitive);
    for name in ["Normalize", "Normalise"] {
        it.def(name, &format!("x::{E} -> {E}, {E}"), "The canonical associate y of x and a unit u with u x = y.", normalize);
    }
    it.def("IsRegular", &format!("x::{E} -> BoolElt"), "Whether x is not a zero divisor.", is_regular);
    it.def("FactoredModulus", "R::RngIntRes -> RngIntEltFact", "The factorization of the modulus of R.", factored_modulus);
    for name in ["Integers", "IntegerRing", "ResidueClassRing"] {
        it.def(name, "Q::RngIntEltFact -> RngIntRes", "The ring of integers modulo the integer Q stands for.", residue_ring_fact);
    }
    it.def("Identity", "R::RngIntRes -> RngIntResElt", "The identity 1 of R.", identity);
    it.def("Generator", "I::RngIntRes -> RngIntResElt", "The generator of the ideal I of a residue class ring.", ideal_generator);
    it.def("IsPrincipal", "I::RngIntRes -> BoolElt", "True: ideals of residue class rings are principal.", ideal_is_principal);
    dirichlet::register(it);
}
