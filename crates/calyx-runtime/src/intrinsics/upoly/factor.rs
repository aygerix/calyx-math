//! Factorization of univariate polynomials, resultants and discriminants,
//! and Hensel lifting.

use std::cmp::Ordering;

use calyx_flint::Integer;
use calyx_flint::gr::{Ctx, Elem, Truth};
use calyx_flint::upoly as fu;
use calyx_syntax::ast::BinOp;

use super::{base_of, bctx, cval, is_integers, len, like, nonzero, not_available, pair, pol, poly_seq, ring_arg};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::{bare, boolv, one};
use crate::rings::props::ring_props;
use crate::rings::{Elt, RingKind, make_elt, ring_of};
use crate::value::*;

// ----- factorization -------------------------------------------------------------------


fn can_factor(f: &Elt) -> RResult<()> {
    if fu::can_factor(f.x.ctx()) { Ok(()) } else { Err(not_available()) }
}

/// Whether polynomials over the ring `r` factor: over the integers, the
/// rationals, finite fields, prime residue rings, and (as Magma has it)
/// polynomial rings over these.
fn has_factorization(r: &Value) -> bool {
    let Value::Struct(s) = r else { return false };
    match &s.kind {
        StructKind::Integers | StructKind::Rationals => true,
        StructKind::Ring(ring) => match &ring.kind {
            RingKind::Finite(_) => true,
            RingKind::Residue(m) => m.is_prime(),
            RingKind::UPoly { base, .. } | RingKind::MPoly { base, .. } => has_factorization(base),
            RingKind::Complex(_) | RingKind::UPolyRes { .. } | RingKind::MPolyRes { .. } => false,
        },
        _ => false,
    }
}

/// Constant polynomials `<p, e>` for the prime powers of an integer.
fn prime_factors(f: &Elt, c: &Integer) -> RResult<Vec<(Elem, u64)>> {
    let zz = bctx(f);
    if c.is_zero() {
        return Ok(Vec::new());
    }
    crate::intrinsics::factseq::factor(&c.abs()).iter().map(|(p, e)| Ok((Elem::poly_from_coeffs(f.x.ctx(), &[Elem::from_integer(&zz, p)?])?, *e))).collect()
}

/// A factorization sequence `[<q, k>, ...]` of polynomials in the ring of
/// `f`, in Magma's order: by multiplicity first if `by_mult`, then by
/// degree and coefficients from the top.
fn factorization_seq(it: &mut Interp, f: &Elt, mut v: Vec<(Elem, u64)>, by_mult: bool) -> Value {
    let ring = f.ring_rc();
    v.sort_by(|a, b| {
        let m = if by_mult { a.1.cmp(&b.1) } else { Ordering::Equal };
        m.then_with(|| it.ring_elt_cmp(&ring, &a.0, &b.0).ok().flatten().unwrap_or(Ordering::Equal))
    });
    Value::seq(None, v.into_iter().map(|(q, k)| Value::tuple(vec![like(f, q), Value::int(k as i64)])).collect())
}

/// The factorization into irreducibles, normalized as `Normalize` does,
/// and the unit: over the integers the prime factors of the content come
/// first as constant factors and the unit is the sign.
pub(super) fn factorization(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    nonzero(&f)?;
    can_factor(&f)?;
    let fac = fu::factor(&f.x)?;
    let mut v = fac.factors;
    let unit = if is_integers(&f) {
        let c = fac.unit.to_integer()?;
        v.extend(prime_factors(&f, &c)?);
        Value::int(if c.sign() < 0 { -1 } else { 1 })
    } else {
        cval(it, &f, fac.unit)
    };
    let seq = factorization_seq(it, &f, v, false);
    if a.nresults >= 2 { Ok(vals![seq, unit]) } else { one(seq) }
}

pub(super) fn is_irreducible(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    nonzero(&f)?;
    can_factor(&f)?;
    boolv(fu::is_irreducible(&f.x)?)
}

/// The squarefree factorization, by increasing multiplicity; over the
/// integers the content contributes its prime powers `<p, e>`.
pub(super) fn squarefree_factorization(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    nonzero(&f)?;
    can_factor(&f)?;
    let fac = fu::factor_squarefree(&f.x)?;
    let mut v = fac.factors;
    if is_integers(&f) {
        v.extend(prime_factors(&f, &fac.unit.to_integer()?)?);
    }
    one(factorization_seq(it, &f, v, true))
}

/// Whether `f` (of positive degree, over a field) has no repeated factor.
fn squarefree(f: &Elem) -> RResult<bool> {
    Ok(fu::gcd(f, &f.poly_derivative()?)?.poly_len() == 1)
}

/// The products of the irreducible factors of each degree: all of them in
/// Magma's order of the products, or those up to degree `Degree` by
/// increasing degree.
pub(super) fn distinct_degree_factorization(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let limit = match a.param("Degree") {
        Some(Value::Int(n)) => n.clone(),
        _ => Integer::zero(),
    };
    if limit.sign() < 0 {
        return Err(RuntimeError::runtime("Degree should be greater than or equal to 0"));
    }
    if !fu::over_finite_field(f.x.ctx()) {
        return Err(RuntimeError::runtime("Coefficient ring of argument 1 is not a finite field"));
    }
    nonzero(&f)?;
    if len(&f) > 1 && !squarefree(&f.x)? {
        return Err(RuntimeError::runtime("Argument 1 is not squarefree"));
    }
    let mut v = fu::distinct_degree(&f.x)?;
    if limit.is_zero() {
        let ring = f.ring_rc();
        v.sort_by(|a, b| it.ring_elt_cmp(&ring, &a.1, &b.1).ok().flatten().unwrap_or(Ordering::Equal));
    } else {
        v.retain(|(d, _)| Integer::from_i64(*d as i64) <= limit);
    }
    one(Value::seq(None, v.into_iter().map(|(d, g)| Value::tuple(vec![Value::int(d as i64), like(&f, g)])).collect()))
}

/// The irreducible factors of `f`, which should be a product of distinct
/// irreducibles of degree `d` (with `g = x^q mod f`); the factors are found
/// by factoring `f`, so other input gives its irreducible factors.
pub(super) fn equal_degree_factorization(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    if !fu::over_finite_field(f.x.ctx()) {
        return Err(RuntimeError::runtime("Coefficient ring of argument 1 is not a finite field"));
    }
    nonzero(&f)?;
    let ring = f.ring_rc();
    let mut v: Vec<Elem> = fu::factor(&f.x)?.factors.into_iter().map(|(q, _)| q).collect();
    v.sort_by(|a, b| it.ring_elt_cmp(&ring, a, b).ok().flatten().unwrap_or(Ordering::Equal));
    one(poly_seq(&f, v))
}

pub(super) fn is_separable(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    if !fu::can_factor(f.x.ctx()) || !fu::over_field(f.x.ctx()) {
        return Err(RuntimeError::runtime("Coefficient ring of argument 1 must be a field with factorization"));
    }
    if len(&f) < 2 {
        return Err(RuntimeError::runtime("Degree must be >= 1"));
    }
    boolv(squarefree(&f.x)?)
}

pub(super) fn has_polynomial_factorization(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(has_factorization(&a.args[0]))
}

/// The product of a factorization sequence of polynomials.
pub(super) fn facpol(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let q = a.seq(0)?.clone();
    let bad = || bare(RuntimeError::runtime("Not the factorisation sequence of a polynomial"));
    let mut prod: Option<Value> = None;
    for t in &q.elems {
        let Value::Tuple(t) = t else { return Err(bad()) };
        let [g @ Value::Elt(e), k @ Value::Int(_)] = &t.elems[..] else { return Err(bad()) };
        if !matches!(e.ring().kind, RingKind::UPoly { .. } | RingKind::MPoly { .. }) {
            return Err(bad());
        }
        let p = it.binop(BinOp::Pow, g.clone(), k.clone())?;
        prod = Some(match prod {
            Some(x) => it.binop(BinOp::Mul, x, p)?,
            None => p,
        });
    }
    match prod {
        Some(p) => one(p),
        None => Err(bare(RuntimeError::runtime("Illegal null sequence"))),
    }
}

// ----- resultants and discriminants --------------------------------------------------------

pub(super) fn resultant(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = pair(it, a)?;
    one(cval(it, &f, fu::resultant(&f.x, &g)?))
}

pub(super) fn discriminant(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    if len(&f) < 2 {
        return Err(RuntimeError::runtime("Degree of argument is less than 1"));
    }
    one(cval(it, &f, fu::discriminant(&f.x)?))
}

// ----- Hensel lifting ------------------------------------------------------------------

/// Lift the factorization of the integer polynomial `f` modulo a prime `p`
/// (monic squarefree factors `s`, whose product is `f / lc(f)`) to monic
/// factors modulo the modulus `p^k` of the coefficient ring of `P`.
pub(super) fn hensel_lift(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    if !is_integers(&f) {
        return Err(RuntimeError::runtime("Argument 1 not a polynomial over Z"));
    }
    let s = a.seq(1)?.clone();
    let (pst, pr) = ring_arg(a, 2);
    let modulus = match pr.base().and_then(ring_of) {
        Some((_, r)) => match &r.kind {
            RingKind::Residue(m) => m.clone(),
            _ => return Err(RuntimeError::runtime("Argument 3 not a polynomial algebra over Zm")),
        },
        None => return Err(RuntimeError::runtime("Argument 3 not a polynomial algebra over Zm")),
    };
    let not_seq = || RuntimeError::runtime("Given sequence is not a factorization sequence");
    let Some(first) = s.elems.first() else { return Err(RuntimeError::runtime("Sequence argument 2 must be non-empty")) };
    let Value::Elt(s1) = first else { return Err(not_seq()) };
    let p = ring_props(&base_of(s1)).map(|pp| pp.characteristic).unwrap_or_default();
    // The modulus must be a power p^k of the characteristic of the factors.
    let (k, m) = if p > Integer::one() { modulus.remove(&p) } else { (0, modulus.clone()) };
    if k == 0 || !m.is_one() {
        return Err(RuntimeError::runtime("Invalid modulus of coefficient ring of argument 3"));
    }
    let pctx = s1.x.ctx().clone();
    let mut factors = Vec::with_capacity(s.elems.len());
    for (i, v) in s.elems.iter().enumerate() {
        let Value::Elt(e) = v else { return Err(not_seq()) };
        if len(e) == 0 || fu::lead(&e.x).is_one() != Truth::True {
            return Err(RuntimeError::runtime(format!("element {} of argument 2 is not monic", i + 1)));
        }
        factors.push(if e.ring().id == s1.ring().id { e.x.clone() } else { fu::convert(&pctx, &e.x).map_err(|_| not_seq())? });
    }
    // f made monic modulo p^k, with its coefficients in [0, p^k).
    let pk = pst.clone();
    let fk = fu::convert(&pr.ctx, &f.x)?;
    let fk = fk.poly_mul_scalar(&fu::lead(&fk).inv().map_err(|_| not_seq())?)?;
    let zx = f.x.ctx().clone();
    let zz = Ctx::integers();
    let lift = |e: &Elem| -> RResult<Elem> {
        let cs: Vec<Elem> = (0..e.poly_len()).map(|i| Elem::from_integer(&zz, &e.poly_coeff(i).to_integer()?)).collect::<Result<_, _>>()?;
        Ok(Elem::poly_from_coeffs(&zx, &cs)?)
    };
    let fz = lift(&fk)?;
    // The factors must multiply to f modulo p and be coprime.
    let mut prod = Elem::one(&pctx)?;
    for g in &factors {
        prod = prod.mul(g)?;
    }
    let fp = fu::convert(&pctx, &fz)?;
    if prod.equal(&fp) != Truth::True || !squarefree(&fp)? {
        return Err(not_seq());
    }
    let lifted = if k == 1 { factors.clone() } else { fu::hensel_lift(&fz, &factors, k).map_err(|_| not_seq())? };
    let out: Vec<Value> = lifted.iter().map(|g| Ok(make_elt(&pk, fu::convert(&pr.ctx, g)?))).collect::<RResult<_>>()?;
    one(Value::seq(Some(Value::Struct(pst)), out))
}
