//! Special families of polynomials: orthogonal polynomials, Dickson,
//! Bernoulli and Swinnerton-Dyer polynomials.

use std::rc::Rc;

use calyx_flint::gr::{Ctx, Elem, GrResult};
use calyx_flint::upoly as fu;

use super::is_field;
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::{arg_ge, bare, one};
use crate::rings::{make_elt, ring_of};
use crate::value::*;

/// Argument 1 of the families: one of Magma's small non-negative integers.
fn family_index(a: &CallArgs) -> RResult<u64> {
    let n = a.int(0)?;
    match n.to_u64() {
        Some(k) if k < 1 << 30 => Ok(k),
        _ => Err(RuntimeError::runtime(format!("Argument 1 ({n}) is not small and non-negative"))),
    }
}

/// A polynomial of a family computed by FLINT, in the global polynomial
/// ring over `base` (the integers or the rationals).
fn family_poly(it: &mut Interp, base: Value, fam: fu::Family, n: Option<u64>) -> RResult<Vals> {
    let px = it.poly_ring(&base, true)?;
    let Some((st, r)) = ring_of(&px) else { unreachable!() };
    let f = match n {
        Some(n) => fu::family(&r.ctx, fam, n),
        None => Elem::zero(&r.ctx),
    };
    one(make_elt(st, f))
}

pub(super) fn chebyshev_t(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = family_index(a)?;
    family_poly(it, Value::integers(), fu::Family::ChebyshevT, Some(n))
}

/// Magma's `ChebyshevU(n)` is `U_(n-1)`, of degree `n - 1` (0 for n = 0).
pub(super) fn chebyshev_u(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = family_index(a)?;
    family_poly(it, Value::integers(), fu::Family::ChebyshevU, n.checked_sub(1))
}

pub(super) fn legendre_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = family_index(a)?;
    family_poly(it, Value::rationals(), fu::Family::Legendre, Some(n))
}

pub(super) fn hermite_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = family_index(a)?;
    family_poly(it, Value::integers(), fu::Family::Hermite, Some(n))
}

pub(super) fn bernoulli_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?;
    if n.sign() < 0 {
        return Err(RuntimeError::runtime(format!("Argument 1 ({n}) should be non-negative")));
    }
    let n = n.to_u64().filter(|&k| k < 1 << 30).ok_or_else(|| RuntimeError::runtime(format!("Argument 1 ({n}) is too large")))?;
    family_poly(it, Value::rationals(), fu::Family::Bernoulli, Some(n))
}

/// The polynomials of a family with parameter `m` are computed over the
/// parent of `m` (its field of fractions if `field`): the global polynomial
/// ring there, its context, and `m` as a coefficient.
fn param_ring(it: &mut Interp, m: &Value, field: bool) -> RResult<(Rc<Struct>, Rc<Ctx>, Elem)> {
    let mut k = it.parent_of(m)?;
    if field && !is_field(&k) {
        if !matches!(k.as_struct(), Some(StructKind::Integers)) {
            return Err(RuntimeError::runtime("Ring does not have a determinable field of fractions"));
        }
        k = Value::rationals();
    }
    let px = it.poly_ring(&k, true)?;
    let Some((st, r)) = ring_of(&px) else { unreachable!() };
    let (st, pctx) = (st.clone(), r.ctx.clone());
    let me = it.to_structure_elem(&k, m, false)?.ok_or_else(|| RuntimeError::runtime("Bad argument types"))?;
    Ok((st, pctx, me))
}

/// The three-term recurrence `f_n = (s_n x + t_n) f_(n-1) + u_n f_(n-2)`
/// in `pctx` from `f_0` and `f_1`, where `coeffs(n)` gives `(s_n, t_n, u_n)`.
fn recurrence(pctx: &Rc<Ctx>, n: u64, f0: Elem, f1: Elem, mut coeffs: impl FnMut(u64) -> GrResult<(Elem, Elem, Elem)>) -> GrResult<Elem> {
    if n == 0 {
        return Ok(f0);
    }
    let (mut a, mut b) = (f0, f1);
    for k in 2..=n {
        let (s, t, u) = coeffs(k)?;
        let lin = Elem::poly_from_coeffs(pctx, &[t, s])?;
        let c = lin.mul(&b)?.add(&a.poly_mul_scalar(&u)?)?;
        a = std::mem::replace(&mut b, c);
    }
    Ok(b)
}

/// `1/n` in the coefficient field (0 where n is not invertible there, which
/// is what Magma's recurrences give).
fn inv_or_zero(k: &Rc<Ctx>, n: u64) -> GrResult<Elem> {
    Ok(Elem::from_i64(k, n as i64)?.inv().unwrap_or_else(|_| Elem::zero(k)))
}

/// The generalized Laguerre polynomial `L_n^(m)`: `L_0 = 1`,
/// `L_1 = 1 + m - x`, `n L_n = (2n + m - 1 - x) L_(n-1) - (n - 1 + m) L_(n-2)`.
pub(super) fn laguerre_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = family_index(a)?;
    if a.args.len() == 1 {
        return family_poly(it, Value::rationals(), fu::Family::Laguerre, Some(n));
    }
    let (st, pctx, m) = param_ring(it, &a.args[1].clone(), true)?;
    let k = pctx.base().expect("a polynomial ring").clone();
    let int = |v: i64| Elem::from_i64(&k, v);
    let f0 = Elem::one(&pctx)?;
    let f1 = Elem::poly_from_coeffs(&pctx, &[int(1)?.add(&m)?, int(-1)?])?;
    let f = recurrence(&pctx, n, f0, f1, |j| {
        let inv = inv_or_zero(&k, j)?;
        let t = int(2 * j as i64 - 1)?.add(&m)?.mul(&inv)?;
        let u = int(j as i64 - 1)?.add(&m)?.neg()?.mul(&inv)?;
        Ok((inv.neg()?, t, u))
    })?;
    one(make_elt(&st, f))
}

/// The Gegenbauer polynomial `C_n^(m)`: `C_0 = 1`, `C_1 = 2 m x`,
/// `n C_n = 2 (n - 1 + m) x C_(n-1) - (n + 2m - 2) C_(n-2)`.
pub(super) fn gegenbauer_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = family_index(a)?;
    let (st, pctx, m) = param_ring(it, &a.args[1].clone(), true)?;
    let k = pctx.base().expect("a polynomial ring").clone();
    let int = |v: i64| Elem::from_i64(&k, v);
    let f0 = Elem::one(&pctx)?;
    let f1 = Elem::poly_from_coeffs(&pctx, &[Elem::zero(&k), m.add(&m)?])?;
    let f = recurrence(&pctx, n, f0, f1, |j| {
        let inv = inv_or_zero(&k, j)?;
        let s = int(j as i64 - 1)?.add(&m)?.mul(&int(2)?)?.mul(&inv)?;
        let u = int(j as i64 - 2)?.add(&m)?.add(&m)?.neg()?.mul(&inv)?;
        Ok((s, Elem::zero(&k), u))
    })?;
    one(make_elt(&st, f))
}

/// The Dickson polynomials `D_n(x, a)` (first kind, `D_0 = 2`) and
/// `E_n(x, a)` (second kind, `E_0 = 1`), with `f_1 = x` and
/// `f_n = x f_(n-1) - a f_(n-2)`, over the parent of `a`.
fn dickson(it: &mut Interp, a: &mut CallArgs, first: bool) -> RResult<Vals> {
    let n = family_index(a)?;
    let (st, pctx, c) = param_ring(it, &a.args[1].clone(), false)?;
    let k = pctx.base().expect("a polynomial ring").clone();
    let f0 = Elem::poly_from_coeffs(&pctx, &[Elem::from_i64(&k, if first { 2 } else { 1 })?])?;
    let f1 = fu::monomial(&pctx, &Elem::one(&k)?, 1)?;
    let nc = c.neg()?;
    let f = recurrence(&pctx, n, f0, f1, |_| Ok((Elem::one(&k)?, Elem::zero(&k), nc.clone())))?;
    one(make_elt(&st, f))
}

pub(super) fn dickson_first(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    dickson(it, a, true)
}

pub(super) fn dickson_second(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    dickson(it, a, false)
}

/// The n-th Swinnerton-Dyer polynomial, over the integers.
pub(super) fn swinnerton_dyer_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?;
    if n.sign() <= 0 {
        return Err(bare(arg_ge(1, n, 1)));
    }
    let n = n.to_u64().filter(|&n| n <= 20).ok_or_else(|| RuntimeError::runtime(format!("Argument 1 ({n}) is too large")))?;
    let zx = it.poly_ring(&Value::integers(), true)?;
    let Some((st, r)) = ring_of(&zx) else { unreachable!() };
    one(make_elt(st, fu::swinnerton_dyer(&r.ctx, n)))
}
