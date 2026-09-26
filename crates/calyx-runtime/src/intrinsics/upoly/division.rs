//! Division of univariate polynomials: quotient and remainder, exact
//! division and modular arithmetic.

use calyx_flint::Integer;
use calyx_flint::gr::{CtxKind, Elem, Truth};
use calyx_flint::upoly as fu;
use calyx_syntax::ast::BinOp;

use super::{is_unit_poly, len, like, package_error, pair, pair_of, pol};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::{arg_ge, boolv, intv, one};
use crate::ops::div_by_zero;
use crate::rings::{Ring, RingKind, make_elt};
use crate::value::*;

// ----- division ----------------------------------------------------------------

/// Quotient and remainder of `f` by `g` in `ring`, as Magma divides: over
/// the integers and fields see `calyx_flint::upoly::divrem`; over other
/// coefficient rings each coefficient of the quotient, from the top, is the
/// coefficient ring's `div` of the current coefficient by the leading
/// coefficient of `g` (exact division when that is a unit).
pub fn quotrem(it: &mut Interp, ring: &Ring, f: &Elem, g: &Elem) -> RResult<(Elem, Elem)> {
    if g.poly_len() == 0 {
        return Err(div_by_zero());
    }
    let b = f.ctx().base().expect("a polynomial").clone();
    let lc = fu::lead(g);
    if matches!(b.kind(), CtxKind::Integers) || fu::over_field(f.ctx()) || lc.is_invertible() == Truth::True {
        return Ok(fu::divrem(f, g)?);
    }
    let base = ring.base().expect("a polynomial ring").clone();
    let lcv = it.elem_to_value(&base, lc);
    let (lf, lg) = (f.poly_len(), g.poly_len());
    let mut r = f.clone();
    let mut q = vec![Elem::zero(&b); lf.saturating_sub(lg - 1)];
    for i in (lg - 1..lf).rev() {
        let c = r.poly_coeff(i);
        if c.is_zero() == Truth::True {
            continue;
        }
        let cv = it.elem_to_value(&base, c);
        let d = it.binop(BinOp::IntDiv, cv, lcv.clone())?;
        let Some(d) = it.to_structure_elem(&base, &d, false)? else { continue };
        if d.is_zero() == Truth::True {
            continue;
        }
        r = r.sub(&fu::shift_left(&g.poly_mul_scalar(&d)?, i + 1 - lg)?)?;
        q[i + 1 - lg] = d;
    }
    Ok((Elem::poly_from_coeffs(f.ctx(), &q)?, r))
}

/// The exact quotient `f / g`, if there is one (`g` non-zero).
fn exact_div(it: &mut Interp, ring: &Ring, f: &Elem, g: &Elem) -> RResult<Option<Elem>> {
    if matches!(g.ctx().base().map(|b| b.kind()), Some(CtxKind::Integers)) {
        return Ok(fu::divides(f, g)?);
    }
    let (q, r) = quotrem(it, ring, f, g)?;
    Ok((r.is_zero() == Truth::True).then_some(q))
}

// ----- quotient and remainder ---------------------------------------------------------

pub(super) fn quotrem_fn(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = pair(it, a)?;
    let ring = f.ring_rc();
    let (q, r) = quotrem(it, &ring, &f.x, &g)?;
    Ok(vals![like(&f, q), like(&f, r)])
}

pub(super) fn is_divisible_by(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = pair(it, a)?;
    if g.poly_len() == 0 {
        return Err(div_by_zero());
    }
    match exact_div(it, &f.ring_rc(), &f.x, &g)? {
        Some(q) => Ok(vals![Value::Bool(true), like(&f, q)]),
        None => boolv(false),
    }
}

pub(super) fn exact_quotient(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = pair(it, a)?;
    if g.poly_len() == 0 {
        return Err(div_by_zero());
    }
    match exact_div(it, &f.ring_rc(), &f.x, &g)? {
        Some(q) => one(like(&f, q)),
        None => Err(RuntimeError::runtime("Argument 1 is not exactly divisible by argument 2")),
    }
}

/// The largest k with `g^k` dividing `f`.
pub(super) fn valuation_by(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = pair(it, a)?;
    if g.poly_len() == 0 {
        return Err(div_by_zero());
    }
    if len(&f) == 0 {
        return one(Value::Infinity(true));
    }
    if is_unit_poly(&g) {
        return Err(RuntimeError::runtime("Argument 2 must not be a unit"));
    }
    let ring = f.ring_rc();
    let (mut h, mut k) = (f.x.clone(), 0u64);
    while let Some(q) = exact_div(it, &ring, &h, &g)? {
        h = q;
        k += 1;
    }
    intv(Integer::from_u64(k))
}

pub(super) fn pseudo_remainder(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = pair(it, a)?;
    if g.poly_len() == 0 {
        return Err(div_by_zero());
    }
    one(like(&f, fu::pseudo_rem(&f.x, &g)?))
}

pub(super) fn euclidean_norm(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(len(&pol(a, 0)) as u64))
}

// ----- modular arithmetic ---------------------------------------------------------------

pub(super) fn modexp(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(1)?.clone();
    let (f, g) = pair_of(it, &a.args[0], &a.args[2])?;
    if n.sign() < 0 {
        return Err(arg_ge(2, &n, 0));
    }
    if !fu::over_field(f.x.ctx()) {
        return Err(RuntimeError::runtime("Algorithm is not available for this kind of coefficient ring"));
    }
    if g.poly_len() == 0 {
        return Err(div_by_zero());
    }
    one(like(&f, fu::powmod(&f.x, &n, &g)?))
}

pub(super) fn crt(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (xs, ms) = (a.seq(0)?.clone(), a.seq(1)?.clone());
    let elt = |v: &Value| match v {
        Value::Elt(e) if matches!(e.ring().kind, RingKind::UPoly { .. }) => Ok(e.clone()),
        _ => Err(RuntimeError::runtime("Bad argument types")),
    };
    let Some(m0) = ms.elems.first() else { return Err(RuntimeError::runtime("Argument 2 must be non-empty")) };
    let m0 = elt(m0)?;
    if !fu::over_field(m0.x.ctx()) {
        return Err(RuntimeError::runtime("Coefficient ring of argument 1 is not a field"));
    }
    let ring = m0.ring_rc();
    let st = m0.parent.clone();
    let get = |it: &mut Interp, v: &Value| -> RResult<Elem> { it.to_ring_elem(&st, v, false)?.ok_or_else(|| RuntimeError::runtime("Arguments are not compatible")) };
    let mods: Vec<Elem> = ms.elems.iter().map(|v| get(it, v)).collect::<RResult<_>>()?;
    for i in 0..mods.len() {
        for j in 0..i {
            if fu::gcd(&mods[i], &mods[j])?.poly_len() != 1 {
                return Err(package_error("Error, ChineseRemainderTheorem: modules must be coprime."));
            }
        }
    }
    if xs.elems.len() < mods.len() {
        return Err(RuntimeError::runtime("Arguments have different lengths"));
    }
    let mut m = mods[0].clone();
    let x0 = get(it, &xs.elems[0])?;
    let mut t = quotrem(it, &ring, &x0, &m)?.1;
    for (xi, mi) in xs.elems.iter().zip(&mods).skip(1) {
        let x = get(it, xi)?;
        let (_, s, _) = fu::xgcd(&m, mi)?;
        let c = quotrem(it, &ring, &x.sub(&t)?.mul(&s)?, mi)?.1;
        t = t.add(&m.mul(&c)?)?;
        m = m.mul(mi)?;
    }
    one(make_elt(&st, t))
}
