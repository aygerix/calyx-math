//! Greatest common divisors, least common multiples, normalization, and
//! content and primitive part of univariate polynomials.

use calyx_flint::Integer;
use calyx_flint::gr::{CtxKind, Elem, GrError, Truth};
use calyx_flint::upoly as fu;

use super::{base_of, bctx, cval, is_field, is_integers, len, like, pair, pol};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::one;
use crate::rings::{Elt, RingKind, ring_of};
use crate::value::*;

/// Over which coefficient rings gcds are computed.
fn gcd_ring(f: &Elt) -> RResult<()> {
    let b = bctx(f);
    if matches!(b.kind(), CtxKind::Integers) || fu::over_field(f.x.ctx()) {
        return Ok(());
    }
    Err(RuntimeError::runtime("Algorithm is not available for this kind of coefficient ring"))
}

pub(super) fn gcd(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = pair(it, a)?;
    gcd_ring(&f)?;
    one(like(&f, fu::gcd(&f.x, &g)?))
}

pub(super) fn xgcd(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = pair(it, a)?;
    match fu::xgcd(&f.x, &g) {
        Ok((d, s, t)) => Ok(vals![like(&f, d), like(&f, s), like(&f, t)]),
        Err(GrError::Domain) => Err(RuntimeError::runtime("Coefficient ring of argument 1 is not a field")),
        Err(e) => Err(e.into()),
    }
}

pub(super) fn lcm(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = pair(it, a)?;
    gcd_ring(&f)?;
    if len(&f) == 0 || g.poly_len() == 0 {
        return one(like(&f, Elem::zero(f.x.ctx())));
    }
    let d = fu::gcd(&f.x, &g)?;
    let l = Elt { parent: f.parent.clone(), x: fu::divides(&f.x, &d)?.expect("the gcd divides").mul(&g)? };
    one(like(&f, normalized(it, &l)?))
}

/// The unit `u` of the coefficient ring `base` making `u c` normalized: the
/// sign over the integers, the inverse over a field, the unit of
/// `Normalize` over a residue class ring, and recursively that of the
/// leading coefficient over a polynomial ring.
pub(crate) fn norm_unit(it: &mut Interp, base: &Value, c: &Elem) -> RResult<Elem> {
    let ctx = c.ctx().clone();
    if c.is_zero() == Truth::True {
        return Ok(Elem::one(&ctx)?);
    }
    if let Some((_, r)) = ring_of(base) {
        match &r.kind {
            RingKind::UPoly { base: b2, .. } => {
                let b2 = b2.clone();
                let u = norm_unit(it, &b2, &fu::lead(c))?;
                return Ok(Elem::poly_from_coeffs(&ctx, &[u])?);
            }
            RingKind::MPoly { base: b2, .. } => {
                let b2 = b2.clone();
                let lc = crate::intrinsics::mpoly::leading(&r, c).expect("a non-zero polynomial").0;
                let u = norm_unit(it, &b2, &lc)?;
                let mut e = Elem::zero(&ctx);
                e.mpoly_set_scalar(&u)?;
                return Ok(e);
            }
            RingKind::Residue(_) => {
                let v = it.elem_to_value(base, c.clone());
                let mut args = vec![v];
                let out = it.call_intrinsic(crate::sym::Sym::new("Normalize"), &mut args, &[false], Vec::new(), 2, false, Default::default(), None)?;
                let u = out.and_then(|vs| vs.into_iter().nth(1)).unwrap_or(Value::int(1));
                return Ok(it.to_structure_elem(base, &u, false)?.unwrap_or(Elem::one(&ctx)?));
            }
            _ => {}
        }
    }
    if matches!(ctx.kind(), CtxKind::Integers) {
        return Ok(Elem::from_i64(&ctx, if c.to_integer()?.sign() < 0 { -1 } else { 1 })?);
    }
    if is_field(base) {
        return Ok(c.inv()?);
    }
    Ok(Elem::one(&ctx)?)
}

/// The normalized associate: positive leading coefficient over the
/// integers, monic over a field, and so on (see `norm_unit`).
fn normalized(it: &mut Interp, f: &Elt) -> RResult<Elem> {
    if len(f) == 0 {
        return Ok(f.x.clone());
    }
    let u = norm_unit(it, &base_of(f), &fu::lead(&f.x))?;
    Ok(f.x.poly_mul_scalar(&u)?)
}

pub(super) fn normalize(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    one(like(&f, normalized(it, &f)?))
}

/// The content and the primitive part: over the integers the gcd of the
/// coefficients (the primitive part keeps the sign), over a field 1, over
/// `Z/nZ` the gcd of the coefficients and n, and over a polynomial ring
/// the gcd of the coefficients there.
fn contpp(it: &Interp, f: &Elt) -> RResult<(Value, Value)> {
    let b = bctx(f);
    if is_integers(f) {
        let c = fu::content_z(&f.x);
        let pp = if c.is_zero() { f.x.clone() } else { fu::divexact_z(&f.x, &c) };
        return Ok((Value::Int(c), like(f, pp)));
    }
    if fu::over_field(f.x.ctx()) {
        let one_c = if len(f) == 0 { Elem::zero(&b) } else { Elem::one(&b)? };
        return Ok((cval(it, f, one_c), like(f, f.x.clone())));
    }
    if let Some((_, r)) = ring_of(&base_of(f)) {
        match &r.kind {
            RingKind::Residue(m) => {
                let cs: Vec<Integer> = (0..len(f)).map(|i| Ok(f.x.poly_coeff(i).to_integer()?)).collect::<RResult<_>>()?;
                let c = cs.iter().fold(m.clone(), |g, x| g.gcd(x));
                let pp: Vec<Elem> = cs.iter().map(|x| Elem::from_integer(&b, &x.divexact(&c))).collect::<Result<_, _>>()?;
                return Ok((cval(it, f, Elem::from_integer(&b, &c)?), like(f, Elem::poly_from_coeffs(f.x.ctx(), &pp)?)));
            }
            RingKind::UPoly { .. } if len(f) > 0 && (matches!(b.base().map(|c| c.kind()), Some(CtxKind::Integers)) || fu::over_field(&b)) => {
                let mut c = Elem::zero(&b);
                for i in 0..len(f) {
                    c = fu::gcd(&c, &f.x.poly_coeff(i))?;
                }
                let pp: Vec<Elem> = (0..len(f)).map(|i| Ok(fu::divides(&f.x.poly_coeff(i), &c)?.expect("the content divides"))).collect::<RResult<_>>()?;
                return Ok((cval(it, f, c), like(f, Elem::poly_from_coeffs(f.x.ctx(), &pp)?)));
            }
            _ => {}
        }
    }
    Err(RuntimeError::runtime("Algorithm is not available for this kind of coefficient ring"))
}

pub(super) fn content(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(contpp(it, &pol(a, 0))?.0)
}

pub(super) fn primitive_part(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(contpp(it, &pol(a, 0))?.1)
}

pub(super) fn content_and_primitive_part(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (c, p) = contpp(it, &pol(a, 0))?;
    Ok(vals![c, p])
}
