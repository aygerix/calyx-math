//! The functions for univariate polynomials over the integers.

use calyx_flint::Integer;
use calyx_flint::gr::{Ctx, Elem, Truth};
use calyx_flint::upoly as fu;

use super::{is_integers, len, like, pol};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::{arg_prime, boolv, intv, one};
use crate::rings::{Elt, ring_of};
use crate::value::*;

/// The coefficients of an integer polynomial.
fn int_coeffs(f: &Elt) -> RResult<Vec<Integer>> {
    if !is_integers(f) {
        return Err(RuntimeError::runtime("Coefficient ring of argument must be Z"));
    }
    (0..len(f)).map(|i| Ok(f.x.poly_coeff(i).to_integer()?)).collect()
}

pub(super) fn sign(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let cs = int_coeffs(&pol(a, 0))?;
    intv(Integer::from_i64(cs.last().map_or(0, |c| c.sign() as i64)))
}

pub(super) fn abs(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let cs = int_coeffs(&f)?;
    one(like(&f, if cs.last().is_some_and(|c| c.sign() < 0) { f.x.neg()? } else { f.x.clone() }))
}

pub(super) fn max_norm(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let cs = int_coeffs(&pol(a, 0))?;
    intv(cs.iter().map(|c| c.abs()).max().unwrap_or_default())
}

pub(super) fn sum_norm(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let cs = int_coeffs(&pol(a, 0))?;
    intv(cs.iter().fold(Integer::zero(), |s, c| &s + &c.abs()))
}

/// Dedekind's criterion: with `f = prod g_i^e_i` mod p, `g = prod g_i`
/// and `h = f / g` mod p (lifted), and `F = (g h - f) / p`, the equation
/// order of `f` is maximal at p iff `gcd(F, g, h) = 1` mod p.
pub(super) fn dedekind_test(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let p = a.int(1)?.clone();
    if !is_integers(&f) {
        return Err(RuntimeError::runtime("argument 1 not a polynomial over Z"));
    }
    if fu::lead(&f.x).is_one() != Truth::True {
        return Err(RuntimeError::runtime("Argument 1 is not monic"));
    }
    if !p.is_prime() {
        return Err(arg_prime(2, &p));
    }
    let fp = it.finite_field(&p, 1)?;
    let px = it.poly_ring(&fp, true)?;
    let Some((_, pr)) = ring_of(&px) else { unreachable!() };
    let pctx = pr.ctx.clone();
    let zx = f.x.ctx().clone();
    let fbar = fu::convert(&pctx, &f.x)?;
    let fac = fu::factor(&fbar)?;
    let mut g = Elem::one(&pctx)?;
    for (q, _) in &fac.factors {
        g = g.mul(q)?;
    }
    let h = fu::divrem(&fbar, &g)?.0;
    let lift = |e: &Elem| -> RResult<Elem> {
        let cs: Vec<Elem> = (0..e.poly_len()).map(|i| Elem::from_integer(&Ctx::integers(), &e.poly_coeff(i).to_integer()?)).collect::<Result<_, _>>()?;
        Ok(Elem::poly_from_coeffs(&zx, &cs)?)
    };
    let big = lift(&g)?.mul(&lift(&h)?)?.sub(&f.x)?;
    let cs: Vec<Elem> = (0..big.poly_len()).map(|i| Ok::<_, RuntimeError>(Elem::from_integer(&Ctx::integers(), &big.poly_coeff(i).to_integer()?.divexact(&p))?)).collect::<Result<_, _>>()?;
    let fq = fu::convert(&pctx, &Elem::poly_from_coeffs(&zx, &cs)?)?;
    let d = fu::gcd(&fu::gcd(&fq, &g)?, &h)?;
    boolv(d.poly_len() == 1)
}
