//! Element operations of univariate polynomials: predicates, coefficients
//! and terms, derivatives, evaluation and interpolation, and other
//! operations.

use calyx_flint::Integer;
use calyx_flint::gr::{Ctx, Elem, Truth};
use calyx_flint::upoly as fu;
use calyx_syntax::ast::BinOp;

use super::{base_of, bctx, coeff_seq, cval, is_field, len, like, nonzero, pair, pol, poly_seq};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::{arg_ge, boolv, intv, one};
use crate::rings::props::ring_props;
use crate::rings::{make_elt, ring_of};
use crate::value::*;

// ----- predicates -----------------------------------------------------------------

pub(super) fn is_monic(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    boolv(len(&f) > 0 && fu::lead(&f.x).is_one() == Truth::True)
}

/// Whether `f` is not a zero divisor: Magma answers only over domains.
pub(super) fn is_regular(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let domain = ring_props(&base_of(&f)).is_some_and(|p| p.domain);
    boolv(domain && len(&f) > 0)
}

// ----- coefficients and terms ---------------------------------------------------------

pub(super) fn coefficients(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let cs = (0..len(&f)).map(|i| f.x.poly_coeff(i)).collect();
    one(coeff_seq(it, &f, cs))
}

/// Argument `i` as a non-negative machine integer.
fn index_arg(a: &CallArgs, i: usize) -> RResult<usize> {
    let n = a.int(i)?;
    if n.sign() < 0 {
        return Err(arg_ge(i + 1, n, 0));
    }
    n.to_u64().filter(|&k| k < 1 << 62).map(|k| k as usize).ok_or_else(|| RuntimeError::runtime(format!("Argument {} ({n}) is too large", i + 1)))
}

pub(super) fn coefficient(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let i = index_arg(a, 1)?;
    let c = if i < len(&f) { f.x.poly_coeff(i) } else { Elem::zero(&bctx(&f)) };
    one(cval(it, &f, c))
}

pub(super) fn monomial_coefficient(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, m) = pair(it, a)?;
    let n = m.poly_len();
    let monomial = n > 0 && m.poly_coeff(n - 1).is_one() == Truth::True && (0..n - 1).all(|i| m.poly_coeff(i).is_zero() == Truth::True);
    if !monomial {
        return Err(RuntimeError::runtime("Argument 2 must be a monomial"));
    }
    let c = if n - 1 < len(&f) { f.x.poly_coeff(n - 1) } else { Elem::zero(&bctx(&f)) };
    one(cval(it, &f, c))
}

/// The index of the lowest non-zero coefficient of a non-zero polynomial.
fn low(f: &Elem) -> usize {
    (0..f.poly_len()).find(|&i| f.poly_coeff(i).is_zero() != Truth::True).unwrap_or(0)
}

pub(super) fn leading_coefficient(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    nonzero(&f)?;
    one(cval(it, &f, fu::lead(&f.x)))
}

pub(super) fn trailing_coefficient(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    nonzero(&f)?;
    one(cval(it, &f, f.x.poly_coeff(low(&f.x))))
}

pub(super) fn constant_coefficient(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let c = if len(&f) > 0 { f.x.poly_coeff(0) } else { Elem::zero(&bctx(&f)) };
    one(cval(it, &f, c))
}

pub(super) fn terms(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let mut out = Vec::new();
    for i in 0..len(&f) {
        let c = f.x.poly_coeff(i);
        if c.is_zero() != Truth::True {
            out.push(fu::monomial(f.x.ctx(), &c, i)?);
        }
    }
    one(poly_seq(&f, out))
}

pub(super) fn leading_term(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    nonzero(&f)?;
    let n = len(&f) - 1;
    one(like(&f, fu::monomial(f.x.ctx(), &f.x.poly_coeff(n), n)?))
}

pub(super) fn trailing_term(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    nonzero(&f)?;
    let k = low(&f.x);
    one(like(&f, fu::monomial(f.x.ctx(), &f.x.poly_coeff(k), k)?))
}

pub(super) fn monomials(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let one_c = Elem::one(&bctx(&f))?;
    let out = (0..len(&f)).map(|i| fu::monomial(f.x.ctx(), &one_c, i)).collect::<Result<Vec<_>, _>>()?;
    one(poly_seq(&f, out))
}

pub(super) fn support(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let (mut idx, mut cs) = (Vec::new(), Vec::new());
    for i in 0..len(&f) {
        let c = f.x.poly_coeff(i);
        if c.is_zero() != Truth::True {
            idx.push(Integer::from_u64(i as u64));
            cs.push(c);
        }
    }
    // The coefficients are returned only when asked for.
    if a.nresults < 2 {
        return one(Value::int_seq(idx));
    }
    Ok(vals![Value::int_seq(idx), coeff_seq(it, &f, cs)])
}

pub(super) fn reductum(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    nonzero(&f)?;
    one(like(&f, fu::truncate(&f.x, len(&f) - 1)?))
}

/// The polynomial over the integers with the coefficients rounded.
pub(super) fn round(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let mut cs = Vec::with_capacity(len(&f));
    for i in 0..len(&f) {
        cs.push(match cval(it, &f, f.x.poly_coeff(i)) {
            Value::Int(n) => n,
            Value::Rat(q) => q.round(),
            Value::Real(r) => r.x.round(),
            _ => return Err(RuntimeError::runtime("Coefficient ring is not a real subring")),
        });
    }
    let zx = it.poly_ring(&Value::integers(), true)?;
    let Some((st, r)) = ring_of(&zx) else { unreachable!() };
    let zz = Ctx::integers();
    let cs: Vec<Elem> = cs.iter().map(|c| Elem::from_integer(&zz, c)).collect::<Result<_, _>>()?;
    one(make_elt(st, Elem::poly_from_coeffs(&r.ctx, &cs)?))
}

pub(super) fn valuation(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    if len(&f) == 0 {
        return one(Value::Infinity(true));
    }
    intv(Integer::from_u64(low(&f.x) as u64))
}

pub(super) fn degree(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_i64(len(&pol(a, 0)) as i64 - 1))
}

// ----- derivatives, evaluation, interpolation -------------------------------------------

pub(super) fn derivative(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let n = if a.args.len() > 1 { index_arg(a, 1)? } else { 1 };
    one(like(&f, fu::nth_derivative(&f.x, n as u64)?))
}

pub(super) fn integral(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let p = ring_props(&base_of(&f));
    if !p.as_ref().is_some_and(|p| p.field) {
        return Err(RuntimeError::runtime("Coefficient ring of argument 1 is not a field"));
    }
    if !p.is_some_and(|p| p.characteristic.is_zero()) {
        return Err(RuntimeError::runtime("Coefficient ring must have characteristic 0"));
    }
    one(like(&f, fu::integral(&f.x)?))
}

/// `Evaluate(f, r)`: in the coefficient ring when `r` coerces into it,
/// else by Horner's rule in the structure of `r`.
pub(super) fn evaluate(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let r = a.args[1].clone();
    let base = base_of(&f);
    let pr = it.parent_of(&r)?;
    if it.auto_coerces(&pr, &base) {
        if let Some(x) = it.to_structure_elem(&base, &r, false)? {
            let v = if len(&f) == 0 { Elem::zero(&bctx(&f)) } else { f.x.poly_evaluate(&x)? };
            return one(it.elem_to_value(&base, v));
        }
    }
    let n = len(&f);
    if n == 0 {
        return one(it.binop(BinOp::Mul, r, Value::int(0))?);
    }
    let mut acc = cval(it, &f, f.x.poly_coeff(n - 1));
    for i in (0..n - 1).rev() {
        acc = it.binop(BinOp::Mul, acc, r.clone())?;
        let c = cval(it, &f, f.x.poly_coeff(i));
        acc = it.binop(BinOp::Add, acc, c)?;
    }
    one(acc)
}

pub(super) fn interpolation(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (xs, ys) = (a.seq(0)?.clone(), a.seq(1)?.clone());
    let (Some(u), Some(v)) = (xs.universe.clone(), ys.universe.clone()) else {
        return Err(RuntimeError::runtime("Must have a ring universe"));
    };
    if u != v {
        return Err(RuntimeError::runtime("Arguments have different rings"));
    }
    let n = xs.elems.len();
    if ys.elems.len() != n {
        return Err(RuntimeError::runtime("Arguments have different lengths"));
    }
    for i in 0..n {
        for j in 0..i {
            if it.values_equal(&xs.elems[i], &xs.elems[j])? {
                return Err(RuntimeError::runtime("Elements of argument 1 are not distinct"));
            }
        }
    }
    if !is_field(&u) {
        return Err(RuntimeError::runtime("Ring is not a field"));
    }
    let p = it.poly_ring(&u, true)?;
    let Some((st, r)) = ring_of(&p) else { unreachable!() };
    let (st, ctx) = (st.clone(), r.ctx.clone());
    let mut conv = |vs: &[Value]| -> RResult<Vec<Elem>> {
        vs.iter().map(|v| it.to_structure_elem(&u, v, false)?.ok_or_else(|| RuntimeError::runtime("Arguments have different rings"))).collect()
    };
    let (px, py) = (conv(&xs.elems)?, conv(&ys.elems)?);
    one(make_elt(&st, fu::interpolate(&ctx, &px, &py)?))
}

// ----- other operations ---------------------------------------------------------------

pub(super) fn reciprocal_polynomial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    one(like(&f, fu::reverse(&f.x, len(&f))?))
}

/// The polynomial whose roots are the n-th powers of those of `f`:
/// `(-1)^((n-1) d) Res_x(f(x), y - x^n)` for `f` of degree `d`, which is
/// `prod_k f(z^k x)` for the n-th roots of unity `z^k` as a polynomial in
/// `x^n`.
pub(super) fn power_polynomial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let n = a.int(1)?;
    if n.sign() <= 0 {
        return Err(arg_ge(2, n, 1));
    }
    let n = n.to_u64().filter(|&k| k < 1 << 20).ok_or_else(|| RuntimeError::runtime("Argument 2 is too large"))? as usize;
    if n == 1 || len(&f) == 0 {
        return one(like(&f, f.x.clone()));
    }
    // Over R[y]: F(x) with constant coefficients, and G(x) = y - x^n.
    let ry = f.x.ctx().clone();
    let outer = Ctx::poly(&ry);
    let cs: Vec<Elem> = (0..len(&f)).map(|i| Elem::poly_from_coeffs(&ry, &[f.x.poly_coeff(i)])).collect::<Result<_, _>>()?;
    let big_f = Elem::poly_from_coeffs(&outer, &cs)?;
    let mut gs = vec![Elem::zero(&ry); n + 1];
    gs[0] = ry.generator()?;
    gs[n] = Elem::from_i64(&ry, -1)?;
    let big_g = Elem::poly_from_coeffs(&outer, &gs)?;
    let mut r = big_f.poly_resultant(&big_g)?;
    if (n - 1) * (len(&f) - 1) % 2 == 1 {
        r = r.neg()?;
    }
    one(like(&f, r))
}
