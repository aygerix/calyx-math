//! Powers of polynomials over real and complex floating-point fields,
//! rounded as Magma rounds them (#73).
//!
//! Magma raises a polynomial to a power by left-to-right binary powering
//! with its own squaring and product, and every operation on coefficients
//! rounds to the precision of the field (each part of a complex number is
//! rounded correctly). Black-box runs of Magma 2.22 give these rules:
//! - A square of at most eight terms (from the lowest nonzero one) has the
//!   coefficients `2 (f_0 f_k + f_1 f_(k-1) + ...) + f_(k/2)^2`: each
//!   product rounded, the cross products added in this order, their sum
//!   doubled, and the square added last.
//! - A product by a polynomial with at most two nonzero terms rounds each
//!   product and then their sum.
//! - `(b x)^e` is `b^e x^e`, with `b^e` the power of the number `b`.
//!
//! Magma's longer squares and its other products follow rules not yet
//! identified; there FLINT rounds each coefficient once.

use flint3_sys as sys;

use crate::gr::{CtxKind, Elem, GrResult, Truth};
use crate::{Complex, Integer};

/// The longest polynomial that Magma squares term by term.
const SQUARE_TERMS: usize = 8;

/// `f^e` as Magma computes it, for a nonzero univariate polynomial `f` over
/// a real or complex floating-point field and `e >= 2`, or `None` for any
/// other polynomial or exponent.
pub(crate) fn pow(f: &Elem, e: &Integer) -> Option<GrResult<Elem>> {
    if !matches!(f.ctx().kind(), CtxKind::Poly) {
        return None;
    }
    let base = f.ctx().base()?;
    if !matches!(base.kind(), CtxKind::RealFloat(_) | CtxKind::ComplexFloat(_)) || f.poly_len() == 0 {
        return None;
    }
    let e = e.to_u64().filter(|&e| e >= 2)?;
    Some(binary_pow(f, e))
}

fn coeffs(f: &Elem) -> Vec<Elem> {
    (0..f.poly_len()).map(|i| f.poly_coeff(i)).collect()
}

fn nonzero(c: &Elem) -> bool {
    c.is_zero() != Truth::True
}

fn binary_pow(f: &Elem, e: u64) -> GrResult<Elem> {
    let fc = coeffs(f);
    let terms = fc.iter().filter(|c| nonzero(c)).count();
    if fc.len() == 2 && terms == 1 {
        return monomial_pow(f, &fc[1], e);
    }
    let mut r = f.clone();
    for bit in (0..63 - e.leading_zeros()).rev() {
        let rc = coeffs(&r);
        let low = rc.iter().position(nonzero).expect("a nonzero polynomial");
        r = if rc.len() - low <= SQUARE_TERMS {
            let mut sq: Vec<Elem> = (0..2 * low).map(|_| Elem::zero(f.ctx().base().expect("a polynomial"))).collect();
            sq.extend(square(&rc[low..])?);
            Elem::poly_from_coeffs(f.ctx(), &sq)?
        } else {
            r.sqr()?
        };
        if e >> bit & 1 == 1 {
            r = if terms <= 2 { Elem::poly_from_coeffs(f.ctx(), &mul_sparse(&coeffs(&r), &fc)?)? } else { r.mul(f)? };
        }
    }
    Ok(r)
}

/// The square of `f` by the rule above.
fn square(f: &[Elem]) -> GrResult<Vec<Elem>> {
    let n = f.len();
    let mut out = Vec::with_capacity(2 * n - 1);
    for k in 0..2 * n - 1 {
        let mut s: Option<Elem> = None;
        for i in (k + 1).saturating_sub(n)..(k + 1) / 2 {
            let t = f[i].mul(&f[k - i])?;
            s = Some(match s {
                None => t,
                Some(s) => s.add(&t)?,
            });
        }
        // Doubling is exact.
        let s = s.map(|s| s.add(&s)).transpose()?;
        out.push(match (s, k % 2 == 0) {
            (None, _) => f[k / 2].sqr()?,
            (Some(s), true) => s.add(&f[k / 2].sqr()?)?,
            (Some(s), false) => s,
        });
    }
    Ok(out)
}

/// `r f` for `f` with at most two nonzero terms: each coefficient is a
/// sum of at most two products, and their order does not matter.
fn mul_sparse(r: &[Elem], f: &[Elem]) -> GrResult<Vec<Elem>> {
    let mut out: Vec<Option<Elem>> = (0..r.len() + f.len() - 1).map(|_| None).collect();
    for (j, c) in f.iter().enumerate().filter(|(_, c)| nonzero(c)) {
        for (i, a) in r.iter().enumerate() {
            let t = a.mul(c)?;
            out[i + j] = Some(match out[i + j].take() {
                None => t,
                Some(s) => s.add(&t)?,
            });
        }
    }
    Ok(out.into_iter().map(|c| c.unwrap_or_else(|| Elem::zero(f[0].ctx()))).collect())
}

/// `(b x)^e = b^e x^e`, with `b^e` as Magma computes powers of numbers.
fn monomial_pow(f: &Elem, b: &Elem, e: u64) -> GrResult<Elem> {
    let be = match b.to_real() {
        Some(x) => Elem::from_real(b.ctx(), &x.pow_integer(&Integer::from_u64(e)))?,
        None => {
            let (re, im) = b.to_complex_parts().expect("a complex number");
            let z = Complex::new(re, im).pow_i64(i64::try_from(e).expect("a small exponent"));
            Elem::from_complex_parts(b.ctx(), &z.re, &z.im)?
        }
    };
    let mut r = Elem::zero(f.ctx());
    let st = unsafe { sys::gr_poly_set_coeff_scalar(r.as_mut_ptr().cast(), e as sys::slong, be.as_ptr(), b.ctx().ptr()) };
    assert_eq!(st, 0, "gr_poly_set_coeff_scalar failed");
    Ok(r)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gr::{Ctx, MonomialOrder};
    use crate::{Rational, Real};

    const P: u64 = 67;

    fn real(n: i64, d: i64) -> Real {
        Real::from_rational(&Rational::new(&Integer::from_i64(n), &Integer::from_i64(d)).unwrap(), P)
    }

    fn poly(cs: &[Real]) -> Elem {
        let ctx = Ctx::poly(&Ctx::real_float(P));
        let cs: Vec<Elem> = cs.iter().map(|c| Elem::from_real(ctx.base().unwrap(), c).unwrap()).collect();
        Elem::poly_from_coeffs(&ctx, &cs).unwrap()
    }

    fn parts(f: &Elem) -> Vec<Real> {
        coeffs(f).iter().map(|c| c.to_real().unwrap()).collect()
    }

    #[test]
    fn squares_round_each_operation() {
        // (a + b x + c x^2)^2: the x^2 coefficient is 2 rnd(a c) + rnd(b^2)
        // rounded, not the exact value rounded once.
        let (a, b, c) = (real(1, 3), real(2, 7), real(-5, 11));
        let f = poly(&[a.clone(), b.clone(), c.clone()]);
        let sq = parts(&f.pow(&Integer::from_i64(2)).unwrap());
        assert_eq!(sq[2], a.mul(&c).mul_2exp(1).add(&b.mul(&b)));
        assert_eq!(sq[1], a.mul(&b).mul_2exp(1));
        assert_eq!(sq[4], c.mul(&c));
        // (x - 1.1)^3 multiplies (x - 1.1)^2 by x - 1.1 with each product
        // rounded, then the sum.
        let t = real(-11, 10);
        let one = Real::from_i64(1, P);
        let l = poly(&[t.clone(), one.clone()]);
        let l2 = parts(&l.pow(&Integer::from_i64(2)).unwrap());
        let l3 = parts(&l.pow(&Integer::from_i64(3)).unwrap());
        assert_eq!(l3[1], l2[1].mul(&t).add(&l2[0]));
        assert_eq!(l3[0], l2[0].mul(&t));
    }

    #[test]
    fn monomials_and_constants() {
        // (b x)^e takes the correctly rounded power of b; a constant is
        // squared and multiplied.
        let b = real(11, 10);
        let m = parts(&poly(&[Real::zero(P), b.clone()]).pow(&Integer::from_i64(7)).unwrap());
        assert_eq!(m.len(), 8);
        assert!(m[..7].iter().all(Real::is_zero));
        assert_eq!(m[7], b.pow_i64(7));
        let c = parts(&poly(&[b.clone()]).pow(&Integer::from_i64(7)).unwrap());
        let b3 = b.mul(&b).mul(&b);
        assert_eq!(c, vec![b3.mul(&b3).mul(&b)]);
        assert_ne!(c[0], b.pow_i64(7));
    }

    #[test]
    fn multivariate_polynomials_are_left_alone() {
        let ctx = Ctx::mpoly(&Ctx::real_float(P), 2, MonomialOrder::Lex);
        let three = Elem::from_i64(&ctx, 3).unwrap();
        let nine = Elem::from_i64(&ctx, 9).unwrap();
        assert_eq!(three.pow(&Integer::from_i64(2)).unwrap().equal(&nine), Truth::True);
    }

    #[test]
    fn dense_products_use_flint() {
        // Four nonzero terms: f^3 is the square times f with FLINT's product.
        let f = poly(&[real(1, 3), real(2, 7), real(-5, 11), real(3, 13)]);
        let f2 = f.pow(&Integer::from_i64(2)).unwrap();
        assert_eq!(parts(&f.pow(&Integer::from_i64(3)).unwrap()), parts(&f2.mul(&f).unwrap()));
    }
}
