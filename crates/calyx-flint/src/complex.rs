//! Complex numbers as pairs of MPFR reals of the same precision. Each part
//! of a result is rounded correctly, as with MPC: arithmetic uses MPFR (or
//! exact rationals), other functions FLINT's `acb` with `ball`'s rounding.

use flint3_sys as sys;

use crate::ball::{self, Acb, Arb};
use crate::{Integer, Rational, Real};

#[derive(Clone)]
pub struct Complex {
    pub re: Real,
    pub im: Real,
}

/// An `acb` function of one argument.
pub type AcbUnary = unsafe extern "C" fn(*mut sys::acb_struct, *const sys::acb_struct, sys::slong);

/// The exact value of a finite real as a rational (for moderate exponents).
fn exact(x: &Real) -> Option<Rational> {
    if x.is_zero() {
        return Some(Rational::zero());
    }
    (x.is_regular() && x.exponent().abs() < 1 << 14).then(|| x.to_rational()).flatten()
}

impl Complex {
    pub fn new(re: Real, im: Real) -> Complex {
        Complex { re, im }
    }

    /// A real as a complex number (with imaginary part +0).
    pub fn from_real(x: Real) -> Complex {
        let im = Real::zero(x.prec());
        Complex { re: x, im }
    }

    pub fn prec(&self) -> u64 {
        self.re.prec()
    }

    pub fn round_to(&self, prec: u64) -> Complex {
        Complex { re: self.re.round_to(prec), im: self.im.round_to(prec) }
    }

    pub fn is_zero(&self) -> bool {
        self.re.is_zero() && self.im.is_zero()
    }

    /// Whether the imaginary part is zero.
    pub fn is_real(&self) -> bool {
        self.im.is_zero()
    }

    fn acb(&self) -> Acb {
        Acb::from_parts(&self.re, &self.im)
    }

    pub fn add(&self, o: &Complex) -> Complex {
        Complex { re: self.re.add(&o.re), im: self.im.add(&o.im) }
    }

    pub fn sub(&self, o: &Complex) -> Complex {
        Complex { re: self.re.sub(&o.re), im: self.im.sub(&o.im) }
    }

    pub fn neg(&self) -> Complex {
        Complex { re: self.re.neg(), im: self.im.neg() }
    }

    pub fn conj(&self) -> Complex {
        Complex { re: self.re.clone(), im: self.im.neg() }
    }

    /// The product (operands of the same precision).
    pub fn mul(&self, o: &Complex) -> Complex {
        Complex { re: Real::fmma(&self.re, &o.re, &self.im, &o.im, true), im: Real::fmma(&self.re, &o.im, &self.im, &o.re, false) }
    }

    /// The product with a real of the same precision.
    pub fn mul_real(&self, x: &Real) -> Complex {
        Complex { re: self.re.mul(x), im: self.im.mul(x) }
    }

    /// The quotient (operands of the same precision), or `None` when
    /// dividing by zero.
    pub fn div(&self, o: &Complex) -> Option<Complex> {
        let bits = self.prec();
        if o.is_zero() {
            return None;
        }
        if o.im.is_zero() {
            return Some(Complex { re: self.re.div(&o.re)?, im: self.im.div(&o.re)? });
        }
        if o.re.is_zero() {
            return Some(Complex { re: self.im.div(&o.im)?, im: self.re.div(&o.im)?.neg() });
        }
        // (a + bi)/(c + di) = ((ac + bd) + (bc - ad)i)/(c^2 + d^2), exactly
        // when possible, then rounded.
        if let (Some(a), Some(b), Some(c), Some(d)) = (exact(&self.re), exact(&self.im), exact(&o.re), exact(&o.im)) {
            let n = &(&c * &c) + &(&d * &d);
            let re = (&(&a * &c) + &(&b * &d)).checked_div(&n)?;
            let im = (&(&b * &c) - &(&a * &d)).checked_div(&n)?;
            return Some(Complex { re: Real::from_rational(&re, bits), im: Real::from_rational(&im, bits) });
        }
        let (u, v) = (self.acb(), o.acb());
        let (re, im) = ball::eval_complex(bits, |out, wp| unsafe { sys::acb_div(out, u.ptr(), v.ptr(), wp) });
        Some(Complex { re, im })
    }

    /// `x^n` (not for `0^n` with `n < 0`).
    pub fn pow_integer(&self, n: &Integer) -> Complex {
        let bits = self.prec();
        if self.im.is_zero() && self.re.sign() > 0 {
            return Complex::from_real(self.re.pow_integer(n));
        }
        let u = self.acb();
        let mut e = Acb::new();
        unsafe { sys::acb_set_arb(e.mut_ptr(), Arb::from_integer(n).ptr()) };
        let (re, im) = ball::eval_complex(bits, |out, wp| unsafe { sys::acb_pow(out, u.ptr(), e.ptr(), wp) });
        Complex { re, im }
    }

    /// `x^y` on the principal branch (operands of the same precision).
    pub fn pow(&self, y: &Complex) -> Complex {
        let (u, v) = (self.acb(), y.acb());
        let (re, im) = ball::eval_complex(self.prec(), |out, wp| unsafe { sys::acb_pow(out, u.ptr(), v.ptr(), wp) });
        Complex { re, im }
    }

    /// An `acb` function, correctly rounded at the same precision.
    pub fn unary(&self, f: AcbUnary) -> Complex {
        let u = self.acb();
        let (re, im) = ball::eval_complex(self.prec(), |out, wp| unsafe { f(out, u.ptr(), wp) });
        Complex { re, im }
    }
}

impl PartialEq for Complex {
    fn eq(&self, o: &Complex) -> bool {
        self.re == o.re && self.im == o.im
    }
}

impl std::fmt::Debug for Complex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({:?}, {:?})", self.re, self.im)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn c(re: &str, im: &str, bits: u64) -> Complex {
        Complex::new(Real::parse(re, bits).unwrap(), Real::parse(im, bits).unwrap())
    }

    #[test]
    fn arithmetic() {
        let x = c("1.5", "2", 34);
        let y = c("-0.25", "3", 34);
        let p = x.mul(&y);
        assert_eq!((p.re.format(10), p.im.format(10)), ("-6.375000000".to_string(), "4.000000000".to_string()));
        let q = p.div(&y).unwrap();
        assert_eq!((q.re.format(10), q.im.format(10)), ("1.500000000".to_string(), "2.000000000".to_string()));
        let s = c("-4", "0", 100).unary(sys::acb_sqrt);
        assert_eq!((s.re.format(30), s.im.format(30)), ("0.000000000000000000000000000000".to_string(), "2.00000000000000000000000000000".to_string()));
        let w = c("1", "1", 100).pow_integer(&Integer::from_i64(8));
        assert_eq!((w.re.format(30), w.im.format(30)), ("16.0000000000000000000000000000".to_string(), "0.000000000000000000000000000000".to_string()));
        let e = c("0", "0", 100).unary(sys::acb_exp);
        assert_eq!(e.re.format(30), "1.00000000000000000000000000000");
    }
}
