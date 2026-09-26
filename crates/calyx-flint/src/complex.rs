//! Complex numbers as pairs of MPFR reals of the same precision. Each part
//! of a result is rounded correctly, as with MPC: arithmetic uses MPFR (or
//! exact rationals), other functions FLINT's `acb` with `ball`'s rounding.

use flint3_sys as sys;

use crate::ball::{self, Acb};
use crate::{Rational, Real};

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

    /// `x^n` as Magma computes it: by binary powering from the lowest bit,
    /// each product rounded, after inverting `x` when `n < 0` (not for
    /// `0^n` with `n < 0`).
    pub fn pow_i64(&self, n: i64) -> Complex {
        let one = Complex::from_real(Real::from_i64(1, self.prec()));
        let mut base = if n < 0 { one.div(self).unwrap_or_else(|| self.clone()) } else { self.clone() };
        let mut k = n.unsigned_abs();
        let mut acc: Option<Complex> = None;
        while k != 0 {
            if k & 1 == 1 {
                acc = Some(match acc {
                    None => base.clone(),
                    Some(a) => a.mul(&base),
                });
            }
            k >>= 1;
            if k != 0 {
                base = base.mul(&base);
            }
        }
        acc.unwrap_or(one)
    }

    /// `x^y` on the principal branch (operands of the same precision).
    pub fn pow(&self, y: &Complex) -> Complex {
        if self.is_zero() {
            return self.pow_zero(y);
        }
        if self.im.is_zero() && self.im.is_sign_negative() {
            return self.conj().pow(&y.conj()).conj();
        }
        let (u, v) = (self.acb(), y.acb());
        let (re, im) = ball::eval_complex(self.prec(), |out, wp| unsafe { sys::acb_pow(out, u.ptr(), v.ptr(), wp) });
        Complex { re, im }
    }

    /// `0^y` as `exp(y·log 0)` with IEEE arithmetic on the special values
    /// (so `0^0` is NaN, as in Magma).
    fn pow_zero(&self, y: &Complex) -> Complex {
        let bits = self.prec();
        let (l_re, l_im) = (Real::infinity(bits, true), self.arg());
        let re = y.re.mul(&l_re).sub(&y.im.mul(&l_im));
        let im = y.re.mul(&l_im).add(&y.im.mul(&l_re));
        Complex { re, im }.exp_special()
    }

    /// `exp` of a number with a non-finite part, following C99.
    fn exp_special(&self) -> Complex {
        let bits = self.prec();
        let (x, y) = (&self.re, &self.im);
        if x.is_nan() {
            return Complex { re: Real::nan(bits), im: if y.is_zero() { y.clone() } else { Real::nan(bits) } };
        }
        if x.is_inf() && x.is_sign_negative() {
            if !y.is_finite() {
                return Complex { re: Real::zero(bits), im: Real::zero(bits) };
            }
            let (s, c) = y.sin_cos();
            return Complex { re: Real::signed_zero(bits, c.is_sign_negative()), im: Real::signed_zero(bits, s.is_sign_negative()) };
        }
        if x.is_inf() {
            if y.is_zero() {
                return self.clone();
            }
            if !y.is_finite() {
                return Complex { re: x.clone(), im: Real::nan(bits) };
            }
            let (s, c) = y.sin_cos();
            return Complex { re: Real::infinity(bits, c.is_sign_negative()), im: Real::infinity(bits, s.is_sign_negative()) };
        }
        if !y.is_finite() {
            return Complex { re: Real::nan(bits), im: Real::nan(bits) };
        }
        self.unary(sys::acb_exp)
    }

    /// An `acb` function, correctly rounded at the same precision. The
    /// function must commute with complex conjugation: on a branch cut, a
    /// negative zero imaginary part selects the limit from below, as in MPC.
    pub fn unary(&self, f: AcbUnary) -> Complex {
        self.symmetric(|z| {
            let u = z.acb();
            let (re, im) = ball::eval_complex(z.prec(), |out, wp| unsafe { f(out, u.ptr(), wp) });
            Complex { re, im }
        })
    }

    /// `f(self)` for a function with `f(conj z) = conj f(z)`, evaluated at
    /// `conj(self)` when the imaginary part is -0 (balls have no signed
    /// zeros).
    fn symmetric(&self, f: impl Fn(&Complex) -> Complex) -> Complex {
        if self.im.is_zero() && self.im.is_sign_negative() {
            f(&self.conj()).conj()
        } else {
            f(self)
        }
    }

    /// The modulus `|x|`.
    pub fn abs(&self) -> Real {
        self.re.binary(&self.im, crate::mpfr::mpfr_hypot)
    }

    /// The argument in `[-pi, pi]` (`atan2(im, re)`, with signed zeros).
    pub fn arg(&self) -> Real {
        self.im.binary(&self.re, crate::mpfr::mpfr_atan2)
    }

    /// The norm `re^2 + im^2`, rounded once.
    pub fn norm(&self) -> Real {
        Real::fmma(&self.re, &self.re, &self.im, &self.im, false)
    }

    /// The principal square root, as MPC's `mpc_sqrt`.
    pub fn sqrt(&self) -> Complex {
        if self.im.is_zero() && self.re.is_finite() {
            // On the real axis: exact signs as in MPC.
            let bits = self.prec();
            let neg = self.im.is_sign_negative();
            return if self.re.is_sign_negative() && !self.re.is_zero() {
                let s = self.re.neg().sqrt();
                Complex { re: Real::zero(bits), im: if neg { s.neg() } else { s } }
            } else {
                Complex { re: self.re.sqrt().abs(), im: self.im.clone() }
            };
        }
        self.unary(sys::acb_sqrt)
    }

    /// The principal `n`-th root (`n > 0`).
    pub fn root(&self, n: u64) -> Complex {
        if n == 1 {
            return self.clone();
        }
        if n == 2 {
            return self.sqrt();
        }
        self.symmetric(|z| {
            let u = z.acb();
            let (re, im) = ball::eval_complex(z.prec(), |out, wp| unsafe { sys::acb_root_ui(out, u.ptr(), n as _, wp) });
            Complex { re, im }
        })
    }

    /// `m·(cos a + i sin a)`, with the cosine and sine rounded first (both
    /// of the same precision).
    pub fn polar(m: &Real, a: &Real) -> Complex {
        let (s, c) = a.sin_cos();
        Complex { re: m.mul(&c), im: m.mul(&s) }
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
        let w = c("1", "1", 100).pow_i64(8);
        assert_eq!((w.re.format(30), w.im.format(30)), ("16.0000000000000000000000000000".to_string(), "-0.000000000000000000000000000000".to_string()));
        let e = c("0", "0", 100).unary(sys::acb_exp);
        assert_eq!(e.re.format(30), "1.00000000000000000000000000000");
    }

    /// Exact results from Magma 2.22 (mantissas at 67 bits).
    #[test]
    fn magma_rounding() {
        let bits = 67;
        let q = |n: i64, d: i64| Real::from_rational(&Rational::new(&crate::Integer::from_i64(n), &crate::Integer::from_i64(d)).unwrap(), bits);
        let m = |x: &Real| x.mantissa_exponent().0.to_string();
        let z = Complex::new(q(1, 3), q(-2, 5));
        // Integer powers: binary powering from the lowest bit.
        let w = z.pow_i64(6);
        assert_eq!((m(&w.re), m(&w.im)), ("97401445201859310371".into(), "80520429590381782685".into()));
        let w = z.pow_i64(-7);
        assert_eq!((m(&w.re), m(&w.im)), ("109857224418120119442".into(), "-133526673318191595649".into()));
        // Correctly rounded powers, division, square roots and cube roots.
        let w = z.pow(&z);
        assert_eq!((m(&w.re), m(&w.im)), ("83587055924703889108".into(), "-82875433993545740596".into()));
        let w = Complex::new(q(3, 7), q(5, 11)).div(&Complex::new(q(-2, 13), q(1, 17))).unwrap();
        assert_eq!((m(&w.re), m(&w.im)), ("-106608349078100617498".into(), "-129384495620273538027".into()));
        let w = z.sqrt();
        assert_eq!((m(&w.re), m(&w.im)), ("96433488850468828742".into(), "-90334060262859331992".into()));
        let w = z.root(3);
        assert_eq!((m(&w.re), m(&w.im)), ("113696643534188528275".into(), "-136714887982540844371".into()));
        let w = Complex::polar(&q(3, 2), &q(-9, 11));
        assert_eq!((m(&w.re), m(&w.im)), ("75655568931853481210".into(), "-80786138035874390898".into()));
        assert_eq!((m(&z.norm()), m(&z.abs()), m(&z.arg())), ("80017876515291210565".into(), "76839294359052279000".into(), "-129283349224782136303".into()));
        // 0^0 is NaN, 0^-1 is infinite.
        let zero = Complex::new(Real::zero(bits), Real::zero(bits));
        let w = zero.pow(&zero);
        assert!(w.re.is_nan() && w.im.is_nan());
        let w = zero.pow(&Complex::from_real(Real::from_i64(-1, bits)));
        assert!(w.re.is_inf() && w.im.is_nan());
    }
}
