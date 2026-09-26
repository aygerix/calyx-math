//! Complex numbers as pairs of MPFR reals of the same precision. Each part
//! of a result is rounded correctly, as with MPC: arithmetic uses MPFR (or
//! exact rationals), other functions FLINT's `acb` with `ball`'s rounding.

use flint3_sys as sys;

use crate::ball::{self, Acb, Arb};
use crate::mpfr as m;
use crate::{Rational, Real};

#[derive(Clone)]
pub struct Complex {
    pub re: Real,
    pub im: Real,
}

/// An `acb` function of one argument.
pub type AcbUnary = unsafe extern "C" fn(*mut sys::acb_struct, *const sys::acb_struct, sys::slong);

/// The elementary functions of a complex variable (those of MPC).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Elementary {
    Exp,
    Log,
    Sin,
    Cos,
    Tan,
    Sinh,
    Cosh,
    Tanh,
    Asin,
    Acos,
    Atan,
    Asinh,
    Acosh,
    Atanh,
}

/// Zagier's modified polylogarithms, with `Re_m` the real part for odd
/// `m` and the imaginary part for even `m`, and `l = log|z|`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ModifiedPolylog {
    /// `D~_m(z) = Re_m(Σ_{k<m} (-l)^k/k! Li_{m-k}(z) + (-l)^(m-1)/m! log|1-z|)`.
    DTilde,
    /// `D_m(z) = Re_m(Σ_{k<m} (-l)^k/k! Li_{m-k}(z) - (-l)^m/(2·m!))`.
    D,
    /// `P_m(z) = Re_m(Σ_{k<m} 2^k B_k/k! l^k Li_{m-k}(z) - 2^(m-1) B_m/m! l^m)`.
    P,
}

/// `|v|` with the sign bit `neg`.
fn signed(v: Real, neg: bool) -> Real {
    if v.is_sign_negative() != neg { v.neg() } else { v }
}

/// `atanh(1/x)` for an exact `x` with `|x| > 1`, correctly rounded.
fn atanh_inv(x: &Real) -> Real {
    let a = Arb::from_real(x);
    let mut t = Arb::new();
    ball::eval_real(x.prec(), |out, wp| unsafe {
        sys::arb_inv(t.mut_ptr(), a.ptr(), wp);
        sys::arb_atanh(out, t.ptr(), wp);
    })
}

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

    pub fn nan(prec: u64) -> Complex {
        Complex { re: Real::nan(prec), im: Real::nan(prec) }
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

    pub(crate) fn acb(&self) -> Acb {
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
        // By a real or imaginary number, as MPC: zero parts get the signs
        // of `(ac + bd) + (bc - ad)i` over `c^2 + d^2`.
        let (sa, sb, sc, sd) = (self.re.is_sign_negative(), self.im.is_sign_negative(), o.re.is_sign_negative(), o.im.is_sign_negative());
        let fix = |x: Real, neg: bool| if x.is_zero() { Real::signed_zero(bits, neg) } else { x };
        if o.im.is_zero() || o.re.is_zero() {
            let (re, im) = if o.im.is_zero() { (self.re.div(&o.re)?, self.im.div(&o.re)?) } else { (self.im.div(&o.im)?, self.re.div(&o.im)?.neg()) };
            return Some(Complex { re: fix(re, sa != sc && sb != sd), im: fix(im, sb != sc && sa == sd) });
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

    /// An elementary function, rounded correctly in each part as by MPC. On
    /// the axes the parts are computed from real functions, with MPC's
    /// signed zeros and its values on the branch cuts (as in Magma, which
    /// uses MPC 0.8: `atan(±i)` has a NaN real part). Arguments with a NaN
    /// or infinite part give NaN, except for `exp` and `log`.
    pub fn elementary(&self, f: Elementary) -> Complex {
        use Elementary::*;
        let bits = self.prec();
        if !self.re.is_finite() || !self.im.is_finite() {
            return match f {
                Exp => self.exp_special(),
                Log => Complex { re: self.abs().unary(m::mpfr_log), im: self.arg() },
                _ => Complex::nan(bits),
            };
        }
        if self.im.is_zero() {
            return self.on_real_axis(f);
        }
        if self.re.is_zero() {
            return self.on_imaginary_axis(f);
        }
        let g: AcbUnary = match f {
            Exp => sys::acb_exp,
            Log => sys::acb_log,
            Sin => sys::acb_sin,
            Cos => sys::acb_cos,
            Tan => sys::acb_tan,
            Sinh => sys::acb_sinh,
            Cosh => sys::acb_cosh,
            Tanh => sys::acb_tanh,
            Asin => sys::acb_asin,
            Acos => sys::acb_acos,
            Atan => sys::acb_atan,
            Asinh => sys::acb_asinh,
            Acosh => sys::acb_acosh,
            Atanh => sys::acb_atanh,
        };
        let u = self.acb();
        let (re, im) = ball::eval_complex(bits, |out, wp| unsafe { g(out, u.ptr(), wp) });
        Complex { re, im }
    }

    /// `f(x ± 0i)`: the signs of zero parts are those of the usual
    /// formulas (`sin(x + iy) = sin x cosh y + i cos x sinh y`, ...)
    /// evaluated with signed zeros.
    fn on_real_axis(&self, f: Elementary) -> Complex {
        use Elementary::*;
        let (x, bits) = (&self.re, self.prec());
        let (sx, sy) = (x.is_sign_negative(), self.im.is_sign_negative());
        let z = |neg: bool| Real::signed_zero(bits, neg);
        let r = |g: m::Unary| x.unary(g);
        let pi = || Real::constant(m::mpfr_const_pi, bits);
        let one = Real::from_i64(1, bits);
        let (re, im) = match f {
            Exp => (r(m::mpfr_exp), z(sy)),
            Log => (x.abs().unary(m::mpfr_log), self.arg()),
            Sin => {
                let (s, c) = x.sin_cos();
                (s, z(c.is_sign_negative() != sy))
            }
            Cos => {
                let (s, c) = x.sin_cos();
                (c, z(s.is_sign_negative() == sy))
            }
            Tan => (r(m::mpfr_tan), z(sy)),
            Sinh => (r(m::mpfr_sinh), z(sy)),
            Cosh => (r(m::mpfr_cosh), z(sx != sy)),
            Tanh => (r(m::mpfr_tanh), z(sy)),
            Asin if x.cmp_abs(&one).is_le() => (r(m::mpfr_asin), z(sy)),
            Asin => (signed(pi().mul_2exp(-1), sx), signed(x.abs().unary(m::mpfr_acosh), sy)),
            Acos if x.cmp_abs(&one).is_le() => (r(m::mpfr_acos), z(!sy)),
            Acos => (if sx { pi() } else { z(false) }, signed(x.abs().unary(m::mpfr_acosh), !sy)),
            Atan => (r(m::mpfr_atan), z(sy)),
            Asinh => (r(m::mpfr_asinh), z(sy)),
            Acosh if x.cmp_magma(&one).is_ge() => (r(m::mpfr_acosh), z(sy)),
            Acosh if x.cmp_abs(&one).is_lt() => (z(false), signed(r(m::mpfr_acos), sy)),
            Acosh => (x.abs().unary(m::mpfr_acosh), signed(pi(), sy)),
            Atanh => match x.cmp_abs(&one) {
                std::cmp::Ordering::Less => (r(m::mpfr_atanh), z(sy)),
                std::cmp::Ordering::Greater => (atanh_inv(x), signed(pi().mul_2exp(-1), sy)),
                std::cmp::Ordering::Equal => (Real::infinity(bits, sx), Real::nan(bits)),
            },
        };
        Complex { re, im }
    }

    /// `f(±0 + iy)` for `y ≠ 0`, as `on_real_axis`.
    fn on_imaginary_axis(&self, f: Elementary) -> Complex {
        use Elementary::*;
        let (y, bits) = (&self.im, self.prec());
        let (sx, sy) = (self.re.is_sign_negative(), y.is_sign_negative());
        let z = |neg: bool| Real::signed_zero(bits, neg);
        let r = |g: m::Unary| y.unary(g);
        let half_pi = || Real::constant(m::mpfr_const_pi, bits).mul_2exp(-1);
        let one = Real::from_i64(1, bits);
        let (re, im) = match f {
            Exp => {
                let (s, c) = y.sin_cos();
                (c, s)
            }
            Log => (y.abs().unary(m::mpfr_log), self.arg()),
            Sin => (z(sx), r(m::mpfr_sinh)),
            Cos => (r(m::mpfr_cosh), z(sx == sy)),
            Tan => (z(sx), r(m::mpfr_tanh)),
            Sinh => {
                let (s, c) = y.sin_cos();
                (z(sx != c.is_sign_negative()), s)
            }
            Cosh => {
                let (s, c) = y.sin_cos();
                (c, z(sx != s.is_sign_negative()))
            }
            Tanh => (z(sx), r(m::mpfr_tan)),
            Asin => (z(sx), r(m::mpfr_asinh)),
            Acos => (half_pi(), r(m::mpfr_asinh).neg()),
            Atan => match y.cmp_abs(&one) {
                std::cmp::Ordering::Less => (z(sx), r(m::mpfr_atanh)),
                std::cmp::Ordering::Greater => (signed(half_pi(), sx), atanh_inv(y)),
                std::cmp::Ordering::Equal => (Real::nan(bits), Real::infinity(bits, sy)),
            },
            Asinh if y.cmp_abs(&one).is_le() => (z(sx), r(m::mpfr_asin)),
            Asinh => (signed(y.abs().unary(m::mpfr_acosh), sx), signed(half_pi(), sy)),
            Acosh => (y.abs().unary(m::mpfr_asinh), signed(half_pi(), sy)),
            Atanh => (z(sx), r(m::mpfr_atan)),
        };
        Complex { re, im }
    }

    /// The polylogarithm `Li_s(z)` for an integer `s`, on the principal
    /// branch; on the cut `(1, ∞)` the limit from below (as PARI).
    pub fn polylog(&self, s: i64) -> Complex {
        let bits = self.prec();
        if !self.re.is_finite() || !self.im.is_finite() {
            return Complex::nan(bits);
        }
        let real = self.im.is_zero();
        let u = self.acb();
        let (re, _) = ball::eval_complex(bits, |out, wp| unsafe {
            sys::acb_polylog_si(out, s as sys::slong, u.ptr(), wp);
            if real {
                // Li_s is real on (-∞, 1), and its real part is continuous
                // across the cut.
                sys::arb_zero(&mut (*out).imag);
            }
        });
        if !real {
            let (re, im) = ball::eval_complex(bits, |out, wp| unsafe { sys::acb_polylog_si(out, s as sys::slong, u.ptr(), wp) });
            return Complex { re, im };
        }
        if s < 1 || self.re.cmp_magma(&Real::from_i64(1, bits)).is_le() {
            return Complex::from_real(re);
        }
        // Below the cut the imaginary part is -pi log(x)^(s-1)/(s-1)!.
        let a = Arb::from_real(&self.re);
        let mut t = Arb::new();
        let im = ball::eval_real(bits, |out, wp| unsafe {
            sys::arb_log(out, a.ptr(), wp);
            sys::arb_pow_ui(out, out, (s - 1) as _, wp);
            sys::arb_const_pi(t.mut_ptr(), wp);
            sys::arb_mul(out, out, t.ptr(), wp);
            sys::arb_fac_ui(t.mut_ptr(), (s - 1) as _, wp);
            sys::arb_div(out, out, t.ptr(), wp);
            sys::arb_neg(out, out);
        });
        Complex { re, im }
    }

    /// One of Zagier's modified polylogarithms (PARI's `polylog(m, z,
    /// flag)`), for `m >= 1`.
    pub fn modified_polylog(&self, m: u64, f: ModifiedPolylog) -> Real {
        let bits = self.prec();
        if !self.re.is_finite() || !self.im.is_finite() {
            return Real::nan(bits);
        }
        let odd = m % 2 == 1;
        // For real z, Re_m is the imaginary part of a real number for even
        // m; and D~_1 vanishes.
        if (self.im.is_zero() && !odd) || (m == 1 && f == ModifiedPolylog::DTilde) {
            return Real::zero(bits);
        }
        if self.is_zero() {
            return if m == 1 { Real::infinity(bits, true) } else { Real::zero(bits) };
        }
        if self.im.is_zero() && self.re.cmp_magma(&Real::from_i64(1, bits)).is_eq() {
            // log|z| = 0: the value is Li_m(1) = zeta(m).
            return if m == 1 { Real::infinity(bits, false) } else { Real::from_i64(m as i64, bits).unary(m::mpfr_zeta) };
        }
        let u = self.acb();
        let (mut l, mut c, mut t, mut e) = (Arb::new(), Arb::new(), Arb::new(), Arb::new());
        let (mut sum, mut li) = (Acb::new(), Acb::new());
        ball::eval_real(bits, |out, wp| unsafe {
            // l = log|z|, sum = Σ c_k Li_{m-k}(z).
            sys::acb_abs(l.mut_ptr(), u.ptr(), wp);
            sys::arb_log(l.mut_ptr(), l.ptr(), wp);
            sys::acb_zero(sum.mut_ptr());
            for k in 0..m {
                match f {
                    ModifiedPolylog::DTilde | ModifiedPolylog::D => sys::arb_neg(c.mut_ptr(), l.ptr()),
                    ModifiedPolylog::P => {
                        if k > 1 && k % 2 == 1 {
                            continue;
                        }
                        sys::arb_mul_2exp_si(c.mut_ptr(), l.ptr(), 1);
                    }
                }
                sys::arb_pow_ui(c.mut_ptr(), c.ptr(), k, wp);
                if f == ModifiedPolylog::P {
                    sys::arb_bernoulli_ui(t.mut_ptr(), k, wp);
                    sys::arb_mul(c.mut_ptr(), c.ptr(), t.ptr(), wp);
                }
                sys::arb_fac_ui(t.mut_ptr(), k, wp);
                sys::arb_div(c.mut_ptr(), c.ptr(), t.ptr(), wp);
                sys::acb_polylog_si(li.mut_ptr(), (m - k) as sys::slong, u.ptr(), wp);
                sys::acb_mul_arb(li.mut_ptr(), li.ptr(), c.ptr(), wp);
                sys::acb_add(sum.mut_ptr(), sum.ptr(), li.ptr(), wp);
            }
            if !odd {
                sys::arb_set(out, &sum.0.imag);
                return;
            }
            // The real term: e.
            sys::arb_fac_ui(t.mut_ptr(), m, wp);
            match f {
                ModifiedPolylog::DTilde => {
                    // (-l)^(m-1)/m! log|1 - z|
                    sys::arb_neg(e.mut_ptr(), l.ptr());
                    sys::arb_pow_ui(e.mut_ptr(), e.ptr(), m - 1, wp);
                    sys::arb_div(e.mut_ptr(), e.ptr(), t.ptr(), wp);
                    sys::acb_sub_ui(li.mut_ptr(), u.ptr(), 1, wp);
                    sys::acb_abs(c.mut_ptr(), li.ptr(), wp);
                    sys::arb_log(c.mut_ptr(), c.ptr(), wp);
                    sys::arb_mul(e.mut_ptr(), e.ptr(), c.ptr(), wp);
                }
                ModifiedPolylog::D => {
                    // -(-l)^m/(2 m!)
                    sys::arb_neg(e.mut_ptr(), l.ptr());
                    sys::arb_pow_ui(e.mut_ptr(), e.ptr(), m, wp);
                    sys::arb_div(e.mut_ptr(), e.ptr(), t.ptr(), wp);
                    sys::arb_mul_2exp_si(e.mut_ptr(), e.ptr(), -1);
                    sys::arb_neg(e.mut_ptr(), e.ptr());
                }
                ModifiedPolylog::P => {
                    // -2^(m-1) B_m/m! l^m
                    sys::arb_pow_ui(e.mut_ptr(), l.ptr(), m, wp);
                    sys::arb_div(e.mut_ptr(), e.ptr(), t.ptr(), wp);
                    sys::arb_bernoulli_ui(c.mut_ptr(), m, wp);
                    sys::arb_mul(e.mut_ptr(), e.ptr(), c.ptr(), wp);
                    sys::arb_mul_2exp_si(e.mut_ptr(), e.ptr(), m as sys::slong - 1);
                    sys::arb_neg(e.mut_ptr(), e.ptr());
                }
            }
            sys::arb_add(out, &sum.0.real, e.ptr(), wp);
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

    /// Transcendental functions: exact results from Magma 2.22 (mantissas at
    /// 67 bits), and MPC's signed zeros on the axes.
    #[test]
    fn transcendental() {
        use Elementary::*;
        let bits = 67;
        let q = |n: i64, d: i64| Real::from_rational(&Rational::new(&crate::Integer::from_i64(n), &crate::Integer::from_i64(d)).unwrap(), bits);
        let m = |x: &Real| x.mantissa_exponent().0.to_string();
        let z = Complex::new(q(1, 3), q(-2, 5));
        let cases = [
            (Exp, "94849038315112340942", "-80203060406931155807"),
            (Log, "-96308719621095169924", "-129283349224782136303"),
            (Tan, "85955184471525343224", "-123449290619052677102"),
            (Asin, "92187752155515620976", "-120671674953283356515"),
            (Acos, "92857373290355060234", "120671674953283356515"),
            (Atanh, "85960894539975326120", "-122763272881683625951"),
        ];
        for (f, re, im) in cases {
            let w = z.elementary(f);
            assert_eq!((m(&w.re), m(&w.im)), (re.to_string(), im.to_string()), "{f:?}");
        }
        let w = z.polylog(2);
        assert_eq!((m(&w.re), m(&w.im)), ("89487221628671051911".into(), "-138980147135785638646".into()));
        let w = z.polylog(3);
        assert_eq!((m(&w.re), m(&w.im)), ("94913116608086734809".into(), "-128428375072755954880".into()));
        assert_eq!(m(&z.modified_polylog(2, ModifiedPolylog::DTilde)), "-121537183697224874066");
        assert_eq!(m(&z.modified_polylog(3, ModifiedPolylog::DTilde)), "81930621254249355953");
        // Signs of zero parts, and sides of the branch cuts.
        let s = |x: &Real| if x.is_sign_negative() { -1 } else { 1 };
        let signs = |w: Complex| (s(&w.re), s(&w.im));
        let two = Complex::from_real(Real::from_i64(2, bits));
        let pole = Complex::new(Real::from_i64(-2, bits), Real::signed_zero(bits, true));
        assert_eq!(signs(two.elementary(Sin)), (1, -1));
        assert_eq!(signs(two.conj().elementary(Cos)), (-1, 1));
        assert_eq!(signs(two.elementary(Asin)), (1, 1));
        assert_eq!(signs(two.conj().elementary(Asin)), (1, -1));
        assert_eq!(signs(two.elementary(Acos)), (1, -1));
        assert_eq!(signs(pole.elementary(Log)), (1, -1));
        assert_eq!(signs(pole.elementary(Acosh)), (1, -1));
        let i2 = Complex::new(Real::zero(bits), Real::from_i64(2, bits));
        assert_eq!(signs(i2.elementary(Sinh)), (-1, 1));
        assert_eq!(signs(i2.elementary(Atan)), (1, 1));
        assert_eq!(signs(i2.neg().elementary(Atan)), (-1, -1));
        // 1/(cos 2 - 0i): MPC's signs of zeros in a division.
        let one = Complex::from_real(Real::from_i64(1, bits));
        assert_eq!(signs(one.div(&two.elementary(Cos)).unwrap()), (-1, 1));
        // Below the cut: Li_2(2) = pi^2/4 - i pi log 2.
        let w = two.polylog(2);
        assert_eq!((w.re.format(15), w.im.format(15)), ("2.46740110027234".to_string(), "-2.17758609030360".to_string()));
        assert!(Complex::from_real(q(1, 2)).polylog(3).im.is_zero());
    }
}
