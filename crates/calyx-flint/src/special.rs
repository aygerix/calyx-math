//! Special functions beyond MPFR and MPC (most of which Magma computes with
//! PARI): Bessel functions of real and complex order, the incomplete gamma
//! function, the complex gamma function and the confluent hypergeometric
//! function U, correctly rounded with FLINT's `arb_hypgeom` and
//! `acb_hypgeom` (see `ball`).

use std::os::raw::c_long;

use flint3_sys as sys;

use crate::ball::{self, Arb};
use crate::mpfr as m;
use crate::{Complex, Real};

/// FLINT's `ARF_PREC_EXACT`: exact arithmetic.
const EXACT: sys::slong = sys::slong::MAX;

/// The value of an `arb` expression of real arguments, correctly rounded
/// to `bits` (NaN if an argument is).
fn eval_arb<const N: usize>(bits: u64, args: [&Real; N], f: impl Fn(*mut sys::arb_struct, [*const sys::arb_struct; N], sys::slong)) -> Real {
    if args.iter().any(|x| x.is_nan()) {
        return Real::nan(bits);
    }
    let balls = args.map(Arb::from_real);
    ball::eval_real(bits, |out, wp| f(out, std::array::from_fn(|i| balls[i].ptr()), wp as sys::slong))
}

/// The value of an `acb` expression of complex arguments, correctly
/// rounded to `bits` in each part (NaN if an argument has a NaN part).
fn eval_acb<const N: usize>(bits: u64, args: [&Complex; N], f: impl Fn(*mut sys::acb_struct, [*const sys::acb_struct; N], sys::slong)) -> Complex {
    if args.iter().any(|z| z.re.is_nan() || z.im.is_nan()) {
        return Complex::nan(bits);
    }
    let balls = args.map(|z| z.acb());
    let (re, im) = ball::eval_complex(bits, |out, wp| f(out, std::array::from_fn(|i| balls[i].ptr()), wp as sys::slong));
    Complex { re, im }
}

impl Real {
    /// The Bessel function of the first kind J_n(x) of integer order (MPFR).
    pub fn bessel_jn(n: i64, x: &Real) -> Real {
        let mut r = Real::zero(x.prec());
        unsafe { m::mpfr_jn(r.raw_mut(), n as c_long, x.raw(), m::RNDN) };
        r
    }

    /// The Bessel function of the second kind Y_n(x) of order n ≥ 0: MPFR's
    /// for n < 2 and for the special values (NaN for x < 0, -infinity at
    /// 0), else by the forward recurrence `Y_(k+1) = (2k/x) Y_k - Y_(k-1)`,
    /// which is stable for Y (MPFR's `mpfr_yn` takes time quadratic in n).
    /// Where the value overflows, the infinity of its sign is returned at
    /// once for a large order (by Stirling's estimate), or where the
    /// recurrence leaves MPFR's exponent range for good.
    pub fn bessel_yn(n: i64, x: &Real) -> Real {
        let bits = x.prec();
        if n < 2 || !x.is_regular() || x.sign() < 0 {
            let mut r = Real::zero(bits);
            unsafe { m::mpfr_yn(r.raw_mut(), n as c_long, x.raw(), m::RNDN) };
            return r;
        }
        let (k, t) = (n as f64, x.to_f64());
        if k > 1e6 && t * t < k {
            // |Y_n(x)| ~ Γ(n)/π (2/x)^n, with Stirling's formula for Γ(n).
            let ln = (k - 0.5) * k.ln() - k + 0.5 * (2.0 * std::f64::consts::PI).ln() + k * (2.0 / t).ln() - std::f64::consts::PI.ln();
            if ln / std::f64::consts::LN_2 > (1u64 << 30) as f64 {
                return Real::infinity(bits, true);
            }
        }
        let emax = unsafe { m::mpfr_get_emax() };
        let z = Arb::from_real(x);
        let mut last = Arb::new();
        for wp in ball::precisions(bits) {
            let w = wp as sys::slong;
            let (mut a, mut b, mut c, mut u) = (Arb::new(), Arb::new(), Arb::new(), Arb::new());
            unsafe {
                // a = Y_0(x) (c is 0), b = Y_1(x), c = 2/x.
                sys::arb_hypgeom_bessel_y(a.mut_ptr(), c.ptr(), z.ptr(), w);
                sys::arb_one(c.mut_ptr());
                sys::arb_hypgeom_bessel_y(b.mut_ptr(), c.ptr(), z.ptr(), w);
                sys::arb_ui_div(c.mut_ptr(), 2, z.ptr(), w);
                for j in 1..n {
                    sys::arb_mul_si(u.mut_ptr(), c.ptr(), j as c_long, w);
                    sys::arb_mul(u.mut_ptr(), u.ptr(), b.ptr(), w);
                    sys::arb_sub(a.mut_ptr(), u.ptr(), a.ptr(), w);
                    std::mem::swap(&mut a, &mut b);
                    // Beyond k = x, |Y_k| grows with k.
                    if j as f64 > 2.0 * t + 2.0 && sys::arf_cmpabs_2exp_si(&b.0.mid, emax + 1) > 0 {
                        return Real::infinity(bits, sys::arf_sgn(&b.0.mid) < 0);
                    }
                }
            }
            if let Some(r) = b.rounded(bits) {
                return r;
            }
            last = b;
        }
        last.mid(bits)
    }

    /// The Bessel function of the first kind J_ν(x) of real order ν, at the
    /// given precision.
    pub fn bessel_j(nu: &Real, x: &Real, bits: u64) -> Real {
        eval_arb(bits, [nu, x], |out, [nu, x], wp| unsafe { sys::arb_hypgeom_bessel_j(out, nu, x, wp) })
    }

    /// The Bessel function of the first kind of order ν + 1/2, J_(ν+1/2)(x),
    /// at the given precision (with ν + 1/2 exact).
    pub fn bessel_j_half(nu: &Real, x: &Real, bits: u64) -> Real {
        eval_arb(bits, [nu, x], |out, [nu, x], wp| unsafe {
            let mut h = Arb::new();
            sys::arb_set_d(h.mut_ptr(), 0.5);
            sys::arb_add(h.mut_ptr(), h.ptr(), nu, EXACT);
            sys::arb_hypgeom_bessel_j(out, h.ptr(), x, wp);
        })
    }

    /// The modified Bessel function of the second kind K_ν(x) of real order
    /// ν, for x > 0, at the given precision.
    pub fn bessel_k(nu: &Real, x: &Real, bits: u64) -> Real {
        eval_arb(bits, [nu, x], |out, [nu, x], wp| unsafe { sys::arb_hypgeom_bessel_k(out, nu, x, wp) })
    }

    /// The lower incomplete gamma function `γ(s, x) = ∫_0^x u^(s-1) e^-u du`,
    /// or with `upper` the upper one, `Γ(s, x) = ∫_x^∞ u^(s-1) e^-u du`.
    pub fn incomplete_gamma(s: &Real, x: &Real, upper: bool, bits: u64) -> Real {
        eval_arb(bits, [s, x], |out, [s, x], wp| unsafe {
            if upper {
                sys::arb_hypgeom_gamma_upper(out, s, x, 0, wp);
            } else {
                sys::arb_hypgeom_gamma_lower(out, s, x, 0, wp);
            }
        })
    }

    /// `Γ(x + 1/2)`, with `x + 1/2` exact.
    pub fn gamma_half(&self) -> Real {
        eval_arb(self.prec(), [self], |out, [x], wp| unsafe {
            sys::arb_set_d(out, 0.5);
            sys::arb_add(out, out, x, EXACT);
            sys::arb_gamma(out, out, wp);
        })
    }

    /// The confluent hypergeometric function U(a, b, x), at the given
    /// precision.
    pub fn hypergeometric_u(a: &Real, b: &Real, x: &Real, bits: u64) -> Real {
        eval_arb(bits, [a, b, x], |out, [a, b, x], wp| unsafe { sys::arb_hypgeom_u(out, a, b, x, wp) })
    }
}

impl Complex {
    /// The gamma function (not at its poles).
    pub fn gamma(&self) -> Complex {
        self.unary(sys::acb_gamma)
    }

    /// The principal branch of the logarithm of the gamma function,
    /// `log(Γ(z))`: its imaginary part is in (-π, π], and π where Γ(z) is
    /// real and negative.
    pub fn log_gamma(&self) -> Complex {
        eval_acb(self.prec(), [self], |out, [z], wp| unsafe {
            sys::acb_gamma(out, z, wp);
            sys::acb_log(out, out, wp);
        })
    }

    /// The logarithmic derivative of the gamma function.
    pub fn digamma(&self) -> Complex {
        self.unary(sys::acb_digamma)
    }

    /// The modified Bessel function of the second kind K_ν(z) of complex
    /// order ν, at the given precision.
    pub fn bessel_k(nu: &Complex, z: &Complex, bits: u64) -> Complex {
        eval_acb(bits, [nu, z], |out, [nu, z], wp| unsafe { sys::acb_hypgeom_bessel_k(out, nu, z, wp) })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Integer, Rational};

    const BITS: u64 = 67;

    fn q(n: i64, d: i64) -> Real {
        Real::from_rational(&Rational::new(&Integer::from_i64(n), &Integer::from_i64(d)).unwrap(), BITS)
    }

    fn m(x: &Real) -> String {
        x.mantissa_exponent().0.to_string()
    }

    /// Correctly rounded values (mantissas at 67 bits), checked with mpmath.
    #[test]
    fn real_functions() {
        let (x, w, y, t) = (q(2, 3), q(5, 2), q(-7, 3), q(1, 3));
        let cases = [
            (Real::bessel_j(&t, &w, BITS), "117068016103432191703"),
            (Real::bessel_j(&w, &x, BITS), "88296645898214865911"),
            (Real::bessel_j(&w.neg(), &w, BITS), "84505361670900632437"),
            (Real::bessel_j_half(&t, &w, BITS), "133488999058309604076"),
            (Real::bessel_j_half(&q(2, 1), &w, BITS), "96835492821726360557"),
            (Real::bessel_j_half(&q(30, 1), &w, BITS), "109298953865934878290"),
            (Real::bessel_k(&t, &w, BITS), "75017787278180480359"),
            (Real::bessel_k(&q(5, 1), &q(1, 10), BITS), "84389738436139216849"),
            (Real::incomplete_gamma(&x, &w, false, BITS), "95869897387619305965"),
            (Real::incomplete_gamma(&x, &w, true, BITS), "129483869096053118969"),
            (Real::incomplete_gamma(&q(5, 1), &q(1, 1), false, BITS), "103698827939308539299"),
            (Real::incomplete_gamma(&q(-1, 2), &w, true, BITS), "132002589024306445424"),
            (Real::incomplete_gamma(&y, &w, false, BITS), "-96481520408512263901"),
            (Real::incomplete_gamma(&q(100, 1), &q(90, 1), true, BITS), "135105709652976039305"),
            (x.gamma_half(), "136907208957645599622"),
            (y.gamma_half(), "134417986976597497817"),
            (Real::hypergeometric_u(&x, &w, &t, BITS), "92543722146555011335"),
        ];
        for (i, (v, s)) in cases.iter().enumerate() {
            assert_eq!(m(v), *s, "case {i}");
        }
    }

    /// The recurrence for Y_n agrees with MPFR's `mpfr_yn`.
    #[test]
    fn bessel_y_recurrence() {
        for x in [q(1, 1000), q(5, 2), q(1000, 3)] {
            for n in [2, 3, 10, 57, 300] {
                let mut r = Real::zero(BITS);
                unsafe { m::mpfr_yn(r.raw_mut(), n as c_long, x.raw(), m::RNDN) };
                assert_eq!(m(&Real::bessel_yn(n, &x)), m(&r), "Y_{n}({})", x.to_f64());
            }
        }
    }

    #[test]
    fn complex_functions() {
        let c = |re: Real, im: Real| Complex::new(re, im);
        let r = |x: Real| Complex::from_real(x);
        let cm = |z: &Complex| (m(&z.re), m(&z.im));
        let (x, w) = (q(2, 3), q(5, 2));
        let cases = [
            (Complex::bessel_k(&c(q(1, 3), q(1, 2)), &r(w.clone()), BITS), "143539975133749528030", "131290557004311676703"),
            // The principal branch of log Γ.
            (c(q(-5, 2), q(1, 100)).log_gamma(), "-133927724748359366348", "-115497317699434653640"),
            (c(q(3, 2), q(1000000, 1)).log_gamma(), "-110533928030765684019", "96011714591178577713"),
            (r(q(-1, 2)).log_gamma(), "93378313056391890986", "115904311329233965478"),
        ];
        for (i, (v, re, im)) in cases.iter().enumerate() {
            assert_eq!(cm(v), (re.to_string(), im.to_string()), "case {i}");
        }
    }
}
