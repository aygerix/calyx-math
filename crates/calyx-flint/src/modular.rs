//! Elliptic and modular functions of a point `tau` of the upper half plane
//! (Dedekind's eta, the j-invariant, the discriminant, Weber's functions and
//! Eisenstein series) and Jacobi's theta function, correctly rounded with
//! FLINT's `acb_modular` (see `ball`). Values that are real by symmetry get
//! an exact zero imaginary part.

use flint3_sys as sys;

use crate::ball::{self, Acb, Arb};
use crate::{Complex, Rational, Real};

/// Modular functions of `tau`, with `q = e^(2πiτ)`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Modular {
    /// Dedekind's eta, `q^(1/24) Π (1 - q^n)`.
    Eta,
    /// The j-invariant, `1/q + 744 + 196884 q + ...`.
    J,
    /// The discriminant `η^24`.
    Delta,
    /// Weber's `f(τ) = e^(-πi/24) η((τ+1)/2)/η(τ)`.
    WeberF,
    /// Weber's `f1(τ) = η(τ/2)/η(τ)`.
    WeberF1,
    /// Weber's `f2(τ) = √2 η(2τ)/η(τ)`.
    WeberF2,
}

/// Whether `q = e^(2πiτ)` is real (`2 Re τ` an integer), so that the
/// Eisenstein series, the discriminant and j are real.
fn q_is_real(tau: &Complex) -> bool {
    tau.re.mul_2exp(1).is_integer()
}

/// Whether `tau` (with rational parts) is equivalent to `i` under SL2(Z),
/// found by reducing it exactly to the fundamental domain.
fn equivalent_to_i(tau: &Complex) -> bool {
    let (Some(mut x), Some(mut y)) = (tau.re.to_rational(), tau.im.to_rational()) else { return false };
    let one = Rational::one();
    for _ in 0..1000 {
        x = &x - &Rational::from(&x.round());
        let n = &(&x * &x) + &(&y * &y);
        if n >= one {
            return x.is_zero() && y == one;
        }
        // tau -> -1/tau
        x = (-&x).checked_div(&n).unwrap();
        y = y.checked_div(&n).unwrap();
    }
    false
}

/// Four vectors of `len` complex balls (for `acb_modular_theta_jet`).
struct Jets {
    v: [sys::acb_ptr; 4],
    len: i64,
}

impl Jets {
    fn new(len: i64) -> Jets {
        Jets { v: std::array::from_fn(|_| unsafe { sys::_acb_vec_init(len as sys::slong) }), len }
    }
}

impl Drop for Jets {
    fn drop(&mut self) {
        for p in self.v {
            unsafe { sys::_acb_vec_clear(p, self.len as sys::slong) };
        }
    }
}

/// `E_2(τ) = -θ1'''(0)/(π² θ1'(0))` (FLINT's θ1 has argument `πz`).
unsafe fn eisenstein_2(out: *mut sys::acb_struct, tau: *const sys::acb_struct, wp: i64) {
    let jets = Jets::new(4);
    let mut z = Acb::new();
    unsafe {
        sys::acb_modular_theta_jet(jets.v[0], jets.v[1], jets.v[2], jets.v[3], z.mut_ptr(), tau, 4, wp as sys::slong);
        sys::acb_div(out, jets.v[0].add(3), jets.v[0].add(1), wp as sys::slong);
        sys::acb_mul_si(out, out, -6, wp as sys::slong);
        sys::acb_const_pi(z.mut_ptr(), wp as sys::slong);
        sys::acb_mul(z.mut_ptr(), z.ptr(), z.ptr(), wp as sys::slong);
        sys::acb_div(out, out, z.ptr(), wp as sys::slong);
    }
}

/// `E_k(τ)` for `k >= 4` from the lattice sum `G_k = Σ' (m + nτ)^(-k)` at
/// the point `w = gτ` of the fundamental domain, truncated to `n <= N` and
/// `|m + n Re w| <= M` with a bound on the rest; `false` if that takes too
/// many terms (small k), when `acb_modular_eisenstein` is used instead.
unsafe fn eisenstein_lattice(out: *mut sys::acb_struct, tau: *const sys::acb_struct, k: u64, wp: i64) -> bool {
    unsafe {
        let prec = wp as sys::slong;
        let mut g: sys::psl2z_struct = std::mem::zeroed();
        sys::psl2z_init(&mut g);
        let mut eps: sys::arf_struct = std::mem::zeroed();
        sys::arf_init(&mut eps);
        sys::arf_set_ui_2exp_si(&mut eps, 63, -6);
        let mut w = Acb::new();
        sys::acb_modular_fundamental_domain_approx(w.mut_ptr(), &mut g, tau, &eps, prec);
        sys::acb_modular_transform(w.mut_ptr(), &g, tau, prec);
        sys::arf_clear(&mut eps);
        let (x, y) = (sys::arf_get_d(&w.0.real.mid, 0), sys::arf_get_d(&w.0.imag.mid, 0));
        let n_max = ((((wp + 10) as f64) / (k as f64 - 2.0)).exp2() / y.max(0.5)).ceil() + 1.0;
        let m_max = (((wp + 10) as f64) / (k as f64 - 1.0)).exp2().ceil() + 1.0;
        if !(y >= 0.8 && n_max * (2.0 * m_max + 4.0) <= 50000.0) {
            sys::psl2z_clear(&mut g);
            return false;
        }
        let (n_max, m_max) = (n_max as i64, m_max as i64);
        // S = Σ_{1<=n<=N} Σ_{|m + nx| <= M} (m + nw)^(-k)
        let (mut s, mut t) = (Acb::new(), Acb::new());
        for n in 1..=n_max {
            let c = -(n as f64) * x;
            for m in (c - m_max as f64).floor() as i64 - 1..=(c + m_max as f64).ceil() as i64 + 1 {
                sys::acb_mul_si(t.mut_ptr(), w.ptr(), n as sys::slong, prec);
                sys::acb_add_si(t.mut_ptr(), t.ptr(), m as sys::slong, prec);
                sys::acb_pow_si(t.mut_ptr(), t.ptr(), -(k as sys::slong), prec);
                sys::acb_add(s.mut_ptr(), s.ptr(), t.ptr(), prec);
            }
        }
        // The rest: 8 y^(1-k) N^(2-k)/(k-2) + 4N (M^(-k) + M^(1-k)/(k-1)),
        // with a lower bound for y.
        let (mut e, mut a, mut b) = (Arb::new(), Arb::new(), Arb::new());
        let mut ylo: sys::arf_struct = std::mem::zeroed();
        sys::arf_init(&mut ylo);
        sys::arb_get_lbound_arf(&mut ylo, &w.0.imag, prec);
        sys::arb_set_arf(a.mut_ptr(), &ylo);
        sys::arf_clear(&mut ylo);
        sys::arb_pow_ui(a.mut_ptr(), a.ptr(), k - 1, prec);
        sys::arb_ui_pow_ui(b.mut_ptr(), n_max as _, k - 2, prec);
        sys::arb_mul(a.mut_ptr(), a.ptr(), b.ptr(), prec);
        sys::arb_mul_ui(a.mut_ptr(), a.ptr(), k - 2, prec);
        sys::arb_ui_div(e.mut_ptr(), 8, a.ptr(), prec);
        sys::arb_ui_pow_ui(a.mut_ptr(), m_max as _, k - 1, prec);
        sys::arb_ui_div(b.mut_ptr(), 1, a.ptr(), prec);
        sys::arb_mul_ui(a.mut_ptr(), a.ptr(), m_max as _, prec);
        sys::arb_ui_div(a.mut_ptr(), 1, a.ptr(), prec);
        sys::arb_div_ui(b.mut_ptr(), b.ptr(), k - 1, prec);
        sys::arb_add(a.mut_ptr(), a.ptr(), b.ptr(), prec);
        sys::arb_mul_ui(a.mut_ptr(), a.ptr(), 4 * n_max as u64, prec);
        sys::arb_add(e.mut_ptr(), e.ptr(), a.ptr(), prec);
        let mut rest: sys::mag_struct = std::mem::zeroed();
        sys::mag_init(&mut rest);
        sys::arb_get_mag(&mut rest, e.ptr());
        // E_k(w) = 1 + 2S/(2ζ(k)) = 1 + S/ζ(k), and E_k(τ) = (cτ + d)^(-k) E_k(w).
        sys::acb_mul_2exp_si(s.mut_ptr(), s.ptr(), 1);
        sys::acb_add_error_mag(s.mut_ptr(), &rest);
        sys::mag_clear(&mut rest);
        sys::arb_zeta_ui(a.mut_ptr(), k, prec);
        sys::arb_mul_2exp_si(a.mut_ptr(), a.ptr(), 1);
        sys::acb_div_arb(s.mut_ptr(), s.ptr(), a.ptr(), prec);
        sys::acb_add_ui(s.mut_ptr(), s.ptr(), 1, prec);
        sys::acb_mul_fmpz(t.mut_ptr(), tau, &g.c, prec);
        sys::acb_add_fmpz(t.mut_ptr(), t.ptr(), &g.d, prec);
        sys::acb_pow_si(t.mut_ptr(), t.ptr(), -(k as sys::slong), prec);
        sys::acb_mul(out, s.ptr(), t.ptr(), prec);
        sys::psl2z_clear(&mut g);
        true
    }
}

impl Complex {
    /// A modular function at `tau` (with `Im tau > 0`).
    pub fn modular(&self, f: Modular) -> Complex {
        let real = match f {
            Modular::J | Modular::Delta => q_is_real(self),
            _ => self.re.is_zero(),
        };
        let t = self.acb();
        let (mut u, mut v) = (Acb::new(), Acb::new());
        let (re, im) = ball::eval_complex(self.prec(), |out, wp| unsafe {
            let wp = wp as sys::slong;
            match f {
                Modular::Eta => sys::acb_modular_eta(out, t.ptr(), wp),
                Modular::J => sys::acb_modular_j(out, t.ptr(), wp),
                Modular::Delta => sys::acb_modular_delta(out, t.ptr(), wp),
                Modular::WeberF | Modular::WeberF1 | Modular::WeberF2 => {
                    match f {
                        Modular::WeberF => {
                            sys::acb_add_ui(u.mut_ptr(), t.ptr(), 1, wp);
                            sys::acb_mul_2exp_si(u.mut_ptr(), u.ptr(), -1);
                        }
                        Modular::WeberF1 => sys::acb_mul_2exp_si(u.mut_ptr(), t.ptr(), -1),
                        _ => sys::acb_mul_2exp_si(u.mut_ptr(), t.ptr(), 1),
                    }
                    sys::acb_modular_eta(u.mut_ptr(), u.ptr(), wp);
                    sys::acb_modular_eta(v.mut_ptr(), t.ptr(), wp);
                    sys::acb_div(out, u.ptr(), v.ptr(), wp);
                    if f == Modular::WeberF {
                        // e^(-πi/24)
                        sys::acb_set_si(u.mut_ptr(), -1);
                        sys::acb_div_ui(u.mut_ptr(), u.ptr(), 24, wp);
                        sys::acb_exp_pi_i(u.mut_ptr(), u.ptr(), wp);
                        sys::acb_mul(out, out, u.ptr(), wp);
                    } else if f == Modular::WeberF2 {
                        sys::acb_set_si(u.mut_ptr(), 2);
                        sys::acb_sqrt(u.mut_ptr(), u.ptr(), wp);
                        sys::acb_mul(out, out, u.ptr(), wp);
                    }
                }
            }
            if real {
                sys::arb_zero(&mut (*out).imag);
            }
        });
        Complex { re, im }
    }

    /// The normalized Eisenstein series `E_k(τ) = G_k(τ)/(2ζ(k))` for even
    /// `k >= 2`, with `E_k = 1 - (2k/B_k) Σ σ_(k-1)(n) q^n` (E_2 is not
    /// modular).
    pub fn eisenstein(&self, k: u64) -> Complex {
        let bits = self.prec();
        if k % 4 == 2 && k > 2 && equivalent_to_i(self) {
            // E_k(i) = i^k E_k(i)
            return Complex::from_real(Real::zero(bits));
        }
        let real = q_is_real(self);
        let t = self.acb();
        let mut z = Arb::new();
        let (re, im) = ball::eval_complex(bits, |out, wp| unsafe {
            if k == 2 {
                eisenstein_2(out, t.ptr(), wp);
            } else if k <= 64 || !eisenstein_lattice(out, t.ptr(), k, wp) {
                let len = (k / 2 - 1) as sys::slong;
                let r = sys::_acb_vec_init(len);
                sys::acb_modular_eisenstein(r, t.ptr(), len, wp as sys::slong);
                sys::arb_zeta_ui(z.mut_ptr(), k, wp as sys::slong);
                sys::arb_mul_2exp_si(z.mut_ptr(), z.ptr(), 1);
                sys::acb_div_arb(out, r.add(len as usize - 1), z.ptr(), wp as sys::slong);
                sys::_acb_vec_clear(r, len);
            }
            if real {
                sys::arb_zero(&mut (*out).imag);
            }
        });
        Complex { re, im }
    }

    /// Jacobi's theta function `θ(q, z) = 2 Σ_(n>=0) (-1)^n q^((n+1/2)^2)
    /// sin((2n+1)z)` for `|q| < 1` (with the principal `q^(1/4)`), at the
    /// given precision.
    pub fn jacobi_theta(q: &Complex, z: &Complex, bits: u64) -> Complex {
        if q.is_zero() {
            return Complex::from_real(Real::zero(bits));
        }
        let real = q.im.is_zero() && q.re.sign() > 0 && z.im.is_zero();
        let (qb, zb) = (q.acb(), z.acb());
        let (mut tau, mut w, mut pi) = (Acb::new(), Acb::new(), Acb::new());
        let (mut t2, mut t3, mut t4) = (Acb::new(), Acb::new(), Acb::new());
        let (re, im) = ball::eval_complex(bits, |out, wp| unsafe {
            let wp = wp as sys::slong;
            // τ = log(q)/(πi), and FLINT's θ1 has argument πz.
            sys::acb_const_pi(pi.mut_ptr(), wp);
            sys::acb_log(tau.mut_ptr(), qb.ptr(), wp);
            sys::acb_div(tau.mut_ptr(), tau.ptr(), pi.ptr(), wp);
            sys::acb_div_onei(tau.mut_ptr(), tau.ptr());
            sys::acb_div(w.mut_ptr(), zb.ptr(), pi.ptr(), wp);
            sys::acb_modular_theta(out, t2.mut_ptr(), t3.mut_ptr(), t4.mut_ptr(), w.ptr(), tau.ptr(), wp);
            if real {
                sys::arb_zero(&mut (*out).imag);
            }
        });
        Complex { re, im }
    }

    /// The k-th derivative at z = 0 of `θ(q, z)`: zero for even k, and for
    /// odd k `2 q^(1/4) Σ (-1)^n q^(n(n+1)) (2n+1)^k`, negated when bit 1
    /// of k is set (so also for negative k, as PARI's `thetanullk`). From
    /// the series, except for `0 < k <= 64`, or when the series is too long
    /// or cancels too much (|q| near 1) and `k <= JET_MAX`: then from FLINT's
    /// theta jets. `Err` if neither works.
    pub fn jacobi_theta_null(q: &Complex, k: i64, bits: u64) -> Result<Complex, ThetaCost> {
        if k % 2 == 0 || q.is_zero() {
            return Ok(Complex::from_real(Real::zero(bits)));
        }
        let real = q.im.is_zero() && q.re.sign() > 0;
        let qb = q.acb();
        // -log|q|, for the length of the series
        let l = -q.abs().to_f64().ln();
        let near_one = !(l > 0.0) || theta_terms(l, 1, bits as i64 + 32).is_none();
        let fail = if near_one { ThetaCost::Nome } else { ThetaCost::Order };
        // For k > 0, the terms near the largest are like e^(-2l (n - n0)^2),
        // and their alternating sum cancels about π²/(8l) nats (1.78/l bits;
        // more for small k, which the Ziv loop finds out).
        let cancel = if k > 0 { 1.78 / l } else { 0.0 };
        if !(1..=64).contains(&k) {
            if !near_one && theta_terms(l, k, bits as i64 + 32).is_some() && cancel + bits as f64 + 64.0 < ball::max_precision(bits) as f64 {
                let v = ball::try_eval_complex(bits, |out, wp| unsafe {
                    match theta_terms(l, k, wp) {
                        Some(n) => theta_null_series(out, qb.ptr(), k, n, wp as sys::slong),
                        None => sys::acb_indeterminate(out),
                    }
                    if real {
                        sys::arb_zero(&mut (*out).imag);
                    }
                });
                if let Some((re, im)) = v {
                    return Ok(Complex { re, im });
                }
            }
            if !(1..=JET_MAX).contains(&k) {
                return Err(fail);
            }
        }
        let (mut tau, mut pi, mut z) = (Acb::new(), Acb::new(), Acb::new());
        let v = ball::try_eval_complex(bits, |out, wp| unsafe {
            // k! c_k/π^k, with c_k the coefficient of z^k in FLINT's θ1(z).
            let wp = wp as sys::slong;
            let len = k + 1;
            let jets = Jets::new(len);
            sys::acb_const_pi(pi.mut_ptr(), wp);
            sys::acb_log(tau.mut_ptr(), qb.ptr(), wp);
            sys::acb_div(tau.mut_ptr(), tau.ptr(), pi.ptr(), wp);
            sys::acb_div_onei(tau.mut_ptr(), tau.ptr());
            sys::acb_zero(z.mut_ptr());
            sys::acb_modular_theta_jet(jets.v[0], jets.v[1], jets.v[2], jets.v[3], z.ptr(), tau.ptr(), len as sys::slong, wp);
            let mut f = Arb::new();
            sys::arb_fac_ui(f.mut_ptr(), k as u64, wp);
            sys::acb_mul_arb(out, jets.v[0].add(k as usize), f.ptr(), wp);
            sys::acb_pow_ui(pi.mut_ptr(), pi.ptr(), k as u64, wp);
            sys::acb_div(out, out, pi.ptr(), wp);
            if real {
                sys::arb_zero(&mut (*out).imag);
            }
        });
        v.map(|(re, im)| Complex { re, im }).ok_or(fail)
    }
}

/// The largest k for theta jets (their cost grows fast with k).
const JET_MAX: i64 = 1024;

/// The most terms of the theta series `jacobi_theta_null` sums.
const MAX_TERMS: i64 = 2_000_000;

/// Why `jacobi_theta_null` declines: its series would take too many terms
/// or cancel too much, because |q| is too close to 1 or k is too large.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ThetaCost {
    Nome,
    Order,
}

/// The number N of terms of the series for `θ^(k)(q, 0)` at working
/// precision `wp`, with `l = -log|q|`, from floating-point estimates of the
/// terms `t_n = (2n+1)^k |q|^(n(n+1))`: N is past the largest term, and
/// `t_N/(1 - r_N)` is below `2^-(wp+20)` of it, with `r_n` the ratio of the
/// terms from n on (a bound, `|q|^(2n+2)`, for k < 0). `None` beyond
/// `MAX_TERMS`.
fn theta_terms(l: f64, k: i64, wp: i64) -> Option<i64> {
    let (kf, l) = (k as f64, l.min(1e6));
    let lt = |n: f64| kf * (2.0 * n + 1.0).ln() - n * (n + 1.0) * l;
    let lr = |n: f64| if k > 0 { kf * (2.0 / (2.0 * n + 1.0)).ln_1p() } else { 0.0 } - (2.0 * n + 2.0) * l;
    let peak = if k > 0 { (((2.0 * kf / l).sqrt() - 1.0) / 2.0).max(0.0) } else { 0.0 };
    let low = lt(peak) - (wp + 20) as f64 * std::f64::consts::LN_2;
    // The condition holds from some n on: gallop, then bisect.
    let ok = |n: f64| {
        let r = lr(n);
        r < 0.0 && lt(n) - (-r.exp_m1()).ln() <= low
    };
    let (mut lo, mut step) = (peak.ceil(), 1.0);
    if !(lo <= MAX_TERMS as f64) {
        return None;
    }
    while !ok(lo + step) {
        lo += step;
        step *= 2.0;
        if lo > MAX_TERMS as f64 {
            return None;
        }
    }
    // ok(lo + step) holds; find the first n in (lo, lo + step] where it does.
    let mut hi = lo + step;
    if ok(lo) {
        hi = lo;
    }
    while hi - lo > 1.0 {
        let mid = ((lo + hi) / 2.0).floor();
        if ok(mid) { hi = mid } else { lo = mid }
    }
    (hi <= MAX_TERMS as f64).then_some(hi as i64)
}

/// `θ^(k)(q, 0)` for odd k from the series `2 q^(1/4) Σ_(n<N) (-1)^n
/// q^(n(n+1)) (2n+1)^k` (see `theta_terms`), with the rest below
/// `t_N/(1 - r_N)` as the ratio of the terms decreases from N on.
unsafe fn theta_null_series(out: *mut sys::acb_struct, qb: *const sys::acb_struct, k: i64, n_max: i64, wp: sys::slong) {
    unsafe {
        let (mut s, mut t, mut p, mut q2, mut qq) = (Acb::new(), Acb::new(), Acb::new(), Acb::new(), Acb::new());
        let (mut c, mut a, mut b) = (Arb::new(), Arb::new(), Arb::new());
        // p = q^(n(n+1)) and q2 = q^(2n+2), from one term to the next
        sys::acb_one(p.mut_ptr());
        sys::acb_mul(qq.mut_ptr(), qb, qb, wp);
        sys::acb_set(q2.mut_ptr(), qq.ptr());
        let power = |c: *mut sys::arb_struct, n: i64| {
            sys::arb_ui_pow_ui(c, (2 * n + 1) as u64, k.unsigned_abs(), wp);
            if k < 0 {
                sys::arb_inv(c, c, wp);
            }
        };
        for n in 0..n_max {
            power(c.mut_ptr(), n);
            sys::acb_mul_arb(t.mut_ptr(), p.ptr(), c.ptr(), wp);
            if n % 2 == 1 {
                sys::acb_sub(s.mut_ptr(), s.ptr(), t.ptr(), wp);
            } else {
                sys::acb_add(s.mut_ptr(), s.ptr(), t.ptr(), wp);
            }
            sys::acb_mul(p.mut_ptr(), p.ptr(), q2.ptr(), wp);
            sys::acb_mul(q2.mut_ptr(), q2.ptr(), qq.ptr(), wp);
        }
        // t_N = (2N+1)^k |q|^(N(N+1)); r_N = ((2N+3)/(2N+1))^k |q|^(2N+2),
        // or |q|^(2N+2) for k < 0.
        let n = n_max as u64;
        sys::acb_abs(a.mut_ptr(), qb, wp);
        sys::arb_pow_ui(b.mut_ptr(), a.ptr(), 2 * n + 2, wp);
        if k > 0 {
            sys::arb_set_ui(c.mut_ptr(), 2 * n + 3);
            sys::arb_div_ui(c.mut_ptr(), c.ptr(), 2 * n + 1, wp);
            sys::arb_pow_ui(c.mut_ptr(), c.ptr(), k as u64, wp);
            sys::arb_mul(b.mut_ptr(), b.ptr(), c.ptr(), wp);
        }
        sys::arb_sub_ui(b.mut_ptr(), b.ptr(), 1, wp);
        sys::arb_neg(b.mut_ptr(), b.ptr());
        sys::arb_pow_ui(a.mut_ptr(), a.ptr(), n * (n + 1), wp);
        power(c.mut_ptr(), n_max);
        sys::arb_mul(a.mut_ptr(), a.ptr(), c.ptr(), wp);
        let (mut rest, mut den): (sys::mag_struct, sys::mag_struct) = (std::mem::zeroed(), std::mem::zeroed());
        sys::mag_init(&mut rest);
        sys::mag_init(&mut den);
        sys::arb_get_mag(&mut rest, a.ptr());
        if sys::arb_is_positive(b.ptr()) != 0 {
            sys::arb_get_mag_lower(&mut den, b.ptr());
            let r: *mut sys::mag_struct = &mut rest;
            sys::mag_div(r, r, &den);
        } else {
            sys::mag_inf(&mut rest);
        }
        sys::acb_add_error_mag(s.mut_ptr(), &rest);
        sys::mag_clear(&mut rest);
        sys::mag_clear(&mut den);
        // 2 q^(1/4) S
        sys::acb_sqrt(t.mut_ptr(), qb, wp);
        sys::acb_sqrt(t.mut_ptr(), t.ptr(), wp);
        sys::acb_mul(out, s.ptr(), t.ptr(), wp);
        sys::acb_mul_2exp_si(out, out, 1);
        if k & 2 != 0 {
            sys::acb_neg(out, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Correctly rounded values (mantissas at 67 bits), checked with mpmath;
    /// Magma 2.22 is a few units in the last place off for most of them.
    #[test]
    fn modular_functions() {
        use Modular::*;
        let bits = 67;
        let q = |n: i64, d: i64| Real::from_rational(&Rational::new(&crate::Integer::from_i64(n), &crate::Integer::from_i64(d)).unwrap(), bits);
        let m = |x: &Real| x.mantissa_exponent().0.to_string();
        let t = Complex::new(q(1, 3), q(4, 5));
        for (k, re, im) in [(2, "79709115889364446788", "-78918033525450898197"), (4, "99178593540994111316", "94687814948915014819"), (14, "-142071670458013069671", "90699551605057419008")] {
            let w = t.eisenstein(k);
            assert_eq!((m(&w.re), m(&w.im)), (re.to_string(), im.to_string()), "E{k}");
        }
        let cases = [
            (Eta, "119685357893030331780", "78343061641562232880"),
            (J, "-125155801621816557277", "123596064622512757238"),
            (Delta, "-101684373499742427879", "124193827538920864557"),
            (WeberF, "85375728961856708819", "129421630394266998796"),
            (WeberF1, "78330588217084574991", "-146814401197391580607"),
            (WeberF2, "83990272465203552484", "125244439902261777602"),
        ];
        for (f, re, im) in cases {
            let w = t.modular(f);
            assert_eq!((m(&w.re), m(&w.im)), (re.to_string(), im.to_string()), "{f:?}");
        }
        // j(i) = 1728, j(2i) = 287496 and E_6(i) = 0, real with exact zero
        // imaginary parts.
        let i = Complex::new(Real::zero(bits), Real::from_i64(1, bits));
        let w = i.modular(J);
        assert!(w.re == Real::from_i64(1728, bits) && w.im.is_zero());
        let w = Complex::new(Real::zero(bits), Real::from_i64(2, bits)).modular(J);
        assert!(w.re == Real::from_i64(287496, bits) && w.im.is_zero());
        let w = i.eisenstein(6);
        assert!(w.re.is_zero() && w.im.is_zero());
    }

    /// Jacobi's theta function and its derivatives at 0 (mantissas at 67
    /// bits, as Magma 2.22 with PARI where that is accurate, else mpmath).
    #[test]
    fn theta() {
        let bits = 67;
        let q = |n: i64, d: i64| Real::from_rational(&Rational::new(&crate::Integer::from_i64(n), &crate::Integer::from_i64(d)).unwrap(), bits);
        let m = |x: &Real| x.mantissa_exponent().0.to_string();
        let third = Complex::from_real(q(1, 3));
        let w = Complex::jacobi_theta(&third, &Complex::from_real(q(2, 5)), bits);
        assert!(m(&w.re) == "128774640818170408307" && w.im.is_zero());
        let w = Complex::jacobi_theta(&Complex::new(q(1, 4), q(1, 5)), &Complex::new(q(1, 2), q(-1, 3)), bits);
        assert_eq!((m(&w.re), m(&w.im)), ("118431349190073554151".into(), "-81799567742847573261".into()));
        // From theta jets (k = 1, 5) and from the series (k = -1, 4097).
        for (k, v) in [(1, "75522240911120890220"), (5, "-76196867548090920210"), (-1, "-108009653149613117056"), (4097, "-117134000269418048452"), (2, "0")] {
            let w = Complex::jacobi_theta_null(&third, k, bits).unwrap();
            assert_eq!(m(&w.re), v, "k = {k}");
        }
        // Near |q| = 1 the series cancels (about 3300 bits for q = 0.999),
        // and for q = 1 - 10^-15 it would be too long.
        let w = Complex::jacobi_theta_null(&Complex::from_real(q(999, 1000)), 65, bits).unwrap();
        assert_eq!(m(&w.re), "93462376948071367661");
        let near = Complex::from_real(Real::from_i64(1, bits).sub(&q(1, 1_000_000_000_000_000)));
        assert_eq!(Complex::jacobi_theta_null(&near, -1, bits).unwrap_err(), ThetaCost::Nome);
        assert_eq!(Complex::jacobi_theta_null(&third, 1 << 62 | 1, bits).unwrap_err(), ThetaCost::Order);
    }
}
