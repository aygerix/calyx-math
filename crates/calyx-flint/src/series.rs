//! Kernels of the summation of infinite series.

use crate::Real;
use crate::mpfr as m;

/// Euler's transformation of an alternating series by van Wijngaarden's
/// algorithm (Numerical Recipes' `eulsum`) in a given precision: the terms
/// go in one at a time, each giving the increment of the sum.
pub struct EulerSum {
    /// The last differences of the terms, halved: `w[k]` is `Δ^k/2^k`.
    w: Vec<Real>,
    tmp: Real,
    s: Real,
}

impl EulerSum {
    pub fn new(bits: u64) -> EulerSum {
        EulerSum { w: Vec::new(), tmp: Real::zero(bits), s: Real::zero(bits) }
    }

    /// Takes the next term (in the working precision) and gives the
    /// increment of the sum.
    pub fn push(&mut self, t: &Real) -> Real {
        let (w, tmp, s) = (&mut self.w, &mut self.tmp, self.s.raw_mut());
        let Some(n) = w.len().checked_sub(1) else {
            w.push(t.clone());
            return t.mul_2exp(-1);
        };
        unsafe {
            m::mpfr_swap(tmp.raw_mut(), w[0].raw_mut());
            m::mpfr_set(w[0].raw_mut(), t.raw(), m::RNDN);
            // (w[k+1], tmp) = ((w[k] + tmp)/2, w[k+1])
            for k in 0..n {
                m::mpfr_add(s, w[k].raw(), tmp.raw(), m::RNDN);
                m::mpfr_mul_2si(s, s, -1, m::RNDN);
                m::mpfr_swap(tmp.raw_mut(), w[k + 1].raw_mut());
                m::mpfr_swap(w[k + 1].raw_mut(), s);
            }
            m::mpfr_add(s, w[n].raw(), tmp.raw(), m::RNDN);
            m::mpfr_mul_2si(s, s, -1, m::RNDN);
            if m::mpfr_cmpabs(s, w[n].raw()) <= 0 {
                w.push(self.s.clone());
                self.s.mul_2exp(-1)
            } else {
                self.s.clone()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn euler_sum() {
        // 1 - 1 + 1 - ... sums to 1/2 at once.
        let mut e = EulerSum::new(128);
        let incs: Vec<Real> = (0..10).map(|n| e.push(&Real::from_i64(if n % 2 == 0 { 1 } else { -1 }, 128))).collect();
        assert_eq!(incs[0].to_f64(), 0.5);
        assert!(incs[1..].iter().all(|x| x.is_zero()));
        // -1 + 1/4 - 1/9 + ... = -π²/12, to about 2^-120 after 204 terms.
        let mut e = EulerSum::new(128);
        let mut sum = Real::zero(128);
        for n in 1..=204i64 {
            let t = Real::from_i64(if n % 2 == 0 { 1 } else { -1 }, 128).div_i64(n * n);
            sum = sum.add(&e.push(&t));
        }
        let pi2 = Real::constant(m::mpfr_const_pi, 128).sqr().div_i64(-12);
        assert!(sum.sub(&pi2).abs().to_f64() < 1e-36);
    }
}
