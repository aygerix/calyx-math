//! Rational approximations of real numbers: continued fractions and best
//! approximations, as Magma computes them (handbook, Real and Complex
//! Fields: Element Operations).
//!
//! A real number `x` of precision `p` bits is `m 2^e` exactly, with `m` of
//! `p` bits. Black-box runs of Magma 2.22 give these rules:
//! - Its continued fraction is that of the rational `m 2^e`, up to the
//!   first convergent `c` with `|x - c| < |x| 2^-p`. With a bound `b` on the
//!   number of terms it is the whole expansion if that has fewer than `b`
//!   terms, and otherwise at most `b` terms, still only up to that
//!   convergent.
//! - Its best approximation with denominator at most `k` is PARI's
//!   `bestappr`, whose continued fraction runs in PARI's floating point
//!   (see `best_approximation`), not on the exact value.

use crate::{Integer, Rational, Real};

/// The partial quotients of the continued fraction of `x`, at most `bound`
/// of them as above, or `None` for a bound of 0 when `x` is not 0, where
/// Magma fails.
pub fn continued_fraction(x: &Real, bound: Option<&Integer>) -> Option<Vec<Integer>> {
    let small = |n: usize| bound.is_none_or(|b| Integer::from_u64(n as u64) <= *b);
    let (m, e) = x.mantissa_exponent();
    if m.is_zero() {
        return Some(if small(1) { vec![Integer::zero()] } else { Vec::new() });
    }
    if !small(1) {
        return None;
    }
    let p = x.prec();
    if e >= 0 {
        return Some(vec![m.mul_2exp(e as u64)]);
    }
    let f = e.unsigned_abs();
    let den = Integer::one().mul_2exp(f);
    // The whole expansion, and the length up to the first convergent p/q
    // with |m/2^f - p/q| < |m|/2^f 2^-p, that is |m q - p 2^f| 2^p < |m| q.
    let (mut num, mut d) = (m.clone(), den.clone());
    let mut terms = Vec::new();
    let mut close = None;
    let (mut p0, mut q0, mut p1, mut q1) = (Integer::zero(), Integer::one(), Integer::one(), Integer::zero());
    let ma = m.abs();
    loop {
        let (a, r) = num.fdiv_qr(&d).expect("a nonzero denominator");
        (p0, p1) = (p1.clone(), &(&a * &p1) + &p0);
        (q0, q1) = (q1.clone(), &(&a * &q1) + &q0);
        terms.push(a);
        if close.is_none() && (&(&m * &q1) - &p1.mul_2exp(f)).abs().mul_2exp(p) < &ma * &q1 {
            close = Some(terms.len());
        }
        if r.is_zero() {
            break;
        }
        (num, d) = (d, r);
    }
    let close = close.unwrap_or(terms.len());
    match bound {
        Some(b) if Integer::from_u64(terms.len() as u64) < *b => {}
        Some(b) => terms.truncate(close.min(b.to_u64().map_or(usize::MAX, |b| b as usize))),
        None => terms.truncate(close),
    }
    Some(terms)
}

/// Why a best approximation fails in Magma.
#[derive(Debug, PartialEq, Eq)]
pub enum ApproxError {
    /// A bound below 1 leaves the approximation 1/0.
    DivisionByZero,
    /// PARI's floor of a number whose integral part exceeds its precision.
    PrecisionLoss,
}

/// A number of PARI's floating point: `n 2^g` with `words` 64-bit words of
/// mantissa.
struct PariReal {
    n: Integer,
    g: i64,
    words: u64,
}

impl PariReal {
    /// The exponent `e` with `2^e <= |x| < 2^(e+1)` (x nonzero).
    fn expo(&self) -> i64 {
        self.n.bits() as i64 - 1 + self.g
    }

    /// PARI's `floorr`, which fails when the integral part is not
    /// significant.
    fn floor(&self) -> Result<Integer, ApproxError> {
        if self.n.is_zero() {
            return Ok(Integer::zero());
        }
        if self.expo() >= 64 * self.words as i64 {
            return Err(ApproxError::PrecisionLoss);
        }
        Ok(if self.g >= 0 { self.n.mul_2exp(self.g as u64) } else { self.n.fdiv_2exp(self.g.unsigned_abs()) })
    }

    /// `x - a` for `a` the floor of x, which is exact. PARI converts a to a
    /// real of x's precision, or of one word more if |a| has the larger
    /// exponent, and drops the words cancelled at the top.
    fn sub_floor(&mut self, a: &Integer) {
        if a.is_zero() {
            return;
        }
        let top = self.expo().max(a.bits() as i64 - 1);
        if (a.bits() as i64 - 1) > self.expo() {
            self.words += 1;
        }
        self.n = if self.g >= 0 { &self.n.mul_2exp(self.g as u64) - a } else { &self.n - &a.mul_2exp(self.g.unsigned_abs()) };
        if self.g >= 0 {
            self.g = 0;
        }
        if !self.n.is_zero() {
            self.words -= ((top - self.expo()) / 64) as u64;
        }
    }

    /// `1/x` for x > 0, truncated to x's precision (PARI's division).
    fn inv(&self) -> PariReal {
        let s = 64 * self.words + self.n.bits() - 1;
        let (q, _) = Integer::one().mul_2exp(s).fdiv_qr(&self.n).expect("a nonzero number");
        let excess = q.bits().saturating_sub(64 * self.words);
        PariReal { n: q.fdiv_2exp(excess), g: -self.g - s as i64 + excess as i64, words: self.words }
    }

    /// Whether x >= b.
    fn ge(&self, b: &Integer) -> bool {
        if self.g >= 0 { self.n.mul_2exp(self.g as u64) >= *b } else { self.n >= b.mul_2exp(self.g.unsigned_abs()) }
    }
}

/// The best approximation of `x` by a rational of denominator at most `k`
/// in Magma, which is PARI's `bestappr`: the continued fraction of x in
/// PARI's floating point of `⌈p/64⌉` words (see `PariReal`), up to the last
/// convergent of denominator at most k; if a complete quotient reaches
/// k + 1 first, the semiconvergent of largest denominator at most k
/// instead of that convergent when it is at least as close to x.
pub fn best_approximation(x: &Real, k: &Integer) -> Result<Rational, ApproxError> {
    let (m, e) = x.mantissa_exponent();
    let words = x.prec().div_ceil(64);
    let mut y = PariReal { n: m.clone(), g: e, words };
    let (mut p1, mut q1) = (Integer::one(), Integer::zero());
    let mut a = y.floor()?;
    let (mut p0, mut q0) = (a.clone(), Integer::one());
    let k1 = k + &Integer::one();
    while q0 <= *k {
        y.sub_floor(&a);
        if y.n.is_zero() {
            (p1, q1) = (p0, q0);
            break;
        }
        y = y.inv();
        if y.ge(&k1) {
            // The semiconvergent with the largest denominator at most k,
            // if it is no farther from x.
            let (b, _) = (k - &q1).fdiv_qr(&q0).expect("q0 > 0");
            let p = &(&b * &p0) + &p1;
            let q = &(&b * &q0) + &q1;
            // |x - p/q| <= |x - p0/q0| with x = m 2^e.
            let dist = |p: &Integer, q: &Integer| match e >= 0 {
                true => (&m.mul_2exp(e as u64) * q - p).abs(),
                false => (&(&m * q) - &p.mul_2exp(e.unsigned_abs())).abs(),
            };
            if &dist(&p, &q) * &q0 <= &dist(&p0, &q0) * &q {
                (p1, q1) = (p, q);
            } else {
                (p1, q1) = (p0, q0);
            }
            break;
        }
        a = y.floor()?;
        (p0, p1) = (&(&a * &p0) + &p1, p0);
        (q0, q1) = (&(&a * &q0) + &q1, q0);
    }
    Rational::new(&p1, &q1).ok_or(ApproxError::DivisionByZero)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ints(v: &[i64]) -> Vec<Integer> {
        v.iter().map(|&n| Integer::from_i64(n)).collect()
    }

    fn real(n: i64, d: i64, p: u64) -> Real {
        Real::from_rational(&Rational::new(&Integer::from_i64(n), &Integer::from_i64(d)).unwrap(), p)
    }

    fn pi(p: u64) -> Real {
        Real::constant(crate::mpfr::mpfr_const_pi, p)
    }

    fn q(s: &str) -> Rational {
        let (n, d) = s.split_once('/').unwrap_or((s, "1"));
        Rational::new(&Integer::parse(n).unwrap(), &Integer::parse(d).unwrap()).unwrap()
    }

    #[test]
    fn continued_fractions_stop_at_the_precision() {
        let pi67 = pi(67);
        assert_eq!(continued_fraction(&pi67, None).unwrap(), ints(&[3, 7, 15, 1, 292, 1, 1, 1, 2, 1, 3, 1, 14, 2, 1, 1, 2, 2, 2, 3]));
        // 2/3 rounded down to 17 bits: its convergent 2/3 is [0, 1, 1, 1].
        assert_eq!(continued_fraction(&real(2, 3, 17), None).unwrap(), ints(&[0, 1, 1, 1]));
        assert_eq!(continued_fraction(&real(2, 3, 34), None).unwrap(), ints(&[0, 1, 2]));
        assert_eq!(continued_fraction(&pi67.neg(), None).unwrap()[..4], ints(&[-4, 1, 6, 15]));
        assert_eq!(continued_fraction(&real(0, 1, 67), None).unwrap(), ints(&[0]));
        assert_eq!(continued_fraction(&real(15, 2, 67), None).unwrap(), ints(&[7, 2]));
    }

    #[test]
    fn bounds_cut_the_expansion() {
        let pi67 = pi(67);
        let b = |n: i64| Some(Integer::from_i64(n));
        assert_eq!(continued_fraction(&pi67, b(3).as_ref()).unwrap(), ints(&[3, 7, 15]));
        // Up to 35 terms the expansion stops at the precision; with more
        // allowed it is the whole expansion of the binary value.
        assert_eq!(continued_fraction(&pi67, b(35).as_ref()).unwrap().len(), 20);
        let all = continued_fraction(&pi67, b(36).as_ref()).unwrap();
        assert_eq!(all.len(), 35);
        assert_eq!(all[34], Integer::from_i64(63));
        assert_eq!(continued_fraction(&pi67, b(0).as_ref()), None);
        assert_eq!(continued_fraction(&real(0, 1, 67), b(0).as_ref()).unwrap(), vec![]);
    }

    #[test]
    fn best_approximations_follow_pari() {
        let pi67 = pi(67);
        let ba = |x: &Real, k: &str| best_approximation(x, &Integer::parse(k).unwrap());
        for (k, r) in [("1", "3"), ("7", "22/7"), ("100", "22/7"), ("106", "333/106"), ("1000", "355/113"), ("1000000", "1146408/364913")] {
            assert_eq!(ba(&pi67, k).unwrap(), q(r));
        }
        // Beyond the precision the floating point takes over.
        assert_eq!(ba(&pi67, "100000000000000000000").unwrap(), q("57952155664616982739/18446744073709551616"));
        assert_eq!(ba(&pi67, "1180591620717411303424").unwrap(), q("1913340346826318379055/609035148029139972261"));
        // Ties go to the semiconvergent.
        assert_eq!(ba(&real(5, 2, 67), "1").unwrap(), q("3"));
        assert_eq!(ba(&real(-1, 2, 67), "1").unwrap(), q("0"));
        assert_eq!(ba(&real(-1, 3, 67), "2").unwrap(), q("0"));
        assert_eq!(ba(&real(1, 3, 67), "3").unwrap(), q("1/3"));
        assert_eq!(ba(&real(1, 3, 67), "1000000000000000000000000000000"), Err(ApproxError::PrecisionLoss));
        assert_eq!(ba(&pi67, "0"), Err(ApproxError::DivisionByZero));
        assert_eq!(ba(&real(0, 1, 67), "0"), Err(ApproxError::DivisionByZero));
        assert_eq!(ba(&real(0, 1, 67), "1").unwrap(), q("0"));
        // A negative number whose floor has a larger exponent gains a word.
        assert_eq!(ba(&pi(17).neg(), "1152921504606846976").unwrap(), q("-3217/1024"));
        // 17 bits run in one word: the last complete quotient 9 comes out
        // as 8.999...
        assert_eq!(ba(&pi(17), "1000").unwrap(), q("2862/911"));
    }
}
