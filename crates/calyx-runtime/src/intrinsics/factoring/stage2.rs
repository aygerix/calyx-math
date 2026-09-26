//! Stage 2 of ECM and the p ± 1 methods. After stage 1, a method succeeds
//! if its element P (a point, or a Lucas value) has prime order q in
//! (B1, B2] modulo some prime p of n. Write q = a d ± b with b < d/2 prime
//! to d: then [a d]P = ±[b]P modulo p, which shows as the values of the two
//! (normalised x-coordinates for ECM, V-values for p ± 1) agreeing modulo
//! p, so the product of their differences shares p with n. Over a short
//! range the product runs over the primes, one product each; over a long
//! one it runs over all the pairs (a, b), as the values at the giant steps
//! of the polynomial whose roots are the baby values (FLINT's product and
//! remainder trees), in more and smaller batches the larger k is.

use calyx_flint::Integer;
use calyx_flint::modn::RootPoly;

use super::arith::Ring;

/// The values of a stage 2's baby and giant steps.
pub trait Steps<R: Ring> {
    /// The values at the baby steps b in `bs` (odd and increasing).
    fn babies(&mut self, r: &R, bs: &[u64]) -> Result<Vec<R::E>, Integer>;
    /// Go to the giant step a d.
    fn start(&mut self, r: &R, d: u64, a: u64);
    /// The values at the next `count` giant steps.
    fn giants(&mut self, r: &R, count: usize) -> Result<Vec<R::E>, Integer>;
    /// The first giant step a method can take: ECM has no value at 0, but
    /// meets the primes below d/2 as the baby steps that do not normalise.
    fn first_giant(&self) -> u64 {
        0
    }

    /// Whether the giant steps' values lie on a geometric progression (for
    /// p ± 1, in an extension of the residues), where the polynomial takes
    /// about a product a batch to evaluate rather than a remainder tree.
    const GEOMETRIC: bool = false;

    /// The polynomial whose roots are the values at the baby steps `bs`,
    /// evaluated at the giant steps `lo..=hi` of d, in batches of `batch`:
    /// the gcd of the product with n, or of a value that fails to normalise.
    fn poly(&mut self, r: &R, bs: &[u64], d: u64, lo: u64, hi: u64, batch: usize) -> Integer {
        multipoint(r, self, bs, d, lo, hi, batch)
    }
}

/// The giant steps the pairing takes at a time.
const BATCH: usize = 64;

/// The largest degree of the polynomials, which bounds their memory: past
/// it they take more batches than k asks for.
const MOST_ROOTS: u64 = 92160;

/// A proper divisor of n from stage 2 over the primes in (b1, b2], if one
/// turns up; b1 is at least 3. A larger k makes the polynomials smaller
/// and their batches more, about k/4 of them for ECM and k/2 for p ± 1.
pub fn stage2<R: Ring, S: Steps<R>>(r: &R, s: &mut S, b1: u64, b2: u64, k: u64) -> Option<Integer> {
    if b2 <= b1 {
        return None;
    }
    let g = match plan(b1, b2, k, r.modulus().bits(), S::GEOMETRIC) {
        Plan::Pairs(d) => pairs(r, s, b1, b2, d),
        Plan::Poly(d, batch) => {
            let (lo, hi) = giant_range(b1, b2, d);
            s.poly(r, &baby_steps(d), d, lo.max(s.first_giant()), hi, batch)
        }
    };
    r.proper(g)
}

enum Plan {
    Pairs(u64),
    /// d and the giant steps per batch.
    Poly(u64, usize),
}

/// The odd b below d/2 prime to d.
fn baby_steps(d: u64) -> Vec<u64> {
    (1..d / 2).step_by(2).filter(|&b| gcd(b, d) == 1).collect()
}

/// The number of baby steps for d: phi(d)/2.
fn baby_count(d: u64) -> u64 {
    let (mut m, mut phi) = (d, d);
    for p in [2, 3, 5, 7, 11, 13, 17] {
        if m % p == 0 {
            phi = phi / p * (p - 1);
            while m % p == 0 {
                m /= p;
            }
        }
    }
    phi / 2
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// The d that stage 2 may use: the products of the primes up to 3, 5, 7,
/// 11, 13 or 17 that are at most b1 (so that the primes q > b1 are prime
/// to d), times up to 16 made of the same primes, which keeps the share
/// of baby steps.
fn steps(b1: u64) -> Vec<u64> {
    let mut ds = Vec::new();
    for (base, p) in [(6u64, 3u64), (30, 5), (210, 7), (2310, 11), (30030, 13), (510510, 17)] {
        if p > b1 {
            break;
        }
        ds.extend((1..=16).filter(|&m| smooth(m, p)).map(|m| base * m));
    }
    ds.sort_unstable();
    ds.dedup();
    ds
}

/// Whether m has no prime factor above p.
fn smooth(mut m: u64, p: u64) -> bool {
    for q in 2..=p {
        while m % q == 0 {
            m /= q;
        }
    }
    m == 1
}

/// The first and last giant steps a for the primes in (b1, b2]: those
/// nearest to them.
fn giant_range(b1: u64, b2: u64, d: u64) -> (u64, u64) {
    ((b1 + 1 + d / 2) / d, (b2 + d / 2) / d)
}

/// How to run stage 2 for n of the given bits: the pairing over a short
/// range, with the d that takes the fewest steps, and past it the
/// polynomials, as measured. Evaluating them at any points costs several
/// times more a point than building them costs a root, so they take about
/// 2 roots a giant step for k = 2 (fewer for a larger k, for less memory),
/// in batches of at most a point a root. On a geometric progression the
/// points cost little, and the polynomials take about 1/8 of a root a giant
/// step for k = 2, in batches of up to 8 points a root.
fn plan(b1: u64, b2: u64, k: u64, bits: u64, geometric: bool) -> Plan {
    let range = b2 - b1;
    let ds = steps(b1.max(3));
    let from: u64 = match (geometric, bits <= 512) {
        (false, true) => 1 << 23,
        (false, false) => 1 << 19,
        (true, true) => 1 << 22,
        (true, false) => 1 << 20,
    };
    if range > from {
        let giants = |d: u64| {
            let (lo, hi) = giant_range(b1, b2, d);
            hi - lo + 1
        };
        let fits = |d: u64| match geometric {
            false => giants(d).saturating_mul(4) <= baby_count(d).saturating_mul(k),
            true => giants(d) <= baby_count(d).saturating_mul(k).saturating_mul(4),
        };
        let fit = ds.iter().copied().filter(|&d| baby_count(d) <= MOST_ROOTS);
        if let Some(d) = fit.clone().find(|&d| fits(d)).or(fit.last()) {
            let most = if geometric { 8 * baby_count(d) } else { baby_count(d) };
            let batches = giants(d).div_ceil(most);
            return Plan::Poly(d, giants(d).div_ceil(batches) as usize);
        }
    }
    let d = ds.iter().copied().min_by_key(|&d| baby_count(d) + range / d).unwrap_or(6);
    Plan::Pairs(d)
}

/// The product over the primes in (b1, b2]; returns its gcd with n, or
/// the gcd that a failed normalisation found.
fn pairs<R: Ring, S: Steps<R>>(r: &R, s: &mut S, b1: u64, b2: u64, d: u64) -> Integer {
    let bs = baby_steps(d);
    let babies = match s.babies(r, &bs) {
        Ok(v) => v,
        Err(g) => return g,
    };
    let (lo, hi) = giant_range(b1, b2, d);
    let lo = lo.max(s.first_giant());
    s.start(r, d, lo);
    let mut window = Window::new(b2 + d);
    let mut acc = r.one();
    let mut a = lo;
    while a <= hi {
        let count = (BATCH as u64).min(hi - a + 1);
        let giants = match s.giants(r, count as usize) {
            Ok(v) => v,
            Err(g) => return g,
        };
        window.fill((a * d).saturating_sub(d / 2) | 1, (a + count - 1) * d + d / 2);
        for (i, g) in giants.iter().enumerate() {
            let c = (a + i as u64) * d;
            for (&b, beta) in bs.iter().zip(&babies) {
                let hit = |q: u64| q > b1 && q <= b2 && window.is_prime(q);
                if c.checked_sub(b).is_some_and(hit) || hit(c + b) {
                    acc = r.mul(&acc, &r.sub(g, beta));
                }
            }
        }
        a += count;
    }
    r.gcd(&acc)
}

/// The product over all the pairs, a batch of giant steps at a time, by
/// FLINT's product and remainder trees.
fn multipoint<R: Ring, S: Steps<R> + ?Sized>(r: &R, s: &mut S, bs: &[u64], d: u64, lo: u64, hi: u64, batch: usize) -> Integer {
    let n = r.modulus();
    let roots: Vec<Integer> = match s.babies(r, bs) {
        Ok(v) => v.iter().map(|x| r.to_int(x)).collect(),
        Err(g) => return g,
    };
    let f = RootPoly::new(n, &roots);
    drop(roots);
    s.start(r, d, lo);
    let mut acc = Integer::one();
    let mut a = lo;
    while a <= hi {
        let count = (batch as u64).min(hi - a + 1);
        let points: Vec<Integer> = match s.giants(r, count as usize) {
            Ok(v) => v.iter().map(|x| r.to_int(x)).collect(),
            Err(g) => return g,
        };
        acc = (&acc * &f.product_at(&points)).div_rem_euclid(n).unwrap().1;
        a += count;
    }
    acc.gcd(n)
}

/// The primes in a window of odd numbers, sieved by the primes up to the
/// square root of a limit.
struct Window {
    base: Vec<u64>,
    /// The first number of the window (odd), and whether each odd number
    /// from it is composite.
    lo: u64,
    composite: Vec<bool>,
}

impl Window {
    fn new(limit: u64) -> Window {
        let base = crate::intrinsics::numtheory::primes_up_to(limit.isqrt() + 1).into_iter().filter(|&p| p > 2).collect();
        Window { base, lo: 1, composite: Vec::new() }
    }

    /// Sieve the odd numbers in [lo, hi] (lo odd).
    fn fill(&mut self, lo: u64, hi: u64) {
        let len = ((hi.max(lo) - lo) / 2 + 1) as usize;
        self.lo = lo;
        self.composite.clear();
        self.composite.resize(len, false);
        for &p in &self.base {
            if p * p > hi {
                break;
            }
            // The first odd multiple of p in the window, from p^2 on.
            let mut m = lo.div_ceil(p).max(p) * p;
            if m % 2 == 0 {
                m += p;
            }
            let mut j = ((m - lo) / 2) as usize;
            while j < len {
                self.composite[j] = true;
                j += p as usize;
            }
        }
        if lo == 1 {
            self.composite[0] = true;
        }
    }

    fn is_prime(&self, q: u64) -> bool {
        q & 1 == 1 && q >= self.lo && !self.composite[((q - self.lo) / 2) as usize]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn windows_find_the_primes() {
        let mut w = Window::new(1 << 20);
        for lo in [1u64, 3, 1001, 999_999] {
            w.fill(lo, lo + 2000);
            let want: Vec<u64> = (lo..=lo + 2000).filter(|&q| q > 2 && Integer::from_u64(q).is_prime()).collect();
            let got: Vec<u64> = (lo..=lo + 2000).filter(|&q| w.is_prime(q)).collect();
            assert_eq!(got, want, "window from {lo}");
        }
    }

    #[test]
    fn every_prime_is_a_pair() {
        for d in steps(17).into_iter().filter(|&d| d <= 60060) {
            let p = [17, 13, 11, 7, 5, 3].into_iter().find(|&p| d % p == 0).unwrap();
            let bs = baby_steps(d);
            assert_eq!(bs.len() as u64, baby_count(d), "d = {d}");
            let (b1, b2) = (p.max(d / 2), 3 * d + 7);
            let (lo, hi) = giant_range(b1, b2, d);
            for q in (b1 + 1..=b2).filter(|&q| Integer::from_u64(q).is_prime()) {
                let a = (q + d / 2) / d;
                assert!(lo <= a && a <= hi, "{q} with d = {d}");
                assert!(bs.binary_search(&q.abs_diff(a * d)).is_ok(), "{q} with d = {d}");
            }
        }
    }
}
