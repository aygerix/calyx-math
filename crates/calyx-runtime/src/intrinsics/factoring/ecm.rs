//! ECM on Montgomery curves with Suyama's parametrization, on numbers in
//! Montgomery form held in fixed arrays of words: stage 1 by Montgomery's
//! ladder on the prime powers up to B1, stage 2 by the standard
//! continuation, which meets the primes up to B2 as kD ± j.

use std::cell::RefCell;

use calyx_flint::Integer;

/// A proper divisor of the odd composite n from one curve with Suyama's
/// parameter `sigma` (at least 6) and the stage bounds b1 < b2, if it finds
/// one. Numbers of more than 512 bits go to FLINT's ECM.
pub fn curve(n: &Integer, b1: u64, b2: u64, sigma: u64) -> Option<Integer> {
    match n.bits().div_ceil(64) {
        0 | 1 => Mont::<1>::new(n).curve(b1, b2, sigma),
        2 => Mont::<2>::new(n).curve(b1, b2, sigma),
        3 => Mont::<3>::new(n).curve(b1, b2, sigma),
        4 => Mont::<4>::new(n).curve(b1, b2, sigma),
        5 => Mont::<5>::new(n).curve(b1, b2, sigma),
        6 => Mont::<6>::new(n).curve(b1, b2, sigma),
        7 => Mont::<7>::new(n).curve(b1, b2, sigma),
        8 => Mont::<8>::new(n).curve(b1, b2, sigma),
        _ => n.ecm(1, b1, b2, sigma),
    }
}

/// The residues modulo an odd n < 2^(64N), each held as x 2^(64N) mod n.
struct Mont<const N: usize> {
    n: [u64; N],
    /// -1/n modulo 2^64.
    ninv: u64,
    modulus: Integer,
}

/// A point of the curve in the coordinates X : Z.
#[derive(Clone, Copy)]
struct Pt<const N: usize> {
    x: [u64; N],
    z: [u64; N],
}

/// `a + b c + carry` as its low and high words.
#[inline(always)]
fn mac(a: u64, b: u64, c: u64, carry: u64) -> (u64, u64) {
    let t = a as u128 + b as u128 * c as u128 + carry as u128;
    (t as u64, (t >> 64) as u64)
}

fn words<const N: usize>(x: &Integer) -> [u64; N] {
    let mut a = [0; N];
    for (w, l) in a.iter_mut().zip(x.to_limbs()) {
        *w = l;
    }
    a
}

impl<const N: usize> Mont<N> {
    fn new(n: &Integer) -> Self {
        let a: [u64; N] = words(n);
        // Newton's iteration for 1/n modulo 2^64 doubles the correct bits.
        let mut inv = 1u64;
        for _ in 0..6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(a[0].wrapping_mul(inv)));
        }
        Mont { n: a, ninv: inv.wrapping_neg(), modulus: n.clone() }
    }

    /// `t + hi 2^(64N)` less n if that is at least n (it is below 2n).
    #[inline(always)]
    fn reduce(&self, t: [u64; N], hi: bool) -> [u64; N] {
        let mut d = [0; N];
        let mut borrow = false;
        for j in 0..N {
            let (x, b1) = t[j].overflowing_sub(self.n[j]);
            let (y, b2) = x.overflowing_sub(borrow as u64);
            d[j] = y;
            borrow = b1 | b2;
        }
        if hi || !borrow { d } else { t }
    }

    /// Montgomery's product a b / 2^(64N) mod n, word by word (CIOS).
    #[inline(always)]
    fn mul(&self, a: &[u64; N], b: &[u64; N]) -> [u64; N] {
        let mut t = [0u64; N];
        let mut top = 0u64;
        for &bi in b.iter() {
            let mut c = 0;
            for j in 0..N {
                (t[j], c) = mac(t[j], a[j], bi, c);
            }
            let (s, over) = top.overflowing_add(c);
            let m = t[0].wrapping_mul(self.ninv);
            let (_, mut c) = mac(t[0], m, self.n[0], 0);
            for j in 1..N {
                (t[j - 1], c) = mac(t[j], m, self.n[j], c);
            }
            let (s2, over2) = s.overflowing_add(c);
            t[N - 1] = s2;
            top = over as u64 + over2 as u64;
        }
        self.reduce(t, top != 0)
    }

    #[inline(always)]
    fn add(&self, a: &[u64; N], b: &[u64; N]) -> [u64; N] {
        let mut s = [0; N];
        let mut carry = false;
        for j in 0..N {
            let (x, c1) = a[j].overflowing_add(b[j]);
            let (y, c2) = x.overflowing_add(carry as u64);
            s[j] = y;
            carry = c1 | c2;
        }
        self.reduce(s, carry)
    }

    #[inline(always)]
    fn sub(&self, a: &[u64; N], b: &[u64; N]) -> [u64; N] {
        let mut d = [0; N];
        let mut borrow = false;
        for j in 0..N {
            let (x, b1) = a[j].overflowing_sub(b[j]);
            let (y, b2) = x.overflowing_sub(borrow as u64);
            d[j] = y;
            borrow = b1 | b2;
        }
        if borrow {
            let mut carry = false;
            for j in 0..N {
                let (x, c1) = d[j].overflowing_add(self.n[j]);
                let (y, c2) = x.overflowing_add(carry as u64);
                d[j] = y;
                carry = c1 | c2;
            }
        }
        d
    }

    /// The Montgomery form of x.
    fn from_int(&self, x: &Integer) -> [u64; N] {
        words(&x.mul_2exp(64 * N as u64).div_rem_euclid(&self.modulus).unwrap().1)
    }

    /// The residue that a Montgomery form stands for.
    #[cfg(test)]
    fn to_int(&self, a: &[u64; N]) -> Integer {
        let mut one = [0; N];
        one[0] = 1;
        Integer::from_limbs(&self.mul(a, &one), false)
    }

    /// gcd(a, n), for a in Montgomery form (2^(64N) is prime to n).
    fn gcd(&self, a: &[u64; N]) -> Integer {
        Integer::from_limbs(a, false).gcd(&self.modulus)
    }

    /// 2P, with a24 = (A + 2) / 4.
    #[inline(always)]
    fn dbl(&self, p: &Pt<N>, a24: &[u64; N]) -> Pt<N> {
        let s = self.add(&p.x, &p.z);
        let d = self.sub(&p.x, &p.z);
        let ss = self.mul(&s, &s);
        let dd = self.mul(&d, &d);
        let t = self.sub(&ss, &dd);
        Pt { x: self.mul(&ss, &dd), z: self.mul(&t, &self.add(&dd, &self.mul(a24, &t))) }
    }

    /// P + Q from P - Q.
    #[inline(always)]
    fn dadd(&self, p: &Pt<N>, q: &Pt<N>, diff: &Pt<N>) -> Pt<N> {
        let u = self.mul(&self.sub(&p.x, &p.z), &self.add(&q.x, &q.z));
        let v = self.mul(&self.add(&p.x, &p.z), &self.sub(&q.x, &q.z));
        let s = self.add(&u, &v);
        let d = self.sub(&u, &v);
        Pt { x: self.mul(&diff.z, &self.mul(&s, &s)), z: self.mul(&diff.x, &self.mul(&d, &d)) }
    }

    /// kP (k at least 1) by Montgomery's ladder.
    fn ladder(&self, p: &Pt<N>, k: u64, a24: &[u64; N]) -> Pt<N> {
        if k == 1 {
            return *p;
        }
        let (mut r0, mut r1) = (*p, self.dbl(p, a24));
        for i in (0..63 - k.leading_zeros()).rev() {
            if k >> i & 1 == 1 {
                r0 = self.dadd(&r1, &r0, p);
                r1 = self.dbl(&r1, a24);
            } else {
                r1 = self.dadd(&r1, &r0, p);
                r0 = self.dbl(&r0, a24);
            }
        }
        r0
    }

    /// A proper divisor of n from g = gcd(., n), if g is one.
    fn proper(&self, g: Integer) -> Option<Integer> {
        (!g.is_one() && g != self.modulus).then_some(g)
    }

    fn curve(&self, b1: u64, b2: u64, sigma: u64) -> Option<Integer> {
        // Suyama's curve: u = sigma^2 - 5, v = 4 sigma, the point u^3 : v^3,
        // and (A + 2) / 4 = (v - u)^3 (3u + v) / (16 u^3 v).
        let n = &self.modulus;
        let s = Integer::from_u64(sigma);
        let u = &(&s * &s) - &Integer::from_u64(5);
        let v = &s * &Integer::from_u64(4);
        let u3 = &(&u * &u) * &u;
        let w = &v - &u;
        let num = &(&(&w * &w) * &w) * &(&(&u * &Integer::from_u64(3)) + &v);
        let den = &(&u3 * &v) * &Integer::from_u64(16);
        let Some(inv) = den.invmod(n) else { return self.proper(den.gcd(n)) };
        let a24 = self.from_int(&(&num * &inv));
        let mut p = Pt { x: self.from_int(&u3), z: self.from_int(&(&(&v * &v) * &v)) };
        let b2 = b2.min(STAGE2_LIMIT).max(b1);
        with_primes(b2 + 2310, |sieve| {
            // Stage 1: the prime powers up to b1, as many to a word as fit.
            let mut k = 1u64;
            for q in sieve.primes(b1) {
                let mut qe = q;
                while qe <= b1 / q {
                    qe *= q;
                }
                if k.checked_mul(qe).is_none_or(|x| x >> 63 != 0) {
                    p = self.ladder(&p, k, &a24);
                    k = 1;
                }
                k *= qe;
            }
            p = self.ladder(&p, k, &a24);
            let g = self.gcd(&p.z);
            if !g.is_one() {
                return self.proper(g);
            }
            match self.stage2(&p, b1, b2, &a24, sieve) {
                Ok(acc) => self.proper(self.gcd(&acc)),
                Err(g) => self.proper(g),
            }
        })
    }

    /// Stage 2: whether the order of P is a prime in (b1, b2]. Each such
    /// prime is kD ± j with 0 < j < D/2 prime to D, and kDP = ±jP exactly
    /// when kDP and jP have the same x = X/Z, so the products of the
    /// differences x(kDP) - x(jP) over the primes meet the factor sought.
    fn stage2(&self, p: &Pt<N>, b1: u64, b2: u64, a24: &[u64; N], sieve: &Sieve) -> Result<[u64; N], Integer> {
        const D: u64 = 2310;
        // jP for odd j < D/2, then DP = 2 (D/2) P.
        let two = self.dbl(p, a24);
        let mut odd = vec![*p, self.dadd(&two, p, p)];
        while (2 * odd.len() as u64 + 1) <= D / 2 {
            let k = odd.len();
            odd.push(self.dadd(&odd[k - 1], &two, &odd[k - 2]));
        }
        let step = self.dbl(&odd[(D / 2 - 1) as usize / 2], a24);
        let (js, babies): (Vec<u64>, Vec<Pt<N>>) = (0..odd.len()).map(|i| (2 * i as u64 + 1, odd[i])).filter(|(j, _)| gcd_u64(*j, D) == 1).unzip();
        let xs = self.normalize(&babies)?;
        let k0 = (b1 / D).max(1);
        let (mut prev, mut cur) = (self.ladder(&step, k0, a24), self.ladder(&step, k0 + 1, a24));
        let mut acc = self.from_int(&Integer::one());
        let kmax = (b2 + D / 2) / D;
        let mut k = k0;
        while k <= kmax {
            // The giant steps a batch at a time, to share one inversion.
            let mut giants = Vec::with_capacity(32);
            while giants.len() < 32 && k + (giants.len() as u64) <= kmax {
                giants.push(prev);
                let next = self.dadd(&cur, &step, &prev);
                prev = cur;
                cur = next;
            }
            for (i, x) in self.normalize(&giants)?.iter().enumerate() {
                let c = (k + i as u64) * D;
                for (j, xj) in js.iter().zip(&xs) {
                    let hit = |y: u64| y > b1 && y <= b2 && sieve.is_prime(y);
                    if hit(c - j) || hit(c + j) {
                        acc = self.mul(&acc, &self.sub(x, xj));
                    }
                }
            }
            k += giants.len() as u64;
        }
        Ok(acc)
    }

    /// The coordinates x = X/Z of the points, by one inversion
    /// (Montgomery's trick); or the gcd of a Z with n when it has none.
    fn normalize(&self, pts: &[Pt<N>]) -> Result<Vec<[u64; N]>, Integer> {
        let mut prefix = Vec::with_capacity(pts.len());
        let mut c = self.from_int(&Integer::one());
        for q in pts {
            prefix.push(c);
            c = self.mul(&c, &q.z);
        }
        let mut one = [0; N];
        one[0] = 1;
        let z = Integer::from_limbs(&self.mul(&c, &one), false);
        let Some(inv) = z.invmod(&self.modulus) else { return Err(z.gcd(&self.modulus)) };
        // inv is 1 / (Z_1 ... Z_m); walk back to each 1 / Z_i.
        let mut inv = self.from_int(&inv);
        let mut xs = vec![[0; N]; pts.len()];
        for i in (0..pts.len()).rev() {
            xs[i] = self.mul(&pts[i].x, &self.mul(&inv, &prefix[i]));
            inv = self.mul(&inv, &pts[i].z);
        }
        Ok(xs)
    }
}

fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// The largest B2 for which the sieve is kept (6 MB).
const STAGE2_LIMIT: u64 = 100 << 20;

/// The odd primes up to a limit, as a bit per odd number.
struct Sieve {
    bits: Vec<u64>,
    limit: u64,
}

impl Sieve {
    fn new(limit: u64) -> Sieve {
        let odd = (limit / 2 + 1) as usize;
        let mut bits = vec![u64::MAX; odd.div_ceil(64)];
        bits[0] &= !1; // 1 is not prime
        let mut i = 1usize;
        while (2 * i + 1) * (2 * i + 1) <= limit as usize {
            if bits[i / 64] >> (i % 64) & 1 == 1 {
                let p = 2 * i + 1;
                let mut m = p * p / 2;
                while m < odd {
                    bits[m / 64] &= !(1 << (m % 64));
                    m += p;
                }
            }
            i += 1;
        }
        Sieve { bits, limit }
    }

    fn is_prime(&self, x: u64) -> bool {
        x == 2 || x & 1 == 1 && x <= self.limit && self.bits[(x / 2 / 64) as usize] >> (x / 2 % 64) & 1 == 1
    }

    /// The primes up to b.
    fn primes(&self, b: u64) -> impl Iterator<Item = u64> + '_ {
        std::iter::once(2).filter(move |_| b >= 2).chain((3..=b.min(self.limit)).step_by(2).filter(|&x| self.is_prime(x)))
    }
}

thread_local! {
    static SIEVE: RefCell<Sieve> = RefCell::new(Sieve::new(1 << 16));
}

/// Run f on a sieve that reaches at least `limit`.
fn with_primes<T>(limit: u64, f: impl FnOnce(&Sieve) -> T) -> T {
    SIEVE.with(|s| {
        if s.borrow().limit < limit {
            let l = limit.max(2 * s.borrow().limit);
            *s.borrow_mut() = Sieve::new(l);
        }
        f(&s.borrow())
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn next(s: &mut u64) -> u64 {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        *s
    }

    fn arith<const N: usize>(s: &mut u64) {
        for _ in 0..200 {
            let limbs: Vec<u64> = (0..N).map(|_| next(s)).collect();
            let mut n = Integer::from_limbs(&limbs, false);
            if n.is_even() {
                n = &n + &Integer::one();
            }
            if n.bits() < 2 {
                continue;
            }
            let m = Mont::<N>::new(&n);
            let x = Integer::from_limbs(&(0..N).map(|_| next(s)).collect::<Vec<_>>(), false).div_rem_euclid(&n).unwrap().1;
            let y = Integer::from_limbs(&(0..N).map(|_| next(s)).collect::<Vec<_>>(), false).div_rem_euclid(&n).unwrap().1;
            let (a, b) = (m.from_int(&x), m.from_int(&y));
            let r = |z: &Integer| z.div_rem_euclid(&n).unwrap().1;
            assert_eq!(m.to_int(&m.mul(&a, &b)), r(&(&x * &y)), "{x} * {y} mod {n}");
            assert_eq!(m.to_int(&m.add(&a, &b)), r(&(&x + &y)), "{x} + {y} mod {n}");
            assert_eq!(m.to_int(&m.sub(&a, &b)), r(&(&x - &y)), "{x} - {y} mod {n}");
        }
    }

    #[test]
    fn montgomery_arithmetic_agrees_with_integers() {
        let mut s = 0x9e37_79b9_7f4a_7c15;
        arith::<1>(&mut s);
        arith::<2>(&mut s);
        arith::<3>(&mut s);
        arith::<5>(&mut s);
        arith::<8>(&mut s);
    }

    #[test]
    fn curves_find_factors() {
        // Factors of 30 to 50 bits of numbers of 100 to 500 bits.
        let mut s = 0x2545_f491_4f6c_dd1d;
        for (i, bits) in [100u32, 180, 250, 320, 400, 500].into_iter().enumerate() {
            let p = Integer::from_u64(next(&mut s) >> (34 - 4 * i as u32)).next_prime();
            let q = Integer::from_u64(1).mul_2exp((bits - p.bits() as u32) as u64);
            let q = (&q + &Integer::from_u64(next(&mut s) >> 1)).next_prime();
            let n = &p * &q;
            let found = (0..400u64).find_map(|c| curve(&n, 2000, 200_000, 6 + next(&mut s) % (1 << 40) + c));
            assert!(found.is_some_and(|d| d == p || d == q), "ECM on {p} * {q}");
        }
    }
}

#[cfg(test)]
mod bench {
    use super::*;

    /// Success rate and time per curve for 58-bit factors of 88-digit numbers
    /// (`cargo test --release -p calyx-runtime --lib -- --ignored ecm_rates --nocapture`).
    #[test]
    #[ignore]
    fn ecm_rates() {
        let big = Integer::from_u64(2).pow(230).next_prime();
        let mut ps = Vec::new();
        let mut x = Integer::from_u64(2).pow(57);
        let step = Integer::parse("1234567891234567").unwrap();
        for _ in 0..60 {
            x = &x + &step;
            ps.push(x.next_prime());
        }
        for b1 in [1000u64, 2000, 3000, 5000, 8000, 11000] {
            for m in [50u64, 100, 200, 400] {
                let t = std::time::Instant::now();
                let (mut hits, mut tot, mut sigma) = (0u64, 0u64, 1000u64);
                for p in &ps {
                    let n = p * &big;
                    for _ in 0..20 {
                        sigma += 7919;
                        tot += 1;
                        hits += curve(&n, b1, m * b1, sigma).is_some() as u64;
                    }
                }
                let ms = t.elapsed().as_secs_f64() * 1000.0 / tot as f64;
                let rate = hits as f64 / tot as f64;
                println!("B1 {b1:6} B2 {m:4}xB1: {ms:.2} ms/curve, rate {rate:.3}, {:.0} ms per factor", ms / rate);
            }
        }
    }
}
