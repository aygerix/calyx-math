//! Arithmetic modulo a word-sized modulus.
//!
//! Residues are plain `u64` values in `0..n`. Multiplication reduces the
//! double-word product with a precomputed reciprocal of the normalised
//! modulus (Möller and Granlund, "Improved division by invariant integers",
//! 2011), the same scheme as FLINT's `nmod` functions, so the hot operations
//! inline into the caller instead of crossing the FFI boundary.

use flint3_sys as sys;

use crate::Integer;

/// A modulus `n ≥ 1` with the data for fast reduction.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Nmod {
    n: u64,
    /// `floor((2^128 - 1) / (n << norm)) - 2^64`, FLINT's `n_preinvert_limb(n)`.
    ninv: u64,
    /// The number of leading zero bits of `n`.
    norm: u32,
}

impl Nmod {
    /// # Panics
    /// If `n` is zero.
    pub fn new(n: u64) -> Nmod {
        assert!(n != 0, "modulus must be positive");
        let norm = n.leading_zeros();
        let d = n << norm;
        Nmod { n, ninv: (u128::MAX / d as u128) as u64, norm }
    }

    #[inline]
    pub fn modulus(self) -> u64 {
        self.n
    }

    /// `u mod n` for a double-word `u < n * 2^64`.
    #[inline]
    fn reduce_wide(self, u: u128) -> u64 {
        let s = self.norm;
        let d = self.n << s;
        // u < n * 2^64, so u << s < d * 2^64 and the high word is below d.
        let u = u << s;
        let (u1, u0) = ((u >> 64) as u64, u as u64);
        let q = (self.ninv as u128) * (u1 as u128) + u;
        let q1 = ((q >> 64) as u64).wrapping_add(1);
        let q0 = q as u64;
        let mut r = u0.wrapping_sub(q1.wrapping_mul(d));
        if r > q0 {
            r = r.wrapping_add(d);
        }
        if r >= d {
            r -= d;
        }
        r >> s
    }

    /// `x mod n`.
    #[inline]
    pub fn reduce(self, x: u64) -> u64 {
        if x < self.n { x } else { self.reduce_wide(x as u128) }
    }

    /// `x mod n` for a signed `x`.
    #[inline]
    pub fn reduce_i64(self, x: i64) -> u64 {
        let r = self.reduce(x.unsigned_abs());
        if x < 0 { self.neg(r) } else { r }
    }

    /// `x mod n` for any integer.
    pub fn reduce_integer(self, x: &Integer) -> u64 {
        match x.to_i64() {
            Some(v) => self.reduce_i64(v),
            None => unsafe { sys::fmpz_fdiv_ui(x.raw_ptr(), self.n as sys::ulong) as u64 },
        }
    }

    #[inline]
    pub fn add(self, a: u64, b: u64) -> u64 {
        let (s, carry) = a.overflowing_add(b);
        if carry || s >= self.n { s.wrapping_sub(self.n) } else { s }
    }

    #[inline]
    pub fn sub(self, a: u64, b: u64) -> u64 {
        if a >= b { a - b } else { a.wrapping_sub(b).wrapping_add(self.n) }
    }

    #[inline]
    pub fn neg(self, a: u64) -> u64 {
        if a == 0 { 0 } else { self.n - a }
    }

    #[inline]
    pub fn mul(self, a: u64, b: u64) -> u64 {
        self.reduce_wide(a as u128 * b as u128)
    }

    /// `a^e`, with `0^0 = 1` (reduced, so `0` in the zero ring).
    pub fn pow(self, a: u64, mut e: u64) -> u64 {
        let mut result = self.reduce(1);
        let mut base = a;
        while e > 0 {
            if e & 1 == 1 {
                result = self.mul(result, base);
            }
            e >>= 1;
            if e > 0 {
                base = self.mul(base, base);
            }
        }
        result
    }

    /// `a^e` for a non-negative integer exponent.
    pub fn pow_integer(self, a: u64, e: &Integer) -> u64 {
        debug_assert!(e.sign() >= 0);
        match e.to_u64() {
            Some(e) => self.pow(a, e),
            None if self.n == 1 => 0,
            None => unsafe { sys::n_powmod2_fmpz_preinv(a as sys::ulong, e.raw_ptr(), self.n as sys::ulong, self.ninv as sys::ulong) as u64 },
        }
    }

    /// The inverse of `a`, if it is a unit.
    pub fn inv(self, a: u64) -> Option<u64> {
        if self.n == 1 {
            return Some(0);
        }
        let (g, s) = gcdinv(a, self.n);
        (g == 1).then_some(s)
    }

    /// `gcd(a, n)`.
    pub fn gcd(self, a: u64) -> u64 {
        gcd(a, self.n)
    }
}

/// The greatest common divisor of two words.
pub fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// `gcd(a, n)` and, when it is 1, the inverse of `a` modulo `n` (for
/// `n ≥ 2`, `a < n`).
fn gcdinv(a: u64, n: u64) -> (u64, u64) {
    let (mut r0, mut r1) = (n as i128, a as i128);
    let (mut s0, mut s1) = (0i128, 1i128);
    while r1 != 0 {
        let q = r0 / r1;
        (r0, r1) = (r1, r0 - q * r1);
        (s0, s1) = (s1, s0 - q * s1);
    }
    (r0 as u64, s0.rem_euclid(n as i128) as u64)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A small deterministic generator (xorshift64*).
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }
    }

    fn moduli() -> Vec<u64> {
        let mut v = vec![1, 2, 3, 4, 5, 6, 7, 12, 255, 256, 257, 1000003, (1 << 31) - 1, 1 << 32, (1 << 32) + 15, (1 << 62) - 57, 1 << 62, (1 << 63) - 25, 1 << 63, (1 << 63) + 1, u64::MAX - 58, u64::MAX - 1, u64::MAX];
        let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
        for k in 1..64 {
            v.push((rng.next() >> k).max(1));
        }
        v
    }

    #[test]
    fn preinverse_matches_flint() {
        for n in moduli() {
            let m = Nmod::new(n);
            assert_eq!(m.ninv, unsafe { sys::n_preinvert_limb(n as sys::ulong) } as u64, "n = {n}");
        }
    }

    #[test]
    fn arithmetic_agrees_with_wide_integers() {
        let mut rng = Rng(12345);
        for n in moduli() {
            let m = Nmod::new(n);
            let mut samples = vec![0, 1, n - 1, n / 2, n.saturating_sub(2)];
            for _ in 0..200 {
                samples.push(rng.next() % n);
            }
            for &a in &samples {
                assert_eq!(m.reduce(a), a % n);
                assert_eq!(m.neg(a), ((n as u128 - a as u128) % n as u128) as u64);
                for &b in samples.iter().take(40) {
                    let (a, b) = (a % n, b % n);
                    assert_eq!(m.mul(a, b), ((a as u128 * b as u128) % n as u128) as u64, "{a} * {b} mod {n}");
                    assert_eq!(m.add(a, b), ((a as u128 + b as u128) % n as u128) as u64, "{a} + {b} mod {n}");
                    assert_eq!(m.sub(a, b), ((a as u128 + n as u128 - b as u128) % n as u128) as u64, "{a} - {b} mod {n}");
                }
            }
            for _ in 0..50 {
                let x = rng.next();
                assert_eq!(m.reduce(x), x % n);
                let y = rng.next() as i64;
                assert_eq!(m.reduce_i64(y), (y as i128).rem_euclid(n as i128) as u64);
            }
        }
    }

    #[test]
    fn powers_and_inverses() {
        let mut rng = Rng(777);
        for n in moduli() {
            let m = Nmod::new(n);
            for _ in 0..20 {
                let a = rng.next() % n;
                let e = rng.next() % 1000;
                let mut slow = 1 % n;
                for _ in 0..e {
                    slow = ((slow as u128 * a as u128) % n as u128) as u64;
                }
                assert_eq!(m.pow(a, e), slow, "{a}^{e} mod {n}");
                // A big exponent agrees with FLINT's.
                let big = &Integer::from_u64(u64::MAX) * &Integer::from_u64(e + 3);
                let direct = if n == 1 { 0 } else { unsafe { sys::n_powmod2_fmpz_preinv(a as sys::ulong, big.raw_ptr(), n as sys::ulong, m.ninv as sys::ulong) as u64 } };
                assert_eq!(m.pow_integer(a, &big), direct);
                match m.inv(a) {
                    Some(b) => assert_eq!(m.mul(a, b), 1 % n),
                    None => assert_ne!(gcd(a, n), 1),
                }
            }
        }
        assert_eq!(Nmod::new(12).inv(5), Some(5));
        assert_eq!(Nmod::new(12).inv(4), None);
        assert_eq!(Nmod::new(1).pow(0, 0), 0);
    }

    #[test]
    fn reduces_big_integers() {
        let m = Nmod::new(1000003);
        let x = Integer::from_u64(u64::MAX).pow(3);
        let expect = {
            let r = (u64::MAX % 1000003) as u128;
            ((r * r % 1000003) * r % 1000003) as u64
        };
        assert_eq!(m.reduce_integer(&x), expect);
        assert_eq!(m.reduce_integer(&-&x), (1000003 - expect) % 1000003);
    }
}
