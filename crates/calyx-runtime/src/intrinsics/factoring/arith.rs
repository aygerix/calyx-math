//! Arithmetic modulo an odd n > 1 for ECM, the p ± 1 methods and ECPP:
//! numbers in Montgomery form in fixed arrays of words for n of up to 1024
//! bits, and FLINT's normalised limbs (calyx_flint::modn) beyond.

use calyx_flint::Integer;
use calyx_flint::modn::ModN;

/// The residues modulo n that the factoring methods compute with. Each has
/// one form, so residues are equal when their forms are.
pub trait Ring {
    type E: Clone + PartialEq;
    fn modulus(&self) -> &Integer;
    /// The residue of any integer.
    fn from_int(&self, x: &Integer) -> Self::E;
    /// The integer in [0, n) that a residue stands for.
    fn to_int(&self, a: &Self::E) -> Integer;
    fn one(&self) -> Self::E;
    fn mul(&self, a: &Self::E, b: &Self::E) -> Self::E;
    fn add(&self, a: &Self::E, b: &Self::E) -> Self::E;
    fn sub(&self, a: &Self::E, b: &Self::E) -> Self::E;
    /// gcd(a, n).
    fn gcd(&self, a: &Self::E) -> Integer;

    fn sqr(&self, a: &Self::E) -> Self::E {
        self.mul(a, a)
    }

    /// x^e for e at least 0, by windows of up to 5 bits.
    fn pow(&self, x: &Self::E, e: &Integer) -> Self::E {
        let limbs = e.to_limbs();
        let bit = |i: usize| limbs[i / 64] >> (i % 64) & 1 == 1;
        let x2 = self.sqr(x);
        let mut odd = vec![x.clone()];
        for i in 1..16 {
            odd.push(self.mul(&odd[i - 1], &x2));
        }
        let mut acc = self.one();
        // The bits below i are still to come.
        let mut i = e.bits() as usize;
        while i > 0 {
            if !bit(i - 1) {
                acc = self.sqr(&acc);
                i -= 1;
                continue;
            }
            // The window from bit i - 1 down to bit j, which is 1.
            let mut j = i.saturating_sub(5);
            while !bit(j) {
                j += 1;
            }
            let mut w = 0;
            for t in (j..i).rev() {
                acc = self.sqr(&acc);
                w = w << 1 | bit(t) as usize;
            }
            acc = self.mul(&acc, &odd[w >> 1]);
            i = j;
        }
        acc
    }

    /// A proper divisor of n from g = gcd(., n), if g is one.
    fn proper(&self, g: Integer) -> Option<Integer> {
        (!g.is_one() && !g.is_zero() && g != *self.modulus()).then_some(g)
    }

    /// 1/(x_1 ... x_m) and so each 1/x_i by one inversion (Montgomery's
    /// trick), or the gcd of their product with n when it has none.
    fn invert_all(&self, xs: &mut [Self::E]) -> Result<(), Integer> {
        let mut prefix = Vec::with_capacity(xs.len());
        let mut c = self.one();
        for x in xs.iter() {
            prefix.push(c.clone());
            c = self.mul(&c, x);
        }
        let z = self.to_int(&c);
        let Some(inv) = z.invmod(self.modulus()) else { return Err(z.gcd(self.modulus())) };
        let mut inv = self.from_int(&inv);
        for i in (0..xs.len()).rev() {
            let xi = self.mul(&inv, &prefix[i]);
            inv = self.mul(&inv, &xs[i]);
            xs[i] = xi;
        }
        Ok(())
    }
}

/// Run `$body` with `$r` bound to the ring for the odd modulus `$n`.
macro_rules! with_ring {
    ($n:expr, |$r:ident| $body:expr) => {{
        use $crate::intrinsics::factoring::arith::{Big, Mont};
        let n: &calyx_flint::Integer = $n;
        match n.bits().div_ceil(64) {
            0 | 1 => { let $r = &Mont::<1>::new(n); $body }
            2 => { let $r = &Mont::<2>::new(n); $body }
            3 => { let $r = &Mont::<3>::new(n); $body }
            4 => { let $r = &Mont::<4>::new(n); $body }
            5 => { let $r = &Mont::<5>::new(n); $body }
            6 => { let $r = &Mont::<6>::new(n); $body }
            7 => { let $r = &Mont::<7>::new(n); $body }
            8 => { let $r = &Mont::<8>::new(n); $body }
            9 | 10 => { let $r = &Mont::<10>::new(n); $body }
            11 | 12 => { let $r = &Mont::<12>::new(n); $body }
            13 | 14 => { let $r = &Mont::<14>::new(n); $body }
            15 | 16 => { let $r = &Mont::<16>::new(n); $body }
            _ => { let $r = &Big::new(n); $body }
        }
    }};
}
pub(crate) use with_ring;

/// The residues modulo an odd n < 2^(64N), each held as x 2^(64N) mod n.
pub struct Mont<const N: usize> {
    n: [u64; N],
    /// -1/n modulo 2^64.
    ninv: u64,
    /// 2^(64N) mod n, the form of 1, and 2^(128N) mod n, which takes a
    /// residue to its form.
    r1: [u64; N],
    r2: [u64; N],
    modulus: Integer,
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
    pub fn new(n: &Integer) -> Self {
        let a: [u64; N] = words(n);
        // Newton's iteration for 1/n modulo 2^64 doubles the correct bits.
        let mut inv = 1u64;
        for _ in 0..6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(a[0].wrapping_mul(inv)));
        }
        let r = |e: u64| words(&Integer::one().mul_2exp(e).div_rem_euclid(n).unwrap().1);
        Mont { n: a, ninv: inv.wrapping_neg(), r1: r(64 * N as u64), r2: r(128 * N as u64), modulus: n.clone() }
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
}

impl<const N: usize> Ring for Mont<N> {
    type E = [u64; N];

    fn modulus(&self) -> &Integer {
        &self.modulus
    }

    fn from_int(&self, x: &Integer) -> [u64; N] {
        if x.sign() >= 0 && *x < self.modulus {
            return self.mul(&words(x), &self.r2);
        }
        words(&x.mul_2exp(64 * N as u64).div_rem_euclid(&self.modulus).unwrap().1)
    }

    fn to_int(&self, a: &[u64; N]) -> Integer {
        let mut one = [0; N];
        one[0] = 1;
        Integer::from_limbs(&self.mul(a, &one), false)
    }

    fn one(&self) -> [u64; N] {
        self.r1
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

    /// a^2 / 2^(64N) mod n: the square with each cross product once, then
    /// Montgomery's reduction word by word (SOS), about 3/4 of the products.
    /// It beats the product (measured) for up to 6 words.
    #[inline(always)]
    fn sqr(&self, a: &[u64; N]) -> [u64; N] {
        if N > 6 {
            return self.mul(a, a);
        }
        // t holds 2N words.
        let mut t = [0u64; 12];
        for i in 0..N {
            let mut c = 0;
            for j in i + 1..N {
                (t[i + j], c) = mac(t[i + j], a[i], a[j], c);
            }
            t[i + N] = c;
        }
        let mut carry = 0;
        for w in t.iter_mut().take(2 * N) {
            (*w, carry) = (*w << 1 | carry, *w >> 63);
        }
        let mut c = 0;
        for i in 0..N {
            let (lo, hi) = mac(0, a[i], a[i], 0);
            let (x, c1) = t[2 * i].overflowing_add(lo);
            let (x, c2) = x.overflowing_add(c);
            t[2 * i] = x;
            let (y, c3) = t[2 * i + 1].overflowing_add(hi);
            let (y, c4) = y.overflowing_add((c1 | c2) as u64);
            t[2 * i + 1] = y;
            c = (c3 | c4) as u64;
        }
        // The carry out of word i + N of each row goes into the next row's.
        let mut over = false;
        for i in 0..N {
            let m = t[i].wrapping_mul(self.ninv);
            let mut c = 0;
            for j in 0..N {
                (t[i + j], c) = mac(t[i + j], m, self.n[j], c);
            }
            let (x, o1) = t[i + N].overflowing_add(c);
            let (x, o2) = x.overflowing_add(over as u64);
            t[i + N] = x;
            over = o1 | o2;
        }
        let mut r = [0; N];
        r.copy_from_slice(&t[N..2 * N]);
        self.reduce(r, over)
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

    /// For a in Montgomery form (2^(64N) is prime to n).
    fn gcd(&self, a: &[u64; N]) -> Integer {
        Integer::from_limbs(a, false).gcd(&self.modulus)
    }
}

/// The residues modulo n of more than 1024 bits, on FLINT's limbs.
pub struct Big {
    m: ModN,
    one: Vec<u64>,
}

impl Big {
    pub fn new(n: &Integer) -> Big {
        let m = ModN::new(n);
        let one = m.one();
        Big { m, one }
    }
}

impl Ring for Big {
    type E = Vec<u64>;

    fn modulus(&self) -> &Integer {
        self.m.modulus()
    }

    fn from_int(&self, x: &Integer) -> Vec<u64> {
        self.m.residue(x)
    }

    fn to_int(&self, a: &Vec<u64>) -> Integer {
        self.m.value(a)
    }

    fn one(&self) -> Vec<u64> {
        self.one.clone()
    }

    fn mul(&self, a: &Vec<u64>, b: &Vec<u64>) -> Vec<u64> {
        let mut r = self.m.zero();
        self.m.mul(&mut r, a, b);
        r
    }

    fn sqr(&self, a: &Vec<u64>) -> Vec<u64> {
        let mut r = self.m.zero();
        self.m.sqr(&mut r, a);
        r
    }

    fn add(&self, a: &Vec<u64>, b: &Vec<u64>) -> Vec<u64> {
        let mut r = self.m.zero();
        self.m.add(&mut r, a, b);
        r
    }

    fn sub(&self, a: &Vec<u64>, b: &Vec<u64>) -> Vec<u64> {
        let mut r = self.m.zero();
        self.m.sub(&mut r, a, b);
        r
    }

    fn gcd(&self, a: &Vec<u64>) -> Integer {
        self.m.gcd(a)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    pub fn next(s: &mut u64) -> u64 {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        *s
    }

    fn check<R: Ring>(r: &R, s: &mut u64) {
        let n = r.modulus().clone();
        let size = n.bits().div_ceil(64) as usize;
        for _ in 0..50 {
            let x = Integer::from_limbs(&(0..size).map(|_| next(s)).collect::<Vec<_>>(), false).div_rem_euclid(&n).unwrap().1;
            let y = Integer::from_limbs(&(0..size).map(|_| next(s)).collect::<Vec<_>>(), false).div_rem_euclid(&n).unwrap().1;
            let (a, b) = (r.from_int(&x), r.from_int(&y));
            let m = |z: &Integer| z.div_rem_euclid(&n).unwrap().1;
            assert_eq!(r.to_int(&r.mul(&a, &b)), m(&(&x * &y)), "{x} * {y} mod {n}");
            assert_eq!(r.to_int(&r.sqr(&a)), m(&(&x * &x)), "{x}^2 mod {n}");
            assert_eq!(r.to_int(&r.add(&a, &b)), m(&(&x + &y)), "{x} + {y} mod {n}");
            assert_eq!(r.to_int(&r.sub(&a, &b)), m(&(&x - &y)), "{x} - {y} mod {n}");
            assert_eq!(r.to_int(&r.one()), Integer::one());
            let e = Integer::from_limbs(&[next(s), next(s) >> (next(s) % 64)], false);
            assert_eq!(r.to_int(&r.pow(&a, &e)), x.powm(&e, &n).unwrap(), "{x}^{e} mod {n}");
            assert_eq!(r.to_int(&r.pow(&a, &Integer::zero())), Integer::one());
            let mut v = vec![a.clone(), b.clone()];
            if r.invert_all(&mut v).is_ok() {
                assert_eq!(r.to_int(&r.mul(&v[0], &a)), Integer::one());
                assert_eq!(r.to_int(&r.mul(&v[1], &b)), Integer::one());
            }
        }
    }

    #[test]
    fn rings_agree_with_integers() {
        let mut s = 0x9e37_79b9_7f4a_7c15;
        for words in [1u64, 2, 3, 5, 8, 9, 13, 16, 20] {
            for _ in 0..4 {
                let limbs: Vec<u64> = (0..words).map(|_| next(&mut s)).collect();
                let mut n = Integer::from_limbs(&limbs, false);
                if n.is_even() {
                    n = &n + &Integer::one();
                }
                if n.bits() < 2 {
                    continue;
                }
                with_ring!(&n, |r| check(r, &mut s));
            }
        }
    }
}


