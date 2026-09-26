//! Discrete logarithms modulo primes and prime powers.
//!
//! Modulo a prime, Pohlig–Hellman reduces the logarithm to subgroups of
//! prime order, solved by baby-step giant-step or, for primes too large
//! for its table, Pollard's rho. The part of order a power of p modulo
//! p^k is read off the p-adic logarithm instead.
//!
//! In groups whose elements are words (modulo a word-sized prime, and in
//! GF(2^n) for n up to 64) the baby steps are kept between logarithms, and
//! the table grows with the number of logarithms taken to the same base, so
//! that many logarithms cost less each.

use std::cell::RefCell;

use calyx_flint::gf2x::Gf2Field;
use calyx_flint::{Integer, Nmod};
use rustc_hash::FxHashMap;

/// Prime orders up to this use baby-step giant-step.
const BSGS_LIMIT: u64 = 1 << 40;

/// Arithmetic in the multiplicative group modulo some integer.
trait Units {
    type E: Clone + PartialEq;
    fn mul(&self, a: &Self::E, b: &Self::E) -> Self::E;
    fn pow(&self, a: &Self::E, e: &Integer) -> Self::E;
    fn inv(&self, a: &Self::E) -> Self::E;
    fn one(&self) -> Self::E;
    /// A hash of the element for the baby-step table.
    fn key(&self, a: &Self::E) -> u64;
    /// For groups of words: the group, as a key for the kept baby steps,
    /// and the element as a word.
    fn word_group(&self) -> Option<(u64, u64)> {
        None
    }
    fn word(&self, _a: &Self::E) -> u64 {
        unreachable!("an element of a group of words")
    }
}

impl Units for Nmod {
    type E = u64;
    fn mul(&self, a: &u64, b: &u64) -> u64 {
        Nmod::mul(*self, *a, *b)
    }
    fn pow(&self, a: &u64, e: &Integer) -> u64 {
        self.pow_integer(*a, e)
    }
    fn inv(&self, a: &u64) -> u64 {
        Nmod::inv(*self, *a).expect("a unit")
    }
    fn one(&self) -> u64 {
        self.reduce(1)
    }
    fn key(&self, a: &u64) -> u64 {
        *a
    }
    fn word_group(&self) -> Option<(u64, u64)> {
        Some((0, self.modulus()))
    }
    fn word(&self, a: &u64) -> u64 {
        *a
    }
}

/// GF(2^n) for n up to 64, in words.
impl Units for Gf2Field {
    type E = u64;
    fn mul(&self, a: &u64, b: &u64) -> u64 {
        Gf2Field::mul(self, *a, *b)
    }
    fn pow(&self, a: &u64, e: &Integer) -> u64 {
        // Exponents modulo 2^n - 1, which the order of a unit divides.
        let e = e.div_rem_euclid(&Integer::from_u64(u64::MAX >> (64 - self.degree()))).and_then(|(_, r)| r.to_u64()).unwrap_or(0);
        Gf2Field::pow(self, *a, e)
    }
    fn inv(&self, a: &u64) -> u64 {
        Gf2Field::inv(self, *a)
    }
    fn one(&self) -> u64 {
        1
    }
    fn key(&self, a: &u64) -> u64 {
        *a
    }
    fn word_group(&self) -> Option<(u64, u64)> {
        // The modulus x^n + g (a modulus of words is at least 2).
        Some((self.degree() as u64, self.modulus_low()))
    }
    fn word(&self, a: &u64) -> u64 {
        *a
    }
}

struct BigMod(Integer);

impl Units for BigMod {
    type E = Integer;
    fn mul(&self, a: &Integer, b: &Integer) -> Integer {
        (a * b).div_rem_euclid(&self.0).unwrap().1
    }
    fn pow(&self, a: &Integer, e: &Integer) -> Integer {
        a.powm(e, &self.0).expect("a unit")
    }
    fn inv(&self, a: &Integer) -> Integer {
        a.invmod(&self.0).expect("a unit")
    }
    fn one(&self) -> Integer {
        Integer::one()
    }
    fn key(&self, a: &Integer) -> u64 {
        a.hash_u64()
    }
}

/// The multiplicative group of a finite field.
struct FieldUnits(std::rc::Rc<calyx_flint::gr::Ctx>);

/// A field element compared by value.
#[derive(Clone)]
struct Fe(calyx_flint::gr::Elem);

impl PartialEq for Fe {
    fn eq(&self, o: &Fe) -> bool {
        self.0.equal(&o.0) == calyx_flint::gr::Truth::True
    }
}

impl Units for FieldUnits {
    type E = Fe;
    fn mul(&self, a: &Fe, b: &Fe) -> Fe {
        Fe(a.0.mul(&b.0).expect("field multiplication"))
    }
    fn pow(&self, a: &Fe, e: &Integer) -> Fe {
        Fe(a.0.pow(e).expect("field power"))
    }
    fn inv(&self, a: &Fe) -> Fe {
        Fe(a.0.inv().expect("a unit"))
    }
    fn one(&self) -> Fe {
        Fe(calyx_flint::gr::Elem::one(&self.0).expect("field one"))
    }
    fn key(&self, a: &Fe) -> u64 {
        a.0.fq_coords_u64().iter().fold(0xcbf2_9ce4_8422_2325u64, |h, &c| (h ^ c).wrapping_mul(0x0100_0000_01b3))
    }
}

/// The least x >= 0 with g^x = y in a finite field of word-sized
/// characteristic, for g of order n with factorisation `nf`. `None` if y is
/// not a power of g, or if n has a prime factor too large to handle.
pub fn log_in_field(y: &calyx_flint::gr::Elem, g: &calyx_flint::gr::Elem, n: &Integer, nf: &[(Integer, u64)]) -> Option<Integer> {
    if let (Some(k), Some(yw), Some(gw)) = (y.ctx().fq_gf2_field(), y.fq_gf2_bits(), g.fq_gf2_bits()) {
        let x = pohlig_hellman(&k, &gw, &yw, n, nf)?;
        return (Units::pow(&k, &gw, &x) == yw).then_some(x);
    }
    let u = FieldUnits(y.ctx().clone());
    let x = pohlig_hellman(&u, &Fe(g.clone()), &Fe(y.clone()), n, nf)?;
    (u.pow(&Fe(g.clone()), &x) == Fe(y.clone())).then_some(x)
}

/// The least x >= 0 with g^x = y modulo the prime p, for a primitive root
/// g, given the factorisation of p - 1. `None` if y is not a unit, or if
/// p - 1 has a prime factor too large to handle.
pub fn log_mod_prime(y: &Integer, g: &Integer, p: &Integer, pm1: &[(Integer, u64)]) -> Option<Integer> {
    let y = y.div_rem_euclid(p)?.1;
    if y.is_zero() {
        return None;
    }
    let n = p - &Integer::one();
    match p.to_u64() {
        Some(q) => {
            let m = Nmod::new(q);
            pohlig_hellman(&m, &m.reduce_integer(g), &m.reduce_integer(&y), &n, pm1)
        }
        None => {
            let m = BigMod(p.clone());
            pohlig_hellman(&m, &g.div_rem_euclid(p)?.1, &y, &n, pm1)
        }
    }
}

/// log_g(y) modulo the order of `(1 + pZ) / (1 + p^k Z)` for `y` and a
/// generator `g` of that group, both 1 modulo p (modulo 4 if p = 2, where
/// the group of such elements has order 2^(k-2)).
///
/// Raising `y` to the order n of the group gives `1 + n*log(y) mod p^k n`
/// (the p-adic logarithm), whose ratio for `y` and `g` is the answer.
pub fn log_one_units(y: &Integer, g: &Integer, p: &Integer, k: u64) -> Option<Integer> {
    let two = p.to_u64() == Some(2);
    let e = if two { k.checked_sub(2)? } else { k - 1 };
    let n = p.pow(e);
    let pk = p.pow(k);
    let big = &pk * &n;
    let lam = |z: &Integer| -> Option<Integer> {
        let w = z.powm(&n, &big)?;
        Some((&w - &Integer::one()).divexact(&pk).div_rem_euclid(&n)?.1)
    };
    if n.is_one() {
        return Some(Integer::zero());
    }
    let inv = lam(g)?.invmod(&n)?;
    Some((&lam(y)? * &inv).div_rem_euclid(&n)?.1)
}

/// x in [0, n) with g^x = y, where g has order n with factorisation `nf`.
fn pohlig_hellman<U: Units>(u: &U, g: &U::E, y: &U::E, n: &Integer, nf: &[(Integer, u64)]) -> Option<Integer> {
    let mut x = Integer::zero();
    let mut modulus = Integer::one();
    for (q, e) in nf {
        let qe = q.pow(*e);
        let co = n.divexact(&qe);
        // gq has order q^e; find log_gq(yq) one base-q digit at a time.
        let gq = u.pow(g, &co);
        let yq = u.pow(y, &co);
        let gamma = u.pow(&gq, &q.pow(e - 1));
        let gq_inv = u.inv(&gq);
        let mut xq = Integer::zero();
        let mut qk = Integer::one();
        let mut rest = yq;
        for k in 0..*e {
            let h = u.pow(&rest, &q.pow(e - 1 - k));
            let d = prime_order_log(u, &gamma, &h, q)?;
            let t = &d * &qk;
            rest = u.mul(&rest, &u.pow(&gq_inv, &t));
            xq += &t;
            qk = &qk * q;
        }
        // Combine x mod `modulus` with xq mod q^e.
        let inv = modulus.invmod(&qe).unwrap_or_else(Integer::one);
        let t = (&(&xq - &x) * &inv).div_rem_euclid(&qe)?.1;
        x = &x + &(&modulus * &t);
        modulus = &modulus * &qe;
    }
    Some(x)
}

/// log_gamma(h) for gamma of prime order q.
fn prime_order_log<U: Units>(u: &U, gamma: &U::E, h: &U::E, q: &Integer) -> Option<Integer> {
    if *h == u.one() {
        return Some(Integer::zero());
    }
    let q = q.to_u64()?;
    let x = if q <= BSGS_LIMIT { bsgs(u, gamma, h, q) } else { rho(u, gamma, h, q) }?;
    Some(Integer::from_u64(x))
}

/// Baby steps gamma^j (j < m) of a group of words, as a table from the
/// word (hashed) to j: slots of a 32-bit fingerprint and j + 1 (0 when
/// empty), at most half full. False matches are caught by the caller.
struct Babies {
    group: (u64, u64),
    gamma: u64,
    q: u64,
    m: u64,
    slots: Vec<u64>,
    /// The logarithms taken with these baby steps.
    uses: u64,
}

/// The most baby steps kept for one base (16 MB of table).
const BABIES_MAX: u64 = 1 << 20;

// Tables of baby steps for the last few bases.
thread_local! {
    static BABIES: RefCell<Vec<Babies>> = const { RefCell::new(Vec::new()) };
}

fn mix(w: u64) -> u64 {
    let w = (w ^ (w >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    let w = (w ^ (w >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    w ^ (w >> 31)
}

impl Babies {
    fn slot(&self, w: u64) -> (usize, u64) {
        let h = mix(w);
        ((h >> (64 - self.slots.len().trailing_zeros())) as usize, h & 0xffff_ffff)
    }

    /// Baby steps up to m.
    fn build<U: Units>(&mut self, u: &U, gamma: &U::E, m: u64) {
        self.m = m;
        self.slots = vec![0; (2 * m).next_power_of_two().max(2) as usize];
        let mask = self.slots.len() - 1;
        let mut cur = u.one();
        for j in 0..m {
            let (mut i, f) = self.slot(u.word(&cur));
            while self.slots[i] != 0 {
                i = (i + 1) & mask;
            }
            self.slots[i] = f << 32 | (j + 1);
            cur = u.mul(&cur, gamma);
        }
    }

    /// The j with gamma^j = w, if w is a baby step (or matches one's
    /// fingerprint).
    fn find(&self, w: u64) -> impl Iterator<Item = u64> + '_ {
        let (i, f) = self.slot(w);
        let mask = self.slots.len() - 1;
        (0..self.slots.len()).map(move |k| self.slots[(i + k) & mask]).take_while(|&s| s != 0).filter(move |&s| s >> 32 == f).map(|s| (s & 0xffff_ffff) - 1)
    }
}

/// Baby-step giant-step with the baby steps kept between calls, for a
/// group of words: the table grows as sqrt(q t) for the t-th logarithm to
/// this base, up to `BABIES_MAX`.
fn bsgs_kept<U: Units>(u: &U, group: (u64, u64), gamma: &U::E, h: &U::E, q: u64) -> Option<u64> {
    let gw = u.word(gamma);
    BABIES.with(|b| {
        let mut b = b.borrow_mut();
        let k = match b.iter().position(|t| (t.group, t.gamma, t.q) == (group, gw, q)) {
            Some(k) => k,
            None => {
                if b.len() >= 4 {
                    b.remove(0);
                }
                b.push(Babies { group, gamma: gw, q, m: 0, slots: Vec::new(), uses: 0 });
                b.len() - 1
            }
        };
        let t = &mut b[k];
        t.uses += 1;
        let want = (((q as f64) * t.uses as f64).sqrt().ceil() as u64).clamp(1, BABIES_MAX.min(q));
        if want >= 2 * t.m || t.m == 0 {
            t.build(u, gamma, want);
        }
        let m = t.m;
        let giant = u.inv(&u.pow(gamma, &Integer::from_u64(m)));
        let mut z = h.clone();
        // Giant steps in blocks, whose first slots are read together, so
        // that the table's cache misses overlap.
        const B: u64 = 16;
        let mut words = [0u64; B as usize];
        let mut i0 = 0;
        while i0 <= q / m {
            for w in words.iter_mut() {
                *w = u.word(&z);
                z = u.mul(&z, &giant);
            }
            let firsts = words.map(|w| t.slots[t.slot(w).0]);
            for (k, (&w, &f)) in words.iter().zip(&firsts).enumerate() {
                if f == 0 {
                    continue;
                }
                for j in t.find(w) {
                    let x = (((i0 + k as u64) as u128 * m as u128 + j as u128) % q as u128) as u64;
                    if u.pow(gamma, &Integer::from_u64(x)) == *h {
                        return Some(x);
                    }
                }
            }
            i0 += B;
        }
        None
    })
}

fn bsgs<U: Units>(u: &U, gamma: &U::E, h: &U::E, q: u64) -> Option<u64> {
    if let Some(group) = u.word_group().filter(|_| q > 1 << 12) {
        return bsgs_kept(u, group, gamma, h, q);
    }
    let m = ((q as f64).sqrt().ceil() as u64).max(1);
    let mut table: FxHashMap<u64, u64> = FxHashMap::with_capacity_and_hasher(m as usize, Default::default());
    let mut cur = u.one();
    for j in 0..m {
        table.entry(u.key(&cur)).or_insert(j);
        cur = u.mul(&cur, gamma);
    }
    let giant = u.inv(&cur);
    let mut z = h.clone();
    for i in 0..=q / m {
        if let Some(&j) = table.get(&u.key(&z)) {
            let x = (i * m + j) % q;
            if u.pow(gamma, &Integer::from_u64(x)) == *h {
                return Some(x);
            }
        }
        z = u.mul(&z, &giant);
    }
    None
}

/// Pollard's rho with an adding walk and Brent's cycle detection.
fn rho<U: Units>(u: &U, gamma: &U::E, h: &U::E, q: u64) -> Option<u64> {
    const R: usize = 20;
    let add = |a: u64, b: u64| ((a as u128 + b as u128) % q as u128) as u64;
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = || {
        seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = seed;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        (z ^ (z >> 31)) % q
    };
    for _attempt in 0..8 {
        let steps: Vec<(U::E, u64, u64)> = (0..R)
            .map(|_| {
                let (a, b) = (next(), next());
                (u.mul(&u.pow(gamma, &Integer::from_u64(a)), &u.pow(h, &Integer::from_u64(b))), a, b)
            })
            .collect();
        let walk = |x: &U::E, a: u64, b: u64| {
            let (m, da, db) = &steps[(u.key(x) % R as u64) as usize];
            (u.mul(x, m), add(a, *da), add(b, *db))
        };
        let (a0, b0) = (next(), next());
        let x0 = u.mul(&u.pow(gamma, &Integer::from_u64(a0)), &u.pow(h, &Integer::from_u64(b0)));
        let (mut tort, mut ta, mut tb) = (x0.clone(), a0, b0);
        let (mut hare, mut ha, mut hb) = walk(&x0, a0, b0);
        let (mut power, mut lam) = (1u64, 1u64);
        let limit = 64 * ((q as f64).sqrt() as u64 + 1);
        let mut count = 0u64;
        while hare != tort {
            if power == lam {
                (tort, ta, tb) = (hare.clone(), ha, hb);
                power *= 2;
                lam = 0;
            }
            (hare, ha, hb) = walk(&hare, ha, hb);
            lam += 1;
            count += 1;
            if count > limit {
                break;
            }
        }
        if hare != tort || hb == tb {
            continue;
        }
        // gamma^ta h^tb = gamma^ha h^hb, so log h = (ta - ha) / (hb - tb).
        let qi = Integer::from_u64(q);
        let num = Integer::from_u64(ta) - Integer::from_u64(ha);
        let den = Integer::from_u64(hb) - Integer::from_u64(tb);
        let inv = den.div_rem_euclid(&qi)?.1.invmod(&qi)?;
        let x = (&num * &inv).div_rem_euclid(&qi)?.1.to_u64()?;
        if u.pow(gamma, &Integer::from_u64(x)) == *h {
            return Some(x);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(n: i64) -> Integer {
        Integer::from_i64(n)
    }

    fn check_prime(p: i64) {
        let pi = int(p);
        let g = crate::intrinsics::ints::primitive_root(&pi).unwrap();
        let f = crate::intrinsics::factseq::factor(&(&pi - &Integer::one()));
        for y in [1, 2, 3, p - 1, p / 2 + 1] {
            if y % p == 0 {
                assert_eq!(log_mod_prime(&int(y), &g, &pi, &f), None);
                continue;
            }
            let x = log_mod_prime(&int(y), &g, &pi, &f).unwrap();
            assert_eq!(g.powm(&x, &pi).unwrap(), int(y).div_rem_euclid(&pi).unwrap().1, "p = {p}, y = {y}");
        }
    }

    #[test]
    fn logs_modulo_primes() {
        for p in [3, 5, 7, 97, 7919, 1_000_003, 2_147_483_647, 1_000_000_007] {
            check_prime(p);
        }
    }

    #[test]
    fn rho_on_a_large_prime_order() {
        // p = 2q + 1 with q = 2^41 + 477 prime, past the BSGS limit.
        let q = (1u64 << 41) + 477;
        assert!(Integer::from_u64(q).is_prime() && Integer::from_u64(2 * q + 1).is_prime());
        check_prime(2 * q as i64 + 1);
    }

    #[test]
    fn logs_of_one_units() {
        // 3 generates the units modulo 49; 3^6 = 43 generates 1 + 7Z.
        let (p, k) = (int(7), 2);
        let g = int(43);
        for x in 0..7 {
            let y = g.powm(&int(x), &int(49)).unwrap();
            assert_eq!(log_one_units(&y, &g, &p, k), Some(int(x)));
        }
        // 5 generates the units 1 mod 4 modulo 2^10.
        let m = int(1024);
        for x in [0, 1, 5, 100, 255] {
            let y = int(5).powm(&int(x), &m).unwrap();
            assert_eq!(log_one_units(&y, &int(5), &int(2), 10), Some(int(x)));
        }
    }
}
