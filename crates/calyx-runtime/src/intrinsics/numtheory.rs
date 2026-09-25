//! Primes, modular arithmetic, residue symbols, norm equations and
//! Dickman's rho function.

use calyx_flint::{Integer, Real, bits_for_digits};

use super::reals::DEFAULT_DIGITS;
use super::{arg_ge, arg_le, arg_prime, boolv, intv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

/// `x mod m` in `[0, m)` for `m > 0`.
pub fn modp(x: &Integer, m: &Integer) -> Integer {
    x.fdiv_qr(m).unwrap().1
}

// ----- primes -------------------------------------------------------------------

/// Primality as the `Proof` parameter asks for (negatives of primes are
/// prime too).
fn prime_test(n: &Integer, proof: bool) -> bool {
    if proof { n.is_prime() } else { n.is_probable_prime() }
}

fn proof(a: &CallArgs) -> bool {
    !matches!(a.param("Proof"), Some(Value::Bool(false)))
}

fn is_prime(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    boolv(prime_test(a.int(0)?, proof(a)))
}

fn is_probable_prime(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    boolv(a.int(0)?.is_probable_prime())
}

fn is_prime_power(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int_ge(0, 2)?;
    let (b, e) = n.perfect_power().unwrap_or((n.clone(), 1));
    // b^e with e largest; b is then prime if n is a prime power.
    if b.is_prime() {
        return Ok(vec![Value::Bool(true), Value::Int(b), Value::Int(Integer::from_u64(e))]);
    }
    Ok(vec![Value::Bool(false), Value::Undef, Value::Undef])
}

fn next_prime(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int_ge(0, 0)?;
    if proof(a) {
        return intv(n.next_prime());
    }
    let mut p = &n + 1;
    while !p.is_probable_prime() {
        p = &p + 1;
    }
    intv(p)
}

fn previous_prime(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    intv(a.int_ge(0, 3)?.previous_prime().unwrap())
}

/// Calls `f` with the primes in `[lo, hi]` in increasing order until it
/// returns false. A segmented sieve of Eratosthenes over the odd numbers,
/// with memory proportional to sqrt(hi); `hi` must be below 2^62.
pub fn each_prime(lo: u64, hi: u64, f: &mut dyn FnMut(u64) -> bool) {
    if hi < 2 || lo > hi {
        return;
    }
    if lo <= 2 && !f(2) {
        return;
    }
    let mut base = Vec::new();
    each_prime(3, hi.isqrt(), &mut |p| {
        base.push(p);
        true
    });
    // Each segment holds SEG odd numbers, from `start` on.
    const SEG: u64 = 1 << 18;
    let mut sieve = vec![false; SEG as usize];
    let mut start = lo.max(3) | 1;
    while start <= hi {
        let end = (start + 2 * (SEG - 1)).min(hi);
        let len = ((end - start) / 2 + 1) as usize;
        sieve[..len].fill(false);
        for &p in &base {
            if p * p > end {
                break;
            }
            let mut m = start.div_ceil(p).max(p) * p;
            if m % 2 == 0 {
                m += p;
            }
            let mut j = ((m - start) / 2) as usize;
            while j < len {
                sieve[j] = true;
                j += p as usize;
            }
        }
        for (j, &composite) in sieve[..len].iter().enumerate() {
            if !composite && !f(start + 2 * j as u64) {
                return;
            }
        }
        start += 2 * SEG;
    }
}

/// The primes up to `n`.
pub fn primes_up_to(n: u64) -> Vec<u64> {
    let mut out = Vec::new();
    each_prime(2, n, &mut |p| {
        out.push(p);
        true
    });
    out
}

fn primes_up_to_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?;
    if n.sign() <= 0 {
        return Err(RuntimeError::runtime("Limit must be positive"));
    }
    let n = n.to_u64().filter(|&n| n < 1 << 30).ok_or_else(|| RuntimeError::runtime("Limit is too large"))?;
    let mut out = Vec::new();
    each_prime(2, n, &mut |p| {
        out.push(Integer::from_u64(p));
        true
    });
    one(Value::int_seq(out))
}

fn primes_in_interval(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (lo, hi) = (a.int(0)?.clone(), a.int(1)?.clone());
    if hi < lo {
        return Err(RuntimeError::runtime("Upper limit < Lower Limit !"));
    }
    if hi.sign() <= 0 {
        return Err(RuntimeError::runtime("Upper limit must be positive"));
    }
    if lo.sign() <= 0 {
        return Err(RuntimeError::runtime("Lower limit must be positive"));
    }
    let hi = hi.to_u64().filter(|&h| h < 1 << 57).ok_or_else(|| RuntimeError::runtime("Limits are too large"))?;
    let lo = lo.to_u64().unwrap().max(2);
    if hi + 1 >= lo + (1 << 30) {
        return Err(RuntimeError::runtime("Interval is too large"));
    }
    let mut out = Vec::new();
    if hi.saturating_sub(lo) < hi.isqrt() / 64 {
        // A short interval high up: cheaper than sieving by every prime
        // below sqrt(hi).
        let hi = Integer::from_u64(hi);
        let mut p = Integer::from_u64(lo - 1).next_prime();
        while p <= hi {
            out.push(p.clone());
            p = p.next_prime();
        }
    } else {
        each_prime(lo, hi, &mut |p| {
            out.push(Integer::from_u64(p));
            true
        });
    }
    one(Value::int_seq(out))
}

/// pi(k 10^8), the number of primes up to k 10^8, for k = 1 .. 100 (a row
/// per 10^9).
#[rustfmt::skip]
const PRIME_COUNTS: [u32; 100] = [
    5761455, 11078937, 16252325, 21336326, 26355867, 31324703, 36252931, 41146179, 46009215, 50847534,
    55662470, 60454705, 65228333, 69985473, 74726528, 79451833, 84163019, 88862422, 93547928, 98222287,
    102886526, 107540122, 112184940, 116818447, 121443371, 126062167, 130670192, 135270258, 139864011, 144449537,
    149028641, 153600805, 158165829, 162725196, 167279333, 171827136, 176369517, 180906194, 185436625, 189961812,
    194481069, 198996103, 203507248, 208013454, 212514323, 217011319, 221504167, 225991743, 230475545, 234954223,
    239429993, 243902342, 248370960, 252834065, 257294520, 261751864, 266206294, 270655552, 275101551, 279545368,
    283984956, 288422869, 292856421, 297285198, 301711468, 306137611, 310558733, 314977166, 319391721, 323804352,
    328215206, 332620900, 337024801, 341426904, 345826612, 350221825, 354615116, 359006517, 363395981, 367783654,
    372168766, 376549859, 380930729, 385307831, 389682427, 394055910, 398425675, 402793457, 407159590, 411523195,
    415885628, 420243162, 424603409, 428958595, 433311792, 437663672, 442014876, 446362736, 450708777, 455052511,
];

/// The nth prime, for 1 <= n <= pi(10^10).
fn nth_prime_of(n: u64) -> u64 {
    // It lies in (k 10^8, (k + 1) 10^8] for the k below.
    let k = PRIME_COUNTS.partition_point(|&c| (c as u64) < n) as u64;
    let mut left = n - if k == 0 { 0 } else { PRIME_COUNTS[k as usize - 1] as u64 };
    let mut found = 0;
    each_prime(k * 100_000_000 + 1, (k + 1) * 100_000_000, &mut |p| {
        left -= 1;
        found = p;
        left > 0
    });
    found
}

fn nth_prime(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int_ge(0, 0)?.to_u64().filter(|&n| n <= PRIME_COUNTS[99] as u64).ok_or_else(|| RuntimeError::runtime("Integer is too large"))?;
    intv(if n == 0 { Integer::one() } else { Integer::from_u64(nth_prime_of(n)) })
}

// ----- modular arithmetic --------------------------------------------------------

fn modexp(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (n, k, m) = (a.int(0)?.clone(), a.int(1)?.clone(), a.int(2)?.clone());
    if m.sign() <= 0 {
        return Err(arg_ge(3, &m, 2));
    }
    if m.is_one() {
        return intv(Integer::zero());
    }
    match n.powm(&k, &m) {
        Some(r) => intv(r),
        // Magma names the exponent as argument 1 here.
        None => Err(RuntimeError::runtime(format!("Argument 1 ({k}) has no inverse modulo argument 3 ({m})"))),
    }
}

fn modinv(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let m = a.int_ge(1, 1)?;
    if m.is_one() {
        return intv(Integer::zero());
    }
    match a.int(0)?.invmod(&m) {
        Some(r) => intv(r),
        None => Err(RuntimeError::runtime("Argument 1 is not a unit mod argument 2")),
    }
}

/// A square root of `n` modulo the odd prime `p` (Tonelli and Shanks, with
/// the least non-residue), for `n` a non-zero square.
fn sqrt_mod_prime(n: &Integer, p: &Integer) -> Integer {
    let one_ = Integer::one();
    let (mut q, mut s) = (p - 1, 0u64);
    while q.is_even() {
        q = q.fdiv_2exp(1);
        s += 1;
    }
    let mut z = Integer::from_i64(2);
    while z.kronecker(p) != -1 {
        z = &z + 1;
    }
    let mut m = s;
    let mut c = z.powm(&q, p).unwrap();
    let mut t = n.powm(&q, p).unwrap();
    let mut r = n.powm(&(&q + 1).fdiv_2exp(1), p).unwrap();
    while t != one_ {
        let (mut i, mut tt) = (0u64, t.clone());
        while tt != one_ {
            tt = modp(&(&tt * &tt), p);
            i += 1;
        }
        let b = c.powm(&Integer::one().mul_2exp(m - i - 1), p).unwrap();
        m = i;
        c = modp(&(&b * &b), p);
        t = modp(&(&t * &c), p);
        r = modp(&(&r * &b), p);
    }
    r
}

/// A square root of `n` modulo `p^k`, the one Magma chooses.
fn sqrt_mod_prime_power(n: &Integer, p: &Integer, k: u64) -> Option<Integer> {
    let m = p.pow(k);
    let n = modp(n, &m);
    if n.is_square() {
        return n.isqrt();
    }
    if n.is_zero() {
        return Some(n);
    }
    if n.is_divisible_by(p) {
        // n = p^e * u: a root of u modulo p^(k - e/2), times p^(e/2).
        let (e, u) = n.remove(p);
        if e % 2 == 1 {
            return None;
        }
        let r = sqrt_mod_prime_power(&u, p, k - e / 2)?;
        return Some(modp(&(&r * &p.pow(e / 2)), &m));
    }
    let two = Integer::from_i64(2);
    let mut r = if *p == two {
        let need = if k >= 3 { 8 } else { 1 << k };
        if n.mod_u64(need) != 1 {
            return None;
        }
        Integer::one()
    } else {
        if n.kronecker(p) != 1 {
            return None;
        }
        sqrt_mod_prime(&modp(&n, p), p)
    };
    // Newton's iteration lifts the root to p^k.
    for _ in 0..300 {
        let d = &(&r * &r) - &n;
        if d.is_divisible_by(&m) {
            return Some(modp(&r, &m));
        }
        r = if *p == two {
            let (h, _) = d.fdiv_qr(&two).unwrap();
            modp(&(&r - &(&h * &r.invmod(&m)?)), &m)
        } else {
            modp(&(&r - &(&d * &(&two * &r).invmod(&m)?)), &m)
        };
    }
    // Lift bit by bit if the iteration did not settle.
    let mut r = Integer::one();
    for j in 3..k {
        let d = &(&r * &r) - &n;
        if !d.is_divisible_by(&two.pow(j + 1)) {
            r = &r + &two.pow(j - 1);
        }
    }
    Some(modp(&r, &m))
}

/// The square roots of a unit `u` modulo `p^j`: y and -y, and for p = 2
/// also y + 2^(j-1) and -y + 2^(j-1).
fn unit_sqrts_mod_prime_power(u: &Integer, p: &Integer, j: u64) -> Vec<Integer> {
    let m = p.pow(j);
    let Some(y) = sqrt_mod_prime_power(u, p, j) else { return Vec::new() };
    let neg = modp(&-&y, &m);
    let mut out = vec![y.clone(), neg.clone()];
    if *p == Integer::from_i64(2) && j >= 3 {
        let half = Integer::one().mul_2exp(j - 1);
        out.extend([modp(&(&y + &half), &m), modp(&(&neg + &half), &m)]);
    }
    out.dedup();
    out
}

/// The square roots of `n` modulo `p^k` (at most `limit` of them), the one
/// `sqrt_mod_prime_power` chooses first.
fn all_sqrt_mod_prime_power(n: &Integer, p: &Integer, k: u64, limit: usize) -> Vec<Integer> {
    let m = p.pow(k);
    let Some(r) = sqrt_mod_prime_power(n, p, k) else { return Vec::new() };
    let mut out = vec![r.clone()];
    if m.to_u64().is_some_and(|m| m <= 1 << 14) {
        // Small moduli: all roots by search.
        let nn = modp(n, &m);
        let mut x = Integer::zero();
        while x < m && out.len() < limit {
            if x != r && modp(&(&x * &x), &m) == nn {
                out.push(x.clone());
            }
            x = &x + 1;
        }
        return out;
    }
    // With n = p^v u (u a unit), a root is p^s y with v = 2s and y^2 = u
    // modulo p^(k-2s), and each such y gives p^s roots modulo p^k. When p^k
    // divides n the roots are the multiples of p^ceil(k/2).
    let nn = modp(n, &m);
    let (units, s) = if nn.is_zero() {
        (vec![Integer::zero()], k / 2)
    } else {
        let (v, u) = nn.remove(p);
        (unit_sqrts_mod_prime_power(&u, p, k - v), v / 2)
    };
    let (ps, step) = (p.pow(s), p.pow(k - s));
    let mut all = Vec::new();
    'units: for y in &units {
        let mut x = &ps * y;
        for _ in 0..ps.to_u64().unwrap_or(u64::MAX) {
            if all.len() >= limit {
                break 'units;
            }
            all.push(modp(&x, &m));
            x = &x + &step;
        }
    }
    all.sort();
    // The roots found before the others were enumerated keep their places.
    let neg = modp(&-&r, &m);
    let mut first = vec![neg.clone()];
    if *p == Integer::from_i64(2) && k >= 3 {
        let half = Integer::one().mul_2exp(k - 1);
        first.extend([modp(&(&r + &half), &m), modp(&(&neg + &half), &m)]);
    }
    for x in first.into_iter().chain(all) {
        if out.len() < limit && !out.contains(&x) {
            out.push(x);
        }
    }
    out
}

/// Square roots of `n` modulo `m`, Magma's choice first, then the others
/// (up to `limit` of them).
fn sqrts_mod(n: &Integer, m: &Integer, limit: usize) -> Vec<Integer> {
    let Some(first) = modsqrt(n, m) else { return Vec::new() };
    let Some(f) = m.factor() else { return vec![first] };
    let mut combos: Vec<(Integer, Integer)> = vec![(Integer::zero(), Integer::one())];
    for (p, k) in &f.factors {
        let pk = p.pow(*k);
        let roots = all_sqrt_mod_prime_power(n, p, *k, limit);
        let mut next = Vec::new();
        for (x, big) in &combos {
            for r in &roots {
                let t = modp(&(&(r - x) * &modp(big, &pk).invmod(&pk).unwrap_or_else(Integer::zero)), &pk);
                next.push((x + &(big * &t), big * &pk));
                if next.len() >= limit {
                    break;
                }
            }
        }
        combos = next;
    }
    let mut out = vec![first.clone()];
    for (x, big) in combos {
        let x = modp(&x, &big);
        if x != first && out.len() < limit {
            out.push(x);
        }
    }
    out
}

/// Magma's square root of `n` modulo `m > 1`.
pub fn modsqrt(n: &Integer, m: &Integer) -> Option<Integer> {
    let n = modp(n, m);
    if n.is_square() {
        return n.isqrt();
    }
    let f = m.factor()?;
    let (mut x, mut big) = (Integer::zero(), Integer::one());
    for (p, k) in &f.factors {
        let pk = p.pow(*k);
        let r = sqrt_mod_prime_power(&n, p, *k)?;
        // Combine by the Chinese remainder theorem, prime by prime.
        let t = modp(&(&(&r - &x) * &modp(&big, &pk).invmod(&pk).unwrap_or_else(Integer::zero)), &pk);
        x = &x + &(&big * &t);
        big = &big * &pk;
    }
    Some(modp(&x, &big))
}

fn modsqrt_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let m = a.int_ge(1, 2)?;
    match modsqrt(a.int(0)?, &m) {
        Some(r) => intv(r),
        None => Err(RuntimeError::runtime("Argument has no square root")),
    }
}

fn modorder_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let m = a.int_ge(1, 2)?;
    intv(super::ints::modorder(a.int(0)?, &m))
}

fn is_primitive(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let m = a.int_ge(1, 2)?;
    let n = a.int_ge(0, 1)?;
    let top = &m - 1;
    if n > top {
        return Err(arg_le(1, &n, &top));
    }
    let order = super::ints::modorder(&n, &m);
    boolv(!order.is_zero() && order == m.euler_phi())
}

fn primitive_root(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let m = a.int_ge(0, 2)?;
    intv(super::ints::primitive_root(&m).unwrap_or_else(Integer::zero))
}

/// The solutions of `a x = b (mod m)` as `x0 + i*k`, if any.
fn linear_congruence(a: &Integer, b: &Integer, m: &Integer) -> Option<(Integer, Integer)> {
    let g = a.gcd(m);
    if !b.is_divisible_by(&g) {
        return None;
    }
    let k = m.divexact(&g);
    if k.is_one() {
        return Some((Integer::zero(), k));
    }
    let inv = modp(&a.divexact(&g), &k).invmod(&k)?;
    Some((modp(&(&b.divexact(&g) * &inv), &k), k))
}

fn solution(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let m = a.int_ge(2, 1)?;
    match linear_congruence(a.int(0)?, a.int(1)?, &m) {
        Some((x, k)) => Ok(vec![Value::Int(x), Value::Int(k)]),
        None => Ok(vec![Value::int(-1), Value::Undef]),
    }
}

/// `x = r (mod m)` combined with the congruences so far (moduli need not
/// be coprime).
fn crt_step(x: &Integer, big: &Integer, r: &Integer, m: &Integer) -> Option<(Integer, Integer)> {
    let (g, s, _) = big.xgcd(m);
    let diff = r - x;
    if !diff.is_divisible_by(&g) {
        return None;
    }
    let l = big.lcm(m);
    let step = &(big * &s) * &diff.divexact(&g);
    Some((modp(&(x + &step), &l), l))
}

fn int_elems(v: &Value) -> RResult<Vec<Integer>> {
    super::ints::ints_of(v)
}

fn crt(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (xs, ms) = (int_elems(&a.args[0])?, int_elems(&a.args[1])?);
    if xs.is_empty() {
        return Err(RuntimeError::runtime("Sequence argument 1 must be non-empty"));
    }
    if xs.len() != ms.len() {
        return Err(RuntimeError::runtime("Lengths of sequence arguments should be the same"));
    }
    if ms.iter().any(|m| m.is_zero()) {
        return Err(RuntimeError::runtime("Element of second argument (moduli M) is zero"));
    }
    let (mut x, mut big) = (Integer::zero(), Integer::one());
    for (r, m) in xs.iter().zip(&ms) {
        match crt_step(&x, &big, r, &m.abs()) {
            Some((nx, nb)) => (x, big) = (nx, nb),
            None => return intv(Integer::from_i64(-1)),
        }
    }
    intv(x)
}

fn solution_seq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (aa, bb, nn) = (int_elems(&a.args[0])?, int_elems(&a.args[1])?, int_elems(&a.args[2])?);
    if aa.len() != bb.len() || aa.len() != nn.len() {
        return Err(RuntimeError::runtime("Lengths of sequence arguments should be the same"));
    }
    let (mut x, mut big) = (Integer::zero(), Integer::one());
    for ((ai, bi), ni) in aa.iter().zip(&bb).zip(&nn) {
        if ni.sign() <= 0 {
            return Err(RuntimeError::runtime("Moduli must be positive"));
        }
        let Some((r, k)) = linear_congruence(ai, bi, ni) else {
            return intv(Integer::from_i64(-1));
        };
        match crt_step(&x, &big, &r, &k) {
            Some((nx, nb)) => (x, big) = (nx, nb),
            None => return intv(Integer::from_i64(-1)),
        }
    }
    intv(x)
}

// ----- residue symbols -------------------------------------------------------------

fn legendre(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let p = a.int_ge(1, 3)?;
    if !p.is_prime() {
        return Err(arg_prime(2, &p));
    }
    one(Value::int(a.int(0)?.kronecker(&p) as i64))
}

fn jacobi(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int_ge(1, 3)?;
    if n.is_even() {
        return Err(RuntimeError::runtime(format!("Argument 2 ({n}) should not be divisible by 2")));
    }
    one(Value::int(a.int(0)?.kronecker(&n) as i64))
}

fn kronecker(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    one(Value::int(a.int(0)?.kronecker(a.int(1)?) as i64))
}

// ----- norm equations ----------------------------------------------------------------

/// Cornacchia's algorithm: x^2 + d y^2 = m from a square root r0 of -d
/// modulo m.
fn cornacchia(d: &Integer, m: &Integer, r0: &Integer) -> Option<(Integer, Integer)> {
    let lim = m.isqrt()?;
    let (mut a, mut b) = (m.clone(), r0.clone());
    while b > lim {
        let r = modp(&a, &b);
        a = b;
        b = r;
    }
    let t = m - &(&b * &b);
    if !t.is_divisible_by(d) {
        return None;
    }
    let y2 = t.divexact(d);
    if !y2.is_square() {
        return None;
    }
    Some((b, y2.isqrt()?))
}

/// Non-negative x, y with x^2 + d y^2 = m, as Magma finds them.
pub fn norm_equation(d: &Integer, m: &Integer) -> Option<(Integer, Integer)> {
    if m.is_zero() {
        return Some((Integer::zero(), Integer::zero()));
    }
    if m.is_one() {
        return Some(if d.is_one() { (Integer::zero(), Integer::one()) } else { (Integer::one(), Integer::zero()) });
    }
    if m.is_square() {
        return Some((m.isqrt()?, Integer::zero()));
    }
    // With h^2 dividing both d and m, h divides x: solve
    // x'^2 + (d/h^2) y^2 = m/h^2 for the largest such h.
    let h: Integer = d.gcd(m).factor()?.factors.iter().map(|(p, e)| p.pow(e / 2)).fold(Integer::one(), |a, b| &a * &b);
    if !h.is_one() {
        let hh = &h * &h;
        let (x, y) = norm_equation(&d.divexact(&hh), &m.divexact(&hh))?;
        return Some((&x * &h, y));
    }
    // Primitive solutions first, then those with a common factor g.
    let f = m.factor()?;
    let mut gs = super::factseq::divisors_of(&f.factors.iter().filter(|(_, e)| *e >= 2).map(|(p, e)| (p.clone(), e / 2)).collect());
    gs.sort();
    for g in gs {
        let mm = m.divexact(&(&g * &g));
        // Magma's square root of -d first, then the others.
        let roots = if mm.is_one() { vec![Integer::zero()] } else { sqrts_mod(&-d, &mm, 4096) };
        for r0 in roots {
            if let Some((x, y)) = cornacchia(d, &mm, &r0).filter(|(x, y)| x.gcd(y).is_one()) {
                return Some((&x * &g, &y * &g));
            }
        }
    }
    None
}

fn norm_equation_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (d, m) = (a.int(0)?.clone(), a.int(1)?.clone());
    if d.sign() <= 0 || m.sign() < 0 {
        return Err(RuntimeError::runtime("Argument 1 must be positive and argument 2 non-negative"));
    }
    match norm_equation(&d, &m) {
        Some((x, y)) => Ok(vec![Value::Bool(true), Value::Int(x), Value::Int(y)]),
        None => Ok(vec![Value::Bool(false), Value::Undef, Value::Undef]),
    }
}

// ----- Dickman's rho ------------------------------------------------------------------

/// rho(u) to `digits` decimal digits: on [k-1, k] rho(k - z) is a power
/// series in z whose coefficients follow from those on [k-2, k-1] by
/// u rho'(u) = -rho(u - 1).
fn dickman_rho(u: &Real, digits: u32) -> Real {
    let bits = bits_for_digits(digits as u64) + 64;
    let one_ = Real::from_integer(&Integer::one(), bits);
    if u.sub(&one_).sign() <= 0 {
        return one_.round_to(bits_for_digits(digits as u64));
    }
    let k = u.ceil();
    let kk = k.to_u64().unwrap_or(u64::MAX);
    let terms = bits as usize + 40;
    let mut c: Vec<Real> = (0..terms).map(|j| if j == 0 { one_.clone() } else { Real::zero(bits) }).collect();
    for i in 2..=kk {
        let ki = Integer::from_u64(i);
        let mut next = vec![Real::zero(bits); terms];
        for j in 0..terms - 1 {
            let num = c[j].add(&next[j].mul(&Real::from_integer(&Integer::from_u64(j as u64), bits)));
            next[j + 1] = num.div(&Real::from_integer(&(&ki * &Integer::from_u64(j as u64 + 1)), bits)).unwrap();
        }
        // Continuity at u = i - 1 (z = 1) fixes the constant term.
        let mut s = Real::zero(bits);
        for x in &next[1..] {
            s = s.add(x);
        }
        next[0] = c[0].sub(&s);
        c = next;
    }
    let z = Real::from_integer(&k, bits).sub(&u.round_to(bits));
    let mut r = Real::zero(bits);
    for x in c.iter().rev() {
        r = r.mul(&z).add(x);
    }
    r.round_to(bits_for_digits(digits as u64))
}

fn dickman_rho_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let digits = match &a.args[0] {
        Value::Real(r) => r.digits,
        _ => DEFAULT_DIGITS,
    };
    let u = super::reals::to_real(&a.args[0], digits).unwrap().round_to(bits_for_digits(digits as u64) + 64);
    one(Value::real(dickman_rho(&u, digits), digits))
}

pub fn register(it: &mut Interp) {
    it.def_params("IsPrime", "n::RngIntElt -> BoolElt", &[("Proof", Value::Bool(true))], "Whether n is a prime number (or the negative of one).", is_prime);
    for name in ["IsProbablePrime", "IsProbablyPrime"] {
        it.def_params(name, "n::RngIntElt -> BoolElt", &[("Bases", Value::int(20))], "Whether |n| passes a strong probable-prime test.", is_probable_prime);
    }
    it.def("IsPrimePower", "n::RngIntElt -> BoolElt, RngIntElt, RngIntElt", "Whether n is a prime power p^k, and p and k.", is_prime_power);
    it.def_params("NextPrime", "n::RngIntElt -> RngIntElt", &[("Proof", Value::Bool(true))], "The least prime greater than n.", next_prime);
    it.def_params("PreviousPrime", "n::RngIntElt -> RngIntElt", &[("Proof", Value::Bool(true))], "The greatest prime less than n.", previous_prime);
    it.def("NthPrime", "n::RngIntElt -> RngIntElt", "The n-th prime (1 for n = 0).", nth_prime);
    it.def("PrimesUpTo", "n::RngIntElt -> [RngIntElt]", "The primes up to n.", primes_up_to_fn);
    it.def("PrimesInInterval", "a::RngIntElt, b::RngIntElt -> [RngIntElt]", "The primes in the interval [a, b].", primes_in_interval);

    it.def("Modexp", "n::RngIntElt, k::RngIntElt, m::RngIntElt -> RngIntElt", "n^k mod m.", modexp);
    for name in ["Modinv", "InverseMod"] {
        it.def(name, "n::RngIntElt, m::RngIntElt -> RngIntElt", "The inverse of n modulo m.", modinv);
    }
    it.def("Modsqrt", "n::RngIntElt, m::RngIntElt -> RngIntElt", "A square root of n modulo m.", modsqrt_fn);
    it.def("Modorder", "n::RngIntElt, m::RngIntElt -> RngIntElt", "The order of n modulo m, or 0 if n is not a unit modulo m.", modorder_fn);
    it.def("IsPrimitive", "n::RngIntElt, m::RngIntElt -> BoolElt", "Whether n is a primitive root modulo m.", is_primitive);
    it.def("PrimitiveRoot", "m::RngIntElt -> RngIntElt", "The least primitive root modulo m, or 0 if there is none.", primitive_root);
    it.def(
        "Solution",
        "a::RngIntElt, b::RngIntElt, m::RngIntElt -> RngIntElt, RngIntElt",
        "x0 and k such that the solutions of a*x = b mod m are x0 + i*k, or -1.",
        solution,
    );
    it.def(
        "Solution",
        "A::[RngIntElt], B::[RngIntElt], N::[RngIntElt] -> RngIntElt",
        "The least x >= 0 with A[i]*x = B[i] mod N[i] for all i, or -1.",
        solution_seq,
    );
    for name in ["CRT", "ChineseRemainderTheorem"] {
        it.def(name, "X::[RngIntElt], N::[RngIntElt] -> RngIntElt", "The least x >= 0 with x = X[i] mod N[i] for all i, or -1.", crt);
    }
    it.def("LegendreSymbol", "n::RngIntElt, p::RngIntElt -> RngIntElt", "The Legendre symbol (n/p) for an odd prime p.", legendre);
    it.def("JacobiSymbol", "n::RngIntElt, m::RngIntElt -> RngIntElt", "The Jacobi symbol (n/m) for odd m >= 3.", jacobi);
    it.def("KroneckerSymbol", "n::RngIntElt, m::RngIntElt -> RngIntElt", "The Kronecker symbol (n/m).", kronecker);
    it.def_params(
        "NormEquation",
        "d::RngIntElt, m::RngIntElt -> BoolElt, RngIntElt, RngIntElt",
        &[("Factorization", Value::seq(None, Vec::new()))],
        "Whether x^2 + d*y^2 = m has a solution, and non-negative x and y.",
        norm_equation_fn,
    );
    for t in ["RngIntElt", "FldRatElt", "FldReElt"] {
        it.def("DickmanRho", &format!("u::{t} -> FldReElt"), "Dickman's rho function at u.", dickman_rho_fn);
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;

    #[test]
    fn segmented_sieve_matches_trial_division() {
        let is_prime = |n: u64| n >= 2 && (2..).take_while(|d| d * d <= n).all(|d| n % d != 0);
        // The last range crosses a segment boundary.
        for (lo, hi) in [(0, 1000), (1, 2), (2, 2), (3, 3), (4, 4), (8, 9), (999_000, 1_001_000), (1 << 20, (1 << 20) + 600_000)] {
            let mut got = Vec::new();
            each_prime(lo, hi, &mut |p| {
                got.push(p);
                true
            });
            let want: Vec<u64> = (lo..=hi).filter(|&n| is_prime(n)).collect();
            assert_eq!(got, want, "primes in [{lo}, {hi}]");
        }
    }

    #[test]
    fn nth_prime_across_the_table() {
        assert_eq!(nth_prime_of(1), 2);
        assert_eq!(nth_prime_of(10), 29);
        assert_eq!(nth_prime_of(5761455), 99999989);
        assert_eq!(nth_prime_of(5761456), 100000007);
        assert_eq!(nth_prime_of(50847535), 1000000007);
    }

    #[test]
    fn square_roots_modulo_prime_powers_are_complete() {
        let roots = |n: u64, p: u64, k: u64| -> Vec<u64> {
            let mut r: Vec<u64> =
                all_sqrt_mod_prime_power(&Integer::from_u64(n), &Integer::from_u64(p), k, usize::MAX).iter().map(|x| x.to_u64().unwrap()).collect();
            r.sort();
            r
        };
        assert_eq!(roots(9, 3, 10), [3, 19680, 19686, 39363, 39369, 59046]);
        // Moduli above 2^14, where the roots are not found by search: every
        // residue for the first two, some for the others.
        for (p, k, all) in [(3u64, 10u64, true), (2, 15, true), (7, 5, false), (5, 7, false), (2, 16, false)] {
            let m = p.pow(k as u32);
            let mut squares: HashMap<u64, Vec<u64>> = HashMap::new();
            for x in 0..m {
                squares.entry(x * x % m).or_default().push(x);
            }
            let ns: Vec<u64> = if all { (0..m).collect() } else { vec![0, 1, 2, 4, 9, 17, p * p, 3 * p * p, p.pow(4), 2 * p.pow(4), m / p, m / (p * p)] };
            for n in ns {
                assert_eq!(roots(n % m, p, k), squares.get(&(n % m)).cloned().unwrap_or_default(), "x^2 = {n} mod {p}^{k}");
            }
        }
    }
}
