//! Primality certificates (text/184): an ECPP prover in the manner of
//! Atkin and Morain, and a checker of its certificates.
//!
//! A certificate is a chain of steps, each showing n prime if the next
//! number p is, down to a step below the Sorenson-Webster bound, where the
//! strong probable prime tests to the prime bases up to 37 decide. A curve
//! step gives a curve modulo n and a point P of prime order p above
//! (n^(1/4) + 1)^2 on it (Goldwasser and Kilian): modulo a prime r of n up
//! to sqrt(n), P would have order p, more than the curve has points. An N-1
//! step gives g of prime order p modulo n with (p + 1)^2 > n (Pocklington):
//! every prime of n is then 1 modulo p, so above sqrt(n).
//!
//! The curves come from complex multiplication: when 4n = u^2 + |D| v^2, the
//! curves whose j-invariants are the roots of the Hilbert class polynomial
//! of D modulo n have n + 1 ± u points (and for D = -3 and -4 their twists a
//! few more orders). The prover tries the fundamental discriminants by class
//! number, and takes an order whose cofactor, after the primes up to 2^20,
//! is a probable prime large enough; the class polynomial's roots give the
//! curve.

use std::collections::{HashMap, VecDeque};
use std::fmt::Write;
use std::sync::OnceLock;

use calyx_flint::Integer;
use calyx_flint::modn::{ModCtx, ModPoly, hilbert_class_poly};

use super::{each_prime, modp};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::factoring::arith::{Ring, with_ring};
use crate::intrinsics::{boolv, factseq, one};
use crate::types::t;
use crate::value::*;

/// A step of a certificate.
#[derive(Clone, Debug, PartialEq)]
pub enum Step {
    /// n is prime if p is: the point (x, y) of y^2 = x^3 + a x + b modulo n,
    /// a curve of discriminant d with m points, has order p.
    Curve { n: Integer, d: Integer, m: Integer, p: Integer, a: Integer, b: Integer, x: Integer, y: Integer },
    /// n is prime if p is: g has order p modulo n.
    Minus { n: Integer, p: Integer, g: Integer },
    /// n is below the Sorenson-Webster bound.
    Det { n: Integer },
}

impl Step {
    fn n(&self) -> &Integer {
        match self {
            Step::Curve { n, .. } | Step::Minus { n, .. } | Step::Det { n } => n,
        }
    }

    /// The number the step leaves to prove prime.
    fn prime(&self) -> Option<&Integer> {
        match self {
            Step::Curve { p, .. } | Step::Minus { p, .. } => Some(p),
            Step::Det { .. } => None,
        }
    }
}

/// Below this bound a number is prime if it is a strong probable prime to
/// the prime bases up to 37 (Sorenson and Webster).
const SW_BOUND: i128 = 3317044064679887385961981;
const SW_BASES: [u64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];

fn sw_bound() -> Integer {
    Integer::from_i128(SW_BOUND)
}

/// Primality of n below the Sorenson-Webster bound.
fn det_prime(n: &Integer) -> bool {
    if n.sign() <= 0 || n.is_one() {
        return false;
    }
    if let Some(&b) = SW_BASES.iter().find(|&&b| n.mod_u64(b) == 0) {
        return *n == Integer::from_u64(b);
    }
    SW_BASES.iter().all(|&b| n.is_strong_probable_prime(&Integer::from_u64(b)))
}

/// Whether p > (n^(1/4) + 1)^2. With s = sqrt(p) that is (s - 1)^4 > n, or
/// p^2 + 6p + 1 - n > 4 s (p + 1), which squares to integers.
fn above_bound(p: &Integer, n: &Integer) -> bool {
    if p.sign() <= 0 {
        return false;
    }
    let l = &(&(&(p * p) + &(p * 6)) + 1) - n;
    let p1 = p + 1;
    l.sign() > 0 && &l * &l > &(p * &(&p1 * &p1)) * 16
}

// ----- the prover -------------------------------------------------------------------------------

/// The largest |D| of the discriminants the prover takes.
const DISC_MAX: usize = 1 << 15;

/// The primes up to this bound come out of the orders at once.
const TRIAL: u64 = 1 << 20;

/// The fundamental discriminants -d (d up to DISC_MAX) and their class
/// numbers h, in the order the prover tries them: by h, as finding the roots
/// of the class polynomial costs more with its degree, then by d.
fn discriminants() -> &'static [(u32, u32)] {
    static DISCS: OnceLock<Vec<(u32, u32)>> = OnceLock::new();
    DISCS.get_or_init(|| {
        let h = form_counts(DISC_MAX);
        let mut ds: Vec<(u32, u32)> = (3..=DISC_MAX).filter(|&d| fundamental(d)).map(|d| (h[d], d as u32)).collect();
        ds.sort_unstable();
        ds.into_iter().map(|(h, d)| (d, h)).collect()
    })
}

/// Whether -d is a fundamental discriminant.
fn fundamental(d: usize) -> bool {
    let squarefree = |m: usize| (2..).take_while(|p| p * p <= m).all(|p| m % (p * p) != 0);
    match d % 4 {
        3 => squarefree(d),
        0 => matches!(d / 4 % 4, 1 | 2) && squarefree(d / 4),
        _ => false,
    }
}

/// The number of reduced forms (a, b, c) of discriminant b^2 - 4ac = -d for
/// each d up to max: the class number when -d is fundamental, as its forms
/// are all primitive.
fn form_counts(max: usize) -> Vec<u32> {
    let mut h = vec![0u32; max + 1];
    let max = max as i64;
    let mut a = 1i64;
    while 3 * a * a <= max {
        for b in 1 - a..=a {
            // c >= a, and c > a when b < 0.
            let mut c = if b < 0 { a + 1 } else { a };
            while 4 * a * c - b * b <= max {
                h[(4 * a * c - b * b) as usize] += 1;
                c += 1;
            }
        }
        a += 1;
    }
    h
}

thread_local! {
    /// The product of the primes up to TRIAL.
    static SMALL: Integer = {
        let mut ps = Vec::new();
        each_prime(2, TRIAL, &mut |p| {
            ps.push(Integer::from_u64(p));
            true
        });
        product(ps)
    };
}

fn product(mut xs: Vec<Integer>) -> Integer {
    while xs.len() > 1 {
        xs = xs.chunks(2).map(|c| if c.len() == 2 { &c[0] * &c[1] } else { c[0].clone() }).collect();
    }
    xs.pop().unwrap_or_else(Integer::one)
}

/// Each m > 0 without its primes up to TRIAL. The product of those primes is
/// reduced modulo each m through a remainder tree, which costs about as much
/// as reducing it modulo the product of the ms.
fn cofactors(ms: &[Integer]) -> Vec<Integer> {
    let mut levels = vec![ms.to_vec()];
    while let Some(top) = levels.last().filter(|l| l.len() > 1) {
        let up = top.chunks(2).map(|c| if c.len() == 2 { &c[0] * &c[1] } else { c[0].clone() }).collect();
        levels.push(up);
    }
    let mut rems: Vec<Integer> = levels.pop().unwrap_or_default().iter().map(|x| SMALL.with(|s| modp(s, x))).collect();
    while let Some(level) = levels.pop() {
        rems = level.iter().enumerate().map(|(i, x)| modp(&rems[i / 2], x)).collect();
    }
    ms.iter()
        .zip(rems)
        .map(|(m, r)| {
            let (mut q, mut g) = (m.clone(), r.gcd(m));
            while !g.is_one() {
                q = q.divexact(&g);
                g = q.gcd(&g);
            }
            q
        })
        .collect()
}

/// Class polynomials computed so far, by |D|.
type Polys = HashMap<u32, Vec<Integer>>;

/// A certificate of the primality of n, or None when n is not prime.
pub fn prove(n: &Integer) -> Option<Vec<Step>> {
    let bound = sw_bound();
    if *n < bound {
        return det_prime(n).then(|| vec![Step::Det { n: n.clone() }]);
    }
    if !n.is_probable_prime() {
        return None;
    }
    let mut polys = Polys::new();
    // searches[i] looks for steps[i], from the prime that steps[i - 1] leaves.
    let mut steps: Vec<Step> = Vec::new();
    let mut searches = vec![Search::new(n.clone())];
    while let Some(s) = searches.last_mut() {
        let Some(step) = s.next(&mut polys) else {
            // Nothing from this prime: take back the step that led to it.
            searches.pop();
            steps.pop();
            continue;
        };
        let p = step.prime().cloned().unwrap_or_default();
        steps.push(step);
        if p >= bound {
            searches.push(Search::new(p));
        } else if det_prime(&p) {
            steps.push(Step::Det { n: p });
            return Some(steps);
        } else {
            steps.pop();
        }
    }
    None
}

/// The search for a step down from a probable prime n above the
/// Sorenson-Webster bound.
struct Search {
    n: Integer,
    /// The next discriminant to try; orders (with the |D| of their curves)
    /// waiting for the trial division, and those past it with their
    /// cofactors.
    next: usize,
    pending: Vec<(u32, Integer)>,
    ready: VecDeque<(u32, Integer, Integer)>,
    minus_tried: bool,
    rng: u64,
    /// The Kronecker symbols (f/n) and square roots modulo n of the prime
    /// discriminants f met so far.
    chars: HashMap<i64, i32>,
    roots: HashMap<i64, Integer>,
}

impl Search {
    fn new(n: Integer) -> Search {
        let rng = n.to_limbs()[0] | 1;
        let (pending, ready) = (Vec::new(), VecDeque::new());
        Search { n, next: 0, pending, ready, minus_tried: false, rng, chars: HashMap::new(), roots: HashMap::new() }
    }

    /// The next step down, or None once every discriminant has been tried.
    fn next(&mut self, polys: &mut Polys) -> Option<Step> {
        let n = self.n.clone();
        with_ring!(&n, |r| self.next_in(r, polys))
    }

    fn next_in<R: Ring>(&mut self, r: &R, polys: &mut Polys) -> Option<Step> {
        let n = r.modulus();
        if !self.minus_tried {
            self.minus_tried = true;
            let n1 = n - 1;
            let p = cofactors(std::slice::from_ref(&n1)).pop().unwrap_or_default();
            if &(&p + 1) * &(&p + 1) > *n && p.is_probable_prime() {
                if let Some(g) = minus_witness(r, &n1, &p) {
                    return Some(Step::Minus { n: n.clone(), p, g });
                }
            }
        }
        let sq = Sqrt::new(r)?;
        // Orders go through the trial division in batches, larger for larger n.
        let batch = (n.bits() as usize / 64).clamp(4, 32);
        'discs: loop {
            while let Some((d, m, p)) = self.ready.pop_front() {
                // p < n: an order that is itself prime can exceed n, and the
                // curves of the same D modulo p then have n points.
                if p < *n && above_bound(&p, n) && p.is_probable_prime() {
                    if let Some(step) = curve_step(r, &sq, d, &m, &p, polys, &mut self.rng) {
                        return Some(step);
                    }
                }
            }
            let next = discriminants().get(self.next);
            if self.pending.len() >= batch || next.is_none() && !self.pending.is_empty() {
                let ms: Vec<Integer> = self.pending.iter().map(|(_, m)| m.clone()).collect();
                let ps = cofactors(&ms);
                self.ready.extend(self.pending.drain(..).zip(ps).map(|((d, m), p)| (d, m, p)));
                continue;
            }
            let &(d, _) = next?;
            self.next += 1;
            // n is a norm from the order of D only if it lies in the
            // principal genus, where each prime discriminant f of D has
            // (f/n) = 1; the square roots of those then give one of D.
            let fs = prime_discriminants(d);
            if !fs.iter().all(|&f| *self.chars.entry(f).or_insert_with(|| Integer::from_i64(f).kronecker(n)) == 1) {
                continue;
            }
            let mut x = r.one();
            for &f in &fs {
                let root = match self.roots.get(&f) {
                    Some(root) => r.from_int(root),
                    None => {
                        let Some(root) = sq.sqrt(r, &r.from_int(&Integer::from_i64(f))) else { continue 'discs };
                        self.roots.insert(f, r.to_int(&root));
                        root
                    }
                };
                x = r.mul(&x, &root);
            }
            if let Some((u, v)) = cornacchia(n, d, r.to_int(&x)) {
                self.pending.extend(orders(n, d, &u, &v).into_iter().filter(|m| m.sign() > 0).map(|m| (d, m)));
            }
        }
    }
}

/// The prime discriminants whose product is the fundamental discriminant
/// -d: f = (-1)^((p - 1)/2) p for the odd primes p of d, and -4, 8 or -8.
fn prime_discriminants(d: u32) -> Vec<i64> {
    let disc = -(d as i64);
    let mut m = d as i64;
    while m % 2 == 0 {
        m /= 2;
    }
    let (mut fs, mut odd, mut p) = (Vec::new(), 1, 3);
    while m > 1 {
        if p * p > m {
            p = m;
        }
        if m % p == 0 {
            let f = if p % 4 == 1 { p } else { -p };
            fs.push(f);
            odd *= f;
            m /= p;
        }
        p += 2;
    }
    if odd != disc {
        fs.push(disc / odd);
    }
    fs
}

/// g = c^((n - 1)/p) for the least c >= 2 with g != 1, if g^p = 1 (as it is
/// for prime n).
fn minus_witness<R: Ring>(r: &R, n1: &Integer, p: &Integer) -> Option<Integer> {
    let e = n1.divexact(p);
    let one = r.one();
    let g = (2..100).find_map(|c| Some(r.pow(&r.from_int(&Integer::from_u64(c)), &e)).filter(|g| *g != one))?;
    (r.pow(&g, p) == one).then(|| r.to_int(&g))
}

/// Square roots modulo the prime n (Tonelli and Shanks).
struct Sqrt<E> {
    /// n - 1 = 2^s t with t odd, the least non-residue c, and z = c^t.
    s: u32,
    t: Integer,
    c: Integer,
    z: E,
}

impl<E: Clone + PartialEq> Sqrt<E> {
    fn new<R: Ring<E = E>>(r: &R) -> Option<Sqrt<E>> {
        let n = r.modulus();
        let (mut t, mut s) = (n - 1, 0);
        while t.is_even() {
            t = t.fdiv_2exp(1);
            s += 1;
        }
        let c = (2..1000).map(Integer::from_u64).find(|c| c.kronecker(n) == -1)?;
        let z = r.pow(&r.from_int(&c), &t);
        Some(Sqrt { s, t, c, z })
    }

    /// A square root of a, if a is a non-zero square.
    fn sqrt<R: Ring<E = E>>(&self, r: &R, a: &E) -> Option<E> {
        let one = r.one();
        let w = r.pow(a, &(&self.t - 1).fdiv_2exp(1));
        let mut x = r.mul(a, &w);
        let mut b = r.mul(&x, &w);
        let (mut z, mut m) = (self.z.clone(), self.s);
        while b != one {
            // The least i with b^(2^i) = 1.
            let (mut i, mut bb) = (0, b.clone());
            while bb != one {
                bb = r.sqr(&bb);
                i += 1;
                if i == m {
                    return None;
                }
            }
            let mut w = z;
            for _ in 0..m - i - 1 {
                w = r.sqr(&w);
            }
            x = r.mul(&x, &w);
            z = r.sqr(&w);
            b = r.mul(&b, &z);
            m = i;
        }
        Some(x)
    }
}

/// u and v with u^2 + d v^2 = 4n, from a square root x of -d modulo the
/// prime n (Cornacchia's algorithm, as modified for 4n).
fn cornacchia(n: &Integer, d: u32, x: Integer) -> Option<(Integer, Integer)> {
    let x = if x.is_odd() == (d % 2 == 1) { x } else { n - &x };
    let four = n.mul_2exp(2);
    let l = four.isqrt()?;
    let (mut a, mut b) = (n.mul_2exp(1), x);
    while b > l {
        let rest = a.fdiv_qr(&b)?.1;
        a = std::mem::replace(&mut b, rest);
    }
    let d = Integer::from_u64(d as u64);
    let rest = &four - &(&b * &b);
    if !rest.is_divisible_by(&d) {
        return None;
    }
    let c = rest.divexact(&d);
    let v = c.isqrt()?;
    (&v * &v == c).then_some((b, v))
}

/// The orders of the curves of discriminant -d modulo n, from
/// 4n = u^2 + d v^2: n + 1 ± u, and for d = 3 and 4 the twists' too.
fn orders(n: &Integer, d: u32, u: &Integer, v: &Integer) -> Vec<Integer> {
    let mut ts = vec![u.clone()];
    match d {
        4 => ts.push(v.mul_2exp(1)),
        3 => {
            let v3 = v * 3;
            ts.push((u + &v3).fdiv_2exp(1));
            ts.push((u - &v3).fdiv_2exp(1));
        }
        _ => {}
    }
    let n1 = n + 1;
    ts.iter().flat_map(|t| [&n1 - t, &n1 + t]).collect()
}

/// The step for a curve of discriminant -d with m = k p points modulo n: the
/// curve among the twists, and a point of order p on it.
fn curve_step<R: Ring>(r: &R, sq: &Sqrt<R::E>, d: u32, m: &Integer, p: &Integer, polys: &mut Polys, rng: &mut u64) -> Option<Step> {
    let n = r.modulus();
    let int = Integer::from_u64;
    let curves: Vec<(Integer, Integer)> = match d {
        // The twists of j = 0 and 1728 by small coefficients.
        3 => (1..64).map(|b| (Integer::zero(), int(b))).collect(),
        4 => (1..64).map(|a| (int(a), Integer::zero())).collect(),
        _ => {
            let h = polys.entry(d).or_insert_with(|| hilbert_class_poly(-(d as i64)));
            let j = ModPoly::new(&ModCtx::new(n), h).one_root(next_rand(rng))?;
            // y^2 = x^3 + 3c x + 2c with c = j/(1728 - j) has invariant j;
            // the other curve is its twist by a non-residue w.
            let c = modp(&(&j * &(&int(1728) - &j).invmod(n)?), n);
            let (a, b) = (modp(&(&c * 3), n), modp(&(&c * 2), n));
            let w2 = modp(&(&sq.c * &sq.c), n);
            let (a2, b2) = (modp(&(&a * &w2), n), modp(&(&(&b * &w2) * &sq.c), n));
            vec![(a, b), (a2, b2)]
        }
    };
    // For j = 0 and 1728, the class of b modulo sixth powers (of a modulo
    // fourth powers) tells the twist: each is tried once.
    let class = match d {
        3 | 4 => Some((n - 1).divexact(&int(if d == 3 { 6 } else { 4 }))),
        _ => None,
    };
    let mut seen = Vec::new();
    let k = m.divexact(p);
    let zero = r.from_int(&Integer::zero());
    for (a, b) in curves {
        let (ae, be) = (r.from_int(&a), r.from_int(&b));
        if let Some(e) = &class {
            let c = r.pow(if d == 3 { &be } else { &ae }, e);
            if seen.contains(&c) {
                continue;
            }
            seen.push(c);
        }
        // For a point P, Q = kP has order p when the curve has m points; a
        // P of order dividing k (rarely) calls for another.
        for _ in 0..3 {
            let (x, y) = random_point(r, sq, &ae, &be, rng)?;
            let q = multiply(r, &ae, &x, &y, &k);
            if q.z == zero {
                continue;
            }
            let (qx, qy) = normalize(r, &q)?;
            if !is_zero_point(r, &multiply(r, &ae, &qx, &qy, p)) {
                break;
            }
            let (d, x, y) = (Integer::from_i64(-(d as i64)), r.to_int(&qx), r.to_int(&qy));
            return Some(Step::Curve { n: n.clone(), d, m: m.clone(), p: p.clone(), a, b, x, y });
        }
    }
    None
}

fn next_rand(s: &mut u64) -> u64 {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    *s
}

/// A point (x, y) with y != 0 of y^2 = x^3 + a x + b, from random x.
fn random_point<R: Ring>(r: &R, sq: &Sqrt<R::E>, a: &R::E, b: &R::E, rng: &mut u64) -> Option<(R::E, R::E)> {
    for _ in 0..200 {
        let x = r.from_int(&Integer::from_u64(next_rand(rng)));
        let rhs = r.add(&r.mul(&r.add(&r.sqr(&x), a), &x), b);
        if r.to_int(&rhs).kronecker(r.modulus()) == 1 {
            return Some((x, sq.sqrt(r, &rhs)?));
        }
    }
    None
}

/// A point X : Y : Z of a curve in Jacobian coordinates (x = X/Z^2,
/// y = Y/Z^3).
struct Jac<E> {
    x: E,
    y: E,
    z: E,
}

/// 2P on y^2 = x^3 + a x + b.
fn double<R: Ring>(r: &R, a: &R::E, p: &Jac<R::E>) -> Jac<R::E> {
    let (xx, yy, zz) = (r.sqr(&p.x), r.sqr(&p.y), r.sqr(&p.z));
    let s = r.mul(&p.x, &yy);
    let s = r.add(&r.add(&s, &s), &r.add(&s, &s));
    let m = r.add(&r.add(&r.add(&xx, &xx), &xx), &r.mul(a, &r.sqr(&zz)));
    let x = r.sub(&r.sqr(&m), &r.add(&s, &s));
    let y4 = r.sqr(&yy);
    let y8 = r.add(&y4, &y4);
    let y8 = r.add(&r.add(&y8, &y8), &r.add(&y8, &y8));
    let y = r.sub(&r.mul(&m, &r.sub(&s, &x)), &y8);
    let yz = r.mul(&p.y, &p.z);
    Jac { x, y, z: r.add(&yz, &yz) }
}

/// P + (x, y). The formula fails, giving 0 : 0 : 0, when P is O or (x, y).
fn add_affine<R: Ring>(r: &R, p: &Jac<R::E>, x: &R::E, y: &R::E) -> Jac<R::E> {
    let zz = r.sqr(&p.z);
    let h = r.sub(&r.mul(x, &zz), &p.x);
    let w = r.sub(&r.mul(y, &r.mul(&p.z, &zz)), &p.y);
    let hh = r.sqr(&h);
    let (hhh, v) = (r.mul(&h, &hh), r.mul(&p.x, &hh));
    let x3 = r.sub(&r.sub(&r.sqr(&w), &hhh), &r.add(&v, &v));
    let y3 = r.sub(&r.mul(&w, &r.sub(&v, &x3)), &r.mul(&p.y, &hhh));
    Jac { x: x3, y: y3, z: r.mul(&p.z, &h) }
}

/// kP for the point P = (x, y) and k >= 1, from the left.
fn multiply<R: Ring>(r: &R, a: &R::E, x: &R::E, y: &R::E, k: &Integer) -> Jac<R::E> {
    let mut acc = Jac { x: x.clone(), y: y.clone(), z: r.one() };
    let limbs = k.to_limbs();
    for i in (0..k.bits() as usize - 1).rev() {
        acc = double(r, a, &acc);
        if limbs[i / 64] >> (i % 64) & 1 == 1 {
            acc = add_affine(r, &acc, x, y);
        }
    }
    acc
}

/// Whether P is O modulo every prime of n: Z = 0 with Y prime to n. A formula
/// that fails gives 0 : 0 : 0, and zeros stay zero, so the Y left shows that
/// the steps went right modulo each prime.
fn is_zero_point<R: Ring>(r: &R, p: &Jac<R::E>) -> bool {
    p.z == r.from_int(&Integer::zero()) && r.gcd(&p.y).is_one()
}

/// The affine coordinates of P, unless P is O.
fn normalize<R: Ring>(r: &R, p: &Jac<R::E>) -> Option<(R::E, R::E)> {
    let zi = r.from_int(&r.to_int(&p.z).invmod(r.modulus())?);
    let zi2 = r.sqr(&zi);
    Some((r.mul(&p.x, &zi2), r.mul(&p.y, &r.mul(&zi2, &zi))))
}

// ----- the checker ------------------------------------------------------------------------------

/// Why a step fails, if it does.
fn step_fails(s: &Step, full: bool) -> Option<&'static str> {
    let int = Integer::from_u64;
    match s {
        Step::Det { n } if *n >= sw_bound() => Some("N is not below 3317044064679887385961981"),
        Step::Det { n } => (!det_prime(n) || full && !n.is_prime()).then_some("N is not prime"),
        Step::Minus { n, p, g } => {
            if *n < int(3) || n.is_even() || *p < int(2) || !(n - 1).is_divisible_by(p) {
                return Some("p does not divide N - 1");
            }
            if &(p + 1) * &(p + 1) <= *n {
                return Some("(p + 1)^2 is not above N");
            }
            let ok = with_ring!(n, |r| {
                let (one, g) = (r.one(), r.from_int(g));
                r.pow(&g, p) == one && r.gcd(&r.sub(&g, &one)).is_one()
            });
            (!ok).then_some("g does not have order p")
        }
        Step::Curve { n, p, a, b, x, y, .. } => {
            if *n <= Integer::one() || !n.gcd(&int(6)).is_one() {
                return Some("N is not prime to 6");
            }
            if !above_bound(p, n) {
                return Some("p is not above (N^(1/4) + 1)^2");
            }
            with_ring!(n, |r| curve_fails(r, p, a, b, x, y))
        }
    }
}

fn curve_fails<R: Ring>(r: &R, p: &Integer, a: &Integer, b: &Integer, x: &Integer, y: &Integer) -> Option<&'static str> {
    let (a, b, x, y) = (r.from_int(a), r.from_int(b), r.from_int(x), r.from_int(y));
    let small = |k: u64| r.from_int(&Integer::from_u64(k));
    let disc = r.add(&r.mul(&small(4), &r.mul(&r.sqr(&a), &a)), &r.mul(&small(27), &r.sqr(&b)));
    if !r.gcd(&disc).is_one() {
        return Some("the curve is singular");
    }
    if r.sqr(&y) != r.add(&r.mul(&r.add(&r.sqr(&x), &a), &x), &b) {
        return Some("P is not on the curve");
    }
    (!is_zero_point(r, &multiply(r, &a, &x, &y, p))).then_some("P does not have order p")
}

/// Whether the steps prove the first N prime: each is valid, the next proves
/// the prime it leaves, and the last is below the Sorenson-Webster bound.
/// The proof is written to `out` if given.
fn check(steps: &[Step], full: bool, mut out: Option<&mut String>) -> bool {
    if steps.is_empty() {
        if let Some(o) = out {
            o.push_str("The certificate has no steps.\n");
        }
        return false;
    }
    for (i, s) in steps.iter().enumerate() {
        let fail = step_fails(s, full).or_else(|| match (s.prime(), steps.get(i + 1)) {
            (Some(p), Some(t)) if p != t.n() => Some("the next step is not about p"),
            (Some(_), None) => Some("no step proves p prime"),
            (None, Some(_)) => Some("steps follow it"),
            _ => None,
        });
        if let Some(o) = out.as_deref_mut() {
            explain(o, i + 1, s, fail);
        }
        if fail.is_some() {
            return false;
        }
    }
    if let Some(o) = out {
        let _ = writeln!(o, "Therefore N = {} is prime.", steps[0].n());
    }
    true
}

/// Step i of a proof, or why it fails.
fn explain(o: &mut String, i: usize, s: &Step, fail: Option<&str>) {
    let _ = writeln!(o, "Step {i}: N = {}", s.n());
    let _ = match (s, fail) {
        (_, Some(why)) => writeln!(o, "  The step fails: {why}."),
        (Step::Curve { d, m, p, a, b, x, y, .. }, None) => {
            // The terms of the curve that are not zero.
            let mut e = "y^2 = x^3".to_string();
            for (c, t) in [(a, "*x"), (b, "")] {
                if !c.is_zero() {
                    let _ = write!(e, " {} {}{t}", if c.sign() < 0 { '-' } else { '+' }, c.abs());
                }
            }
            writeln!(o, "  E: {e} (from the discriminant {d}, with {m} points modulo N)\n  P = ({x}, {y}) on E has order p = {p} > (N^(1/4) + 1)^2")
        }
        (Step::Minus { p, g, .. }, None) => writeln!(o, "  g = {g} has order p = {p} modulo N, and (p + 1)^2 > N"),
        (Step::Det { .. }, None) => writeln!(o, "  N < {SW_BOUND} is a strong probable prime to the bases 2, 3, 5, ..., 37"),
    };
}

// ----- certificates as values -------------------------------------------------------------------

/// The certificate as Magma gives it: a sequence of lists.
fn certificate(steps: &[Step]) -> Value {
    let int = |x: &Integer| Value::Int(x.clone());
    let pair = |x: &Integer, y: &Integer| Value::int_seq([x.clone(), y.clone()]);
    let steps = steps
        .iter()
        .map(|s| match s {
            Step::Curve { n, d, m, p, a, b, x, y } => {
                Value::list(vec![Value::str("E"), int(n), int(d), int(m), int(p), pair(a, b), pair(x, y)])
            }
            Step::Minus { n, p, g } => Value::list(vec![Value::str("N-1"), int(n), int(p), int(g)]),
            Step::Det { n } => Value::list(vec![Value::str("Det"), int(n)]),
        })
        .collect();
    Value::seq(Some(Value::structure(StructKind::PowerStructure(t::LIST))), steps)
}

/// The steps of a certificate, if the value has the form of one. The curve
/// may also be given by [0, 0, 0, a, b] and the point by [x, y, 1].
fn parse(v: &Value) -> Option<Vec<Step>> {
    let Value::Seq(s) = v else { return None };
    s.elems.iter().map(parse_step).collect()
}

fn parse_step(v: &Value) -> Option<Step> {
    let Value::List(l) = v else { return None };
    let int = |i: usize| match l.get(i) {
        Some(Value::Int(x)) => Some(x.clone()),
        _ => None,
    };
    let ints = |i: usize| -> Option<Vec<Integer>> {
        let Some(Value::Seq(s)) = l.get(i) else { return None };
        s.elems.iter().map(|e| if let Value::Int(x) = e { Some(x.clone()) } else { None }).collect()
    };
    let Some(Value::Str(kind)) = l.first() else { return None };
    match (kind.as_str(), l.len()) {
        ("E", 7) => {
            let (a, b) = match ints(5)?.as_slice() {
                [a, b] => (a.clone(), b.clone()),
                [a1, a2, a3, a, b] if a1.is_zero() && a2.is_zero() && a3.is_zero() => (a.clone(), b.clone()),
                _ => return None,
            };
            let (x, y) = match ints(6)?.as_slice() {
                [x, y] => (x.clone(), y.clone()),
                [x, y, z] if z.is_one() => (x.clone(), y.clone()),
                _ => return None,
            };
            Some(Step::Curve { n: int(1)?, d: int(2)?, m: int(3)?, p: int(4)?, a, b, x, y })
        }
        ("N-1", 4) => Some(Step::Minus { n: int(1)?, p: int(2)?, g: int(3)? }),
        ("Det", 2) => Some(Step::Det { n: int(1)? }),
        _ => None,
    }
}

// ----- the format of Magma 2.28 and earlier -----------------------------------------------------

/// Below this bound the old format proves a prime by Pratt's certificate.
const PRATT: u64 = 100;

/// The certificate in the format of Magma 2.28 and earlier: a list of steps
/// [* n, -D, h or -1, m, [* a, b *], [* x, y, 1 *], [* [* p, 1 *] *] *] for a
/// curve (h the class number, -1 when it is 1), and for N - 1 steps
/// [* n, -1, 3, factors of (n - 1)/p, [* w *] *] (w^((n - 1)/2) = -1 and
/// w^((n - 1)/2p) != -1), [* n, -1, 1, factors of n - 1, witnesses *] (a
/// witness a_q^((n - 1)/q) != 1 for each prime q), or [* n, -1, 0, Pratt's
/// certificate *]. None if a step cannot be put so (as when N is not prime).
fn old_format(steps: &[Step]) -> Option<Value> {
    let mut out = Vec::new();
    for s in steps {
        match s {
            Step::Curve { n, d, m, p, a, b, x, y } => {
                let d = -d;
                let h = class_number(&d)?;
                let int = |x: &Integer| Value::Int(x.clone());
                out.push(Value::list(vec![
                    int(n),
                    int(&d),
                    Value::int(if h > 1 { h as i64 } else { -1 }),
                    int(m),
                    Value::list(vec![int(a), int(b)]),
                    Value::list(vec![int(x), int(y), Value::int(1)]),
                    Value::list(vec![Value::list(vec![int(p), Value::int(1)])]),
                ]));
            }
            Step::Minus { n, p, .. } => out.push(old_minus(n, p)?),
            Step::Det { n } => {
                // A chain of N - 1 steps down to a small prime.
                let mut n = n.clone();
                while n >= Integer::from_u64(PRATT) {
                    let f = factors(&(&n - 1));
                    let q = f.first()?.0.clone();
                    out.push(old_minus(&n, &q)?);
                    n = q;
                }
                if n < Integer::from_u64(2) {
                    return None;
                }
                out.push(Value::list(vec![Value::Int(n.clone()), Value::int(-1), Value::int(0), pratt(&n)?]));
            }
        }
    }
    Some(Value::list(out))
}

/// The prime factors of n > 0 with their exponents, largest first.
fn factors(n: &Integer) -> Vec<(Integer, u64)> {
    let mut f = factseq::factor(n);
    f.sort_by(|x, y| y.0.cmp(&x.0));
    f
}

fn factor_list(f: &[(Integer, u64)]) -> Value {
    Value::list(f.iter().map(|(q, e)| Value::list(vec![Value::Int(q.clone()), Value::Int(Integer::from_u64(*e))])).collect())
}

/// The old N - 1 step for n from the prime p dividing n - 1: by p alone
/// when p is odd and 2p + 1 > sqrt(n) (and p not small), else by the
/// primes of n - 1.
fn old_minus(n: &Integer, p: &Integer) -> Option<Value> {
    let n1 = n - 1;
    let half = n1.fdiv_2exp(1);
    let big = p.is_odd() && *p >= Integer::from_u64(PRATT) && {
        let s = &(p * 2) + 1;
        &s * &s > *n
    };
    if big {
        let k = n1.divexact(p);
        let (minus, kh) = (n1.clone(), k.fdiv_2exp(1));
        let w = (2..10000u64).map(Integer::from_u64).find(|w| w.powm(&half, n) == Some(minus.clone()) && w.powm(&kh, n) != Some(minus.clone()))?;
        return Some(Value::list(vec![Value::Int(n.clone()), Value::int(-1), Value::int(3), factor_list(&factors(&k)), Value::list(vec![Value::Int(w)])]));
    }
    let f = factors(&n1);
    let mut a = 2u64;
    let mut ws = Vec::new();
    for (q, _) in &f {
        let e = n1.divexact(q);
        while Integer::from_u64(a).powm(&e, n)?.is_one() {
            a += 1;
            if a > 10000 {
                return None;
            }
        }
        ws.push(Value::Int(Integer::from_u64(a)));
    }
    Some(Value::list(vec![Value::Int(n.clone()), Value::int(-1), Value::int(1), factor_list(&f), Value::list(ws)]))
}

/// Pratt's certificate [* p, g, [* certificates of the primes of p - 1 *] *]
/// of the prime p, with g its least primitive root; [* 2, 1 *] for 2.
fn pratt(p: &Integer) -> Option<Value> {
    if *p == Integer::from_u64(2) {
        return Some(Value::list(vec![Value::int(2), Value::int(1)]));
    }
    let p1 = p - 1;
    let mut qs: Vec<Integer> = factors(&p1).into_iter().map(|(q, _)| q).collect();
    qs.reverse();
    let g = (2..p.to_u64()?).map(Integer::from_u64).find(|g| qs.iter().all(|q| g.powm(&p1.divexact(q), p).is_some_and(|x| !x.is_one())))?;
    let subs = qs.iter().map(pratt).collect::<Option<Vec<Value>>>()?;
    Some(Value::list(vec![Value::Int(p.clone()), Value::Int(g), Value::list(subs)]))
}

/// The class number of the discriminant -d, by counting the primitive
/// reduced forms, which takes about d/6 steps; None unless 0 < d < 2^28 and
/// -d is 0 or 1 modulo 4.
fn class_number(d: &Integer) -> Option<u64> {
    let d = d.to_u64().filter(|&d| d > 0 && d < 1 << 28 && matches!(d % 4, 0 | 3))?;
    let gcd = |mut x: u64, mut y: u64| {
        while y != 0 {
            (x, y) = (y, x % y);
        }
        x
    };
    let mut h = 0;
    let mut a = 1u64;
    while 3 * a * a <= d {
        // b^2 + d = 4ac, so b has the parity of d.
        let lo = 1 - a as i64;
        for b in (lo + (lo - d as i64).rem_euclid(2)..=a as i64).step_by(2) {
            let b2 = (b * b) as u64;
            if (b2 + d) % (4 * a) != 0 {
                continue;
            }
            let c = (b2 + d) / (4 * a);
            if c < a || c == a && b < 0 || gcd(gcd(a, b.unsigned_abs()), c) != 1 {
                continue;
            }
            h += 1;
        }
        a += 1;
    }
    Some(h)
}

// ----- the intrinsics ---------------------------------------------------------------------------

fn primality_certificate(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int_ge(0, 1)?;
    match prove(&n) {
        Some(steps) => one(certificate(&steps)),
        None => Err(RuntimeError::runtime("Argument 1 was not proven to be prime")),
    }
}

fn check_certificate(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let print = a.param_bool("Print")?;
    let full = !matches!(a.param("Full"), Some(Value::Bool(false)));
    let mut text = String::new();
    let ok = match parse(&a.args[0]) {
        Some(steps) => check(&steps, full, print.then_some(&mut text)),
        None => {
            text.push_str("The argument does not have the form of a primality certificate.\n");
            false
        }
    };
    if print {
        it.out.write(&text);
    }
    boolv(ok)
}

fn old_certificate(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let steps = parse(&a.args[0]).ok_or_else(|| RuntimeError::runtime("Argument 1 is not a primality certificate"))?;
    one(old_format(&steps).ok_or_else(|| RuntimeError::runtime("Argument 1 is not a valid primality certificate"))?)
}

pub fn register(it: &mut Interp) {
    it.def("PrimalityCertificate", "n::RngIntElt -> SeqEnum", "A certificate of the primality of n, by ECPP.", primality_certificate);
    // The checker and the conversion are taken to be package intrinsics, as
    // IsPrimeCertificate, which they replace, was.
    it.def_params(
        "CheckCertificate",
        "cert::SeqEnum -> BoolElt",
        &[("Print", Value::Bool(false)), ("Full", Value::Bool(true))],
        "Whether cert is a valid primality certificate (printing the proof if Print is true).",
        check_certificate,
    )
    .package = true;
    it.def("OldCertificate", "cert::SeqEnum -> List", "The primality certificate cert in the format of Magma 2.28 and earlier.", old_certificate)
        .package = true;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bounds_are_exact() {
        // (n^(1/4) + 1)^2 for n = 10^40 is 10^20 + 2 10^10 + 1.
        let n = Integer::from_u64(10).pow(40);
        let edge = &(&Integer::from_u64(10).pow(20) + &Integer::from_u64(20_000_000_000)) + 1;
        assert!(!above_bound(&edge, &n));
        assert!(above_bound(&(&edge + 1), &n));
        // Just past a non-square n the bound is irrational.
        let n = &n + 1;
        assert!(!above_bound(&edge, &n));
        assert!(above_bound(&(&edge + 1), &n));
        assert!(det_prime(&Integer::from_u64(2)) && det_prime(&Integer::from_u64(37)) && !det_prime(&Integer::from_u64(1)));
        assert!(!det_prime(&Integer::from_u64(3215031751)) && det_prime(&Integer::from_u64(1000003)));
    }

    #[test]
    fn class_numbers_match() {
        let h = form_counts(1000);
        for (d, want) in [(3, 1), (4, 1), (23, 3), (47, 5), (71, 7), (163, 1), (292, 4), (1048, 6)] {
            if d <= 1000 {
                assert_eq!(h[d], want, "h(-{d})");
            }
            assert_eq!(class_number(&Integer::from_u64(d as u64)), Some(want as u64), "h(-{d})");
        }
        // -12 = -3 * 2^2 is not fundamental; its forms are x^2 + 3y^2 and
        // 2x^2 + 2xy + 2y^2, of which one is primitive.
        assert_eq!(class_number(&Integer::from_u64(12)), Some(1));
        for (d, want) in [(3, vec![-3]), (4, vec![-4]), (8, vec![-8]), (24, vec![-3, 8]), (20, vec![5, -4]), (1048, vec![-131, 8]), (4099, vec![-4099])] {
            assert_eq!(prime_discriminants(d), want, "D = -{d}");
        }
        let ds = discriminants();
        assert!(ds[..9].iter().all(|&(_, h)| h == 1) && ds[9].1 == 2);
        assert!(ds.windows(2).all(|w| (w[0].1, w[0].0) < (w[1].1, w[1].0)));
    }

    #[test]
    fn certificates_check() {
        let big = |e: u64| Integer::from_u64(10).pow(e);
        // Past 1024 bits the residues are FLINT's limbs rather than Montgomery's words.
        let mut wide = &Integer::one().mul_2exp(1030) + 1;
        while !wide.is_probable_prime() {
            wide = &wide + 2;
        }
        for n in [big(25) + Integer::from_u64(13), big(30).next_prime(), big(60).next_prime(), (&big(99) * 7).next_prime(), wide] {
            let steps = prove(&n).unwrap_or_else(|| panic!("no certificate for {n}"));
            assert_eq!(steps[0].n(), &n);
            assert!(check(&steps, true, None), "certificate of {n}: {steps:?}");
            // Any change to a curve step's point breaks it.
            if let Some(i) = steps.iter().position(|s| matches!(s, Step::Curve { .. })) {
                let mut bad = steps.clone();
                if let Step::Curve { x, .. } = &mut bad[i] {
                    *x = &*x + 1;
                }
                assert!(!check(&bad, true, None));
            }
        }
        assert_eq!(prove(&Integer::from_u64(1000003)), Some(vec![Step::Det { n: Integer::from_u64(1000003) }]));
        assert_eq!(prove(&(&big(30) + 1)), None);
        assert_eq!(prove(&Integer::one()), None);
    }
}
