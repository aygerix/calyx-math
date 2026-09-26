//! Pollard's p - 1 and Williams's p + 1 methods. Stage 1 raises x0 to the
//! prime powers up to B1: as a power for p - 1, as the Lucas value
//! V_k(x0) (V_0 = 2, V_1 = x0, V_(k+1) = x0 V_k - V_(k-1)) for p + 1. Stage 2
//! runs on the Lucas values of the result v, for p - 1 of v = x + 1/x: if
//! x has order q modulo p, V_(ad)(v) = V_b(v) modulo p for q = ad ± b.
//!
//! Over a long range, stage 2 works with a root alpha of X^2 - v X + 1, so
//! that V_k(v) = alpha^k + alpha^-k: the polynomial f = prod_b (X^2 - V_b X
//! + 1) has the values f(alpha^(ad)) = alpha^(ad|S|) prod_b (V_(ad) - V_b),
//! and those at the geometric progression of the alpha^(ad) come from one
//! product of polynomials (Bluestein's chirp: aj = C(a+j, 2) - C(a, 2) -
//! C(j, 2)), as in Montgomery and Kruppa's stage 2 for p ± 1.

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::modn::{ModCtx, ModPoly};

use super::arith::{Ring, with_ring};
use super::stage1::stage1;
use super::stage2::{Steps, stage2};

/// A proper divisor of the odd n > 1 by the p - 1 method from x0, with
/// the bounds b1 and b2 and k as `stage2` takes it.
pub fn p_minus_1(n: &Integer, b1: u64, b2: u64, k: u64, x0: &Integer) -> Option<Integer> {
    with_ring!(n, |r| minus(r, b1, b2, k, x0))
}

/// A proper divisor of the odd n > 1 by the p + 1 method from x0, with
/// the bounds b1 and b2 and k as `stage2` takes it.
pub fn p_plus_1(n: &Integer, b1: u64, b2: u64, k: u64, x0: &Integer) -> Option<Integer> {
    with_ring!(n, |r| plus(r, b1, b2, k, x0))
}

fn minus<R: Ring>(r: &R, b1: u64, b2: u64, k: u64, x0: &Integer) -> Option<Integer> {
    let one = r.one();
    // Stage 2 needs the primes up to 3 in stage 1.
    let b1 = if b2 > b1 { b1.max(3) } else { b1 };
    let step = |x: &R::E, ws: &[u64]| r.pow(x, &ws.iter().fold(Integer::one(), |e, &w| &e * &Integer::from_u64(w)));
    let x = match stage1(r.modulus(), b1, r.from_int(x0), step, |x| r.gcd(&r.sub(x, &one))) {
        Ok(x) => x,
        Err(d) => return d,
    };
    if b2 <= b1 {
        return None;
    }
    let mut inv = [x.clone()];
    if let Err(g) = r.invert_all(&mut inv) {
        return r.proper(g);
    }
    let [inv] = inv;
    stage2(r, &mut Lucas::new(r, r.add(&x, &inv)), b1, b2, k)
}

fn plus<R: Ring>(r: &R, b1: u64, b2: u64, k: u64, x0: &Integer) -> Option<Integer> {
    let two = r.add(&r.one(), &r.one());
    let b1 = if b2 > b1 { b1.max(3) } else { b1 };
    let step = |v: &R::E, ws: &[u64]| ws.iter().fold(v.clone(), |v, &w| lucas(r, &v, &two, w).0);
    let v = match stage1(r.modulus(), b1, r.from_int(x0), step, |v| r.gcd(&r.sub(v, &two))) {
        Ok(v) => v,
        Err(d) => return d,
    };
    stage2(r, &mut Lucas::new(r, v), b1, b2, k)
}

/// V_k(v) and V_(k+1)(v) for k at least 1, by the ladder V_2k = V_k^2 - 2,
/// V_(2k+1) = V_k V_(k+1) - v.
fn lucas<R: Ring>(r: &R, v: &R::E, two: &R::E, k: u64) -> (R::E, R::E) {
    let (mut a, mut b) = (v.clone(), r.sub(&r.sqr(v), two));
    for i in (0..63 - k.leading_zeros()).rev() {
        if k >> i & 1 == 1 {
            a = r.sub(&r.mul(&a, &b), v);
            b = r.sub(&r.sqr(&b), two);
        } else {
            b = r.sub(&r.mul(&a, &b), v);
            a = r.sub(&r.sqr(&a), two);
        }
    }
    (a, b)
}

/// The Lucas values of v for stage 2, by V_(m+n) = V_m V_n - V_(m-n).
struct Lucas<R: Ring> {
    v: R::E,
    two: R::E,
    /// V_d, and the values at the giant steps a d and (a + 1) d to come.
    step: R::E,
    cur: R::E,
    next: R::E,
}

impl<R: Ring> Lucas<R> {
    fn new(r: &R, v: R::E) -> Self {
        let two = r.add(&r.one(), &r.one());
        Lucas { step: two.clone(), cur: two.clone(), next: two.clone(), v, two }
    }
}

impl<R: Ring> Steps<R> for Lucas<R> {
    const GEOMETRIC: bool = true;

    fn poly(&mut self, r: &R, bs: &[u64], d: u64, lo: u64, hi: u64, batch: usize) -> Integer {
        let n = r.modulus();
        let ctx = ModCtx::new(n);
        let f = quadratics(&ctx, n, &self.babies(r, bs).unwrap().iter().map(|x| r.to_int(x)).collect::<Vec<_>>());
        let deg = f.len() - 1;
        let fc: Vec<R::E> = f.coeffs(0, deg + 1).iter().map(|c| r.from_int(c)).collect();
        drop(f);
        let e = Ext::new(r, self.v.clone());
        let step = e.pow(&e.alpha(), d);
        // The chirp step^C(m, 2), the same for every batch.
        let mut h = Vec::with_capacity(deg + batch);
        let (mut hm, mut sm) = (e.one(), e.one());
        for _ in 0..deg + batch {
            let next = e.mul(&hm, &sm);
            h.push(std::mem::replace(&mut hm, next));
            sm = e.mul(&sm, &step);
        }
        let (h0, h1) = e.split(&ctx, h.iter());
        let h01 = h0.add(&h1);
        let (mut acc, mut start) = (e.one(), e.pow(&step, lo));
        let mut a = lo;
        while a <= hi {
            let count = (batch as u64).min(hi - a + 1) as usize;
            // The values at start step^i, i < count, times units, are the sums
            // over j of f_j start^j step^-C(j, 2) step^C(i+j, 2).
            let mut g = Vec::with_capacity(deg + 1);
            let mut sj = e.one();
            for (j, c) in fc.iter().enumerate() {
                g.push(e.scale(&e.mul(&sj, &e.conj(&h[j])), c));
                sj = e.mul(&sj, &start);
            }
            g.reverse();
            let (g0, g1) = e.split(&ctx, g.iter());
            let g01 = g0.add(&g1);
            let (p0, p2, p1) = (h0.mulmid(&g0, deg, deg + count), h1.mulmid(&g1, deg, deg + count), h01.mulmid(&g01, deg, deg + count));
            for i in 0..count {
                let (p0, p2, p1) = (r.from_int(&p0[i]), r.from_int(&p2[i]), r.from_int(&p1[i]));
                acc = e.mul(&acc, &e.karatsuba(p0, p1, p2));
            }
            start = e.mul(&start, &e.pow(&step, count as u64));
            a += count as u64;
        }
        // The norm drops the unit alpha^k and squares the product in Z/n.
        r.gcd(&e.norm(&acc))
    }

    fn babies(&mut self, r: &R, bs: &[u64]) -> Result<Vec<R::E>, Integer> {
        let v2 = r.sub(&r.sqr(&self.v), &self.two);
        // V_(b-2) and V_b, from V_(-1) = V_1.
        let (mut prev, mut cur) = (self.v.clone(), self.v.clone());
        let mut vals = Vec::with_capacity(bs.len());
        let mut b = 1;
        for &want in bs {
            while b < want {
                let next = r.sub(&r.mul(&cur, &v2), &prev);
                prev = std::mem::replace(&mut cur, next);
                b += 2;
            }
            vals.push(cur.clone());
        }
        Ok(vals)
    }

    fn start(&mut self, r: &R, d: u64, a: u64) {
        self.step = lucas(r, &self.v, &self.two, d).0;
        // V_a(V_d) = V_(ad).
        (self.cur, self.next) = if a == 0 { (self.two.clone(), self.step.clone()) } else { lucas(r, &self.step, &self.two, a) };
    }

    fn giants(&mut self, r: &R, count: usize) -> Result<Vec<R::E>, Integer> {
        let mut vals = Vec::with_capacity(count);
        for _ in 0..count {
            let after = r.sub(&r.mul(&self.next, &self.step), &self.cur);
            vals.push(std::mem::replace(&mut self.cur, std::mem::replace(&mut self.next, after)));
        }
        Ok(vals)
    }
}

/// prod (X^2 - v X + 1) over the values v (in [0, n)), by a product tree.
fn quadratics(ctx: &Rc<ModCtx>, n: &Integer, vs: &[Integer]) -> ModPoly {
    let one = Integer::one();
    let mut level: Vec<ModPoly> = vs.iter().map(|v| ModPoly::new(ctx, &[one.clone(), n - v, one.clone()])).collect();
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len().div_ceil(2));
        let mut polys = level.into_iter();
        while let Some(a) = polys.next() {
            next.push(match polys.next() {
                Some(b) => a.mul(&b),
                None => a,
            });
        }
        level = next;
    }
    level.pop().unwrap_or_else(|| ModPoly::new(ctx, &[one]))
}

/// An element u + w alpha of (Z/n)[alpha] with alpha^2 = v alpha - 1.
#[derive(Clone)]
struct Quad<E> {
    u: E,
    w: E,
}

/// The arithmetic of (Z/n)[alpha], alpha^2 = v alpha - 1: alpha has norm 1,
/// and 1/alpha = v - alpha is its conjugate.
struct Ext<'a, R: Ring> {
    r: &'a R,
    v: R::E,
    zero: R::E,
}

impl<'a, R: Ring> Ext<'a, R> {
    fn new(r: &'a R, v: R::E) -> Self {
        let zero = r.sub(&r.one(), &r.one());
        Ext { r, v, zero }
    }

    fn one(&self) -> Quad<R::E> {
        Quad { u: self.r.one(), w: self.zero.clone() }
    }

    fn alpha(&self) -> Quad<R::E> {
        Quad { u: self.zero.clone(), w: self.r.one() }
    }

    /// The product from p0 = a_u b_u, p1 = (a_u + a_w)(b_u + b_w), p2 = a_w b_w.
    fn karatsuba(&self, p0: R::E, p1: R::E, p2: R::E) -> Quad<R::E> {
        let r = self.r;
        Quad { w: r.add(&r.sub(&p1, &r.add(&p0, &p2)), &r.mul(&self.v, &p2)), u: r.sub(&p0, &p2) }
    }

    fn mul(&self, a: &Quad<R::E>, b: &Quad<R::E>) -> Quad<R::E> {
        let r = self.r;
        self.karatsuba(r.mul(&a.u, &b.u), r.mul(&r.add(&a.u, &a.w), &r.add(&b.u, &b.w)), r.mul(&a.w, &b.w))
    }

    fn scale(&self, a: &Quad<R::E>, c: &R::E) -> Quad<R::E> {
        Quad { u: self.r.mul(&a.u, c), w: self.r.mul(&a.w, c) }
    }

    fn conj(&self, a: &Quad<R::E>) -> Quad<R::E> {
        let r = self.r;
        Quad { u: r.add(&a.u, &r.mul(&self.v, &a.w)), w: r.sub(&self.zero, &a.w) }
    }

    /// a times its conjugate: u^2 + v u w + w^2.
    fn norm(&self, a: &Quad<R::E>) -> R::E {
        let r = self.r;
        r.add(&r.mul(&a.u, &r.add(&a.u, &r.mul(&self.v, &a.w))), &r.sqr(&a.w))
    }

    fn pow(&self, a: &Quad<R::E>, k: u64) -> Quad<R::E> {
        let mut acc = self.one();
        for i in (0..64 - k.leading_zeros()).rev() {
            acc = self.mul(&acc, &acc);
            if k >> i & 1 == 1 {
                acc = self.mul(&acc, a);
            }
        }
        acc
    }

    /// The polynomials of the u and w parts of a sequence.
    fn split<'b>(&self, ctx: &Rc<ModCtx>, xs: impl Iterator<Item = &'b Quad<R::E>> + Clone) -> (ModPoly, ModPoly)
    where
        R::E: 'b,
    {
        let us: Vec<Integer> = xs.clone().map(|x| self.r.to_int(&x.u)).collect();
        let ws: Vec<Integer> = xs.map(|x| self.r.to_int(&x.w)).collect();
        (ModPoly::new(ctx, &us), ModPoly::new(ctx, &ws))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Primes p with p - 1 or p + 1 1000-smooth but for one prime q are
    /// found just when q is at most B2: by the pairing for q below 2^19, by
    /// the polynomials past 2^23 (which reach a little beyond B2), and for n
    /// past 512 and 1024 bits too.
    #[test]
    fn stage2_meets_the_last_prime() {
        let r = Integer::from_u64(10).pow(30).next_prime();
        let big = &r * &Integer::one().mul_2exp(600).next_prime();
        let huge = &r * &Integer::one().mul_2exp(1100).next_prime();
        for (q, below) in [(300_000u64, 1u64), (300_000_000, 1 << 21)] {
            let q = Integer::from_u64(q).next_prime();
            for sign in [1i64, -1] {
                let p = (1..500u64).map(|j| &(&q * &Integer::from_u64(2 * j)) + &Integer::from_i64(sign)).find(|p| p.is_prime()).unwrap();
                // For p + 1, x0^2 - 4 is not a square modulo p.
                let x0 = match sign {
                    1 => Integer::from_u64(3),
                    _ => (3..100u64).map(Integer::from_u64).find(|x| (&(x * x) - &Integer::from_u64(4)).kronecker(&p) == -1).unwrap(),
                };
                let q = q.to_u64().unwrap();
                // A larger k takes more batches.
                for (n, k) in [(&p * &r, 2), (&p * &big, 2), (&p * &huge, 2), (&p * &r, 40)] {
                    for (b2, found) in [(q, true), (q - below, false)] {
                        let got = if sign == 1 { p_minus_1(&n, 1000, b2, k, &x0) } else { p_plus_1(&n, 1000, b2, k, &x0) };
                        assert_eq!(got.as_ref() == Some(&p), found, "p {sign:+}: q {q}, B2 {b2}, k {k}, n of {} bits", n.bits());
                    }
                }
            }
        }
    }

    #[test]
    fn stage1_finds_smooth_orders() {
        // 1000003 - 1 = 2 * 3 * 166667 and 1000033 - 1 = 2^5 * 3 * 11 * 947.
        let n = Integer::from_u64(1000003 * 1000033);
        assert_eq!(p_minus_1(&n, 1000, 1000, 2, &Integer::from_u64(3)), Some(Integer::from_u64(1000033)));
        assert_eq!(p_minus_1(&n, 100, 100, 2, &Integer::from_u64(3)), None);
        // The powers of 1 and -1 show all of n at once.
        assert_eq!(p_minus_1(&n, 1000, 10000, 2, &Integer::one()), None);
        assert_eq!(p_plus_1(&n, 1000, 10000, 2, &Integer::from_u64(2)), None);
    }
}
