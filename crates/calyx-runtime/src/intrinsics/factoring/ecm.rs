//! ECM on Montgomery curves with Suyama's parametrization: stage 1 by
//! Montgomery's ladder on the prime powers up to B1, stage 2 by the
//! continuation of `stage2` on the normalised x-coordinates of the odd
//! multiples of the point.

use calyx_flint::Integer;

use super::arith::{Ring, with_ring};
use super::stage1::stage1;
use super::stage2::{Steps, stage2};

/// A proper divisor of the odd composite n from one curve with Suyama's
/// parameter `sigma` and the stage bounds b1 < b2, if it finds one (as
/// Factorization runs it).
pub fn curve(n: &Integer, b1: u64, b2: u64, sigma: u64) -> Option<Integer> {
    run(n, b1, b2, 2, &Integer::from_u64(sigma), None)
}

/// A proper divisor of the odd n > 1 from the curve of Suyama's `sigma`,
/// starting from x0 : 1 when x0 is given, with the bounds b1 and b2 and k
/// as `stage2` takes it.
pub fn run(n: &Integer, b1: u64, b2: u64, k: u64, sigma: &Integer, x0: Option<&Integer>) -> Option<Integer> {
    with_ring!(n, |r| on_curve(r, b1, b2, k, sigma, x0))
}

/// A point of the curve in the coordinates X : Z.
#[derive(Clone)]
struct Pt<E> {
    x: E,
    z: E,
}

/// The curve B y^2 = x^3 + A x^2 + x, by a24 = (A + 2) / 4.
struct Curve<'a, R: Ring> {
    r: &'a R,
    a24: R::E,
}

impl<R: Ring> Curve<'_, R> {
    /// 2P.
    #[inline(always)]
    fn dbl(&self, p: &Pt<R::E>) -> Pt<R::E> {
        let r = self.r;
        let ss = r.sqr(&r.add(&p.x, &p.z));
        let dd = r.sqr(&r.sub(&p.x, &p.z));
        let t = r.sub(&ss, &dd);
        Pt { x: r.mul(&ss, &dd), z: r.mul(&t, &r.add(&dd, &r.mul(&self.a24, &t))) }
    }

    /// P + Q from P - Q.
    #[inline(always)]
    fn dadd(&self, p: &Pt<R::E>, q: &Pt<R::E>, diff: &Pt<R::E>) -> Pt<R::E> {
        let r = self.r;
        let u = r.mul(&r.sub(&p.x, &p.z), &r.add(&q.x, &q.z));
        let v = r.mul(&r.add(&p.x, &p.z), &r.sub(&q.x, &q.z));
        Pt { x: r.mul(&diff.z, &r.sqr(&r.add(&u, &v))), z: r.mul(&diff.x, &r.sqr(&r.sub(&u, &v))) }
    }

    /// P + Q from P - Q = x : 1, a product fewer.
    #[inline(always)]
    fn dadd1(&self, p: &Pt<R::E>, q: &Pt<R::E>, x: &R::E) -> Pt<R::E> {
        let r = self.r;
        let u = r.mul(&r.sub(&p.x, &p.z), &r.add(&q.x, &q.z));
        let v = r.mul(&r.add(&p.x, &p.z), &r.sub(&q.x, &q.z));
        Pt { x: r.sqr(&r.add(&u, &v)), z: r.mul(x, &r.sqr(&r.sub(&u, &v))) }
    }

    /// kP for P = x : 1 and k at least 1, by Montgomery's ladder.
    fn ladder1(&self, x: &R::E, k: &Integer) -> Pt<R::E> {
        let p = Pt { x: x.clone(), z: self.r.one() };
        let limbs = k.to_limbs();
        let two = self.dbl(&p);
        let (mut r0, mut r1) = (p, two);
        for i in (0..k.bits() as usize - 1).rev() {
            if limbs[i / 64] >> (i % 64) & 1 == 1 {
                r0 = self.dadd1(&r1, &r0, x);
                r1 = self.dbl(&r1);
            } else {
                r1 = self.dadd1(&r1, &r0, x);
                r0 = self.dbl(&r0);
            }
        }
        r0
    }

    /// kP and (k + 1)P (k at least 1) by Montgomery's ladder.
    fn ladder(&self, p: &Pt<R::E>, k: u64) -> (Pt<R::E>, Pt<R::E>) {
        let (mut r0, mut r1) = (p.clone(), self.dbl(p));
        for i in (0..63 - k.leading_zeros()).rev() {
            if k >> i & 1 == 1 {
                r0 = self.dadd(&r1, &r0, p);
                r1 = self.dbl(&r1);
            } else {
                r1 = self.dadd(&r1, &r0, p);
                r0 = self.dbl(&r0);
            }
        }
        (r0, r1)
    }

    /// The x-coordinates X/Z of the points, by one inversion.
    fn normalize(&self, pts: &[Pt<R::E>]) -> Result<Vec<R::E>, Integer> {
        let mut zs: Vec<R::E> = pts.iter().map(|p| p.z.clone()).collect();
        self.r.invert_all(&mut zs)?;
        Ok(pts.iter().zip(&zs).map(|(p, z)| self.r.mul(&p.x, z)).collect())
    }
}

fn on_curve<R: Ring>(r: &R, b1: u64, b2: u64, k: u64, sigma: &Integer, x0: Option<&Integer>) -> Option<Integer> {
    let n = r.modulus();
    let (num, den, xn, xd) = super::suyama(sigma);
    let den = den.div_rem_euclid(n).unwrap().1;
    let Some(inv) = den.invmod(n) else { return r.proper(den.gcd(n)) };
    let c = Curve { r, a24: r.from_int(&(&num * &inv)) };
    let p = match x0 {
        Some(x) => Pt { x: r.from_int(x), z: r.one() },
        None => Pt { x: r.from_int(&xn), z: r.from_int(&xd) },
    };
    // Stage 2 needs the primes up to 3 in stage 1.
    let b1 = if b2 > b1 { b1.max(3) } else { b1 };
    // Each chunk's words multiply the point at once, normalised to Z = 1 (it
    // is invertible once the gcds have been 1).
    let step = |p: &Pt<R::E>, ws: &[u64]| {
        let mut z = [p.z.clone()];
        match r.invert_all(&mut z) {
            Ok(()) => c.ladder1(&r.mul(&p.x, &z[0]), &ws.iter().fold(Integer::one(), |k, &w| &k * &Integer::from_u64(w))),
            Err(_) => p.clone(),
        }
    };
    let p = match stage1(n, b1, p, step, |p| r.gcd(&p.z)) {
        Ok(p) => p,
        Err(d) => return d,
    };
    let (step, cur, next) = (p.clone(), p.clone(), p.clone());
    stage2(r, &mut Multiples { c: &c, p, step, cur, next }, b1, b2, k)
}

/// The multiples of the stage 1 point P for stage 2.
struct Multiples<'a, 'b, R: Ring> {
    c: &'a Curve<'b, R>,
    p: Pt<R::E>,
    /// dP, and the giant steps a dP and (a + 1) dP to come.
    step: Pt<R::E>,
    cur: Pt<R::E>,
    next: Pt<R::E>,
}

impl<R: Ring> Steps<R> for Multiples<'_, '_, R> {
    /// bP for the odd b, each from (b - 2)P and 2P.
    fn babies(&mut self, _r: &R, bs: &[u64]) -> Result<Vec<R::E>, Integer> {
        let c = self.c;
        let two = c.dbl(&self.p);
        // bP and (b + 2)P.
        let (mut cur, mut next) = (self.p.clone(), c.dadd(&two, &self.p, &self.p));
        let mut pts = Vec::with_capacity(bs.len());
        let mut b = 1;
        for &want in bs {
            while b < want {
                let after = c.dadd(&next, &two, &cur);
                cur = std::mem::replace(&mut next, after);
                b += 2;
            }
            pts.push(cur.clone());
        }
        c.normalize(&pts)
    }

    fn start(&mut self, _r: &R, d: u64, a: u64) {
        self.step = self.c.ladder(&self.p, d).0;
        (self.cur, self.next) = self.c.ladder(&self.step, a);
    }

    fn giants(&mut self, _r: &R, count: usize) -> Result<Vec<R::E>, Integer> {
        let c = self.c;
        let mut pts = Vec::with_capacity(count);
        for _ in 0..count {
            let after = c.dadd(&self.next, &self.step, &self.cur);
            pts.push(std::mem::replace(&mut self.cur, std::mem::replace(&mut self.next, after)));
        }
        c.normalize(&pts)
    }

    fn first_giant(&self) -> u64 {
        1
    }
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

    /// Curves whose order modulo p is 1000-smooth but for one prime q find
    /// p just when q is at most B2: by the pairing for q below 2^19, by the
    /// polynomials past 2^23 (which reach a little beyond B2), and for n
    /// past 512 and 1024 bits too.
    #[test]
    fn stage2_meets_the_last_prime() {
        let p = Integer::from_u64(10u64.pow(15)).next_prime();
        let pr = &p * &Integer::from_u64(10).pow(30).next_prime();
        let (big, huge) = (&pr * &Integer::one().mul_2exp(600).next_prime(), &pr * &Integer::one().mul_2exp(1100).next_prime());
        // A larger k takes more batches.
        for (n, k) in [(&pr, 2), (&big, 2), (&huge, 2), (&pr, 40)] {
            // Sigma and q, from the factored orders ECMOrder(p, sigma).
            for (sigma, q, below) in [(10u64, 244_003u64, 1u64), (187, 34_037_779, 1 << 21), (7, 197_543_509, 1 << 21)] {
                for (b2, found) in [(q, true), (q - below, false)] {
                    let got = run(n, 1000, b2, k, &Integer::from_u64(sigma), None);
                    assert_eq!(got.as_ref() == Some(&p), found, "sigma {sigma}, B2 {b2}, k {k}, n of {} bits", n.bits());
                }
            }
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
