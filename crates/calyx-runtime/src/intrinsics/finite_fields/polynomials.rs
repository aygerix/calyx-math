//! Polynomials for finite fields: irreducible, primitive and Conway
//! polynomials.

use super::*;

pub(super) fn conway_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = a.int(0)?.clone();
    let n = a.int(1)?.clone();
    if !p.is_prime() {
        return Err(super::arg_prime(1, &p));
    }
    if n.sign() <= 0 {
        return Err(super::arg_ge(2, &n, 1));
    }
    let c = p.to_u64().zip(n.to_u64()).and_then(|(p, n)| calyx_flint::gr::conway_polynomial(p, n));
    let Some(c) = c else {
        return Err(RuntimeError::runtime("Conway polynomial not known for these parameters"));
    };
    one(int_poly_value(it, &p, &c)?)
}

pub(super) fn exists_conway_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = a.int(0)?.clone();
    let n = a.int(1)?.clone();
    if !p.is_prime() {
        return Err(super::arg_prime(1, &p));
    }
    if n.sign() <= 0 {
        return Err(super::arg_ge(2, &n, 1));
    }
    match p.to_u64().zip(n.to_u64()).and_then(|(p, n)| calyx_flint::gr::conway_polynomial(p, n)) {
        Some(c) => Ok(vals![Value::Bool(true), int_poly_value(it, &p, &c)?]),
        None => Ok(vals![Value::Bool(false), Value::Undef]),
    }
}

/// An irreducible polynomial of degree n over `k`: the Conway polynomial or
/// the defining polynomial of the default field over a prime field, else
/// the first sparse one.
fn irreducible_over(it: &mut Interp, k: &Rc<Struct>, n: u64) -> RResult<Vec<Elem>> {
    let ctx = ff(k).0.ctx.clone();
    if n == 1 {
        return Ok(vec![Elem::zero(&ctx), Elem::one(&ctx)?]);
    }
    if degree(k) == 1 {
        let p = ff(k).1.p.clone();
        let d = it.default_field(&p, n)?;
        return Ok(finite::int_poly_in(&ff(&d).1.modulus.clone(), &ctx));
    }
    it.ff_irreducible(k, n)
}

pub(super) fn irreducible_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = field_arg(a, 0)?;
    let n = a.small_ge(1, 1)?;
    let cs = irreducible_over(it, &k, n)?;
    one(poly_value(it, &k, &cs)?)
}

pub(super) fn random_irreducible_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = field_arg(a, 0)?;
    let n = a.small_ge(1, 1).map_err(super::bare)?;
    let cs = random_irreducible(it, &k, n)?;
    one(poly_value(it, &k, &cs)?)
}

/// Whether x generates the multiplicative group of k[x]/(f) for an
/// irreducible f of degree n over k.
fn poly_is_primitive(k: &Rc<Struct>, f: &Elem) -> RResult<bool> {
    let n = f.poly_len() as u64 - 1;
    if n == 0 || !f.poly_is_irreducible()? {
        return Ok(false);
    }
    let q1 = &ff(k).1.order().pow(n) - &Integer::one();
    let primes: Vec<Integer> = q1.factor().map(|x| x.factors.into_iter().map(|(p, _)| p).collect()).unwrap_or_default();
    let ctx = f.ctx().clone();
    let base = ctx.base().unwrap().clone();
    let x = Elem::poly_from_coeffs(&ctx, &[Elem::zero(&base), Elem::one(&base)?])?;
    let one_ = Elem::poly_from_coeffs(&ctx, &[Elem::one(&base)?])?;
    // x^(q1/r) mod f for each prime r.
    for r in &primes {
        let e = q1.divexact(r);
        if poly_powmod(&x, &e, f)?.equal(&one_) == Truth::True {
            return Ok(false);
        }
    }
    // x must also be a unit: f(0) != 0 (true for irreducible f of degree > 1).
    Ok(n > 1 || poly_powmod(&x, &q1, f)?.equal(&one_) == Truth::True && !is_zero(&f.poly_coeff(0)))
}

/// `b^e mod f` for polynomials.
pub(super) fn poly_powmod(b: &Elem, e: &Integer, f: &Elem) -> RResult<Elem> {
    let ctx = b.ctx().clone();
    let base = ctx.base().unwrap().clone();
    let mut acc = Elem::poly_from_coeffs(&ctx, &[Elem::one(&base)?])?;
    let b = b.poly_divrem(f)?.1;
    for i in (0..e.bits()).rev() {
        acc = acc.mul(&acc)?.poly_divrem(f)?.1;
        if !e.fdiv_2exp(i).is_even() {
            acc = acc.mul(&b)?.poly_divrem(f)?.1;
        }
    }
    Ok(acc)
}

pub(super) fn is_primitive_poly(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (k, f) = ff_poly_arg(&a.args[0])?;
    if f.poly_len() < 2 {
        return Err(RuntimeError::runtime("Argument 1 must have positive degree"));
    }
    boolv(poly_is_primitive(&k, &f)?)
}

pub(super) fn primitive_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = field_arg(a, 0)?;
    let m = a.small_ge(1, 2)?;
    let ctx = ff(&k).0.ctx.clone();
    let px = Ctx::poly(&ctx);
    // The defining polynomial of the default field when it is primitive.
    if degree(&k) == 1 {
        let cs = irreducible_over(it, &k, m)?;
        if poly_is_primitive(&k, &Elem::poly_from_coeffs(&px, &cs)?)? {
            return one(poly_value(it, &k, &cs)?);
        }
    }
    for _ in 0..100_000 {
        let cs = random_irreducible(it, &k, m)?;
        if poly_is_primitive(&k, &Elem::poly_from_coeffs(&px, &cs)?)? {
            return one(poly_value(it, &k, &cs)?);
        }
    }
    Err(RuntimeError::runtime("No primitive polynomial found"))
}

pub(super) fn all_irreducible_polynomials(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = field_arg(a, 0)?;
    let m = a.small_ge(1, 1)?;
    let (r, kf) = ff(&k);
    let ctx = r.ctx.clone();
    let q = kf.order().to_u64().ok_or_else(|| RuntimeError::runtime("Too many polynomials"))?;
    let total = (q as u128).checked_pow(m as u32).filter(|&t| t <= 1 << 24).ok_or_else(|| RuntimeError::runtime("Too many polynomials"))? as u64;
    let elems: Vec<Elem> = (0..q).map(|i| finite::nth_elem(&ctx, kf, i)).collect();
    let px = Ctx::poly(&ctx);
    let pv = it.poly_ring(&Value::Struct(k.clone()), true)?;
    let Value::Struct(ps) = &pv else { unreachable!() };
    let mut out = Vec::new();
    for i in 0..total {
        let mut cs = Vec::with_capacity(m as usize + 1);
        let mut c = i;
        for _ in 0..m {
            cs.push(elems[(c % q) as usize].clone());
            c /= q;
        }
        cs.push(Elem::one(&ctx)?);
        let f = Elem::poly_from_coeffs(&px, &cs)?;
        if f.poly_is_irreducible()? {
            out.push(make_elt(ps, f));
        }
    }
    let set: VSet = out.into_iter().collect();
    one(Value::Set(Rc::new(SetEnum::new(Some(pv.clone()), set))))
}

/// A polynomial over GF(2) with the given exponents.
fn gf2_poly(it: &mut Interp, exps: &[u64]) -> RResult<Value> {
    let n = *exps.iter().max().unwrap_or(&0) as usize;
    let mut cs = vec![Integer::zero(); n + 1];
    for &e in exps {
        cs[e as usize] = Integer::one();
    }
    int_poly_value(it, &Integer::from_u64(2), &cs)
}

/// Polynomials over GF(2) as bits (bit i is the coefficient of x^i), for
/// the searches for sparse irreducible polynomials of large degree.
mod gf2 {
    fn deg(a: u64) -> u32 {
        63 - a.leading_zeros()
    }

    /// The product of polynomials of degree below 32.
    fn clmul(a: u64, b: u64) -> u64 {
        (0..32).filter(|i| b >> i & 1 == 1).fold(0, |r, i| r ^ a << i)
    }

    fn rem(mut a: u64, h: u64) -> u64 {
        let dh = deg(h);
        while a != 0 && deg(a) >= dh {
            a ^= h << (deg(a) - dh);
        }
        a
    }

    /// x^e mod h for h of degree below 32.
    fn xpow_mod(e: u64, h: u64) -> u64 {
        let mut r = 1;
        for i in (0..64 - e.leading_zeros()).rev() {
            r = rem(clmul(r, r), h);
            if e >> i & 1 == 1 {
                r = rem(r << 1, h);
            }
        }
        r
    }

    /// Trial division of x^n + g by the irreducible polynomials of degree at
    /// most 12, for n above 12.
    pub struct Sieve {
        hs: Vec<(u64, u64)>,
    }

    impl Sieve {
        pub fn new(n: u64) -> Sieve {
            let mut irr: Vec<u64> = Vec::new();
            for h in 2u64..1 << 13 {
                if irr.iter().take_while(|&&g| 2 * deg(g) <= deg(h)).all(|&g| rem(h, g) != 0) {
                    irr.push(h);
                }
            }
            Sieve { hs: irr.into_iter().map(|h| (h, xpow_mod(n, h))).collect() }
        }

        /// Whether x^n + g (the sum of x^e over `low`) has a small factor.
        pub fn divides(&self, low: &[u64]) -> bool {
            self.hs.iter().any(|&(h, r)| low.iter().fold(0, |a, &e| a ^ if e < 64 { rem(1 << e, h) } else { xpow_mod(e, h) }) == r)
        }
    }

    /// Swan's theorem: x^n + x^k + 1 (0 < k < n) has an even number of
    /// irreducible factors, so is reducible.
    pub fn swan_reducible(n: u64, k: u64) -> bool {
        let k = if n % 2 == 1 && k % 2 == 1 { n - k } else { k };
        match (n % 2, k % 2) {
            (0, 0) => true,
            (0, _) => n != 2 * k && (n * k / 2) % 4 <= 1,
            _ if (2 * n) % k != 0 => matches!(n % 8, 3 | 5),
            _ => matches!(n % 8, 1 | 7),
        }
    }

    fn degree(a: &[u64]) -> Option<usize> {
        a.iter().rposition(|&w| w != 0).map(|i| i * 64 + deg(a[i]) as usize)
    }

    /// dst ^= src * x^s, within the words of dst.
    fn xor_shifted(dst: &mut [u64], src: &[u64], s: usize) {
        let (ws, bs) = (s / 64, s % 64);
        for (i, &w) in src.iter().enumerate().filter(|(_, w)| **w != 0) {
            if let Some(d) = dst.get_mut(i + ws) {
                *d ^= w << bs;
            }
            if bs > 0 {
                if let Some(d) = dst.get_mut(i + ws + 1) {
                    *d ^= w >> (64 - bs);
                }
            }
        }
    }

    /// The bits of `a` from `n` up.
    fn high(a: &[u64], n: usize) -> Vec<u64> {
        let (ws, bs) = (n / 64, n % 64);
        (ws..a.len()).map(|i| if bs == 0 { a[i] } else { a[i] >> bs | a.get(i + 1).map_or(0, |w| w << (64 - bs)) }).collect()
    }

    /// Clear the bits of `a` from `n` up.
    fn truncate(a: &mut [u64], n: usize) {
        let (ws, bs) = (n / 64, n % 64);
        for (i, w) in a.iter_mut().enumerate().skip(ws) {
            *w &= if i == ws && bs > 0 { (1 << bs) - 1 } else { 0 };
        }
    }

    /// Interleave the bits of a 32-bit word with zeros.
    fn spread(x: u64) -> u64 {
        let x = (x | x << 16) & 0x0000_ffff_0000_ffff;
        let x = (x | x << 8) & 0x00ff_00ff_00ff_00ff;
        let x = (x | x << 4) & 0x0f0f_0f0f_0f0f_0f0f;
        let x = (x | x << 2) & 0x3333_3333_3333_3333;
        (x | x << 1) & 0x5555_5555_5555_5555
    }

    /// t^2 modulo x^n + (the sum of x^e over `low`, all below n).
    fn sqr_mod(t: &[u64], n: usize, low: &[u64]) -> Vec<u64> {
        let mut a: Vec<u64> = t.iter().flat_map(|&w| [spread(w & 0xffff_ffff), spread(w >> 32)]).collect();
        loop {
            let h = high(&a, n);
            if h.iter().all(|&w| w == 0) {
                break;
            }
            truncate(&mut a, n);
            for &e in low {
                xor_shifted(&mut a, &h, e as usize);
            }
        }
        a.truncate(t.len());
        a
    }

    fn gcd_is_one(mut a: Vec<u64>, mut b: Vec<u64>) -> bool {
        loop {
            let Some(db) = degree(&b) else { return degree(&a) == Some(0) };
            while let Some(da) = degree(&a).filter(|&da| da >= db) {
                let b2 = b.clone();
                xor_shifted(&mut a, &b2, da - db);
            }
            std::mem::swap(&mut a, &mut b);
        }
    }

    /// Rabin's test: whether x^n + (the sum of x^e over `low`, all below n)
    /// is irreducible.
    pub fn is_irreducible(n: u64, low: &[u64]) -> bool {
        let n = n as usize;
        if n < 2 {
            return n == 1;
        }
        let mut f = vec![0u64; (n + 1).div_ceil(64)];
        f[n / 64] |= 1 << (n % 64);
        for &e in low {
            f[e as usize / 64] ^= 1 << (e % 64);
        }
        let mut x = vec![0u64; n.div_ceil(64)];
        x[0] = 2;
        let qs: Vec<usize> = (2..=n).filter(|&q| n % q == 0 && (2..q).take_while(|r| r * r <= q).all(|r| q % r != 0)).collect();
        let mut t = x.clone();
        for i in 1..=n {
            t = sqr_mod(&t, n, low);
            if qs.iter().any(|&q| i == n / q) {
                let mut u = t.clone();
                u[0] ^= 2;
                if !gcd_is_one(f.clone(), u) {
                    return false;
                }
            }
        }
        t == x
    }
}

/// `IrreducibleLowTermGF2Polynomial` and `IrreducibleSparseGF2Polynomial`
/// look their degree up in tables in Magma.
fn gf2_degree(a: &CallArgs, range: std::ops::RangeInclusive<u64>) -> RResult<u64> {
    let n = a.int(0)?;
    if n.sign() <= 0 {
        // (sic: Magma numbers the argument 2)
        return Err(super::arg_ge(2, n, 1));
    }
    n.to_u64().filter(|n| range.contains(n)).ok_or_else(|| RuntimeError::runtime("No polynomial known for this degree"))
}

pub(super) fn irreducible_low_term_gf2(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = gf2_degree(a, 1..=100_000)?;
    let sieve = (n > 12).then(|| gf2::Sieve::new(n));
    // x^n + g with deg g minimal, then g least with its top coefficients
    // compared first.
    for d in 0..n.min(64) {
        for bits in (1..1u64 << d).step_by(2).chain((d == 0).then_some(0)) {
            let low: Vec<u64> = std::iter::once(d).chain((0..d).filter(|i| bits >> i & 1 == 1)).collect();
            if sieve.as_ref().is_none_or(|s| !s.divides(&low)) && gf2::is_irreducible(n, &low) {
                return one(gf2_poly(it, &[&[n][..], &low].concat())?);
            }
        }
    }
    Err(RuntimeError::runtime("No polynomial known for this degree"))
}

pub(super) fn irreducible_sparse_gf2(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = gf2_degree(a, 4..=12_800)?;
    let sieve = (n > 12).then(|| gf2::Sieve::new(n));
    let found = |low: &[u64]| sieve.as_ref().is_none_or(|s| !s.divides(low)) && gf2::is_irreducible(n, low);
    for k in (1..n).filter(|&k| !gf2::swan_reducible(n, k)) {
        if found(&[k, 0]) {
            return one(gf2_poly(it, &[n, k, 0])?);
        }
    }
    for k3 in 3..n {
        for k2 in 2..k3 {
            for k1 in 1..k2 {
                if found(&[k3, k2, k1, 0]) {
                    return one(gf2_poly(it, &[n, k3, k2, k1, 0])?);
                }
            }
        }
    }
    Err(RuntimeError::runtime("No polynomial known for this degree"))
}


#[cfg(test)]
mod tests {
    use super::*;

    /// FLINT's test of x^n + (the sum of x^e over `low`) over GF(2).
    fn flint_irreducible(n: u64, low: &[u64]) -> bool {
        let fp = Ctx::residue_ring(&Integer::from_u64(2));
        let mut cs = vec![Elem::zero(&fp); n as usize + 1];
        for &e in low.iter().chain([n].iter()) {
            cs[e as usize] = cs[e as usize].add(&Elem::one(&fp).unwrap()).unwrap();
        }
        Elem::poly_from_coeffs(&Ctx::poly(&fp), &cs).unwrap().poly_is_irreducible().unwrap()
    }

    #[test]
    fn gf2_irreducibility_agrees_with_flint() {
        for n in 1..=11u64 {
            for bits in 0..1u64 << n {
                let low: Vec<u64> = (0..n).filter(|i| bits >> i & 1 == 1).collect();
                assert_eq!(gf2::is_irreducible(n, &low), flint_irreducible(n, &low), "{n} {bits:b}");
            }
        }
        let mut seed = 12345u64;
        for _ in 0..300 {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let n = 13 + seed % 300;
            let low: Vec<u64> = std::iter::once(0).chain((1..n).filter(|i| (seed >> (i % 61)) & 7 == 0 && i % 3 == 1)).collect();
            let sieve = gf2::Sieve::new(n);
            let fast = !sieve.divides(&low) && gf2::is_irreducible(n, &low);
            assert_eq!(fast, flint_irreducible(n, &low), "{n} {low:?}");
        }
    }

    #[test]
    fn swan_reducible_trinomials_are_reducible() {
        for n in 2..=64u64 {
            for k in 1..n {
                if gf2::swan_reducible(n, k) {
                    assert!(!flint_irreducible(n, &[k, 0]), "{n} {k}");
                }
            }
        }
    }
}
