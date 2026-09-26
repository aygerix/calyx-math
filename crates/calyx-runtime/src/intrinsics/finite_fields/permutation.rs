//! Permutation polynomials.

use super::*;

// (DicksonFirst and DicksonSecond are in `upoly.rs`.)

pub(super) fn is_probably_permutation_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (k, f) = ff_poly_arg(&a.args[0]).map_err(|_| RuntimeError::runtime("Ring needs to be a finite field"))?;
    let attempts = match a.param("NumAttempts") {
        Some(Value::Int(n)) => n.to_u64().filter(|n| (1..1 << 30).contains(n)),
        _ => None,
    };
    let attempts = attempts.ok_or_else(|| RuntimeError::runtime("Integer must be small"))?;
    let (r, kf) = ff(&k);
    let ctx = r.ctx.clone();
    if f.poly_len() < 2 {
        return boolv(kf.order().is_one());
    }
    // Small fields: all values are distinct.
    if let Some(q) = kf.order().to_u64().filter(|&q| q <= 1 << 16) {
        let mut seen: Vec<Vec<u64>> = Vec::with_capacity(q as usize);
        for i in 0..q {
            seen.push(f.poly_evaluate(&finite::nth_elem(&ctx, kf, i))?.fq_coords_u64());
        }
        seen.sort();
        seen.dedup();
        return boolv(seen.len() as u64 == q);
    }
    // Otherwise f(x) - f(x0) has the single root x0 for random x0.
    let q = kf.order();
    let px = f.ctx().clone();
    let x = Elem::poly_from_coeffs(&px, &[Elem::zero(&ctx), Elem::one(&ctx)?])?;
    for _ in 0..attempts.min(1000) {
        let x0 = random_elem(it, &k);
        let y = f.poly_evaluate(&x0)?;
        let g = f.sub(&Elem::poly_from_coeffs(&px, &[y])?)?;
        let h = poly_powmod(&x, &q, &g)?.sub(&x)?;
        if h.poly_gcd(&g)?.poly_len() != 2 {
            return boolv(false);
        }
    }
    boolv(true)
}
