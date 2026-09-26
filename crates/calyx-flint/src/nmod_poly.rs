//! Polynomials modulo a word-sized prime that the caller keeps as slices of
//! residues below the prime, from the constant term up, and FLINT's
//! algorithms for them.

use flint3_sys as sys;

fn modulus(p: u64) -> sys::nmod_t {
    let mut m = sys::nmod_t { n: 0, ninv: 0, norm: 0 };
    unsafe { sys::nmod_init(&mut m, p) };
    m
}

/// The length of `a` without its leading zeros.
fn len(a: &[u64]) -> usize {
    a.iter().rposition(|&c| c != 0).map_or(0, |i| i + 1)
}

/// `a b` modulo `f`, for a prime p and `f` of positive degree: the
/// remainder, with the length of `f` less one.
pub fn mulmod(a: &[u64], b: &[u64], f: &[u64], p: u64) -> Vec<u64> {
    let (la, lb, lf) = (len(a), len(b), len(f));
    assert!(lf >= 2, "a modulus of positive degree");
    let mut out = vec![0; lf - 1];
    if la == 0 || lb == 0 {
        return out;
    }
    let m = modulus(p);
    unsafe {
        if la + lb <= lf {
            // The product is its own remainder.
            let ((x, lx), (y, ly)) = if la >= lb { ((a, la), (b, lb)) } else { ((b, lb), (a, la)) };
            sys::_nmod_poly_mul(out.as_mut_ptr(), x.as_ptr(), lx as sys::slong, y.as_ptr(), ly as sys::slong, m);
        } else {
            sys::_nmod_poly_mulmod(out.as_mut_ptr(), a.as_ptr(), la as sys::slong, b.as_ptr(), lb as sys::slong, f.as_ptr(), lf as sys::slong, m);
        }
    }
    out
}

/// The inverse of `a` modulo `f`, for a prime p and `a` of lower degree
/// than `f`, with the length of `f` less one; None if they have a common
/// factor.
pub fn invmod(a: &[u64], f: &[u64], p: u64) -> Option<Vec<u64>> {
    let (la, lf) = (len(a), len(f));
    assert!(la < lf, "a reduced modulo f");
    if la == 0 {
        return None;
    }
    let mut out = vec![0; lf - 1];
    let ok = unsafe { sys::_nmod_poly_invmod(out.as_mut_ptr(), a.as_ptr(), la as sys::slong, f.as_ptr(), lf as sys::slong, modulus(p)) };
    (ok != 0).then_some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    const P: u64 = 2147483647;

    /// The remainder of `a` by `f`, with the length of `f` less one, by
    /// long division.
    fn rem(a: &[u64], f: &[u64]) -> Vec<u64> {
        let lf = len(f);
        let u = crate::Nmod::new(P);
        let inv = u.inv(f[lf - 1]).unwrap();
        let mut r = a.to_vec();
        r.resize(r.len().max(lf - 1), 0);
        for k in (lf - 1..r.len()).rev() {
            let c = u.mul(r[k], inv);
            for (j, &x) in f[..lf].iter().enumerate() {
                r[k + 1 - lf + j] = u.sub(r[k + 1 - lf + j], u.mul(c, x));
            }
        }
        r.truncate(lf - 1);
        r
    }

    fn mul(a: &[u64], b: &[u64]) -> Vec<u64> {
        let u = crate::Nmod::new(P);
        let mut out = vec![0; (a.len() + b.len()).max(1) - 1];
        for (i, &x) in a.iter().enumerate() {
            for (j, &y) in b.iter().enumerate() {
                out[i + j] = u.add(out[i + j], u.mul(x, y));
            }
        }
        out
    }

    #[test]
    fn products_and_inverses_modulo_polynomials() {
        let mut s = 12345u64;
        let mut next = || {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            (s >> 33) % P
        };
        for (la, lb, lf) in [(1, 1, 2), (3, 2, 5), (4, 4, 5), (7, 3, 4), (1, 9, 6), (20, 20, 21), (2, 0, 3)] {
            let a: Vec<u64> = (0..la).map(|_| next()).collect();
            let b: Vec<u64> = (0..lb).map(|_| next()).collect();
            let f: Vec<u64> = (0..lf).map(|_| next().max(1)).collect();
            assert_eq!(mulmod(&a, &b, &f, P), rem(&mul(&a, &b), &f));
            let a = rem(&a, &f);
            if let Some(x) = invmod(&a, &f, P) {
                let mut one = vec![0; lf - 1];
                one[0] = 1;
                assert_eq!(mulmod(&a, &x, &f, P), one);
            }
        }
        // Leading zeros are ignored, and x - 1 divides (x - 1)(x - 2).
        assert_eq!(mulmod(&[0, 1, 0], &[0, 1], &[P - 2, 0, 1], P), vec![2, 0]);
        assert_eq!(invmod(&[P - 1, 1], &[2, P - 3, 1], P), None);
        assert_eq!(invmod(&[0, 0], &[2, P - 3, 1], P), None);
        assert_eq!(invmod(&[3], &[5, 1], P), Some(vec![1431655765]));
    }
}
