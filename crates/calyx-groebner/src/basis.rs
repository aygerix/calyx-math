//! Functions on bases that need not be Gröbner bases: interreduction and
//! the test for a Gröbner basis.

use crate::field::Field;
use crate::poly::{Poly, Ring, cmp_poly, coprime, divides, lcm, mask, quotient, reduce, sub_mul};

fn same<F: Field>(field: &F, a: &Poly<F::E>, b: &Poly<F::E>) -> bool {
    a.len() == b.len() && a.e == b.e && a.c.iter().zip(&b.c).all(|(x, y)| field.is_zero(&field.sub(x, y)))
}

/// Reduce each polynomial modulo the others until none changes, dropping
/// those that become zero (Magma's `Reduce`). The polynomials are sorted as
/// by `cmp_poly` and taken in turn, each divided by the others in that
/// order; the result is monic, sorted by decreasing leading monomial.
pub fn interreduce<F: Field>(field: &F, ring: &Ring, polys: Vec<Poly<F::E>>) -> Vec<Poly<F::E>> {
    let n = ring.n;
    let mut s: Vec<Poly<F::E>> = polys.into_iter().filter(|p| !p.is_zero()).collect();
    loop {
        s.sort_by(|a, b| cmp_poly(field, ring, a, b));
        let mut changed = false;
        let mut i = 0;
        while i < s.len() {
            let masks: Vec<u64> = s.iter().map(|g| mask(g.lm(n))).collect();
            let others: Vec<usize> = (0..s.len()).filter(|&j| j != i).collect();
            let mut h = reduce(field, ring, s[i].clone(), 0, &s, &masks, &others);
            if h.is_zero() {
                s.remove(i);
                changed = true;
                continue;
            }
            h.make_monic(field);
            if !same(field, &h, &s[i]) {
                s[i] = h;
                changed = true;
            }
            i += 1;
        }
        if !changed {
            break;
        }
    }
    s.sort_by(|a, b| ring.cmp(b.lm(n), a.lm(n)));
    s
}

/// Drop each polynomial whose leading monomial is a multiple of that of
/// another, keeping the least by `cmp_poly` of those with equal leading
/// monomials, and interreduce the rest (Magma's `ReduceGroebnerBasis`).
pub fn reduce_basis<F: Field>(field: &F, ring: &Ring, polys: Vec<Poly<F::E>>) -> Vec<Poly<F::E>> {
    let n = ring.n;
    let mut s: Vec<Poly<F::E>> = polys.into_iter().filter(|p| !p.is_zero()).collect();
    // A divisor of a leading monomial is no larger, so it comes first.
    s.sort_by(|a, b| cmp_poly(field, ring, a, b));
    let mut kept: Vec<Poly<F::E>> = Vec::new();
    for p in s {
        if !kept.iter().any(|g| divides(g.lm(n), p.lm(n))) {
            kept.push(p);
        }
    }
    interreduce(field, ring, kept)
}

/// Whether the polynomials form a Gröbner basis of the ideal they generate:
/// Buchberger's criterion, with the pairs of coprime leading monomials
/// skipped.
pub fn is_groebner<F: Field>(field: &F, ring: &Ring, polys: Vec<Poly<F::E>>) -> bool {
    let n = ring.n;
    let mut g: Vec<Poly<F::E>> = polys.into_iter().filter(|p| !p.is_zero()).collect();
    g.iter_mut().for_each(|p| p.make_monic(field));
    let masks: Vec<u64> = g.iter().map(|p| mask(p.lm(n))).collect();
    let all: Vec<usize> = (0..g.len()).collect();
    for i in 0..g.len() {
        for j in i + 1..g.len() {
            let (a, b) = (g[i].lm(n), g[j].lm(n));
            if coprime(a, b) {
                continue;
            }
            let l = lcm(a, b);
            let s = sub_mul(field, ring, &g[i].shift(&quotient(&l, a), n), 1, &field.one(), &quotient(&l, b), &g[j], 1);
            if !reduce(field, ring, s, 0, &g, &masks, &all).is_zero() {
                return false;
            }
        }
    }
    true
}
