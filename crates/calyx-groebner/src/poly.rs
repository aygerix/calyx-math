//! Sparse distributive polynomials.
//!
//! A polynomial is a list of terms in decreasing order: its coefficients
//! and, n words per term, its exponent vectors. Exponents are u32; larger
//! ones are refused on input and every product is checked.

use std::cmp::Ordering;

use crate::field::Field;
use crate::order::Order;

/// The monomials of a computation: the rank and the order.
#[derive(Clone, Debug)]
pub struct Ring {
    pub n: usize,
    pub order: Order,
}

impl Ring {
    #[inline]
    pub fn cmp(&self, a: &[u32], b: &[u32]) -> Ordering {
        self.order.cmp(a, b)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Poly<E> {
    pub c: Vec<E>,
    pub e: Vec<u32>,
}

impl<E: Clone> Poly<E> {
    fn with_capacity(terms: usize, n: usize) -> Poly<E> {
        Poly { c: Vec::with_capacity(terms), e: Vec::with_capacity(terms * n) }
    }

    pub fn len(&self) -> usize {
        self.c.len()
    }

    pub fn is_zero(&self) -> bool {
        self.c.is_empty()
    }

    #[inline]
    pub fn exp(&self, i: usize, n: usize) -> &[u32] {
        &self.e[i * n..(i + 1) * n]
    }

    pub fn lm(&self, n: usize) -> &[u32] {
        self.exp(0, n)
    }

    pub fn lc(&self) -> &E {
        &self.c[0]
    }

    #[inline]
    fn push(&mut self, c: E, e: &[u32]) {
        self.c.push(c);
        self.e.extend_from_slice(e);
    }

    /// The polynomial with the terms `terms`, in any order: equal monomials
    /// are combined and zero terms dropped.
    pub fn from_terms<F: Field<E = E>>(field: &F, ring: &Ring, mut terms: Vec<(E, Vec<u32>)>) -> Poly<E> {
        let n = ring.n;
        terms.sort_by(|a, b| ring.cmp(&b.1, &a.1));
        let mut p = Poly::with_capacity(terms.len(), n);
        for (c, e) in terms {
            match p.len() {
                k if k > 0 && p.exp(k - 1, n) == &e[..] => p.c[k - 1] = field.add(&p.c[k - 1], &c),
                _ => p.push(c, &e),
            }
        }
        let mut q = Poly::with_capacity(p.len(), n);
        for (i, c) in p.c.iter().enumerate() {
            if !field.is_zero(c) {
                q.push(c.clone(), p.exp(i, n));
            }
        }
        q
    }

    /// The total degree (0 for zero).
    pub fn degree(&self, n: usize) -> u64 {
        (0..self.len()).map(|i| degree(self.exp(i, n))).max().unwrap_or(0)
    }

    /// The product with the monomial `t`.
    pub fn shift(&self, t: &[u32], n: usize) -> Poly<E> {
        let mut p = Poly::with_capacity(self.len(), n);
        p.c.extend_from_slice(&self.c);
        for chunk in self.e.chunks(n) {
            p.e.extend(chunk.iter().zip(t).map(|(x, y)| x.checked_add(*y).expect("exponent overflow")));
        }
        p
    }

    /// Divide by the leading coefficient.
    pub fn make_monic<F: Field<E = E>>(&mut self, field: &F) {
        if self.is_zero() || field.is_one(self.lc()) {
            return;
        }
        let u = field.inv(self.lc());
        self.c.iter_mut().for_each(|c| *c = field.mul(c, &u));
    }
}

#[inline]
pub fn divides(a: &[u32], b: &[u32]) -> bool {
    a.iter().zip(b).all(|(x, y)| x <= y)
}

pub fn lcm(a: &[u32], b: &[u32]) -> Vec<u32> {
    a.iter().zip(b).map(|(x, y)| *x.max(y)).collect()
}

pub fn coprime(a: &[u32], b: &[u32]) -> bool {
    a.iter().zip(b).all(|(x, y)| *x == 0 || *y == 0)
}

/// `a / b`, for `b` dividing `a`.
pub fn quotient(a: &[u32], b: &[u32]) -> Vec<u32> {
    a.iter().zip(b).map(|(x, y)| x - y).collect()
}

pub fn degree(a: &[u32]) -> u64 {
    a.iter().map(|&x| x as u64).sum()
}

/// The variables of a monomial as a bit mask (variable i at bit i mod 64):
/// if `a` divides `b` then `mask(a) & !mask(b) == 0`.
pub fn mask(a: &[u32]) -> u64 {
    a.iter().enumerate().filter(|(_, x)| **x > 0).fold(0, |m, (i, _)| m | 1 << (i % 64))
}

/// `f - c t g` on the terms of `f` from `i0` on and of `g` from `j0` on,
/// for a monomial `t`.
#[allow(clippy::too_many_arguments)]
pub fn sub_mul<F: Field>(field: &F, ring: &Ring, f: &Poly<F::E>, i0: usize, c: &F::E, t: &[u32], g: &Poly<F::E>, j0: usize) -> Poly<F::E> {
    let n = ring.n;
    let mut out = Poly::with_capacity(f.len() - i0 + g.len() - j0, n);
    let nc = field.neg(c);
    let mut m = vec![0u32; n];
    let set = |m: &mut [u32], j: usize| {
        for (k, x) in m.iter_mut().enumerate() {
            *x = g.e[j * n + k].checked_add(t[k]).expect("exponent overflow");
        }
    };
    let (mut i, mut j) = (i0, j0);
    if j < g.len() {
        set(&mut m, j);
    }
    while i < f.len() && j < g.len() {
        match ring.cmp(f.exp(i, n), &m) {
            Ordering::Greater => {
                out.push(f.c[i].clone(), f.exp(i, n));
                i += 1;
                continue;
            }
            Ordering::Less => out.push(field.mul(&nc, &g.c[j]), &m),
            Ordering::Equal => {
                let v = field.sub_mul(&f.c[i], c, &g.c[j]);
                if !field.is_zero(&v) {
                    out.push(v, &m);
                }
                i += 1;
            }
        }
        j += 1;
        if j < g.len() {
            set(&mut m, j);
        }
    }
    for i in i..f.len() {
        out.push(f.c[i].clone(), f.exp(i, n));
    }
    while j < g.len() {
        out.push(field.mul(&nc, &g.c[j]), &m);
        j += 1;
        if j < g.len() {
            set(&mut m, j);
        }
    }
    out
}

/// Reduce the terms of `f` from index `start` on modulo the polynomials
/// `basis[k]` for `k` in `active` (the first whose leading monomial divides
/// a term is used), where `masks[k]` is the mask of the leading monomial of
/// `basis[k]`. The earlier terms are kept.
pub fn reduce<F: Field>(field: &F, ring: &Ring, f: Poly<F::E>, start: usize, basis: &[Poly<F::E>], masks: &[u64], active: &[usize]) -> Poly<F::E> {
    let n = ring.n;
    let mut done = Poly { c: f.c[..start].to_vec(), e: f.e[..start * n].to_vec() };
    let mut p = f;
    let mut i = start;
    while i < p.len() {
        let m = p.exp(i, n);
        let mm = mask(m);
        match active.iter().copied().find(|&k| masks[k] & !mm == 0 && divides(basis[k].lm(n), m)) {
            Some(k) => {
                let g = &basis[k];
                let c = if field.is_one(g.lc()) { p.c[i].clone() } else { field.mul(&p.c[i], &field.inv(g.lc())) };
                let t = quotient(m, g.lm(n));
                p = sub_mul(field, ring, &p, i + 1, &c, &t, g, 1);
                i = 0;
            }
            None => {
                done.push(p.c[i].clone(), m);
                i += 1;
            }
        }
    }
    done
}

/// The division of `f` by the polynomials `divisors`, some of which may be
/// zero: the leading term of what is left is divided by the first divisor
/// whose leading monomial divides it, or else moves to the remainder.
/// Returns the remainder and the quotients.
pub fn divide<F: Field>(field: &F, ring: &Ring, f: Poly<F::E>, divisors: &[Poly<F::E>]) -> (Poly<F::E>, Vec<Poly<F::E>>) {
    let n = ring.n;
    let active: Vec<usize> = (0..divisors.len()).filter(|&k| !divisors[k].is_zero()).collect();
    let masks: Vec<u64> = divisors.iter().map(|g| if g.is_zero() { 0 } else { mask(g.lm(n)) }).collect();
    let mut quotients: Vec<Poly<F::E>> = divisors.iter().map(|_| Poly::with_capacity(0, n)).collect();
    let mut rem = Poly::with_capacity(f.len(), n);
    let mut p = f;
    let mut i = 0;
    while i < p.len() {
        let m = p.exp(i, n);
        let mm = mask(m);
        match active.iter().copied().find(|&k| masks[k] & !mm == 0 && divides(divisors[k].lm(n), m)) {
            Some(k) => {
                let g = &divisors[k];
                let c = if field.is_one(g.lc()) { p.c[i].clone() } else { field.mul(&p.c[i], &field.inv(g.lc())) };
                let t = quotient(m, g.lm(n));
                // The leading terms only decrease, so each quotient is built
                // in decreasing order.
                quotients[k].push(c.clone(), &t);
                p = sub_mul(field, ring, &p, i + 1, &c, &t, g, 1);
                i = 0;
            }
            None => {
                rem.push(p.c[i].clone(), m);
                i += 1;
            }
        }
    }
    (rem, quotients)
}

/// Compare polynomials term by term from the largest, by monomial and then
/// by coefficient, a leading part of a polynomial being smaller than it:
/// the order in which Magma sorts a basis before reducing it.
pub fn cmp_poly<F: Field>(field: &F, ring: &Ring, a: &Poly<F::E>, b: &Poly<F::E>) -> Ordering {
    let n = ring.n;
    (0..a.len().min(b.len()))
        .map(|i| ring.cmp(a.exp(i, n), b.exp(i, n)).then_with(|| field.cmp(&a.c[i], &b.c[i])))
        .find(|o| o.is_ne())
        .unwrap_or_else(|| a.len().cmp(&b.len()))
}
