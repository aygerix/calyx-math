//! The change of order of the Gröbner basis of a zero-dimensional ideal over
//! GF(p), p < 2^31, by the algorithm of Faugère, Gianni, Lazard and Mora.
//!
//! The quotient by the ideal has for basis the monomials that no leading
//! monomial of the Gröbner basis divides, the staircase; its elements are
//! written as vectors over it, their normal forms. The monomials are taken
//! in increasing order for the new order, each a variable times one taken
//! before: if its normal form is a combination of those of the monomials
//! kept so far, this gives an element of the new basis, and otherwise the
//! monomial is kept, in the staircase of the new basis.
//!
//! The normal form of x m is x times that of m: a combination of the normal
//! forms of the products x s for s in the staircase, each in the staircase
//! or on its border. A monomial on the border is a leading monomial of the
//! basis, or a variable times another on the border, and then its normal
//! form follows from those of smaller monomials. They are found as they are
//! needed, and kept.

use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap};

use crate::f4::Modulus;
use crate::field::{Field, Zp};
use crate::order::Order;
use crate::poly::{Poly, Ring, divides, mask};

/// Marks an index on the border rather than in the staircase.
const BORDER: u32 = 1 << 31;

/// How the normal form of a monomial on the border is found: it is the
/// leading monomial of a basis element, or a variable times another
/// monomial on the border.
#[derive(Clone, Copy)]
enum How {
    Lead(usize),
    Times(usize, u32),
}

/// The quotient by the ideal, with the normal forms found so far.
struct Quotient<'a> {
    md: Modulus,
    batch: usize,
    gb: &'a [Poly<u64>],
    n: usize,
    /// The size of the staircase.
    d: usize,
    /// The index in the staircase of each of its monomials.
    at: HashMap<Vec<u32>, u32>,
    /// For each variable k and each monomial s of the staircase, where x_k s
    /// is: its index in the staircase, or BORDER and its index on the border.
    next: Vec<u32>,
    how: Vec<How>,
    /// The normal forms of the monomials on the border, empty until found.
    nf: Vec<Vec<u32>>,
}

impl Quotient<'_> {
    /// Whether the normal form of the monomial at `q` (from `next`) is yet
    /// to be found.
    fn missing(&self, q: u32) -> bool {
        q & BORDER != 0 && self.nf[(q & !BORDER) as usize].is_empty()
    }

    /// The normal form of x_k times the element with normal form `w`, whose
    /// products with x_k have their normal forms found.
    fn times(&self, k: usize, w: &[u32]) -> Vec<u32> {
        let (d, md) = (self.d, self.md);
        let mut acc = vec![0u64; d];
        let mut count = 0;
        for (s, &x) in w.iter().enumerate() {
            if x == 0 {
                continue;
            }
            let q = self.next[k * d + s];
            if q & BORDER == 0 {
                // No two monomials of the staircase have the same product, so
                // this adds at most one residue to each entry.
                acc[q as usize] += x as u64;
                continue;
            }
            let x = x as u64;
            for (a, &y) in acc.iter_mut().zip(&self.nf[(q & !BORDER) as usize]) {
                *a += x * y as u64;
            }
            count += 1;
            if count == self.batch {
                acc.iter_mut().for_each(|a| *a = md.reduce(*a));
                count = 0;
            }
        }
        acc.into_iter().map(|a| md.reduce(a) as u32).collect()
    }

    /// Find the normal form of the monomial on the border with index `b`,
    /// and those it follows from.
    fn find(&mut self, b: u32) {
        let (d, p) = (self.d, self.md.p);
        let mut stack = vec![b];
        while let Some(&t) = stack.last() {
            let t = t as usize;
            if !self.nf[t].is_empty() {
                stack.pop();
                continue;
            }
            match self.how[t] {
                How::Lead(g) => {
                    // The basis is reduced: the tail is in the staircase.
                    let g = &self.gb[g];
                    let mut v = vec![0u32; d];
                    for i in 1..g.len() {
                        v[self.at[g.exp(i, self.n)] as usize] = (p - g.c[i]) as u32;
                    }
                    self.nf[t] = v;
                    stack.pop();
                }
                How::Times(k, m) => {
                    if self.nf[m as usize].is_empty() {
                        stack.push(m);
                        continue;
                    }
                    let depth = stack.len();
                    for (s, &x) in self.nf[m as usize].iter().enumerate() {
                        let q = self.next[k * d + s];
                        if x != 0 && self.missing(q) {
                            stack.push(q & !BORDER);
                        }
                    }
                    if stack.len() == depth {
                        self.nf[t] = self.times(k, &self.nf[m as usize]);
                        stack.pop();
                    }
                }
            }
        }
    }

    /// The normal form of x_k times the element with normal form `w`.
    fn product(&mut self, k: usize, w: &[u32]) -> Vec<u32> {
        let d = self.d;
        for (s, &x) in w.iter().enumerate() {
            let q = self.next[k * d + s];
            if x != 0 && self.missing(q) {
                self.find(q & !BORDER);
            }
        }
        self.times(k, w)
    }
}

/// A monomial to consider, x_k times the monomial kept with index `from`;
/// the least for the new order comes out first.
struct Next<'a> {
    order: &'a Order,
    e: Vec<u32>,
    from: usize,
    k: usize,
}

impl Ord for Next<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.order.cmp(&other.e, &self.e)
    }
}

impl PartialOrd for Next<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Next<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.e == other.e
    }
}

impl Eq for Next<'_> {}

/// The reduced Gröbner basis for the order of `to` of the ideal of which `gb`
/// is the reduced Gröbner basis for the order of `from`, or None if the
/// ideal is not zero-dimensional.
pub fn fglm(field: &Zp, from: &Ring, gb: &[Poly<u64>], to: &Ring) -> Option<Vec<Poly<u64>>> {
    let (n, p) = (from.n, field.modulus());
    debug_assert!(p < 1 << 31);
    let lms: Vec<(u64, &[u32])> = gb.iter().map(|g| (mask(g.lm(n)), g.lm(n))).collect();
    if lms.iter().any(|(_, l)| l.iter().all(|&x| x == 0)) {
        return Some(gb.to_vec());
    }
    // Zero-dimensional: a power of each variable is a leading monomial.
    if gb.is_empty() || !(0..n).all(|k| lms.iter().any(|(_, l)| l.iter().enumerate().all(|(i, &x)| (x > 0) == (i == k)))) {
        return None;
    }
    let standard = |e: &[u32]| {
        let m = mask(e);
        !lms.iter().any(|&(k, l)| k & !m == 0 && divides(l, e))
    };
    // The staircase, from 1: it has each divisor of its monomials.
    let mut stair: Vec<Vec<u32>> = vec![vec![0; n]];
    let mut at: HashMap<Vec<u32>, u32> = HashMap::from([(vec![0; n], 0)]);
    let mut j = 0;
    while j < stair.len() {
        for k in 0..n {
            let mut e = stair[j].clone();
            e[k] += 1;
            if !at.contains_key(&e) && standard(&e) {
                at.insert(e.clone(), stair.len() as u32);
                stair.push(e);
            }
        }
        j += 1;
    }
    let d = stair.len();
    // The border, and how to find the normal form of each of its monomials.
    let mut border: Vec<Vec<u32>> = Vec::new();
    let mut on: HashMap<Vec<u32>, u32> = HashMap::new();
    let mut next = vec![0u32; n * d];
    for k in 0..n {
        for (s, e) in stair.iter().enumerate() {
            let mut e = e.clone();
            e[k] += 1;
            next[k * d + s] = match at.get(&e) {
                Some(&i) => i,
                None => {
                    let len = border.len() as u32;
                    BORDER | *on.entry(e.clone()).or_insert_with(|| {
                        border.push(e);
                        len
                    })
                }
            };
        }
    }
    let lead: HashMap<&[u32], usize> = lms.iter().enumerate().map(|(g, &(_, l))| (l, g)).collect();
    let how: Vec<How> = border
        .iter()
        .map(|e| {
            if let Some(&g) = lead.get(&e[..]) {
                return How::Lead(g);
            }
            // A leading monomial divides e properly, so e is a variable times
            // another monomial on the border; best a leading monomial.
            let below: Vec<(usize, u32)> = (0..n)
                .filter(|&k| e[k] > 0)
                .filter_map(|k| {
                    let mut f = e.clone();
                    f[k] -= 1;
                    on.get(&f).map(|&b| (k, b))
                })
                .collect();
            let &(k, b) = below.iter().find(|&&(_, b)| lead.contains_key(&border[b as usize][..])).unwrap_or(&below[0]);
            How::Times(k, b)
        })
        .collect();
    let md = Modulus::new(p);
    let batch = md.batch();
    let nf = vec![Vec::new(); border.len()];
    let mut q = Quotient { md, batch, gb, n, d, at, next, how, nf };

    // The monomials kept and their normal forms, reduced to an echelon form:
    // the row of each is 0 before its pivot, where it is 1, and at the pivots
    // of the rows before it. The normal form of the ith monomial is leads[i]
    // times its row plus mu[i][j] times the jth row for j < i.
    let (mut kept, mut forms): (Vec<Vec<u32>>, Vec<Vec<u32>>) = (Vec::new(), Vec::new());
    let (mut rows, mut pivots, mut mu, mut leads): (Vec<Vec<u32>>, Vec<usize>, Vec<Vec<u32>>, Vec<u64>) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
    let mut basis: Vec<Poly<u64>> = Vec::new();
    let mut new_lms: Vec<(u64, Vec<u32>)> = Vec::new();
    let mut heap: BinaryHeap<Next> = BinaryHeap::from([Next { order: &to.order, e: vec![0; n], from: usize::MAX, k: 0 }]);
    let mut last: Option<Vec<u32>> = None;
    while let Some(Next { e, from, k, .. }) = heap.pop() {
        if last.as_ref() == Some(&e) {
            continue;
        }
        last = Some(e.clone());
        let m = mask(&e);
        if new_lms.iter().any(|(ml, l)| ml & !m == 0 && divides(l, &e)) {
            continue;
        }
        let v = if from == usize::MAX {
            let mut v = vec![0u32; d];
            v[0] = 1;
            v
        } else {
            let w = std::mem::take(&mut forms[from]);
            let v = q.product(k, &w);
            forms[from] = w;
            v
        };
        // Reduce v by the rows, in turn.
        let mut acc: Vec<u64> = v.iter().map(|&x| x as u64).collect();
        let mut lambda: Vec<u64> = Vec::with_capacity(rows.len());
        let mut count = 0;
        for (row, &c) in rows.iter().zip(&pivots) {
            let x = md.reduce(acc[c]);
            acc[c] = x;
            lambda.push(x);
            if x == 0 {
                continue;
            }
            let y = p - x;
            for (a, &r) in acc[c..].iter_mut().zip(row) {
                *a += y * r as u64;
            }
            count += 1;
            if count == batch {
                acc.iter_mut().for_each(|a| *a = md.reduce(*a));
                count = 0;
            }
        }
        acc.iter_mut().for_each(|a| *a = md.reduce(*a));
        match acc.iter().position(|&a| a != 0) {
            None => {
                // v is the sum of lambda[i] times the ith row: as a combination
                // of the normal forms of the monomials kept, it gives a
                // polynomial of the new basis.
                let mut c = vec![0u64; kept.len()];
                for i in (0..kept.len()).rev() {
                    let x = md.reduce(lambda[i] * field.inv(&leads[i]));
                    c[i] = x;
                    if x != 0 {
                        for (l, &u) in lambda[..i].iter_mut().zip(&mu[i]) {
                            *l = md.reduce(*l + (p - x) * u as u64);
                        }
                    }
                }
                let mut g = Poly { c: vec![1], e: e.clone() };
                for i in (0..kept.len()).rev().filter(|&i| c[i] != 0) {
                    g.c.push(p - c[i]);
                    g.e.extend_from_slice(&kept[i]);
                }
                basis.push(g);
                new_lms.push((m, e));
            }
            Some(c) => {
                let (x, u) = (acc[c], field.inv(&acc[c]));
                rows.push(acc[c..].iter().map(|&a| md.reduce(a * u) as u32).collect());
                pivots.push(c);
                mu.push(lambda.iter().map(|&l| l as u32).collect());
                leads.push(x);
                for k in 0..n {
                    let mut f = e.clone();
                    f[k] += 1;
                    heap.push(Next { order: &to.order, e: f, from: kept.len(), k });
                }
                kept.push(e);
                forms.push(v);
            }
        }
    }
    debug_assert_eq!(kept.len(), d);
    basis.reverse();
    Some(basis)
}
