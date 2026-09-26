//! The change of order of the Gröbner basis of a zero-dimensional ideal by
//! the algorithm of Faugère, Gianni, Lazard and Mora.
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
//!
//! Over GF(p), p < 2^31, the vectors are of words, reduced mod p only as
//! often as the sums of products would overflow; over the other fields
//! they are of the field's elements.

use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap};

use crate::f4::Modulus;
use crate::field::{Field, Zp};
use crate::order::Order;
use crate::poly::{Poly, Ring, divides, mask};

/// Marks an index on the border rather than in the staircase.
const BORDER: u32 = 1 << 31;

/// The arithmetic of the vectors over the staircase.
trait Lin {
    /// An entry of a vector.
    type E: Clone;
    /// A coefficient of a polynomial.
    type C: Clone;
    /// A vector to which multiples of vectors are added; an entry is exact
    /// once read.
    type Acc;
    fn zero(&self) -> Self::E;
    fn one(&self) -> Self::E;
    fn is_zero(&self, x: &Self::E) -> bool;
    fn neg(&self, x: &Self::E) -> Self::E;
    fn mul(&self, x: &Self::E, y: &Self::E) -> Self::E;
    /// `x - y z`.
    fn sub_mul(&self, x: &Self::E, y: &Self::E, z: &Self::E) -> Self::E;
    fn inv(&self, x: &Self::E) -> Self::E;
    /// The entry -c for a coefficient c.
    fn neg_coef(&self, c: &Self::C) -> Self::E;
    /// The coefficient -x for an entry x.
    fn coef(&self, x: &Self::E) -> Self::C;
    fn one_coef(&self) -> Self::C;
    fn acc(&self, v: &[Self::E]) -> Self::Acc;
    fn zeros(&self, d: usize) -> Self::Acc;
    /// Add `x` to the entry `i`, at most once for each entry.
    fn add_at(&self, acc: &mut Self::Acc, i: usize, x: &Self::E);
    /// Subtract `x` times `row` from the entries from `from` on.
    fn sub_row(&self, acc: &mut Self::Acc, from: usize, x: &Self::E, row: &[Self::E]);
    /// The entry `i`.
    fn get(&self, acc: &mut Self::Acc, i: usize) -> Self::E;
    fn finish(&self, acc: Self::Acc) -> Vec<Self::E>;
}

/// Vectors of words over GF(p), p < 2^31, reduced when a batch of products
/// has been added.
struct Words<'a> {
    field: &'a Zp,
    md: Modulus,
    batch: usize,
}

impl Lin for Words<'_> {
    type E = u32;
    type C = u64;
    /// The entries, and the products added since they were reduced.
    type Acc = (Vec<u64>, usize);

    fn zero(&self) -> u32 {
        0
    }

    fn one(&self) -> u32 {
        1
    }

    fn is_zero(&self, x: &u32) -> bool {
        *x == 0
    }

    fn neg(&self, x: &u32) -> u32 {
        if *x == 0 { 0 } else { (self.md.p - *x as u64) as u32 }
    }

    fn mul(&self, x: &u32, y: &u32) -> u32 {
        self.md.reduce(*x as u64 * *y as u64) as u32
    }

    fn sub_mul(&self, x: &u32, y: &u32, z: &u32) -> u32 {
        self.md.reduce(*x as u64 + (self.md.p - *y as u64) * *z as u64) as u32
    }

    fn inv(&self, x: &u32) -> u32 {
        self.field.inv(&(*x as u64)) as u32
    }

    fn neg_coef(&self, c: &u64) -> u32 {
        self.neg(&(*c as u32))
    }

    fn coef(&self, x: &u32) -> u64 {
        self.neg(x) as u64
    }

    fn one_coef(&self) -> u64 {
        1
    }

    fn acc(&self, v: &[u32]) -> (Vec<u64>, usize) {
        (v.iter().map(|&x| x as u64).collect(), 0)
    }

    fn zeros(&self, d: usize) -> (Vec<u64>, usize) {
        (vec![0; d], 0)
    }

    fn add_at(&self, acc: &mut (Vec<u64>, usize), i: usize, x: &u32) {
        // A residue more than the products fits: see Modulus::batch.
        acc.0[i] += *x as u64;
    }

    fn sub_row(&self, acc: &mut (Vec<u64>, usize), from: usize, x: &u32, row: &[u32]) {
        let y = self.md.p - *x as u64;
        for (a, &r) in acc.0[from..].iter_mut().zip(row) {
            *a += y * r as u64;
        }
        acc.1 += 1;
        if acc.1 == self.batch {
            acc.0.iter_mut().for_each(|a| *a = self.md.reduce(*a));
            acc.1 = 0;
        }
    }

    fn get(&self, acc: &mut (Vec<u64>, usize), i: usize) -> u32 {
        let x = self.md.reduce(acc.0[i]);
        acc.0[i] = x;
        x as u32
    }

    fn finish(&self, acc: (Vec<u64>, usize)) -> Vec<u32> {
        acc.0.into_iter().map(|a| self.md.reduce(a) as u32).collect()
    }
}

/// Vectors of the elements of a field.
struct Elements<'a, F: Field>(&'a F);

impl<F: Field> Lin for Elements<'_, F> {
    type E = F::E;
    type C = F::E;
    type Acc = Vec<F::E>;

    fn zero(&self) -> F::E {
        self.0.zero()
    }

    fn one(&self) -> F::E {
        self.0.one()
    }

    fn is_zero(&self, x: &F::E) -> bool {
        self.0.is_zero(x)
    }

    fn neg(&self, x: &F::E) -> F::E {
        self.0.neg(x)
    }

    fn mul(&self, x: &F::E, y: &F::E) -> F::E {
        self.0.mul(x, y)
    }

    fn sub_mul(&self, x: &F::E, y: &F::E, z: &F::E) -> F::E {
        self.0.sub_mul(x, y, z)
    }

    fn inv(&self, x: &F::E) -> F::E {
        self.0.inv(x)
    }

    fn neg_coef(&self, c: &F::E) -> F::E {
        self.0.neg(c)
    }

    fn coef(&self, x: &F::E) -> F::E {
        self.0.neg(x)
    }

    fn one_coef(&self) -> F::E {
        self.0.one()
    }

    fn acc(&self, v: &[F::E]) -> Vec<F::E> {
        v.to_vec()
    }

    fn zeros(&self, d: usize) -> Vec<F::E> {
        vec![self.0.zero(); d]
    }

    fn add_at(&self, acc: &mut Vec<F::E>, i: usize, x: &F::E) {
        acc[i] = self.0.add(&acc[i], x);
    }

    fn sub_row(&self, acc: &mut Vec<F::E>, from: usize, x: &F::E, row: &[F::E]) {
        for (a, r) in acc[from..].iter_mut().zip(row) {
            if !self.0.is_zero(r) {
                *a = self.0.sub_mul(a, x, r);
            }
        }
    }

    fn get(&self, acc: &mut Vec<F::E>, i: usize) -> F::E {
        acc[i].clone()
    }

    fn finish(&self, acc: Vec<F::E>) -> Vec<F::E> {
        acc
    }
}

/// How the normal form of a monomial on the border is found: it is the
/// leading monomial of a basis element, or a variable times another
/// monomial on the border.
#[derive(Clone, Copy)]
enum How {
    Lead(usize),
    Times(usize, u32),
}

/// The quotient by the ideal, with the normal forms found so far.
struct Quotient<'a, L: Lin> {
    lin: &'a L,
    gb: &'a [Poly<L::C>],
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
    nf: Vec<Vec<L::E>>,
}

impl<L: Lin> Quotient<'_, L> {
    /// Whether the normal form of the monomial at `q` (from `next`) is yet
    /// to be found.
    fn missing(&self, q: u32) -> bool {
        q & BORDER != 0 && self.nf[(q & !BORDER) as usize].is_empty()
    }

    /// The normal form of x_k times the element with normal form `w`, whose
    /// products with x_k have their normal forms found.
    fn times(&self, k: usize, w: &[L::E]) -> Vec<L::E> {
        let (d, lin) = (self.d, self.lin);
        let mut acc = lin.zeros(d);
        for (s, x) in w.iter().enumerate() {
            if lin.is_zero(x) {
                continue;
            }
            let q = self.next[k * d + s];
            if q & BORDER == 0 {
                // No two monomials of the staircase have the same product.
                lin.add_at(&mut acc, q as usize, x);
                continue;
            }
            lin.sub_row(&mut acc, 0, &lin.neg(x), &self.nf[(q & !BORDER) as usize]);
        }
        lin.finish(acc)
    }

    /// Find the normal form of the monomial on the border with index `b`,
    /// and those it follows from.
    fn find(&mut self, b: u32) {
        let d = self.d;
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
                    let mut v = vec![self.lin.zero(); d];
                    for i in 1..g.len() {
                        v[self.at[g.exp(i, self.n)] as usize] = self.lin.neg_coef(&g.c[i]);
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
                    for (s, x) in self.nf[m as usize].iter().enumerate() {
                        let q = self.next[k * d + s];
                        if !self.lin.is_zero(x) && self.missing(q) {
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
    fn product(&mut self, k: usize, w: &[L::E]) -> Vec<L::E> {
        let d = self.d;
        for (s, x) in w.iter().enumerate() {
            let q = self.next[k * d + s];
            if !self.lin.is_zero(x) && self.missing(q) {
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
/// is the reduced Gröbner basis for the order of `from`, over GF(p) for a
/// prime p < 2^31, or None if the ideal is not zero-dimensional.
pub fn fglm(field: &Zp, from: &Ring, gb: &[Poly<u64>], to: &Ring) -> Option<Vec<Poly<u64>>> {
    debug_assert!(field.modulus() < 1 << 31);
    let md = Modulus::new(field.modulus());
    change(&Words { field, md, batch: md.batch() }, from, gb, to)
}

/// As `fglm`, over any field.
pub fn fglm_field<F: Field>(field: &F, from: &Ring, gb: &[Poly<F::E>], to: &Ring) -> Option<Vec<Poly<F::E>>> {
    change(&Elements(field), from, gb, to)
}

fn change<L: Lin>(lin: &L, from: &Ring, gb: &[Poly<L::C>], to: &Ring) -> Option<Vec<Poly<L::C>>> {
    let n = from.n;
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
    let nf = vec![Vec::new(); border.len()];
    let mut q = Quotient { lin, gb, n, d, at, next, how, nf };

    // The monomials kept and their normal forms, reduced to an echelon form:
    // the row of each is 0 before its pivot, where it is 1, and at the pivots
    // of the rows before it. The normal form of the ith monomial is leads[i]
    // times its row plus mu[i][j] times the jth row for j < i.
    let (mut kept, mut forms): (Vec<Vec<u32>>, Vec<Vec<L::E>>) = (Vec::new(), Vec::new());
    let (mut rows, mut pivots, mut mu, mut leads): (Vec<Vec<L::E>>, Vec<usize>, Vec<Vec<L::E>>, Vec<L::E>) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
    let mut basis: Vec<Poly<L::C>> = Vec::new();
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
            let mut v = vec![lin.zero(); d];
            v[0] = lin.one();
            v
        } else {
            let w = std::mem::take(&mut forms[from]);
            let v = q.product(k, &w);
            forms[from] = w;
            v
        };
        // Reduce v by the rows, in turn.
        let mut acc = lin.acc(&v);
        let mut lambda: Vec<L::E> = Vec::with_capacity(rows.len());
        for (row, &c) in rows.iter().zip(&pivots) {
            let x = lin.get(&mut acc, c);
            if !lin.is_zero(&x) {
                lin.sub_row(&mut acc, c, &x, row);
            }
            lambda.push(x);
        }
        let acc = lin.finish(acc);
        match acc.iter().position(|a| !lin.is_zero(a)) {
            None => {
                // v is the sum of lambda[i] times the ith row: as a combination
                // of the normal forms of the monomials kept, it gives a
                // polynomial of the new basis.
                let mut c = vec![lin.zero(); kept.len()];
                for i in (0..kept.len()).rev() {
                    let x = lin.mul(&lambda[i], &lin.inv(&leads[i]));
                    if !lin.is_zero(&x) {
                        for (l, u) in lambda[..i].iter_mut().zip(&mu[i]) {
                            *l = lin.sub_mul(l, &x, u);
                        }
                    }
                    c[i] = x;
                }
                let mut g = Poly { c: vec![lin.one_coef()], e: e.clone() };
                for i in (0..kept.len()).rev().filter(|&i| !lin.is_zero(&c[i])) {
                    g.c.push(lin.coef(&c[i]));
                    g.e.extend_from_slice(&kept[i]);
                }
                basis.push(g);
                new_lms.push((m, e));
            }
            Some(c) => {
                let u = lin.inv(&acc[c]);
                rows.push(acc[c..].iter().map(|a| lin.mul(a, &u)).collect());
                pivots.push(c);
                mu.push(lambda);
                leads.push(acc[c].clone());
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
