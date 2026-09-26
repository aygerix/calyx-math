//! Faugère's F4 algorithm over prime fields GF(p) with p < 2^31.
//!
//! Each step takes the pairs of least degree together: the halves of their
//! S-polynomials, and the multiples of basis elements that reduce the
//! monomials these contain (found by symbolic preprocessing), become the
//! rows of a matrix over GF(p) whose columns are the monomials in
//! decreasing order. The rows of its echelon form whose leading monomials
//! are new join the basis, with the criteria of Gebauer and Möller.
//!
//! Monomials are stored once each in a hash table and referred to by
//! index; their hashes are additive, so the hash of a product is the sum of
//! the hashes.
//!
//! The linear algebra follows the structure of these matrices: most rows
//! are reducers, one per column they lead, so their leading columns (the
//! pivots) need no search. The reducers are first reduced by each other,
//! from the last, into dense rows over the other (free) columns; each row
//! asked for is then reduced by adding one multiple of these for each of
//! its terms in a pivot column, and what is left over the free columns is
//! put in echelon form. The additions are dense, four rows at a time, with
//! the modular reductions delayed as long as the sums fit in 64 bits. When
//! there are few rows, reducing them by the reducers as they are is cheaper,
//! and the first rows are reduced so to see which way to go.
//!
//! With an order graded by the degree, the reduced reducers of the degrees
//! below the least degree of the new polynomials are the same in the next
//! matrix, and are carried over to it.
//!
//! For the modular method a run can be traced and replayed modulo other
//! primes (Traverso's Gröbner trace): the replay takes, from each matrix,
//! only the rows that its new polynomials needed, and has neither pairs nor
//! symbolic preprocessing.

use std::cmp::Ordering;
use std::collections::HashMap;

use crate::field::Zp;
use crate::order::Order;
use crate::poly::{self, Ring};

/// Monomials, each stored once and referred to by index.
#[derive(Clone)]
struct Monomials {
    n: usize,
    exps: Vec<u32>,
    hash: Vec<u64>,
    mask: Vec<u64>,
    /// The weighted degree by which pairs are selected and limited.
    deg: Vec<u64>,
    /// The total degree, which bounds the exponents.
    tdeg: Vec<u64>,
    /// Open addressing: the high half of the hash of a monomial and its
    /// index plus 1 in the low half; 0 when empty.
    table: Vec<u64>,
    rnd: Vec<u64>,
    weights: Vec<u64>,
    scratch: Vec<u32>,
}

impl Monomials {
    fn new(n: usize, weights: &[u64]) -> Monomials {
        // A fixed xorshift sequence: the hashes need only be spread out.
        let mut s = 0x9e37_79b9_7f4a_7c15u64;
        let rnd = (0..n)
            .map(|_| {
                s ^= s << 13;
                s ^= s >> 7;
                s ^= s << 17;
                s | 1
            })
            .collect();
        let (exps, hash, mask, deg, tdeg) = (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new());
        Monomials { n, exps, hash, mask, deg, tdeg, table: vec![0; 1 << 12], rnd, weights: weights.to_vec(), scratch: vec![0; n] }
    }

    fn len(&self) -> usize {
        self.hash.len()
    }

    fn exp(&self, i: u32) -> &[u32] {
        &self.exps[i as usize * self.n..(i as usize + 1) * self.n]
    }

    fn slot(&self, h: u64) -> usize {
        (h ^ h >> 29) as usize & (self.table.len() - 1)
    }

    /// The index of the monomial with hash `h` for which `same` holds, or
    /// the empty slot where it would go.
    #[inline(always)]
    fn find(&self, h: u64, same: impl Fn(&[u32]) -> bool) -> Result<u32, usize> {
        let mask = self.table.len() - 1;
        let mut k = self.slot(h);
        loop {
            let t = self.table[k];
            if t == 0 {
                return Err(k);
            }
            let id = (t as u32).wrapping_sub(1);
            if t >> 32 == h >> 32 && same(self.exp(id)) {
                return Ok(id);
            }
            k = (k + 1) & mask;
        }
    }

    /// Add the monomial `e` with hash `h` at the empty slot `k`.
    fn add(&mut self, e: &[u32], h: u64, k: usize) -> u32 {
        let id = self.len() as u32;
        self.exps.extend_from_slice(e);
        self.hash.push(h);
        self.mask.push(e.iter().enumerate().filter(|(_, x)| **x > 0).fold(0, |m, (i, _)| m | 1 << (i % 64)));
        self.deg.push(e.iter().zip(&self.weights).map(|(&x, &w)| x as u64 * w).sum());
        self.tdeg.push(e.iter().map(|&x| x as u64).sum());
        self.table[k] = h >> 32 << 32 | (id as u64 + 1);
        if 2 * self.len() > self.table.len() {
            self.grow();
        }
        id
    }

    fn grow(&mut self) {
        self.table = vec![0; 2 * self.table.len()];
        let mask = self.table.len() - 1;
        for id in 0..self.len() {
            let h = self.hash[id];
            let mut k = self.slot(h);
            while self.table[k] != 0 {
                k = (k + 1) & mask;
            }
            self.table[k] = h >> 32 << 32 | (id as u64 + 1);
        }
    }

    fn insert_hashed(&mut self, e: &[u32], h: u64) -> u32 {
        match self.find(h, |x| x == e) {
            Ok(id) => id,
            Err(k) => self.add(e, h, k),
        }
    }

    fn hash_of(&self, e: &[u32]) -> u64 {
        e.iter().zip(&self.rnd).fold(0u64, |h, (&x, &r)| h.wrapping_add(r.wrapping_mul(x as u64)))
    }

    fn insert(&mut self, e: &[u32]) -> u32 {
        self.insert_hashed(e, self.hash_of(e))
    }

    /// The index of the monomial `e`, if it is stored.
    fn lookup(&self, e: &[u32]) -> Option<u32> {
        self.find(self.hash_of(e), |x| x == e).ok()
    }

    fn mul(&mut self, a: u32, b: u32) -> u32 {
        // No exponent exceeds the total degree.
        assert!(self.tdeg[a as usize] + self.tdeg[b as usize] <= u32::MAX as u64, "exponent overflow");
        let h = self.hash[a as usize].wrapping_add(self.hash[b as usize]);
        let (x, y) = (self.exp(a), self.exp(b));
        match self.find(h, |e| e.iter().zip(x).zip(y).all(|((&e, &x), &y)| e == x + y)) {
            Ok(id) => id,
            Err(k) => {
                let mut e = std::mem::take(&mut self.scratch);
                let n = self.n;
                for (i, v) in e.iter_mut().enumerate() {
                    *v = self.exps[a as usize * n + i] + self.exps[b as usize * n + i];
                }
                let id = self.add(&e, h, k);
                self.scratch = e;
                id
            }
        }
    }

    /// `b / a`, for `a` dividing `b`.
    fn quotient(&mut self, b: u32, a: u32) -> u32 {
        let h = self.hash[b as usize].wrapping_sub(self.hash[a as usize]);
        let (x, y) = (self.exp(b), self.exp(a));
        match self.find(h, |e| e.iter().zip(x).zip(y).all(|((&e, &x), &y)| e == x - y)) {
            Ok(id) => id,
            Err(k) => {
                let mut e = std::mem::take(&mut self.scratch);
                let n = self.n;
                for (i, v) in e.iter_mut().enumerate() {
                    *v = self.exps[b as usize * n + i] - self.exps[a as usize * n + i];
                }
                let id = self.add(&e, h, k);
                self.scratch = e;
                id
            }
        }
    }

    /// Whether the lcm of `a` and `b` is `c`.
    fn is_lcm(&self, a: u32, b: u32, c: u32) -> bool {
        self.exp(a).iter().zip(self.exp(b)).zip(self.exp(c)).all(|((&x, &y), &z)| x.max(y) == z)
    }

    fn divides(&self, a: u32, b: u32) -> bool {
        self.mask[a as usize] & !self.mask[b as usize] == 0 && self.exp(a).iter().zip(self.exp(b)).all(|(x, y)| x <= y)
    }
}

/// A polynomial: monic, its terms in decreasing order.
struct Poly {
    c: Vec<u32>,
    m: Vec<u32>,
}

struct Pair {
    i: u32,
    j: u32,
    lcm: u32,
}

const NONE: u32 = u32::MAX;

/// A matrix from symbolic preprocessing: the columns (monomials in
/// decreasing order) and the rows, each the columns of a multiple of a
/// polynomial, whose coefficients are the polynomial's. The first `given`
/// rows are those asked for; the others reduce, one per leading column.
struct Matrix {
    cols: Vec<u32>,
    rows: Vec<(Vec<u32>, u32)>,
    given: usize,
}

/// Reduction modulo p < 2^32 by Barrett's method.
#[derive(Clone, Copy)]
pub(crate) struct Modulus {
    pub(crate) p: u64,
    /// 2^64 / p, rounded down.
    r: u64,
}

impl Modulus {
    pub(crate) fn new(p: u64) -> Modulus {
        Modulus { p, r: u64::MAX / p }
    }

    #[inline(always)]
    pub(crate) fn reduce(self, a: u64) -> u64 {
        // The quotient is off by at most one.
        let t = a - ((a as u128 * self.r as u128) >> 64) as u64 * self.p;
        if t >= self.p { t - self.p } else { t }
    }

    /// How many products of residues can be added to a residue in a u64.
    pub(crate) fn batch(self) -> usize {
        let p = self.p;
        ((u64::MAX - 2 * p) / ((p - 1) * (p - 1)).max(1)).clamp(1, 1 << 32) as usize
    }
}

/// The number of entries of the reduced pivot rows kept at once.
const BUDGET: usize = 1 << 22;

/// About how much more a term subtracted in a cascade costs than a term of
/// a dense addition.
const SCATTER: u64 = 4;

/// The most entries of the reduced pivot rows kept at once, all of them, so
/// that they can be carried over to the next matrix.
const WHOLE: usize = 1 << 26;

const NOWHERE: usize = usize::MAX;

/// The reduced pivot rows of a matrix: that of column c is `data` from
/// `start[c]`, over the free columns from `before[c]` on.
struct Reduced<E> {
    before: Vec<u32>,
    start: Vec<usize>,
    data: Vec<E>,
}

/// The type in which the reduced pivot rows keep their residues: u16 when
/// p < 2^16, which halves the memory they take and the time to read them.
trait Entry: Copy + Default + Send + Sync {
    fn of(x: u64) -> Self;
    fn get(self) -> u64;
}

impl Entry for u16 {
    fn of(x: u64) -> u16 {
        x as u16
    }
    fn get(self) -> u64 {
        self as u64
    }
}

impl Entry for u32 {
    fn of(x: u64) -> u32 {
        x as u32
    }
    fn get(self) -> u64 {
        self as u64
    }
}

/// Reduced pivot rows carried from one matrix to the next.
#[derive(Default)]
struct Cache<E> {
    /// Rows are kept for monomials of degree below this.
    deg: u64,
    /// The free monomials of the last matrix of degree below `deg`, in
    /// decreasing order.
    low: Vec<u32>,
    /// The row kept for each monomial.
    rows: HashMap<u32, Kept>,
    data: Vec<E>,
    /// The monomials of the rows.
    mons: Vec<u32>,
}

/// A reduced pivot row carried over: the polynomial it is a multiple of,
/// where its monomials are in `mons` of the cache, and where it is in
/// `data`, reduced, with its length; it covers the last free columns of
/// `low`.
#[derive(Clone, Copy)]
struct Kept {
    g: u32,
    mons: usize,
    data: usize,
    len: usize,
}

/// A pass of the elimination over the free columns from `f0` to `f1`,
/// with the pivot rows reduced so far: the one of column c is `store` from
/// `start[c]`, over the free columns from `before[c]` (or f0) to f1.
struct Pass<'a, E> {
    p: u64,
    md: Modulus,
    batch: usize,
    f0: usize,
    f1: usize,
    before: &'a [u32],
    pivot: &'a [u32],
    start: &'a [usize],
    store: &'a [E],
}

impl<E: Entry> Pass<'_, E> {
    /// Add the row with columns `cols` and coefficients `xs`, reduced by
    /// the pivot rows, to `acc`.
    fn add(&self, acc: &mut [u64], cols: &[u32], xs: &[u32]) {
        #[cfg(target_arch = "x86_64")]
        if std::arch::is_x86_feature_detected!("avx2") {
            // SAFETY: the processor has AVX2.
            return unsafe { self.add_avx2(acc, cols, xs) };
        }
        self.add_any(acc, cols, xs)
    }

    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "avx2")]
    unsafe fn add_avx2(&self, acc: &mut [u64], cols: &[u32], xs: &[u32]) {
        self.add_any(acc, cols, xs)
    }

    #[inline(always)]
    fn add_any(&self, acc: &mut [u64], cols: &[u32], xs: &[u32]) {
        let (f0, f1) = (self.f0, self.f1);
        // The multiples of pivot rows to subtract are taken four at a time
        // where they overlap, which saves loads and stores of acc.
        let four = self.batch >= 8;
        let mut q = [(0usize, 0usize, 0u32); 4];
        let (mut k, mut n) = (0, 0);
        for (&c, &x) in cols.iter().zip(xs) {
            let c = c as usize;
            let b = self.before[c] as usize;
            if self.pivot[c] == NONE {
                if (f0..f1).contains(&b) {
                    acc[b] += x as u64;
                }
                continue;
            }
            let l = b.clamp(f0, f1);
            if l == f1 {
                continue;
            }
            if n + 4 > self.batch {
                acc[f0..f1].iter_mut().for_each(|a| *a = self.md.reduce(*a));
                n = 0;
            }
            q[k] = (self.start[c], l, (self.p - x as u64) as u32);
            k += 1;
            if k == 4 || !four {
                self.sub(acc, &q[..k]);
                n += k;
                k = 0;
            }
        }
        self.sub(acc, &q[..k]);
    }

    /// Subtract from `acc` the multiples of pivot rows in `q`: (the start of
    /// the row in `store`, its first column, the multiplier), in increasing
    /// order of first column.
    #[inline(always)]
    fn sub(&self, acc: &mut [u64], q: &[(usize, usize, u32)]) {
        let f1 = self.f1;
        let row = |&(s, l, _): &(usize, usize, u32), from: usize| &self.store[s + from - l..s + f1 - l];
        let get = |y: E| y.get();
        if q.len() < 4 {
            for e in q {
                let (a, r, m) = (&mut acc[e.1..f1], row(e, e.1), e.2 as u64);
                for (a, &y) in a.iter_mut().zip(r) {
                    *a += m * get(y);
                }
            }
            return;
        }
        let l = q[3].1;
        for e in &q[..3] {
            let (a, r, m) = (&mut acc[e.1..l], &self.store[e.0..e.0 + l - e.1], e.2 as u64);
            for (a, &y) in a.iter_mut().zip(r) {
                *a += m * get(y);
            }
        }
        let a = &mut acc[l..f1];
        let n = a.len();
        let (r0, r1, r2, r3) = (&row(&q[0], l)[..n], &row(&q[1], l)[..n], &row(&q[2], l)[..n], &row(&q[3], l)[..n]);
        let (m0, m1, m2, m3) = (q[0].2 as u64, q[1].2 as u64, q[2].2 as u64, q[3].2 as u64);
        for j in 0..n {
            a[j] += m0 * get(r0[j]) + m1 * get(r1[j]) + m2 * get(r2[j]) + m3 * get(r3[j]);
        }
    }
}

struct F4<'a, E> {
    p: u64,
    md: Modulus,
    ring: &'a Ring,
    mons: Monomials,
    polys: Vec<Poly>,
    basis: Vec<u32>,
    pairs: Vec<Pair>,
    limit: Option<i128>,
    /// Whether the order is graded by the degree of the monomials, so that
    /// reduced pivot rows can be carried over.
    graded: bool,
    cache: Cache<E>,
    /// The steps traced so far, when the run is traced.
    steps: Option<Vec<Traced>>,
}

/// A run of F4 to replay modulo other primes: its monomials, the monomials
/// of the generators as they were taken, the matrix of each step reduced to
/// the rows its new polynomials needed, and the interreduction at the end.
pub(crate) struct Trace {
    mons: Monomials,
    graded: bool,
    inputs: Vec<Vec<u32>>,
    steps: Vec<Traced>,
    last: Traced,
}

/// A matrix of a traced run, reduced to the rows that its new polynomials
/// needed, and the monomials of each new polynomial (of each polynomial of
/// the basis at the end), by decreasing order.
struct Traced {
    mat: Matrix,
    new: Vec<Vec<u32>>,
}

/// What reducing a matrix gives: the new rows of the echelon form (see
/// `reduce_matrix`), which of the rows reduced gave each, the free columns,
/// the pivot row of each column, and the rows reduced.
struct Reduction {
    new: Vec<(usize, Vec<u32>)>,
    gave: Vec<usize>,
    free: Vec<u32>,
    pivot: Vec<u32>,
    rest: Vec<usize>,
}

/// The rows of `mat` that the rows `start` need: those, and the pivot rows
/// of the columns of the rows needed. The columns are those they meet, in
/// the same order.
fn needed(mat: Matrix, pivot: &[u32], start: impl Iterator<Item = usize>) -> Matrix {
    let mut need = vec![false; mat.rows.len()];
    let mut stack: Vec<usize> = start.collect();
    stack.iter().for_each(|&r| need[r] = true);
    while let Some(r) = stack.pop() {
        for &c in &mat.rows[r].0 {
            let q = pivot[c as usize];
            if q != NONE && !need[q as usize] {
                need[q as usize] = true;
                stack.push(q as usize);
            }
        }
    }
    let mut col = vec![NONE; mat.cols.len()];
    for r in (0..mat.rows.len()).filter(|&r| need[r]) {
        mat.rows[r].0.iter().for_each(|&c| col[c as usize] = 0);
    }
    let mut cols = Vec::new();
    for (c, k) in col.iter_mut().enumerate().filter(|(_, k)| **k == 0) {
        *k = cols.len() as u32;
        cols.push(mat.cols[c]);
    }
    let given = (0..mat.given).filter(|&r| need[r]).count();
    let mut rows = mat.rows;
    let mut r = 0;
    rows.retain_mut(|(cs, _)| {
        r += 1;
        cs.iter_mut().for_each(|c| *c = col[*c as usize]);
        need[r - 1]
    });
    Matrix { cols, rows, given }
}

/// The polynomial of the new row of `mat` with leading column `l` among the
/// `free` columns and entries `xs` from there.
fn new_poly(mat: &Matrix, free: &[u32], l: usize, xs: &[u32]) -> Poly {
    let (mut m, mut c) = (vec![mat.cols[free[l] as usize]], vec![1]);
    for (j, &x) in xs.iter().enumerate().skip(1) {
        if x != 0 {
            m.push(mat.cols[free[l + j] as usize]);
            c.push(x);
        }
    }
    Poly { c, m }
}

/// As `new_poly` in a replay, over the monomials `sup` the polynomial had in
/// the run traced (with zero coefficients where it has fewer terms); None if
/// it has another leading monomial or other terms.
fn traced_poly(mat: &Matrix, free: &[u32], l: usize, xs: &[u32], sup: &[u32]) -> Option<Poly> {
    if mat.cols[free[l] as usize] != sup[0] {
        return None;
    }
    let mut c = vec![0; sup.len()];
    c[0] = 1;
    let mut k = 1;
    for (j, &x) in xs.iter().enumerate().skip(1) {
        // The monomials of sup are free columns, in the same order.
        if k < sup.len() && mat.cols[free[l + j] as usize] == sup[k] {
            c[k] = x;
            k += 1;
        } else if x != 0 {
            return None;
        }
    }
    (k == sup.len()).then_some(Poly { c, m: sup.to_vec() })
}

impl<E: Entry> F4<'_, E> {
    fn cmp(&self, a: u32, b: u32) -> Ordering {
        self.ring.order.cmp(self.mons.exp(a), self.mons.exp(b))
    }

    fn lm(&self, i: u32) -> u32 {
        self.polys[i as usize].m[0]
    }

    /// `f` with its exponents, dropping zero terms.
    fn export(&self, f: &Poly) -> poly::Poly<u64> {
        let n = self.mons.n;
        let (mut c, mut e) = (Vec::with_capacity(f.c.len()), Vec::with_capacity(f.m.len() * n));
        for (&x, &m) in f.c.iter().zip(&f.m) {
            if x != 0 {
                c.push(x as u64);
                e.extend_from_slice(self.mons.exp(m));
            }
        }
        poly::Poly { c, e }
    }

    fn inv(&self, a: u64) -> u64 {
        let (mut r0, mut r1) = (self.p as i128, a as i128);
        let (mut s0, mut s1) = (0i128, 1i128);
        while r1 != 0 {
            let q = r0 / r1;
            (r0, r1) = (r1, r0 - q * r1);
            (s0, s1) = (s1, s0 - q * s1);
        }
        s0.rem_euclid(self.p as i128) as u64
    }

    /// Add `f` to the polynomials and to the basis, updating the pairs (the
    /// UPDATE procedure of Gebauer and Möller). The unit ideal is reported.
    fn add(&mut self, f: Poly) -> bool {
        let k = self.polys.len() as u32;
        let lm = f.m[0];
        self.polys.push(f);
        if self.mons.deg[lm as usize] == 0 && self.mons.exp(lm).iter().all(|&x| x == 0) {
            self.basis = vec![k];
            return true;
        }
        // The lcms of the new pairs, with their masks and whether the
        // leading monomials are coprime; only those of the pairs kept go in
        // the table.
        let n = self.mons.n;
        let len = self.basis.len();
        let (mut lcms, mut masks, mut coprime) = (Vec::with_capacity(len * n), Vec::with_capacity(len), Vec::with_capacity(len));
        let e = self.mons.exp(lm);
        for &i in &self.basis {
            let (mut mask, mut cop) = (0u64, true);
            for (v, (&x, &y)) in self.mons.exp(self.lm(i)).iter().zip(e).enumerate() {
                lcms.push(x.max(y));
                if x.max(y) > 0 {
                    mask |= 1 << (v % 64);
                }
                cop &= x == 0 || y == 0;
            }
            masks.push(mask);
            coprime.push(cop);
        }
        let divides = |b: usize, a: usize| masks[b] & !masks[a] == 0 && lcms[b * n..b * n + n].iter().zip(&lcms[a * n..a * n + n]).all(|(x, y)| x <= y);
        // Among the new pairs, drop one whose lcm is a multiple of the lcm
        // of another still in play, keeping the coprime ones until this is
        // done; then drop the coprime ones.
        let mut keep = vec![true; len];
        for a in 0..len {
            if !coprime[a] && (0..len).any(|b| b != a && keep[b] && divides(b, a)) {
                keep[a] = false;
            }
        }
        let mut new: Vec<Pair> = Vec::new();
        for a in (0..len).filter(|&a| keep[a] && !coprime[a]) {
            let l = self.mons.insert(&lcms[a * n..a * n + n]);
            if self.limit.is_none_or(|d| self.mons.deg[l as usize] as i128 <= d) {
                new.push(Pair { i: self.basis[a], j: k, lcm: l });
            }
        }
        // An old pair goes if lm divides its lcm, unless its lcm is that of
        // one of its members with the new polynomial.
        let (mons, polys) = (&self.mons, &self.polys);
        self.pairs.retain(|p| {
            if !mons.divides(lm, p.lcm) {
                return true;
            }
            let (a, b) = (polys[p.i as usize].m[0], polys[p.j as usize].m[0]);
            mons.is_lcm(a, lm, p.lcm) || mons.is_lcm(b, lm, p.lcm)
        });
        self.pairs.extend(new);
        let mons = &self.mons;
        self.basis.retain(|&i| !mons.divides(lm, polys[i as usize].m[0]));
        self.basis.push(k);
        false
    }

    /// The basis elements in the order in which they are tried as reducers:
    /// by number of terms, then as in the basis. Each with the mask of its
    /// leading monomial.
    fn reducers(&self) -> Vec<(u64, u32)> {
        let mut by: Vec<(usize, u32)> = self.basis.iter().map(|&g| (self.polys[g as usize].m.len(), g)).collect();
        by.sort_unstable();
        by.into_iter().map(|(_, g)| (self.mons.mask[self.lm(g) as usize], g)).collect()
    }

    /// A basis element whose leading monomial divides `m`: the one with the
    /// fewest terms.
    fn reducer(&self, reducers: &[(u64, u32)], m: u32) -> Option<u32> {
        let (mask, e) = (self.mons.mask[m as usize], self.mons.exp(m));
        reducers.iter().find(|&&(k, g)| k & !mask == 0 && self.mons.exp(self.lm(g)).iter().zip(e).all(|(x, y)| x <= y)).map(|&(_, g)| g)
    }

    /// The monomials of `t` times the polynomial `g`.
    fn product(&mut self, t: u32, g: u32) -> Vec<u32> {
        let len = self.polys[g as usize].m.len();
        (0..len).map(|k| self.mons.mul(t, self.polys[g as usize].m[k])).collect()
    }

    /// The matrix of the rows `(t, g)` (the polynomials g times the
    /// monomials t) of `todo` and of the multiples of basis elements that
    /// reduce every other monomial they come to contain.
    fn symbolic(&mut self, todo: &[(u32, u32)]) -> Matrix {
        // 1: seen, 2: the leading monomial of a row.
        let mut seen: Vec<u8> = Vec::new();
        let mut queue: Vec<u32> = Vec::new();
        let mut rows: Vec<(Vec<u32>, u32)> = Vec::with_capacity(todo.len());
        let visit = |seen: &mut Vec<u8>, queue: &mut Vec<u32>, ms: &[u32], len: usize| {
            seen.resize(len, 0);
            seen[ms[0] as usize] = 2;
            for &m in &ms[1..] {
                if seen[m as usize] == 0 {
                    seen[m as usize] = 1;
                    queue.push(m);
                }
            }
        };
        for &(t, g) in todo {
            let ms = self.product(t, g);
            visit(&mut seen, &mut queue, &ms, self.mons.len());
            rows.push((ms, g));
        }
        let given = rows.len();
        // The rows carried over are known; they come below the rows asked
        // for.
        let top = rows.iter().map(|r| self.mons.deg[r.0[0] as usize]).min().unwrap_or(0);
        let deg = top.min(self.cache.deg);
        let reducers = self.reducers();
        while let Some(m) = queue.pop() {
            if seen[m as usize] == 2 {
                continue;
            }
            let kept = if self.mons.deg[m as usize] < deg { self.cache.rows.get(&m).copied() } else { None };
            let (ms, g) = if let Some(k) = kept {
                (self.cache.mons[k.mons..k.mons + self.polys[k.g as usize].m.len()].to_vec(), k.g)
            } else {
                let Some(g) = self.reducer(&reducers, m) else { continue };
                let t = self.mons.quotient(m, self.lm(g));
                (self.product(t, g), g)
            };
            visit(&mut seen, &mut queue, &ms, self.mons.len());
            rows.push((ms, g));
        }
        seen.resize(self.mons.len(), 0);
        let mut cols: Vec<u32> = (0..seen.len() as u32).filter(|&m| seen[m as usize] != 0).collect();
        cols.sort_unstable_by(|&a, &b| self.cmp(b, a));
        let mut col_of = vec![NONE; self.mons.len()];
        for (k, &m) in cols.iter().enumerate() {
            col_of[m as usize] = k as u32;
        }
        for row in &mut rows {
            row.0.iter_mut().for_each(|m| *m = col_of[*m as usize]);
        }
        Matrix { cols, rows, given }
    }

    /// Reduce the rows `rows` (columns and coefficients) of `mat` by its
    /// pivot rows. Returns the free columns, those of no pivot, the reduced
    /// rows over them, densely, one after another, and the reduced pivot
    /// rows when they were all kept at once.
    ///
    /// The pivot rows are reduced first, from the last: each is then its
    /// leading term and a dense row over the free columns after it, so a
    /// row is reduced by adding multiples of these, one for each of its
    /// terms in a pivot column, with no cascade. Most of the work is in
    /// these dense additions. Without a `cache` the free columns are taken
    /// in chunks, so that the reduced pivot rows take bounded memory; with
    /// one, those it has are not reduced again.
    fn eliminate(&self, mat: &Matrix, pivot: &[u32], rows: &[(&[u32], &[u32])], cache: Option<&mut Cache<E>>) -> (Vec<u32>, Vec<u32>, Option<Reduced<E>>) {
        let width = mat.cols.len();
        let md = self.md;
        let mut before = vec![0u32; width];
        let mut free: Vec<u32> = Vec::new();
        for c in 0..width {
            before[c] = free.len() as u32;
            if pivot[c] == NONE {
                free.push(c as u32);
            }
        }
        let nf = free.len();
        let mut all = vec![0u32; rows.len() * nf];
        if nf == 0 {
            return (free, all, None);
        }
        let pivots: Vec<usize> = (0..width).rev().filter(|&c| pivot[c] != NONE).collect();
        // The reduced pivot row of column c is data from start[c], over the
        // free columns from before[c] (or the start of the chunk) on.
        let mut start = vec![NOWHERE; width];
        let mut data: Vec<E> = Vec::new();
        let whole = pivots.iter().map(|&c| nf - before[c] as usize).sum::<usize>() <= WHOLE;
        let cache = cache.filter(|_| whole);
        let whole = cache.is_some();
        if let Some(cache) = cache {
            data = self.recall(cache, mat, pivot, &free, &before, &mut start);
        }
        // Reducing the pivot rows first costs about as much as reducing
        // each row by the pivot rows as they are, in a cascade, from left
        // to right; but it is dense work, and pays off when there are many
        // rows. The first rows are reduced in the cascade to see.
        let length = |cols: &[u32]| cols.iter().filter(|&&c| pivot[c as usize] != NONE).map(|&c| (nf - before[c as usize] as usize) as u64).sum::<u64>();
        let fixed: u64 = pivots.iter().filter(|&&c| start[c] == NOWHERE).map(|&c| length(&mat.rows[pivot[c] as usize].0[1..])).sum();
        let per_row: u64 = rows.iter().map(|(cols, _)| length(cols)).sum::<u64>() / rows.len().max(1) as u64;
        let mut acc = vec![0u64; width];
        let (mut done, mut spent) = (0, 0u64);
        while done < rows.len() {
            let left = (rows.len() - done) as u64;
            if done >= 1 && spent / done as u64 * left * SCATTER > fixed + per_row * left {
                break;
            }
            let (cols, xs) = rows[done];
            spent += self.cascade(&mut acc, mat, pivot, cols, xs, &before, &mut all[done * nf..(done + 1) * nf]);
            done += 1;
        }
        let rows = &rows[done..];
        let out = &mut all[done * nf..];
        if !rows.is_empty() {
            let chunk = if whole { nf } else { (BUDGET / pivots.len().max(1)).max(64).min(nf) };
            acc.truncate(nf);
            for f0 in (0..nf).step_by(chunk) {
                let f1 = (f0 + chunk).min(nf);
                if !whole {
                    start.iter_mut().for_each(|s| *s = NOWHERE);
                    data.clear();
                }
                for &k in &pivots {
                    if start[k] != NOWHERE {
                        continue;
                    }
                    let l = (before[k] as usize).clamp(f0, f1);
                    if l < f1 {
                        let (cols, g) = &mat.rows[pivot[k] as usize];
                        let pass = Pass { p: self.p, md, batch: self.batch(), f0, f1, before: &before, pivot, start: &start, store: &data };
                        pass.add(&mut acc, &cols[1..], &self.polys[*g as usize].c[1..]);
                    }
                    start[k] = data.len();
                    data.extend(acc[l..f1].iter_mut().map(|a| E::of(md.reduce(std::mem::take(a)))));
                }
                let pass = Pass { p: self.p, md, batch: self.batch(), f0, f1, before: &before, pivot, start: &start, store: &data };
                for (i, &(cols, xs)) in rows.iter().enumerate() {
                    pass.add(&mut acc, cols, xs);
                    for (d, a) in out[i * nf + f0..i * nf + f1].iter_mut().zip(&mut acc[f0..f1]) {
                        *d = md.reduce(*a) as u32;
                        *a = 0;
                    }
                }
            }
        }
        let reduced = whole.then_some(Reduced { before, start, data });
        (free, all, reduced)
    }

    /// Take the reduced pivot rows of `mat` that `cache` has, setting where
    /// each is in `start`. They are moved to the free columns of `mat`
    /// unless those of the degrees they cover are the same as before.
    fn recall(&self, cache: &mut Cache<E>, mat: &Matrix, pivot: &[u32], free: &[u32], before: &[u32], start: &mut [usize]) -> Vec<E> {
        let nf = free.len();
        let (rows, old, mut low) = (std::mem::take(&mut cache.rows), std::mem::take(&mut cache.data), std::mem::take(&mut cache.low));
        cache.mons.clear();
        // Rows of the degree of the rows asked for or above may depend on
        // those, which are new.
        let top = mat.rows[..mat.given].iter().map(|r| self.mons.deg[mat.cols[r.0[0] as usize] as usize]).min().unwrap_or(0);
        let deg = top.min(cache.deg);
        let below = |m: u32| self.mons.deg[m as usize] < deg;
        low.retain(|&m| below(m));
        // The free columns of low degree come last.
        let nlow = free.iter().rev().take_while(|&&c| below(mat.cols[c as usize])).count();
        let same = nlow == low.len() && free[nf - nlow..].iter().zip(&low).all(|(&c, &m)| mat.cols[c as usize] == m);
        let mut at: HashMap<u32, u32> = HashMap::new();
        if !same {
            at = free[nf - nlow..].iter().map(|&c| (mat.cols[c as usize], before[c as usize])).collect();
        }
        let mut data = Vec::new();
        for (c, &m) in mat.cols.iter().enumerate() {
            let Some(&Kept { g, data: s, len, .. }) = rows.get(&m) else { continue };
            if pivot[c] == NONE || mat.rows[pivot[c] as usize].1 != g || !below(m) {
                continue;
            }
            let b = before[c] as usize;
            if same {
                debug_assert_eq!(len, nf - b);
                start[c] = s;
                continue;
            }
            let offset = data.len();
            data.resize(offset + nf - b, E::default());
            let from = &low[low.len() - len..];
            let moved = old[s..s + len].iter().zip(from).filter(|(x, _)| x.get() != 0).all(|(&x, m)| match at.get(m) {
                Some(&j) if j as usize >= b => {
                    data[offset + j as usize - b] = x;
                    true
                }
                _ => false,
            });
            if moved {
                start[c] = offset;
            } else {
                data.truncate(offset);
            }
        }
        if same { old } else { data }
    }

    /// Keep in `cache` the reduced pivot rows of `mat` of degree below
    /// `deg`, the least degree of the new polynomials: with an order graded
    /// by the degree, those rows and all they depend on are the same in the
    /// next matrix.
    fn remember(&self, cache: &mut Cache<E>, mat: &Matrix, pivot: &[u32], free: &[u32], red: Reduced<E>, deg: u64) {
        let nf = free.len();
        let low = |m: u32| self.mons.deg[m as usize] < deg;
        let nlow = free.iter().rev().take_while(|&&c| low(mat.cols[c as usize])).count();
        cache.deg = deg;
        cache.low = free[nf - nlow..].iter().map(|&c| mat.cols[c as usize]).collect();
        cache.rows.clear();
        cache.mons.clear();
        // The rows kept are moved to the front of the data, in place.
        let mut kept: Vec<usize> = (0..mat.cols.len()).filter(|&c| pivot[c] != NONE && red.start[c] != NOWHERE && low(mat.cols[c])).collect();
        kept.sort_unstable_by_key(|&c| red.start[c]);
        let mut data = red.data;
        let mut end = 0;
        for c in kept {
            let (cols, g) = &mat.rows[pivot[c] as usize];
            let (s, len) = (red.start[c], nf - red.before[c] as usize);
            data.copy_within(s..s + len, end);
            cache.rows.insert(mat.cols[c], Kept { g: *g, mons: cache.mons.len(), data: end, len });
            cache.mons.extend(cols.iter().map(|&k| mat.cols[k as usize]));
            end += len;
        }
        data.truncate(end);
        cache.data = data;
    }

    /// Reduce the row with columns `cols` and coefficients `xs` by the
    /// pivot rows of `mat` as they are, from left to right, into `out`,
    /// densely over the free columns. `acc`, as wide as the matrix, is zero
    /// and left so. Returns the number of terms subtracted.
    #[allow(clippy::too_many_arguments)]
    fn cascade(&self, acc: &mut [u64], mat: &Matrix, pivot: &[u32], cols: &[u32], xs: &[u32], before: &[u32], out: &mut [u32]) -> u64 {
        let (p, md) = (self.p, self.md);
        let Some(&first) = cols.first() else { return 0 };
        for (&c, &x) in cols.iter().zip(xs) {
            acc[c as usize] = x as u64;
        }
        // Each entry takes at most one product per row of the matrix, so
        // when these cannot add up to 2^64 no entry needs reducing early.
        let safe = (mat.rows.len() as u64) < self.batch() as u64;
        let mut spent = 0;
        for col in first as usize..acc.len() {
            if acc[col] == 0 {
                continue;
            }
            let v = md.reduce(acc[col]);
            acc[col] = 0;
            if v == 0 {
                continue;
            }
            if pivot[col] == NONE {
                out[before[col] as usize] = v as u32;
                continue;
            }
            let (cols, g) = &mat.rows[pivot[col] as usize];
            let coeffs = &self.polys[*g as usize].c;
            let m = p - v;
            spent += cols.len() as u64;
            if safe {
                for (&k, &x) in cols[1..].iter().zip(&coeffs[1..]) {
                    acc[k as usize] += m * x as u64;
                }
            } else {
                for (&k, &x) in cols[1..].iter().zip(&coeffs[1..]) {
                    let a = &mut acc[k as usize];
                    *a += m * x as u64;
                    if *a >= 1 << 63 {
                        *a = md.reduce(*a);
                    }
                }
            }
        }
        spent
    }

    fn batch(&self) -> usize {
        self.md.batch()
    }

    /// The reduced echelon form of the dense rows `rows` of width `nf`: for
    /// each row, its leading column and its entries from there on, monic;
    /// and which of the rows gave each.
    ///
    /// The rows found so far are kept reduced by each other, so a row is
    /// reduced by subtracting multiples of them, one for each of its terms
    /// in their leading columns, with no cascade, as in `eliminate`.
    fn echelon(&self, rows: &[u32], nf: usize) -> (Vec<(usize, Vec<u32>)>, Vec<usize>) {
        let (p, md) = (self.p, self.md);
        // The row with leading column l has its tail in `store` from
        // start[l], over the columns after l (which `before` gives).
        let (mut before, mut lead, mut start): (Vec<u32>, Vec<u32>, Vec<usize>) = ((0..nf as u32).collect(), vec![NONE; nf], vec![NOWHERE; nf]);
        let mut store: Vec<u32> = Vec::new();
        let (mut leads, mut gave): (Vec<usize>, Vec<usize>) = (Vec::new(), Vec::new());
        let mut acc = vec![0u64; nf];
        let (mut cols, mut xs) = (Vec::new(), Vec::new());
        for (i, row) in rows.chunks_exact(nf.max(1)).enumerate() {
            cols.clear();
            xs.clear();
            for (j, &x) in row.iter().enumerate() {
                if x != 0 {
                    cols.push(j as u32);
                    xs.push(x);
                }
            }
            let pass = Pass { p, md, batch: self.batch(), f0: 0, f1: nf, before: &before, pivot: &lead, start: &start, store: &store };
            pass.add(&mut acc, &cols, &xs);
            let Some(l) = acc.iter_mut().position(|a| {
                *a = md.reduce(*a);
                *a != 0
            }) else {
                continue;
            };
            let u = self.inv(acc[l]);
            acc[l] = 0;
            let tail: Vec<u32> = acc[l + 1..].iter_mut().map(|a| md.reduce(md.reduce(std::mem::take(a)) * u) as u32).collect();
            // Reduce the other rows by the new one.
            for &k in leads.iter().filter(|&&k| k < l) {
                let (s, w) = (start[k], nf - k - 1);
                let row = &mut store[s..s + w];
                let v = row[l - k - 1] as u64;
                if v != 0 {
                    row[l - k - 1] = 0;
                    for (x, &y) in row[l - k..].iter_mut().zip(&tail) {
                        *x = md.reduce(*x as u64 + (p - v) * y as u64) as u32;
                    }
                }
            }
            before[l] = l as u32 + 1;
            lead[l] = leads.len() as u32;
            start[l] = store.len();
            store.extend_from_slice(&tail);
            leads.push(l);
            gave.push(i);
        }
        let new = leads.into_iter().map(|l| (l, std::iter::once(1).chain(store[start[l]..start[l] + nf - l - 1].iter().copied()).collect())).collect();
        (new, gave)
    }

    /// Reduce the rows `(t, g)` of `todo` by each other and by the reducers
    /// symbolic preprocessing finds. Returns the rows of the echelon form
    /// whose leading monomials are not those of rows of the matrix: monic
    /// and reduced by each other.
    fn reduce(&mut self, todo: &[(u32, u32)]) -> Vec<Poly> {
        let mat = self.symbolic(todo);
        let red = self.reduce_matrix(&mat);
        let new: Vec<Poly> = red.new.iter().map(|(l, xs)| new_poly(&mat, &red.free, *l, xs)).collect();
        if let Some(steps) = &mut self.steps {
            let mat = needed(mat, &red.pivot, red.gave.iter().map(|&k| red.rest[k]));
            steps.push(Traced { mat, new: new.iter().map(|f| f.m.clone()).collect() });
        }
        new
    }

    /// Reduce the rows asked for of `mat` by each other and by its other
    /// rows. The new rows are those of the echelon form whose leading
    /// monomials are not those of rows of the matrix, each with its leading
    /// column among the free columns and its entries from there: monic and
    /// reduced by each other.
    fn reduce_matrix(&mut self, mat: &Matrix) -> Reduction {
        let width = mat.cols.len();
        // The pivots: the reducers, and for each leading column of the rows
        // asked for, the one with the fewest terms; the others are reduced.
        let mut pivot = vec![NONE; width];
        for (r, row) in mat.rows.iter().enumerate().skip(mat.given) {
            pivot[row.0[0] as usize] = r as u32;
        }
        let mut asked: Vec<usize> = (0..mat.given).collect();
        asked.sort_by_key(|&r| (mat.rows[r].0[0], mat.rows[r].0.len()));
        let mut rest: Vec<usize> = Vec::new();
        for r in asked {
            let c = mat.rows[r].0[0] as usize;
            if pivot[c] == NONE {
                pivot[c] = r as u32;
            } else {
                rest.push(r);
            }
        }
        let rows: Vec<(&[u32], &[u32])> = rest.iter().map(|&r| (&mat.rows[r].0[..], &self.polys[mat.rows[r].1 as usize].c[..])).collect();
        let mut cache = std::mem::take(&mut self.cache);
        let (free, reduced, red) = self.eliminate(mat, &pivot, &rows, Some(&mut cache).filter(|_| self.graded));
        let (new, gave) = self.echelon(&reduced, free.len());
        if let Some(red) = red {
            let deg = new.iter().map(|&(l, _)| self.mons.deg[mat.cols[free[l] as usize] as usize]).min().unwrap_or(u64::MAX);
            self.remember(&mut cache, mat, &pivot, &free, red, deg);
        }
        self.cache = cache;
        Reduction { new, gave, free, pivot, rest }
    }

    /// The basis after the last step: minimal, reduced and sorted by
    /// decreasing leading monomial.
    fn reduced_basis(&mut self) -> Vec<Poly> {
        self.cache = Cache::default();
        let basis = std::mem::take(&mut self.basis);
        let minimal: Vec<u32> = basis.iter().copied().filter(|&k| !basis.iter().any(|&j| j != k && self.mons.divides(self.lm(j), self.lm(k)))).collect();
        self.basis = minimal.clone();
        // The rows (1, g) are all pivots, one per leading column; reducing
        // the tail of each by all rows gives the reduced basis.
        let one = self.mons.insert(&vec![0; self.ring.n]);
        let todo: Vec<(u32, u32)> = minimal.iter().map(|&g| (one, g)).collect();
        let mat = self.symbolic(&todo);
        let mut pivot = vec![NONE; mat.cols.len()];
        for (r, row) in mat.rows.iter().enumerate() {
            pivot[row.0[0] as usize] = r as u32;
        }
        let out = self.interreduce(&mat, &pivot, None).expect("no trace");
        if let Some(steps) = &mut self.steps {
            let given = mat.given;
            steps.push(Traced { mat: needed(mat, &pivot, 0..given), new: out.iter().map(|f| f.m.clone()).collect() });
        }
        self.sorted(out)
    }

    /// The rows asked for of `mat`, all pivots, with their tails reduced by
    /// all rows. In a replay, `sups` are the monomials of the polynomials in
    /// the run traced, and None comes when one has others.
    fn interreduce(&self, mat: &Matrix, pivot: &[u32], sups: Option<&[Vec<u32>]>) -> Option<Vec<Poly>> {
        let tails: Vec<(&[u32], &[u32])> = mat.rows[..mat.given].iter().map(|(cols, g)| (&cols[1..], &self.polys[*g as usize].c[1..])).collect();
        let (free, reduced, _) = self.eliminate(mat, pivot, &tails, None);
        let nf = free.len();
        let mut out: Vec<Poly> = Vec::with_capacity(mat.given);
        for (i, (cols, _)) in mat.rows[..mat.given].iter().enumerate() {
            let (mut m, mut c) = (vec![mat.cols[cols[0] as usize]], vec![1]);
            for (j, &x) in reduced[i * nf..(i + 1) * nf].iter().enumerate() {
                if x != 0 {
                    m.push(mat.cols[free[j] as usize]);
                    c.push(x);
                }
            }
            // The terms are among those of the polynomial traced, in order.
            if let Some(sup) = sups.map(|s| &s[i]) {
                let mut k = 0;
                if !m.iter().all(|x| sup[k..].iter().position(|y| y == x).map(|j| k += j + 1).is_some()) {
                    return None;
                }
            }
            out.push(Poly { c, m });
        }
        Some(out)
    }

    /// The polynomials `out`, by decreasing leading monomial.
    fn sorted(&self, mut out: Vec<Poly>) -> Vec<Poly> {
        out.sort_by(|a, b| self.cmp(b.m[0], a.m[0]));
        out
    }
}

/// The reduced Gröbner basis of the ideal generated by `gens` over GF(p),
/// p < 2^31, by F4. The pairs are taken by the degree of their lcm with the
/// weights `weights`; with a `limit`, those beyond it are ignored, which
/// gives a truncated basis. The generators are taken as they are, in the
/// order given, as Magma does.
pub fn groebner(field: &Zp, ring: &Ring, gens: Vec<poly::Poly<u64>>, weights: &[u64], limit: Option<i128>) -> Vec<poly::Poly<u64>> {
    debug_assert!(field.modulus() < 1 << 31);
    if field.modulus() < 1 << 16 {
        run::<u16>(field, ring, gens, weights, limit, false).0
    } else {
        run::<u32>(field, ring, gens, weights, limit, false).0
    }
}

/// As `groebner` (with no limit), with a trace of the run to replay modulo
/// other primes; none for the unit ideal.
pub(crate) fn learn(field: &Zp, ring: &Ring, gens: Vec<poly::Poly<u64>>, weights: &[u64]) -> Run {
    debug_assert!(field.modulus() < 1 << 31);
    if field.modulus() < 1 << 16 {
        run::<u16>(field, ring, gens, weights, None, true)
    } else {
        run::<u32>(field, ring, gens, weights, None, true)
    }
}

/// The reduced Gröbner basis over GF(p) of the ideal generated by `gens`,
/// by replaying `trace`, a run modulo another prime with generators of the
/// same monomials; None if the run goes otherwise modulo p: a leading
/// coefficient vanishes, or a polynomial has terms that it had not. Rows
/// that reduced to zero in the run traced are left out, so a prime unlucky
/// for the trace can give a basis that is not the reduced basis modulo p.
pub(crate) fn replay(trace: &Trace, field: &Zp, ring: &Ring, gens: &[poly::Poly<u64>]) -> Option<Vec<poly::Poly<u64>>> {
    debug_assert!(field.modulus() < 1 << 31);
    if field.modulus() < 1 << 16 { replay_in::<u16>(trace, field, ring, gens) } else { replay_in::<u32>(trace, field, ring, gens) }
}

fn replay_in<E: Entry>(trace: &Trace, field: &Zp, ring: &Ring, gens: &[poly::Poly<u64>]) -> Option<Vec<poly::Poly<u64>>> {
    let (n, p) = (ring.n, field.modulus());
    let mons = trace.mons.clone();
    let (polys, basis, pairs) = (Vec::new(), Vec::new(), Vec::new());
    let graded = trace.graded;
    let mut f4: F4<E> = F4 { p, md: Modulus::new(p), ring, mons, polys, basis, pairs, limit: None, graded, cache: Cache::default(), steps: None };
    let gens: Vec<&poly::Poly<u64>> = gens.iter().filter(|g| !g.is_zero()).collect();
    if gens.len() != trace.inputs.len() {
        return None;
    }
    for (g, sup) in gens.into_iter().zip(&trace.inputs) {
        let mut g = g.clone();
        g.make_monic(field);
        // The terms are among those the generator had, in order.
        let mut c = vec![0; sup.len()];
        let mut k = 0;
        for i in 0..g.len() {
            let m = f4.mons.lookup(g.exp(i, n))?;
            k += sup[k..].iter().position(|&x| x == m)?;
            c[k] = g.c[i] as u32;
            k += 1;
        }
        if c[0] != 1 {
            return None;
        }
        f4.polys.push(Poly { c, m: sup.clone() });
    }
    for step in &trace.steps {
        let red = f4.reduce_matrix(&step.mat);
        if red.new.len() != step.new.len() {
            return None;
        }
        for ((l, xs), sup) in red.new.iter().zip(&step.new) {
            let f = traced_poly(&step.mat, &red.free, *l, xs, sup)?;
            f4.polys.push(f);
        }
    }
    f4.cache = Cache::default();
    let mat = &trace.last.mat;
    let mut pivot = vec![NONE; mat.cols.len()];
    for (r, row) in mat.rows.iter().enumerate() {
        pivot[row.0[0] as usize] = r as u32;
    }
    let out = f4.interreduce(mat, &pivot, Some(&trace.last.new))?;
    Some(f4.sorted(out).into_iter().map(|f| f4.export(&f)).collect())
}

/// A basis and, when asked to `record`, the trace of the run.
type Run = (Vec<poly::Poly<u64>>, Option<Trace>);

fn run<E: Entry>(field: &Zp, ring: &Ring, gens: Vec<poly::Poly<u64>>, weights: &[u64], limit: Option<i128>, record: bool) -> Run {
    let (n, p) = (ring.n, field.modulus());
    let graded = match &ring.order {
        Order::GRevLex | Order::GLex => weights.iter().all(|&w| w == 1),
        Order::GRevLexW(w) => w[..] == weights[..],
        _ => false,
    };
    let mons = Monomials::new(n, weights);
    let (polys, basis, pairs) = (Vec::new(), Vec::new(), Vec::new());
    let steps = record.then(Vec::new);
    let mut f4: F4<E> = F4 { p, md: Modulus::new(p), ring, mons, polys, basis, pairs, limit, graded, cache: Cache::default(), steps };
    let one = || (vec![poly::Poly { c: vec![1], e: vec![0; n] }], None);
    for mut g in gens.into_iter().filter(|g| !g.is_zero()) {
        g.make_monic(field);
        let m = (0..g.len()).map(|i| f4.mons.insert(g.exp(i, n))).collect();
        if f4.add(Poly { c: g.c.iter().map(|&x| x as u32).collect(), m }) {
            return one();
        }
    }
    let inputs: Vec<Vec<u32>> = f4.polys.iter().map(|f| f.m.clone()).collect();
    while !f4.pairs.is_empty() {
        // The pairs of least degree.
        let d = f4.pairs.iter().map(|q| f4.mons.deg[q.lcm as usize]).min().unwrap();
        let (sel, rest): (Vec<Pair>, Vec<Pair>) = std::mem::take(&mut f4.pairs).into_iter().partition(|q| f4.mons.deg[q.lcm as usize] == d);
        f4.pairs = rest;
        let mut todo: Vec<(u32, u32)> = Vec::with_capacity(2 * sel.len());
        for q in &sel {
            for g in [q.i, q.j] {
                let t = f4.mons.quotient(q.lcm, f4.lm(g));
                todo.push((t, g));
            }
        }
        todo.sort_unstable();
        todo.dedup();
        for f in f4.reduce(&todo) {
            if f4.add(f) {
                return one();
            }
        }
    }
    let basis: Vec<poly::Poly<u64>> = f4.reduced_basis().iter().map(|f| f4.export(f)).collect();
    let trace = f4.steps.take().map(|mut steps| {
        let last = steps.pop().expect("the interreduction");
        Trace { mons: f4.mons, graded, inputs, steps, last }
    });
    (basis, trace)
}
