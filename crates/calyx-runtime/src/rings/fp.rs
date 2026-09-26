//! Linear algebra over prime fields, for the maps between finite fields:
//! embeddings, restrictions to subfields and changes of basis.
//!
//! Elements of finite fields are handled through their coordinates in the
//! power basis of the FLINT generator. Word-sized characteristics use
//! `u64` arithmetic; larger ones fall back to `Integer`s.

use std::rc::Rc;

use calyx_flint::gr::{Ctx, CtxKind, Elem};
use calyx_flint::{Integer, Nmod};

/// Arithmetic in `F_p` on some representation of its elements.
trait Arith {
    type E: Clone + PartialEq;
    fn zero(&self) -> Self::E;
    fn one(&self) -> Self::E;
    fn is_zero(&self, a: &Self::E) -> bool;
    fn add(&self, a: &Self::E, b: &Self::E) -> Self::E;
    fn sub(&self, a: &Self::E, b: &Self::E) -> Self::E;
    fn mul(&self, a: &Self::E, b: &Self::E) -> Self::E;
    fn inv(&self, a: &Self::E) -> Self::E;
}

impl Arith for Nmod {
    type E = u64;
    fn zero(&self) -> u64 {
        0
    }
    fn one(&self) -> u64 {
        1
    }
    fn is_zero(&self, a: &u64) -> bool {
        *a == 0
    }
    fn add(&self, a: &u64, b: &u64) -> u64 {
        Nmod::add(*self, *a, *b)
    }
    fn sub(&self, a: &u64, b: &u64) -> u64 {
        Nmod::sub(*self, *a, *b)
    }
    fn mul(&self, a: &u64, b: &u64) -> u64 {
        Nmod::mul(*self, *a, *b)
    }
    fn inv(&self, a: &u64) -> u64 {
        Nmod::inv(*self, *a).expect("inverse of zero in F_p")
    }
}

/// `F_p` for a prime beyond a word.
#[derive(Clone)]
pub struct Big(Integer);

impl Big {
    fn red(&self, a: Integer) -> Integer {
        a.div_rem_euclid(&self.0).unwrap().1
    }
}

impl Arith for Big {
    type E = Integer;
    fn zero(&self) -> Integer {
        Integer::zero()
    }
    fn one(&self) -> Integer {
        Integer::one()
    }
    fn is_zero(&self, a: &Integer) -> bool {
        a.is_zero()
    }
    fn add(&self, a: &Integer, b: &Integer) -> Integer {
        self.red(a + b)
    }
    fn sub(&self, a: &Integer, b: &Integer) -> Integer {
        self.red(a - b)
    }
    fn mul(&self, a: &Integer, b: &Integer) -> Integer {
        self.red(a * b)
    }
    fn inv(&self, a: &Integer) -> Integer {
        a.invmod(&self.0).expect("inverse of zero in F_p")
    }
}

/// A dense matrix, stored by rows.
#[derive(Clone)]
pub struct Dense<E> {
    rows: usize,
    cols: usize,
    a: Vec<E>,
}

impl<E: Clone + PartialEq> Dense<E> {
    fn from_columns(cols: &[Vec<E>], rows: usize, zero: E) -> Dense<E> {
        let mut a = vec![zero; rows * cols.len()];
        for (j, c) in cols.iter().enumerate() {
            for (i, x) in c.iter().enumerate().take(rows) {
                a[i * cols.len() + j] = x.clone();
            }
        }
        Dense { rows, cols: cols.len(), a }
    }

    fn mul_vec<A: Arith<E = E>>(&self, f: &A, v: &[E]) -> Vec<E> {
        (0..self.rows)
            .map(|i| {
                let row = &self.a[i * self.cols..(i + 1) * self.cols];
                let mut s = f.zero();
                for (x, y) in row.iter().zip(v) {
                    if !f.is_zero(x) && !f.is_zero(y) {
                        s = f.add(&s, &f.mul(x, y));
                    }
                }
                s
            })
            .collect()
    }

    /// The inverse of a square matrix.
    fn inverse<A: Arith<E = E>>(&self, f: &A) -> Option<Dense<E>> {
        let n = self.rows;
        let w = 2 * n;
        let mut m = vec![f.zero(); n * w];
        for i in 0..n {
            m[i * w..i * w + n].clone_from_slice(&self.a[i * n..(i + 1) * n]);
            m[i * w + n + i] = f.one();
        }
        for c in 0..n {
            let r = (c..n).find(|&r| !f.is_zero(&m[r * w + c]))?;
            if r != c {
                for k in 0..w {
                    m.swap(r * w + k, c * w + k);
                }
            }
            let inv = f.inv(&m[c * w + c]);
            for k in c..w {
                m[c * w + k] = f.mul(&m[c * w + k], &inv);
            }
            for r in 0..n {
                if r == c || f.is_zero(&m[r * w + c]) {
                    continue;
                }
                let t = m[r * w + c].clone();
                for k in c..w {
                    if !f.is_zero(&m[c * w + k]) {
                        m[r * w + k] = f.sub(&m[r * w + k], &f.mul(&t, &m[c * w + k]));
                    }
                }
            }
        }
        let a = (0..n).flat_map(|i| m[i * w + n..(i + 1) * w].to_vec()).collect();
        Some(Dense { rows: n, cols: n, a })
    }

    /// A solution of `M x = b` whose free variables are zero, pivoting on
    /// the first columns possible, if there is one.
    fn solve<A: Arith<E = E>>(&self, f: &A, b: &[E]) -> Option<Vec<E>> {
        let (n, d) = (self.rows, self.cols);
        let w = d + 1;
        let mut m = Vec::with_capacity(n * w);
        for (i, bi) in b.iter().enumerate().take(n) {
            m.extend_from_slice(&self.a[i * d..(i + 1) * d]);
            m.push(bi.clone());
        }
        let mut pivots = Vec::new();
        for c in 0..d {
            let row = pivots.len();
            if row == n {
                break;
            }
            let Some(r) = (row..n).find(|&r| !f.is_zero(&m[r * w + c])) else { continue };
            if r != row {
                for k in 0..w {
                    m.swap(r * w + k, row * w + k);
                }
            }
            let inv = f.inv(&m[row * w + c]);
            for k in c..w {
                m[row * w + k] = f.mul(&m[row * w + k], &inv);
            }
            for r in 0..n {
                if r == row || f.is_zero(&m[r * w + c]) {
                    continue;
                }
                let t = m[r * w + c].clone();
                for k in c..w {
                    if !f.is_zero(&m[row * w + k]) {
                        m[r * w + k] = f.sub(&m[r * w + k], &f.mul(&t, &m[row * w + k]));
                    }
                }
            }
            pivots.push(c);
        }
        if (pivots.len()..n).any(|r| !f.is_zero(&m[r * w + d])) {
            return None;
        }
        let mut x = vec![f.zero(); d];
        for (i, &c) in pivots.iter().enumerate() {
            x[c] = m[i * w + d].clone();
        }
        Some(x)
    }

    /// For a matrix of full column rank, a left inverse `L` (`L M = 1`) that
    /// reads only `cols` of the rows.
    fn left_inverse<A: Arith<E = E>>(&self, f: &A) -> Option<Dense<E>> {
        let (n, d) = (self.rows, self.cols);
        // Choose independent rows greedily by elimination on the rows.
        let mut basis: Vec<(usize, Vec<E>)> = Vec::new();
        let mut chosen = Vec::new();
        for i in 0..n {
            if chosen.len() == d {
                break;
            }
            let mut r = self.a[i * d..(i + 1) * d].to_vec();
            for (c, b) in &basis {
                if !f.is_zero(&r[*c]) {
                    let t = r[*c].clone();
                    for k in 0..d {
                        r[k] = f.sub(&r[k], &f.mul(&t, &b[k]));
                    }
                }
            }
            if let Some(c) = (0..d).find(|&c| !f.is_zero(&r[c])) {
                let inv = f.inv(&r[c]);
                for x in r.iter_mut() {
                    *x = f.mul(x, &inv);
                }
                basis.push((c, r));
                chosen.push(i);
            }
        }
        if chosen.len() < d {
            return None;
        }
        let sub = Dense { rows: d, cols: d, a: chosen.iter().flat_map(|&i| self.a[i * d..(i + 1) * d].to_vec()).collect() };
        let s = sub.inverse(f)?;
        let mut a = vec![f.zero(); d * n];
        for r in 0..d {
            for (k, &i) in chosen.iter().enumerate() {
                a[r * n + i] = s.a[r * d + k].clone();
            }
        }
        Some(Dense { rows: d, cols: n, a })
    }
}

/// Coordinates over `F_p`.
#[derive(Clone, Debug, PartialEq)]
pub enum Coords {
    W(Vec<u64>),
    B(Vec<Integer>),
}

impl Coords {
    /// The coordinates of a finite field element in the power basis of the
    /// FLINT generator (the residue of a prime field element).
    pub fn of(x: &Elem) -> Coords {
        match x.ctx().kind() {
            CtxKind::Nmod(_) | CtxKind::FqZech { .. } | CtxKind::FqNmod { .. } => Coords::W(x.fq_coords_u64()),
            CtxKind::FmpzMod(_) => Coords::B(vec![x.to_integer().unwrap_or_default()]),
            _ => Coords::B(x.fq_coords()),
        }
    }

    /// The zero vector of length `n` over the prime of `ctx`.
    pub fn zero(ctx: &Ctx, n: usize) -> Coords {
        match ctx.kind() {
            CtxKind::Nmod(_) | CtxKind::FqZech { .. } | CtxKind::FqNmod { .. } => Coords::W(vec![0; n]),
            _ => Coords::B(vec![Integer::zero(); n]),
        }
    }

    pub fn len(&self) -> usize {
        match self {
            Coords::W(v) => v.len(),
            Coords::B(v) => v.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn is_zero(&self) -> bool {
        match self {
            Coords::W(v) => v.iter().all(|&c| c == 0),
            Coords::B(v) => v.iter().all(Integer::is_zero),
        }
    }

    /// The element of a field (or prime field) with these coordinates.
    pub fn to_elem(&self, ctx: &Rc<Ctx>) -> Elem {
        match (self, ctx.kind()) {
            (Coords::W(v), CtxKind::Nmod(_)) => Elem::from_word(ctx, v.first().copied().unwrap_or(0)),
            (Coords::W(v), _) => Elem::fq_from_coords_u64(ctx, v),
            (Coords::B(v), CtxKind::Nmod(_) | CtxKind::FmpzMod(_)) => {
                Elem::from_integer(ctx, v.first().unwrap_or(&Integer::zero())).expect("a prime field element")
            }
            (Coords::B(v), _) => Elem::fq_from_coords(ctx, v).expect("a finite field element"),
        }
    }

    /// Coordinates `[i*d, (i+1)*d)`.
    pub fn chunk(&self, i: usize, d: usize) -> Coords {
        match self {
            Coords::W(v) => Coords::W(v[i * d..(i + 1) * d].to_vec()),
            Coords::B(v) => Coords::B(v[i * d..(i + 1) * d].to_vec()),
        }
    }

    /// The concatenation of coordinate vectors.
    pub fn concat(parts: &[Coords]) -> Coords {
        match parts.first() {
            Some(Coords::B(_)) => Coords::B(parts.iter().flat_map(|c| c.integers()).collect()),
            _ => Coords::W(parts.iter().flat_map(|c| if let Coords::W(v) = c { v.clone() } else { Vec::new() }).collect()),
        }
    }

    pub fn integers(&self) -> Vec<Integer> {
        match self {
            Coords::W(v) => v.iter().map(|&c| Integer::from_u64(c)).collect(),
            Coords::B(v) => v.clone(),
        }
    }
}

/// A linear map between coordinate spaces over `F_p`.
#[derive(Clone)]
pub enum LinMap {
    W(Nmod, Dense<u64>),
    B(Big, Dense<Integer>),
}

impl LinMap {
    /// The matrix with the given columns (all of length `rows`).
    pub fn from_columns(p: &Integer, cols: &[Coords], rows: usize) -> LinMap {
        match p.to_u64() {
            Some(pw) => {
                let words = |c: &Coords| match c {
                    Coords::W(v) => v.clone(),
                    Coords::B(_) => c.integers().iter().map(|x| x.mod_u64(pw)).collect(),
                };
                let cs: Vec<Vec<u64>> = cols.iter().map(words).collect();
                LinMap::W(Nmod::new(pw), Dense::from_columns(&cs, rows, 0))
            }
            None => LinMap::B(Big(p.clone()), Dense::from_columns(&cols.iter().map(Coords::integers).collect::<Vec<_>>(), rows, Integer::zero())),
        }
    }

    pub fn apply(&self, v: &Coords) -> Coords {
        match (self, v) {
            (LinMap::W(f, m), Coords::W(x)) => Coords::W(m.mul_vec(f, x)),
            (LinMap::B(f, m), _) => Coords::B(m.mul_vec(f, &v.integers())),
            (LinMap::W(f, m), Coords::B(x)) => Coords::W(m.mul_vec(f, &x.iter().map(|c| c.mod_u64(f.modulus())).collect::<Vec<_>>())),
        }
    }

    pub fn inverse(&self) -> Option<LinMap> {
        match self {
            LinMap::W(f, m) => Some(LinMap::W(*f, m.inverse(f)?)),
            LinMap::B(f, m) => Some(LinMap::B(f.clone(), m.inverse(f)?)),
        }
    }

    /// A solution of `M x = b` whose free variables are zero, pivoting on
    /// the first columns possible (so the least solution counting
    /// coordinates from the last), if there is one.
    pub fn solve(&self, b: &Coords) -> Option<Coords> {
        match self {
            LinMap::W(f, m) => {
                let v: Vec<u64> = b.integers().iter().map(|c| c.mod_u64(f.modulus())).collect();
                Some(Coords::W(m.solve(f, &v)?))
            }
            LinMap::B(f, m) => Some(Coords::B(m.solve(f, &b.integers())?)),
        }
    }

    /// A left inverse of an injective map.
    pub fn left_inverse(&self) -> Option<LinMap> {
        match self {
            LinMap::W(f, m) => Some(LinMap::W(*f, m.left_inverse(f)?)),
            LinMap::B(f, m) => Some(LinMap::B(f.clone(), m.left_inverse(f)?)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inverse_and_left_inverse() {
        let p = Integer::from_u64(7);
        let cols = [Coords::W(vec![1, 2, 0]), Coords::W(vec![0, 1, 3]), Coords::W(vec![5, 0, 1])];
        let m = LinMap::from_columns(&p, &cols, 3);
        let inv = m.inverse().unwrap();
        let v = Coords::W(vec![3, 4, 5]);
        assert_eq!(m.apply(&inv.apply(&v)), v);
        // An injective 3x2 map.
        let e = LinMap::from_columns(&p, &cols[..2], 3);
        let l = e.left_inverse().unwrap();
        let x = Coords::W(vec![6, 2]);
        assert_eq!(l.apply(&e.apply(&x)), x);
        // The same over a large prime.
        let q = Integer::from_i64(2).pow(89) - Integer::one();
        let m = LinMap::from_columns(&q, &cols, 3);
        let v = Coords::B(vec![Integer::from_u64(3), Integer::from_u64(4), Integer::from_u64(5)]);
        assert_eq!(m.apply(&m.inverse().unwrap().apply(&v)), v);
    }

    fn int(n: u64) -> Integer {
        Integer::from_u64(n)
    }

    #[test]
    fn solve_singular_systems() {
        let p = Integer::from_u64(5);
        // The first column is zero and the third twice the second: both free.
        let cols = [Coords::W(vec![0, 0]), Coords::W(vec![1, 2]), Coords::W(vec![2, 4])];
        let m = LinMap::from_columns(&p, &cols, 2);
        let b = Coords::W(vec![3, 1]);
        assert_eq!(m.solve(&b), Some(Coords::W(vec![0, 3, 0])));
        assert_eq!(m.solve(&Coords::W(vec![1, 1])), None);
        let q = Integer::from_i64(2).pow(89) - Integer::one();
        let m = LinMap::from_columns(&q, &cols, 2);
        let b = Coords::B(vec![int(3), int(6)]);
        assert_eq!(m.solve(&b), Some(Coords::B(vec![int(0), int(3), int(0)])));
    }
}
