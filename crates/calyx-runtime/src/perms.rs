//! Permutations and the symmetric groups `Sym(n)` they belong to.
//!
//! A permutation acts on `{1, ..., n}` on the right: `i^(p*q) = (i^p)^q`.
//! There is one `Sym(n)` per degree, as in Magma, so a group named by an
//! assignment prints with that name wherever it turns up (`Id(G)`).

use std::rc::Rc;

use calyx_flint::Integer;
use rustc_hash::FxHashMap;

use calyx_syntax::ast::BinOp;

use crate::error::{RResult, RuntimeError};
use crate::interp::Interp;
use crate::value::{Struct, StructKind, Value};

/// A permutation of `{1, ..., n}`, an element of `Sym(n)`.
pub struct Perm {
    /// The group `Sym(n)`.
    pub group: Rc<Struct>,
    /// The images of `1, ..., n`, each less one.
    pub images: Box<[u32]>,
}

impl Perm {
    pub fn degree(&self) -> usize {
        self.images.len()
    }

    pub fn is_identity(&self) -> bool {
        self.images.iter().enumerate().all(|(i, &x)| x as usize == i)
    }

    fn with(&self, images: Vec<u32>) -> Perm {
        Perm { group: self.group.clone(), images: images.into_boxed_slice() }
    }

    /// `self * other`: first `self`, then `other`.
    pub fn mul(&self, other: &Perm) -> Perm {
        self.with(self.images.iter().map(|&x| other.images[x as usize]).collect())
    }

    pub fn inverse(&self) -> Perm {
        let mut inv = vec![0u32; self.degree()];
        for (i, &x) in self.images.iter().enumerate() {
            inv[x as usize] = i as u32;
        }
        self.with(inv)
    }

    /// `self^e` for any integer `e`, moving each cycle along by `e`.
    pub fn pow(&self, e: &Integer) -> Perm {
        let mut images = vec![0u32; self.degree()];
        for c in self.cycles() {
            let len = Integer::from_u64(c.len() as u64);
            let k = e.div_rem_euclid(&len).map(|(_, r)| r.to_u64().unwrap_or(0) as usize).unwrap_or(0);
            for (j, &x) in c.iter().enumerate() {
                images[x as usize] = c[(j + k) % c.len()];
            }
        }
        self.with(images)
    }

    /// `other^-1 * self * other`
    pub fn conjugate(&self, other: &Perm) -> Perm {
        other.inverse().mul(self).mul(other)
    }

    /// All cycles, fixed points included, each starting at its smallest
    /// point, ordered by that point (points less one).
    pub fn cycles(&self) -> Vec<Vec<u32>> {
        let mut seen = vec![false; self.degree()];
        let mut out = Vec::new();
        for i in 0..self.degree() {
            if seen[i] {
                continue;
            }
            let mut c = vec![i as u32];
            seen[i] = true;
            let mut j = self.images[i] as usize;
            while j != i {
                seen[j] = true;
                c.push(j as u32);
                j = self.images[j] as usize;
            }
            out.push(c);
        }
        out
    }

    pub fn order(&self) -> Integer {
        let mut o = Integer::one();
        for c in self.cycles() {
            o = o.lcm(&Integer::from_u64(c.len() as u64));
        }
        o
    }

    /// 1 for even permutations, -1 for odd ones.
    pub fn sign(&self) -> i64 {
        let transpositions: usize = self.cycles().iter().map(|c| c.len() - 1).sum();
        if transpositions % 2 == 0 { 1 } else { -1 }
    }

    /// Cycle notation, `(1, 2, 3)(4, 5)`; `None` for the identity.
    pub fn cycle_notation(&self) -> Option<String> {
        let mut s = String::new();
        for c in self.cycles().iter().filter(|c| c.len() > 1) {
            s.push('(');
            for (k, x) in c.iter().enumerate() {
                if k > 0 {
                    s.push_str(", ");
                }
                s.push_str(&(x + 1).to_string());
            }
            s.push(')');
        }
        if s.is_empty() { None } else { Some(s) }
    }
}

/// The degree `n` of `Sym(n)`.
pub fn sym_degree(s: &Struct) -> Option<usize> {
    match s.kind {
        StructKind::SymGroup(n) => Some(n as usize),
        _ => None,
    }
}

/// `n!` as Magma prints a group order's factorisation: `2^3 * 3 * 5`
/// (just the number for 1 and for primes).
pub fn factorial_factorization(n: usize) -> String {
    let mut sieve = vec![true; n + 1];
    let mut parts = Vec::new();
    for p in 2..=n {
        if !sieve[p] {
            continue;
        }
        for m in (p * p..=n).step_by(p) {
            sieve[m] = false;
        }
        let (mut e, mut q) = (0, n);
        while q > 0 {
            q /= p;
            e += q;
        }
        parts.push(if e == 1 { p.to_string() } else { format!("{p}^{e}") });
    }
    if parts.is_empty() { "1".to_string() } else { parts.join(" * ") }
}

#[derive(Default)]
pub struct GroupCache {
    sym: FxHashMap<usize, Rc<Struct>>,
}

impl Interp {
    /// The symmetric group of degree `n ≥ 1`.
    pub fn sym_group(&mut self, n: usize) -> Rc<Struct> {
        self.groups.sym.entry(n).or_insert_with(|| Struct::new(StructKind::SymGroup(n as u32))).clone()
    }

    /// The permutation of degree `n` with the given images (less one).
    pub fn perm(&mut self, images: Vec<u32>) -> Value {
        let group = self.sym_group(images.len().max(1));
        let images = if images.is_empty() { vec![0] } else { images };
        Value::Perm(Rc::new(Perm { group, images: images.into_boxed_slice() }))
    }

    pub fn perm_identity(&mut self, n: usize) -> Value {
        self.perm((0..n as u32).collect())
    }

    /// Operators with a permutation operand; `None` if there is no rule.
    pub fn perm_binop(&mut self, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
        let err = |msg: &str| Err(RuntimeError::runtime(msg).in_context(op.intrinsic_name()));
        let incompatible = "Arguments are not compatible\nArgument types given: GrpPermElt, GrpPermElt";
        Ok(Some(match (op, a, b) {
            (BinOp::Mul, Value::Perm(x), Value::Perm(y)) => {
                if x.degree() != y.degree() {
                    return err(incompatible);
                }
                Value::Perm(Rc::new(x.mul(y)))
            }
            (BinOp::Pow, Value::Perm(x), Value::Int(e)) => Value::Perm(Rc::new(x.pow(e))),
            (BinOp::Pow, Value::Perm(x), Value::Perm(y)) => {
                if x.degree() != y.degree() {
                    return err(incompatible);
                }
                Value::Perm(Rc::new(x.conjugate(y)))
            }
            // The image of a point.
            (BinOp::Pow, Value::Int(i), Value::Perm(x)) => match i.to_u64() {
                Some(k) if k >= 1 && k as usize <= x.degree() => Value::Int(Integer::from_u64(x.images[k as usize - 1] as u64 + 1)),
                _ => return err("Cannot apply permutation to this object"),
            },
            (BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge, Value::Perm(_), Value::Perm(_)) => return err("No comparison algorithm exists for given objects"),
            _ => return Ok(None),
        }))
    }

    /// `Sym(n) ! x`: from 1, a sequence of images, or a permutation of the
    /// same degree.
    pub fn coerce_into_sym(&mut self, n: usize, x: &Value) -> RResult<Result<Value, Option<String>>> {
        Ok(match x {
            Value::Int(i) if i.is_one() => Ok(self.perm_identity(n)),
            Value::Seq(s) => match images_from_seq(&s.elems, n) {
                Some(images) => Ok(self.perm(images)),
                None => Err(None),
            },
            Value::Perm(p) if p.degree() == n => Ok(x.clone()),
            Value::Perm(_) => Err(Some("Could not find a covering group".into())),
            _ => Err(None),
        })
    }

    /// The i-th generator of `Sym(n)`: `(1, 2, ..., n)` and `(1, 2)`.
    pub fn sym_generator(&mut self, n: usize, i: usize) -> Value {
        let images: Vec<u32> = match (n, i) {
            (2, 1) | (_, 2) => (0..n as u32).map(|x| if x < 2 { 1 - x } else { x }).collect(),
            _ => (0..n as u32).map(|x| (x + 1) % n as u32).collect(),
        };
        self.perm(images)
    }
}

/// The images (less one) of the sequence `s` if it is a permutation of
/// `1, ..., n`.
pub fn images_from_seq(s: &[Value], n: usize) -> Option<Vec<u32>> {
    if s.len() != n {
        return None;
    }
    let mut seen = vec![false; n];
    let mut images = Vec::with_capacity(n);
    for v in s {
        let Value::Int(x) = v else { return None };
        let x = x.to_u64()? as usize;
        if x == 0 || x > n || seen[x - 1] {
            return None;
        }
        seen[x - 1] = true;
        images.push((x - 1) as u32);
    }
    Some(images)
}
