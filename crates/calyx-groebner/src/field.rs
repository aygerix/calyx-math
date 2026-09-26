//! Coefficient fields.
//!
//! The algorithms are generic over a `Field`, whose elements are plain
//! values for word-sized primes and FLINT's generic elements otherwise.
//! Elements cross to and from calyx as `Elem`s of the field's gr context.

use std::cmp::Ordering;
use std::fmt::Debug;
use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{Ctx, CtxKind, Elem, Truth};

pub trait Field {
    type E: Clone + Debug;
    fn zero(&self) -> Self::E;
    fn one(&self) -> Self::E;
    fn is_zero(&self, a: &Self::E) -> bool;
    fn is_one(&self, a: &Self::E) -> bool;
    fn neg(&self, a: &Self::E) -> Self::E;
    fn add(&self, a: &Self::E, b: &Self::E) -> Self::E;
    fn sub(&self, a: &Self::E, b: &Self::E) -> Self::E;
    fn mul(&self, a: &Self::E, b: &Self::E) -> Self::E;
    /// The inverse of a non-zero element.
    fn inv(&self, a: &Self::E) -> Self::E;
    /// `a - b c`.
    fn sub_mul(&self, a: &Self::E, b: &Self::E, c: &Self::E) -> Self::E {
        self.sub(a, &self.mul(b, c))
    }
    fn from_elem(&self, x: &Elem) -> Self::E;
    fn to_elem(&self, x: &Self::E) -> Elem;
    /// The order in which Magma sorts coefficients where it breaks ties:
    /// numerically for the rationals and the residues mod p.
    fn cmp(&self, a: &Self::E, b: &Self::E) -> Ordering;
}

/// The field of a prime p < 2^63, so that sums of two residues fit a word.
#[derive(Clone, Debug)]
pub struct Zp {
    p: u64,
    ctx: Rc<Ctx>,
}

impl Zp {
    /// The field of `ctx`, an integers-mod-p context.
    pub fn new(ctx: &Rc<Ctx>) -> Zp {
        let CtxKind::Nmod(p) = *ctx.kind() else { panic!("Zp needs an nmod context") };
        assert!(p < 1 << 63);
        Zp { p, ctx: ctx.clone() }
    }

    pub fn modulus(&self) -> u64 {
        self.p
    }
}

impl Field for Zp {
    type E = u64;

    fn zero(&self) -> u64 {
        0
    }

    fn one(&self) -> u64 {
        1 % self.p
    }

    fn is_zero(&self, a: &u64) -> bool {
        *a == 0
    }

    fn is_one(&self, a: &u64) -> bool {
        *a == 1
    }

    fn neg(&self, a: &u64) -> u64 {
        if *a == 0 { 0 } else { self.p - a }
    }

    fn add(&self, a: &u64, b: &u64) -> u64 {
        let s = a + b;
        if s >= self.p { s - self.p } else { s }
    }

    fn sub(&self, a: &u64, b: &u64) -> u64 {
        if a >= b { a - b } else { a + (self.p - b) }
    }

    fn mul(&self, a: &u64, b: &u64) -> u64 {
        (*a as u128 * *b as u128 % self.p as u128) as u64
    }

    fn inv(&self, a: &u64) -> u64 {
        // Extended Euclid on (a, p), tracking the coefficient of a.
        let (mut r0, mut r1) = (self.p as i128, *a as i128);
        let (mut s0, mut s1) = (0i128, 1i128);
        while r1 != 0 {
            let q = r0 / r1;
            (r0, r1) = (r1, r0 - q * r1);
            (s0, s1) = (s1, s0 - q * s1);
        }
        debug_assert_eq!(r0, 1, "inverse of a non-unit");
        s0.rem_euclid(self.p as i128) as u64
    }

    fn from_elem(&self, x: &Elem) -> u64 {
        x.to_word().expect("an element of Z/pZ")
    }

    fn to_elem(&self, x: &u64) -> Elem {
        Elem::from_word(&self.ctx, *x)
    }

    fn cmp(&self, a: &u64, b: &u64) -> Ordering {
        a.cmp(b)
    }
}

/// A field that FLINT's generic rings compute in exactly: Q, a prime field
/// or a finite field.
#[derive(Clone, Debug)]
pub struct GrField {
    ctx: Rc<Ctx>,
}

const EXACT: &str = "arithmetic in an exact field";

impl GrField {
    pub fn new(ctx: &Rc<Ctx>) -> GrField {
        GrField { ctx: ctx.clone() }
    }
}

impl Field for GrField {
    type E = Elem;

    fn zero(&self) -> Elem {
        Elem::zero(&self.ctx)
    }

    fn one(&self) -> Elem {
        Elem::one(&self.ctx).expect(EXACT)
    }

    fn is_zero(&self, a: &Elem) -> bool {
        a.is_zero() == Truth::True
    }

    fn is_one(&self, a: &Elem) -> bool {
        a.is_one() == Truth::True
    }

    fn neg(&self, a: &Elem) -> Elem {
        a.neg().expect(EXACT)
    }

    fn add(&self, a: &Elem, b: &Elem) -> Elem {
        a.add(b).expect(EXACT)
    }

    fn sub(&self, a: &Elem, b: &Elem) -> Elem {
        a.sub(b).expect(EXACT)
    }

    fn mul(&self, a: &Elem, b: &Elem) -> Elem {
        a.mul(b).expect(EXACT)
    }

    fn inv(&self, a: &Elem) -> Elem {
        a.inv().expect(EXACT)
    }

    fn from_elem(&self, x: &Elem) -> Elem {
        x.clone()
    }

    fn to_elem(&self, x: &Elem) -> Elem {
        x.clone()
    }

    fn cmp(&self, a: &Elem, b: &Elem) -> Ordering {
        let int = |x: &Elem| x.to_word().map(Integer::from_u64).or_else(|| x.to_integer().ok());
        match self.ctx.kind() {
            CtxKind::Rationals => a.to_rational().ok().cmp(&b.to_rational().ok()),
            CtxKind::Nmod(_) | CtxKind::FmpzMod(_) => int(a).cmp(&int(b)),
            _ => Ordering::Equal,
        }
    }
}

/// How the engine computes with the coefficients of a gr context.
pub enum Coefficients {
    Zp(Zp),
    Gr(GrField),
}

/// The engine's field for the coefficient ring `ctx`, if it is a field the
/// engine handles.
pub fn coefficients(ctx: &Rc<Ctx>) -> Option<Coefficients> {
    match ctx.kind() {
        CtxKind::Nmod(p) if *p < 1 << 63 && Integer::from_u64(*p).is_prime() => Some(Coefficients::Zp(Zp::new(ctx))),
        CtxKind::Nmod(p) if Integer::from_u64(*p).is_prime() => Some(Coefficients::Gr(GrField::new(ctx))),
        CtxKind::FmpzMod(m) if m.is_probable_prime() => Some(Coefficients::Gr(GrField::new(ctx))),
        CtxKind::Rationals | CtxKind::FqZech { .. } | CtxKind::FqNmod { .. } | CtxKind::Fq { .. } => Some(Coefficients::Gr(GrField::new(ctx))),
        _ => None,
    }
}
