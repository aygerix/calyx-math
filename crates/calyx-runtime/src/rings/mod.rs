//! Rings whose arithmetic is done by FLINT's generic rings: residue class
//! rings, finite fields, polynomial rings and the complex field.
//!
//! A ring is a structure (`Value::Struct` with `StructKind::Ring`), and its
//! elements are `Value::Elt`, which pair a FLINT element with the ring.
//! The integers, rationals and reals keep their own value types, but can
//! serve as coefficient rings.

mod arith;
mod coerce;
pub mod finite;
pub mod fp;
pub mod ideals;
mod print;
pub mod props;
pub mod small;

use std::cell::{Cell, OnceCell, RefCell};
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use calyx_flint::gr::{Ctx, CtxKind, Elem, GrError, Truth};
use calyx_flint::Integer;
use calyx_groebner::Order;
use rustc_hash::{FxHashMap, FxHasher};

use crate::error::{RResult, RuntimeError};
use crate::interp::Interp;
use crate::types::{TypeId, t};
use crate::value::{Struct, StructKind, Value};

pub use arith::small_binop;
pub use print::{format_ring_elt, upoly_text};

/// Largest field whose elements are stored as Zech logarithms (and printed
/// as powers of the primitive element).
pub const ZECH_LIMIT: u64 = 1 << 20;

pub struct Ring {
    pub kind: RingKind,
    pub ctx: Rc<Ctx>,
    /// Names of the generators, used for printing.
    pub names: RefCell<Vec<Rc<str>>>,
    /// Distinguishes rings; equal rings are the same object.
    pub id: u64,
    /// Set when the elements are stored inline (see `small`).
    pub small: Option<small::SmallRing>,
    /// The factorization of the modulus of a residue class ring, once known.
    pub factored: OnceCell<Rc<[(Integer, u64)]>>,
}

pub enum RingKind {
    /// `Z/mZ`.
    Residue(Integer),
    /// A finite field (a prime field if its degree is 1).
    Finite(FiniteField),
    /// Univariate polynomials over `base`.
    UPoly { base: Value, global: bool },
    /// Multivariate polynomials over `base` in the monomial order `order`
    /// (FLINT keeps the terms in `order.storage()`), with the variable
    /// weights `grading` of a graded ring (all 1 otherwise).
    MPoly { base: Value, rank: usize, order: Order, grading: Option<Rc<[u64]>> },
    /// The quotient `P/(f)` of the univariate polynomial ring `preimage`
    /// over `base` by a non-constant `modulus` (monic, or normalized over a
    /// field). The elements are the remainders modulo `f`, in the context
    /// of `P`.
    UPolyRes { base: Value, preimage: Rc<Struct>, modulus: Elem },
    /// The quotient `P/J` of a multivariate polynomial ring P of the given
    /// rank over `base` by an ideal J, an affine algebra
    /// (`intrinsics/poly_ideals/affine.rs`). The elements are the normal
    /// forms modulo J, in the context of P.
    MPolyRes { base: Value, rank: usize, affine: Rc<crate::intrinsics::poly_ideals::Affine> },
    /// The complex field with the given precision in bits.
    Complex(u64),
}

pub struct FiniteField {
    pub p: Integer,
    /// The degree over the prime field.
    pub degree: u64,
    /// The defining polynomial over the prime field (constant term first);
    /// empty for a prime field and for an extension of a non-prime field.
    pub modulus: Vec<Integer>,
    pub conway: bool,
    /// Created by `GF(q)` and friends rather than from a user polynomial.
    pub default: bool,
    pub power_printing: Cell<bool>,
    /// `F.1` in the FLINT context, when it is not the generator of the
    /// context.
    pub generator: Option<Elem>,
    /// For an extension of a non-prime field: that field and the defining
    /// polynomial over it.
    pub ground: Option<finite::Ground>,
    /// The default field whose FLINT context represents this field, if it
    /// is not its own.
    pub rep: Option<Rc<Struct>>,
    /// The known subfields and overfields.
    pub links: RefCell<finite::Links>,
    pub cache: finite::Cache,
}

impl FiniteField {
    pub fn new(p: Integer, degree: u64, modulus: Vec<Integer>, conway: bool, default: bool, power_printing: bool) -> FiniteField {
        FiniteField {
            p,
            degree,
            modulus,
            conway,
            default,
            power_printing: Cell::new(power_printing),
            generator: None,
            ground: None,
            rep: None,
            links: RefCell::default(),
            cache: finite::Cache::default(),
        }
    }

    pub fn order(&self) -> Integer {
        self.p.pow(self.degree)
    }
}

thread_local! {
    static NEXT_RING_ID: Cell<u64> = const { Cell::new(1) };
}

fn next_ring_id() -> u64 {
    NEXT_RING_ID.with(|c| {
        let v = c.get();
        c.set(v + 1);
        v
    })
}

impl Ring {
    pub fn type_id(&self) -> TypeId {
        match &self.kind {
            RingKind::Residue(_) => t::RNG_INT_RES,
            RingKind::Finite(_) => t::FLD_FIN,
            RingKind::UPoly { .. } => t::RNG_UPOL,
            RingKind::MPoly { .. } => t::RNG_MPOL,
            RingKind::UPolyRes { .. } => t::RNG_UPOL_RES,
            RingKind::MPolyRes { .. } => t::RNG_MPOL_RES,
            RingKind::Complex(_) => t::FLD_COM,
        }
    }

    pub fn elt_type(&self) -> TypeId {
        match &self.kind {
            RingKind::Residue(_) => t::RNG_INT_RES_ELT,
            RingKind::Finite(_) => t::FLD_FIN_ELT,
            RingKind::UPoly { .. } => t::RNG_UPOL_ELT,
            RingKind::MPoly { .. } => t::RNG_MPOL_ELT,
            RingKind::UPolyRes { .. } => t::RNG_UPOL_RES_ELT,
            RingKind::MPolyRes { .. } => t::RNG_MPOL_RES_ELT,
            RingKind::Complex(_) => t::FLD_COM_ELT,
        }
    }

    /// The printing name of the i-th generator (1-based).
    pub fn gen_name(&self, i: usize) -> String {
        match self.names.borrow().get(i - 1) {
            Some(n) => n.to_string(),
            None => format!("$.{i}"),
        }
    }

    pub fn has_names(&self) -> bool {
        !self.names.borrow().is_empty()
    }

    /// The number of generators over the coefficient (or ground) ring.
    pub fn ngens(&self) -> usize {
        match &self.kind {
            RingKind::Residue(_) => 1,
            RingKind::Finite(_) => 1,
            RingKind::UPoly { .. } => 1,
            RingKind::MPoly { rank, .. } | RingKind::MPolyRes { rank, .. } => *rank,
            RingKind::UPolyRes { .. } => 1,
            RingKind::Complex(_) => 1,
        }
    }

    pub fn finite_field(&self) -> Option<&FiniteField> {
        match &self.kind {
            RingKind::Finite(f) => Some(f),
            _ => None,
        }
    }

    pub fn is_prime_field(&self) -> bool {
        matches!(&self.kind, RingKind::Finite(f) if f.degree == 1)
    }

    /// The factorization of the modulus of a residue class ring (increasing
    /// primes; empty for `Z/1Z`).
    pub fn modulus_factors(&self) -> Option<Rc<[(Integer, u64)]>> {
        self.modulus_factors_by(crate::intrinsics::factseq::factor)
    }

    /// `modulus_factors`, found by `factor` if not yet known.
    pub fn modulus_factors_by(&self, factor: impl FnOnce(&Integer) -> Vec<(Integer, u64)>) -> Option<Rc<[(Integer, u64)]>> {
        let RingKind::Residue(m) = &self.kind else { return None };
        Some(self.factored.get_or_init(|| factor(m).into()).clone())
    }

    /// The coefficient ring of a polynomial ring (or of a quotient of one).
    pub fn base(&self) -> Option<&Value> {
        match &self.kind {
            RingKind::UPoly { base, .. } | RingKind::MPoly { base, .. } | RingKind::UPolyRes { base, .. } | RingKind::MPolyRes { base, .. } => Some(base),
            _ => None,
        }
    }
}

/// An element of a `Ring`.
pub struct Elt {
    pub parent: Rc<Struct>,
    pub x: Elem,
}

impl Elt {
    pub fn ring(&self) -> &Ring {
        match &self.parent.kind {
            StructKind::Ring(r) => r,
            _ => unreachable!("ring element with a non-ring parent"),
        }
    }

    pub fn ring_rc(&self) -> Rc<Ring> {
        match &self.parent.kind {
            StructKind::Ring(r) => r.clone(),
            _ => unreachable!("ring element with a non-ring parent"),
        }
    }

    pub fn parent_value(&self) -> Value {
        Value::Struct(self.parent.clone())
    }

    pub fn same_as(&self, o: &Elt) -> bool {
        self.ring().id == o.ring().id && self.x.equal(&o.x) == Truth::True
    }

    pub fn hash_u64(&self) -> u64 {
        let mut h = FxHasher::default();
        match self.x.ctx().kind() {
            CtxKind::Nmod(_) | CtxKind::FmpzMod(_) => {
                self.x.to_integer().ok().hash(&mut h);
            }
            CtxKind::FqZech { .. } | CtxKind::FqNmod { .. } | CtxKind::FqPacked { .. } | CtxKind::Fq { .. } => self.x.fq_coords().hash(&mut h),
            _ => self.x.to_flint_string().hash(&mut h),
        }
        h.finish()
    }

    /// The order used when sorting sets for printing.
    pub fn natural_cmp(&self, o: &Elt) -> Option<Ordering> {
        if self.ring().id != o.ring().id {
            return None;
        }
        match self.x.ctx().kind() {
            CtxKind::Nmod(_) | CtxKind::FmpzMod(_) => Some(self.x.to_integer().ok()?.cmp(&o.x.to_integer().ok()?)),
            // Powers of the primitive element in order, zero last.
            CtxKind::FqZech { .. } => Some(self.x.zech_log().unwrap_or(u64::MAX).cmp(&o.x.zech_log().unwrap_or(u64::MAX))),
            // By coordinates, most significant first.
            CtxKind::FqNmod { .. } | CtxKind::FqPacked { .. } | CtxKind::Fq { .. } => {
                let (a, b) = (self.x.fq_coords(), o.x.fq_coords());
                Some(a.iter().rev().cmp(b.iter().rev()))
            }
            _ => None,
        }
    }

    /// The integer representing an element of a residue class ring or a
    /// prime field.
    pub fn residue(&self) -> Option<Integer> {
        match self.x.ctx().kind() {
            CtxKind::Nmod(_) | CtxKind::FmpzMod(_) => self.x.to_integer().ok(),
            CtxKind::FqZech { .. } | CtxKind::FqNmod { .. } | CtxKind::FqPacked { .. } | CtxKind::Fq { .. } => self.x.fq_prime_value(),
            _ => None,
        }
    }
}

/// The ring and its structure, if `v` is a ring.
pub fn ring_of(v: &Value) -> Option<(&Rc<Struct>, &Ring)> {
    match v {
        Value::Struct(s) => match &s.kind {
            StructKind::Ring(r) => Some((s, r)),
            _ => None,
        },
        _ => None,
    }
}

pub fn make_elt(parent: &Rc<Struct>, x: Elem) -> Value {
    if let StructKind::Ring(r) = &parent.kind {
        if let Some(s) = r.small {
            return Value::Small(s, x.to_word().expect("a word-sized ring with a non-word element"));
        }
        // Complex numbers have their own values.
        if let RingKind::Complex(_) = r.kind {
            let (re, im) = x.to_complex_parts().expect("a complex field element");
            return Value::complex(re, im);
        }
    }
    Value::Elt(Rc::new(Elt { parent: parent.clone(), x }))
}

/// Map a FLINT failure to a runtime error.
pub fn gr_error(e: GrError, what: &str) -> RuntimeError {
    match e {
        GrError::Domain => RuntimeError::runtime(what.to_string()),
        GrError::Unable => RuntimeError::runtime(format!("{what} (not implemented for this ring)")),
    }
}

/// A key identifying a coefficient ring, for caching the rings built on it.
pub fn structure_key(s: &Value) -> Option<String> {
    Some(match s.as_struct()? {
        StructKind::Integers => "Z".to_string(),
        StructKind::Rationals => "Q".to_string(),
        StructKind::Reals(d) => format!("R{d}"),
        StructKind::Ring(r) => format!("#{}", r.id),
        _ => return None,
    })
}

/// Canonical rings, so that equal rings are the same object.
#[derive(Default)]
pub struct RingCache {
    residue: FxHashMap<Integer, Value>,
    finite: FxHashMap<(Integer, u64), Value>,
    upoly: FxHashMap<String, Value>,
    /// Global multivariate polynomial rings by coefficient ring and rank.
    mpoly: FxHashMap<(String, usize), Value>,
    complex: FxHashMap<u64, Value>,
    /// Ideals of the integers by generator.
    pub(crate) ideals: FxHashMap<Integer, Value>,
    /// Ideals of residue class rings by ring and generator.
    pub(crate) res_ideals: FxHashMap<(u64, Integer), Value>,
    reals: FxHashMap<u64, Rc<Ctx>>,
}

impl Interp {
    fn new_ring(&mut self, kind: RingKind, ctx: Rc<Ctx>) -> Value {
        let info = small::small_info(&kind, ctx.kind());
        let idx = info.map(|_| small::next_index());
        let ring = Ring { kind, ctx, names: RefCell::default(), id: next_ring_id(), small: idx, factored: OnceCell::new() };
        let st = Struct::new(StructKind::Ring(Rc::new(ring)));
        if let (Some(info), Some(idx)) = (info, idx) {
            small::register(idx, info, st.clone());
        }
        Value::Struct(st)
    }

    /// `Z/mZ` for `m ≥ 1`.
    pub fn residue_ring(&mut self, m: &Integer) -> Value {
        if let Some(r) = self.rings.residue.get(m) {
            return r.clone();
        }
        let ctx = Ctx::residue_ring(m);
        let r = self.new_ring(RingKind::Residue(m.clone()), ctx);
        self.rings.residue.insert(m.clone(), r.clone());
        r
    }

    /// The default field `GF(p^n)` (defined by a Conway polynomial when one
    /// is known). `p` must be prime.
    pub fn finite_field(&mut self, p: &Integer, n: u64) -> RResult<Value> {
        let key = (p.clone(), n);
        if let Some(f) = self.rings.finite.get(&key) {
            return Ok(f.clone());
        }
        let f = if n == 1 {
            let ctx = Ctx::residue_ring(p);
            let ff = FiniteField::new(p.clone(), 1, Vec::new(), false, true, false);
            self.new_ring(RingKind::Finite(ff), ctx)
        } else {
            let conway = p.to_u64().and_then(|pw| calyx_flint::gr::conway_polynomial(pw, n));
            let is_conway = conway.is_some();
            let modulus = match conway {
                Some(c) => c,
                None => crate::rings::coerce::default_irreducible(p, n)?,
            };
            self.field_from_modulus(p, modulus, is_conway, true)?
        };
        self.rings.finite.insert(key, f.clone());
        Ok(f)
    }

    /// The field `F_p[x]/(f)` for a monic irreducible `f` over `F_p`.
    pub fn field_from_modulus(&mut self, p: &Integer, modulus: Vec<Integer>, conway: bool, default: bool) -> RResult<Value> {
        let degree = modulus.len() as u64 - 1;
        let q = p.pow(degree);
        let small = q.to_u64().is_some_and(|q| q <= ZECH_LIMIT);
        let (ctx, zech) = match small.then(|| Ctx::finite_field(p, &modulus, true)) {
            Some(Ok(c)) => (c, true),
            _ => (Ctx::finite_field(p, &modulus, false).map_err(|e| gr_error(e, "Cannot create the finite field"))?, false),
        };
        let ff = FiniteField::new(p.clone(), degree, modulus, conway, default, zech);
        Ok(self.new_ring(RingKind::Finite(ff), ctx))
    }

    /// The univariate polynomial ring over `base`; the global one unless
    /// `global` is false.
    pub fn poly_ring(&mut self, base: &Value, global: bool) -> RResult<Value> {
        let key = structure_key(base);
        if global {
            if let Some(r) = key.as_ref().and_then(|k| self.rings.upoly.get(k)) {
                return Ok(r.clone());
            }
        }
        let bctx = self.ctx_of(base).ok_or_else(|| RuntimeError::runtime("Polynomial rings over this ring are not supported"))?;
        let ctx = Ctx::poly(&bctx);
        let r = self.new_ring(RingKind::UPoly { base: base.clone(), global }, ctx);
        if global {
            if let Some(k) = key {
                self.rings.upoly.insert(k, r.clone());
            }
        }
        Ok(r)
    }

    /// The quotient of the univariate polynomial ring `p` by `modulus`.
    pub fn upoly_res(&mut self, p: &Rc<Struct>, modulus: Elem) -> Value {
        let StructKind::Ring(pr) = &p.kind else { unreachable!("a polynomial ring") };
        let base = pr.base().expect("a polynomial ring").clone();
        self.new_ring(RingKind::UPolyRes { base, preimage: p.clone(), modulus }, pr.ctx.clone())
    }

    /// The affine algebra `affine` (a quotient of the multivariate
    /// polynomial ring `p`), with the names of the variables of `p`.
    pub fn mpoly_res(&mut self, p: &Rc<Struct>, affine: Rc<crate::intrinsics::poly_ideals::Affine>) -> Value {
        let StructKind::Ring(pr) = &p.kind else { unreachable!("a polynomial ring") };
        let RingKind::MPoly { base, rank, .. } = &pr.kind else { unreachable!("a multivariate polynomial ring") };
        let q = self.new_ring(RingKind::MPolyRes { base: base.clone(), rank: *rank, affine }, pr.ctx.clone());
        if let Some(StructKind::Ring(qr)) = q.as_struct() {
            *qr.names.borrow_mut() = pr.names.borrow().clone();
        }
        q
    }

    /// The multivariate polynomial ring of the given rank over `base` (with
    /// `global`, the one lexicographical ring shared by all such requests).
    pub fn mpoly_ring(&mut self, base: &Value, rank: usize, order: Order, grading: Option<Rc<[u64]>>, global: bool) -> RResult<Value> {
        let key = structure_key(base).filter(|_| global).map(|k| (k, rank));
        if let Some(r) = key.as_ref().and_then(|k| self.rings.mpoly.get(k)) {
            return Ok(r.clone());
        }
        let bctx = self.ctx_of(base).ok_or_else(|| RuntimeError::runtime("Polynomial rings over this ring are not supported"))?;
        let ctx = Ctx::mpoly(&bctx, rank, order.storage());
        let r = self.new_ring(RingKind::MPoly { base: base.clone(), rank, order, grading }, ctx);
        if let Some(k) = key {
            self.rings.mpoly.insert(k, r.clone());
        }
        Ok(r)
    }

    /// The complex field with the given precision in bits.
    pub fn complex_field(&mut self, bits: u64) -> Value {
        if let Some(c) = self.rings.complex.get(&bits) {
            return c.clone();
        }
        let ctx = Ctx::complex_float(bits);
        let c = self.new_ring(RingKind::Complex(bits), ctx);
        self.rings.complex.insert(bits, c.clone());
        c
    }

    /// All elements of a finite ring, in the order Magma enumerates them.
    pub fn enumerate_ring(&mut self, st: &Rc<Struct>) -> RResult<Vec<Value>> {
        let StructKind::Ring(r) = &st.kind else { unreachable!() };
        let size = match &r.kind {
            RingKind::Residue(m) => m.clone(),
            RingKind::Finite(f) => f.order(),
            RingKind::UPolyRes { .. } => return crate::intrinsics::upoly::enumerate_res(self, st, r),
            _ => return Err(RuntimeError::runtime(crate::error::NOT_ITERABLE)),
        };
        let n = size.to_u64().filter(|&n| n <= 1 << 26).ok_or_else(|| RuntimeError::runtime("The ring is too large to enumerate"))?;
        let mut out = Vec::with_capacity(n as usize);
        let ctx = r.ctx.clone();
        match &r.kind {
            RingKind::Finite(f) if f.degree > 1 => {
                out.push(make_elt(st, Elem::zero(&ctx)));
                if matches!(ctx.kind(), CtxKind::FqZech { .. }) {
                    // Zero, then the powers of the primitive element.
                    let g = ctx.generator().map_err(|e| gr_error(e, "No generator"))?;
                    let mut x = Elem::one(&ctx).map_err(|e| gr_error(e, "No one"))?;
                    for _ in 1..n {
                        out.push(make_elt(st, x.clone()));
                        x = x.mul(&g).map_err(|e| gr_error(e, "Arithmetic error"))?;
                    }
                } else {
                    let p = f.p.to_u64().unwrap();
                    let d = f.degree as usize;
                    let mut coords = vec![0u64; d];
                    for _ in 1..n {
                        // Next coordinate vector (counting in base p).
                        for c in coords.iter_mut() {
                            *c += 1;
                            if *c < p {
                                break;
                            }
                            *c = 0;
                        }
                        let cs: Vec<Integer> = coords.iter().map(|&c| Integer::from_u64(c)).collect();
                        out.push(make_elt(st, Elem::fq_from_coords(&ctx, &cs).map_err(|e| gr_error(e, "Arithmetic error"))?));
                    }
                }
            }
            _ => match r.small {
                Some(s) => out.extend((0..n).map(|i| Value::Small(s, i))),
                None => {
                    for i in 0..n {
                        out.push(make_elt(st, Elem::from_integer(&ctx, &Integer::from_u64(i)).map_err(|e| gr_error(e, "Arithmetic error"))?));
                    }
                }
            },
        }
        Ok(out)
    }

    /// The FLINT context for the reals with the given precision in bits.
    pub fn real_ctx(&mut self, bits: u64) -> Rc<Ctx> {
        self.rings.reals.entry(bits).or_insert_with(|| Ctx::real_float(bits)).clone()
    }

    /// The FLINT context whose elements represent the elements of the
    /// structure `s`, if it has one.
    pub fn ctx_of(&mut self, s: &Value) -> Option<Rc<Ctx>> {
        match s.as_struct()? {
            StructKind::Integers => Some(Ctx::integers()),
            StructKind::Rationals => Some(Ctx::rationals()),
            StructKind::Reals(d) => Some(self.real_ctx(*d)),
            // The elements of a polynomial quotient ring are reduced by the
            // ring, not by FLINT.
            StructKind::Ring(r) if matches!(r.kind, RingKind::UPolyRes { .. }) => None,
            StructKind::Ring(r) => Some(r.ctx.clone()),
            _ => None,
        }
    }

    /// Wrap an element of the context of structure `s` as a value of `s`.
    pub fn elem_to_value(&self, s: &Value, e: Elem) -> Value {
        match s {
            Value::Struct(st) => match &st.kind {
                StructKind::Integers => Value::Int(e.to_integer().unwrap_or_default()),
                StructKind::Rationals => Value::rat(e.to_rational().unwrap_or_default()),
                StructKind::Reals(_) => match e.to_real() {
                    Some(r) => Value::real(r),
                    None => Value::Undef,
                },
                StructKind::Ring(_) => make_elt(st, e),
                _ => Value::Undef,
            },
            _ => Value::Undef,
        }
    }
}
