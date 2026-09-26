//! Rings whose elements fit in a machine word: residue class rings `Z/nZ`
//! and prime fields `GF(p)` with a modulus below `2^64`, and finite fields
//! with Zech logarithms.
//!
//! Their elements are stored inline as `Value::Small(ring, word)`, the word
//! being the residue or the Zech logarithm (see `Zech`), so arithmetic on
//! them never allocates. Each such ring is registered once, when it is
//! created, and its elements refer to it by index. Rings are never freed
//! (the ring cache keeps them alive anyway).
//!
//! The generic code paths work with FLINT elements (`Value::Elt`); `expand`
//! turns an inline element into one, and `make_elt` turns results back.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::rc::Rc;

use calyx_flint::fq::Zech;
use calyx_flint::gr::{Ctx, CtxKind, Elem};
use calyx_flint::{Integer, Nmod};

use super::{Elt, Ring, RingKind};
use crate::types::{TypeId, t};
use crate::value::{Struct, StructKind, Value};

/// The index of a ring with word-sized elements.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SmallRing(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SmallKind {
    /// `Z/nZ` (type `RngIntRes`).
    Residue,
    /// `GF(p)` (type `FldFin`).
    PrimeField,
    /// `GF(q)` with Zech logarithms (type `FldFin`).
    Zech(Zech),
}

#[derive(Clone, Copy)]
pub struct SmallInfo {
    /// The modulus, or the characteristic of a field with Zech logarithms.
    pub m: Nmod,
    pub kind: SmallKind,
}

struct Entry {
    info: SmallInfo,
    parent: Rc<Struct>,
}

thread_local! {
    static RINGS: RefCell<Vec<Entry>> = const { RefCell::new(Vec::new()) };
}

impl SmallRing {
    #[inline]
    pub fn info(self) -> SmallInfo {
        RINGS.with(|r| r.borrow()[self.0 as usize].info)
    }

    #[inline]
    pub fn modulus(self) -> Nmod {
        self.info().m
    }

    pub fn parent(self) -> Rc<Struct> {
        RINGS.with(|r| r.borrow()[self.0 as usize].parent.clone())
    }

    pub fn parent_value(self) -> Value {
        Value::Struct(self.parent())
    }

    pub fn elt_type(self) -> TypeId {
        match self.info().kind {
            SmallKind::Residue => t::RNG_INT_RES_ELT,
            SmallKind::PrimeField | SmallKind::Zech(_) => t::FLD_FIN_ELT,
        }
    }

    /// The tables of a field with Zech logarithms.
    #[inline]
    pub fn zech(self) -> Option<Zech> {
        match self.info().kind {
            SmallKind::Zech(z) => Some(z),
            _ => None,
        }
    }

    /// The word of the integer `n`.
    pub fn word_of_integer(self, n: &Integer) -> u64 {
        let info = self.info();
        match info.kind {
            SmallKind::Zech(z) => z.from_integer(n),
            _ => info.m.reduce_integer(n),
        }
    }

    /// The word of `-x`.
    pub fn neg(self, x: u64) -> u64 {
        let info = self.info();
        match info.kind {
            SmallKind::Zech(z) => z.neg(x),
            _ => info.m.neg(x),
        }
    }

    /// The order of the ring's elements for sorting: by residue, or zero
    /// and then the powers of the primitive element.
    pub fn cmp_words(self, x: u64, y: u64) -> Ordering {
        match self.zech() {
            Some(z) => (x != z.zero(), x).cmp(&(y != z.zero(), y)),
            None => x.cmp(&y),
        }
    }

    /// The ring an inline element belongs to.
    pub fn ring(self) -> Rc<Ring> {
        match &self.parent().kind {
            StructKind::Ring(r) => r.clone(),
            _ => unreachable!("small ring with a non-ring parent"),
        }
    }
}

/// How the ring of the given kind and context stores its elements inline,
/// if it does.
pub fn small_info(kind: &RingKind, ctx: &Rc<Ctx>) -> Option<SmallInfo> {
    let (n, kind) = match (kind, ctx.kind()) {
        (RingKind::Residue(_), CtxKind::Nmod(n)) => (*n, SmallKind::Residue),
        (RingKind::Finite(f), CtxKind::Nmod(n)) if f.degree == 1 => (*n, SmallKind::PrimeField),
        (RingKind::Finite(_), CtxKind::FqZech { p, .. }) => (*p, SmallKind::Zech(Zech::of(ctx)?)),
        _ => return None,
    };
    Some(SmallInfo { m: Nmod::new(n), kind })
}

/// The index the next registered ring will get.
pub fn next_index() -> SmallRing {
    RINGS.with(|r| SmallRing(u32::try_from(r.borrow().len()).expect("too many residue class rings")))
}

/// Register the ring `parent` under the index `idx` from `next_index`.
pub fn register(idx: SmallRing, info: SmallInfo, parent: Rc<Struct>) {
    RINGS.with(|r| {
        let mut r = r.borrow_mut();
        assert_eq!(r.len(), idx.0 as usize, "small rings registered out of order");
        r.push(Entry { info, parent });
    });
}

/// The word of `x`, an element of the ring `r` in its FLINT context.
pub fn word_of(r: SmallRing, x: &Elem) -> u64 {
    match r.zech() {
        Some(z) => x.zech_log().unwrap_or(z.zero()),
        None => x.to_word().expect("a word-sized ring with a non-word element"),
    }
}

/// The element of the ring `r`, whose FLINT context is `ctx`, with word `v`.
pub fn elem_of(r: SmallRing, ctx: &Rc<Ctx>, v: u64) -> Elem {
    match r.zech() {
        Some(_) => Elem::fq_from_zech_log(ctx, v).expect("a field with Zech logarithms"),
        None => Elem::from_word(ctx, v),
    }
}

/// An inline element as a FLINT-backed ring element.
pub fn to_elt(r: SmallRing, v: u64) -> Rc<Elt> {
    let parent = r.parent();
    let x = match &parent.kind {
        StructKind::Ring(ring) => elem_of(r, &ring.ctx, v),
        _ => unreachable!(),
    };
    Rc::new(Elt { parent, x })
}

/// `v` with an inline element replaced by the equivalent `Value::Elt`, for
/// code that handles all ring elements generically.
pub fn expand(v: &Value) -> Value {
    match v {
        Value::Small(r, x) => Value::Elt(to_elt(*r, *x)),
        _ => v.clone(),
    }
}

/// The ring element `v` as a FLINT-backed element, if it is one.
pub fn elt_of(v: &Value) -> Option<Rc<Elt>> {
    match v {
        Value::Elt(e) => Some(e.clone()),
        Value::Small(r, x) => Some(to_elt(*r, *x)),
        _ => None,
    }
}
