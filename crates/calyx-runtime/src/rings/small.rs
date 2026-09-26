//! Rings whose elements fit in a machine word: residue class rings `Z/nZ`
//! and prime fields `GF(p)` with a modulus below `2^64`.
//!
//! Their elements are stored inline as `Value::Small(ring, residue)`, so
//! arithmetic on them never allocates. Each such ring is registered once,
//! when it is created, and its elements refer to it by index. Rings are
//! never freed (the ring cache keeps them alive anyway).
//!
//! The generic code paths work with FLINT elements (`Value::Elt`); `expand`
//! turns an inline element into one, and `make_elt` turns results back.

use std::cell::RefCell;
use std::rc::Rc;

use calyx_flint::Nmod;
use calyx_flint::gr::{CtxKind, Elem};

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
}

#[derive(Clone, Copy)]
pub struct SmallInfo {
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
            SmallKind::PrimeField => t::FLD_FIN_ELT,
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
pub fn small_info(kind: &RingKind, ctx_kind: &CtxKind) -> Option<SmallInfo> {
    let CtxKind::Nmod(n) = ctx_kind else { return None };
    let kind = match kind {
        RingKind::Residue(_) => SmallKind::Residue,
        RingKind::Finite(f) if f.degree == 1 => SmallKind::PrimeField,
        _ => return None,
    };
    Some(SmallInfo { m: Nmod::new(*n), kind })
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

/// An inline element as a FLINT-backed ring element.
pub fn to_elt(r: SmallRing, v: u64) -> Rc<Elt> {
    let parent = r.parent();
    let x = match &parent.kind {
        StructKind::Ring(ring) => Elem::from_word(&ring.ctx, v),
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
