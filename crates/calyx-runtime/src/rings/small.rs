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

use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::rc::Rc;

use calyx_flint::fq::Zech;
use calyx_flint::gr::{Ctx, CtxKind, Elem};
use calyx_flint::{Integer, Nmod};

use super::{Elt, Ring, RingKind};
use crate::interp::Interp;
use crate::sym::Sym;
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

/// Where `reachable` last found an inline element of a ring, and how many
/// more calls take it to be there still, after a costly search.
#[derive(Default)]
pub struct Sighting {
    global: Cell<Option<Sym>>,
    skip: Cell<u32>,
}

/// The most values `reachable` looks at.
const SEARCH_LIMIT: usize = 1 << 16;

/// Whether an inline element of `s` is among the values the program can
/// reach outside the calls of user functions: its results `$1`, `$2`, ...,
/// its globals and the variables of `eval` code and packages. It is also
/// true when the search gives up.
pub fn reachable(it: &Interp, s: SmallRing, seen: &Sighting) -> bool {
    if seen.skip.get() > 0 {
        seen.skip.set(seen.skip.get() - 1);
        return true;
    }
    let mut budget = SEARCH_LIMIT;
    let found = find(it, s, seen, &mut budget);
    let cost = SEARCH_LIMIT - budget;
    if found != Some(false) && cost > 4096 {
        // Spread the cost of a long search over the calls that follow.
        seen.skip.set((cost / 8) as u32);
    }
    found != Some(false)
}

fn find(it: &Interp, s: SmallRing, seen: &Sighting, budget: &mut usize) -> Option<bool> {
    let first = seen.global.get().and_then(|g| it.globals.get(&g));
    if search(first.into_iter().chain(it.previous.iter().flatten()).chain(it.self_seqs.iter().flatten()), s, budget)? {
        return Some(true);
    }
    for (g, v) in &it.globals {
        if search([v], s, budget)? {
            seen.global.set(Some(*g));
            return Some(true);
        }
    }
    let envs = it.eval_env.iter().chain(&it.package_stack).chain(it.packages.iter().map(|p| &p.globals));
    search(envs.flat_map(|e| e.values()), s, budget)
}

/// Whether the values `vs`, or the values inside them, include an inline
/// element of `s`; `None` when that takes more than `budget` steps.
///
/// When `renew_if_unreferenced` searches, no value refers to the parent of
/// `s`, as a sequence or set of its elements would: so a sequence is
/// searched only when it holds other containers, and a set never.
fn search<'a>(vs: impl IntoIterator<Item = &'a Value>, s: SmallRing, budget: &mut usize) -> Option<bool> {
    let mut todo: Vec<&Value> = Vec::new();
    for v in vs {
        push(&mut todo, std::slice::from_ref(v), budget)?;
    }
    while let Some(v) = todo.pop() {
        match v {
            Value::Small(r, _) if *r == s => return Some(true),
            Value::Tuple(t) => push(&mut todo, &t.elems, budget)?,
            Value::List(l) => push(&mut todo, l, budget)?,
            Value::Rec(r) => push(&mut todo, &r.fields, budget)?,
            Value::Assoc(a) => {
                for x in a.map.values().chain(&a.default) {
                    push(&mut todo, std::slice::from_ref(x), budget)?;
                }
            }
            Value::Func(c) => push(&mut todo, &c.captures, budget)?,
            Value::Seq(q) if q.elems.first().is_some_and(container) => push(&mut todo, &q.elems, budget)?,
            _ => {}
        }
    }
    Some(false)
}

fn push<'a>(todo: &mut Vec<&'a Value>, xs: &'a [Value], budget: &mut usize) -> Option<()> {
    *budget = budget.checked_sub(xs.len())?;
    todo.extend(xs);
    Some(())
}

fn container(v: &Value) -> bool {
    matches!(v, Value::Tuple(_) | Value::List(_) | Value::Rec(_) | Value::Assoc(_) | Value::Func(_) | Value::Seq(_))
}
