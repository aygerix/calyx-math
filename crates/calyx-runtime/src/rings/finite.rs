//! The lattice of finite fields ([BCS97]): fields defined by polynomials,
//! extensions of non-prime fields and subfields, the embeddings between
//! them and the maps they induce on elements.
//!
//! As in Magma, a field small enough for Zech logarithms is represented in
//! the FLINT context of the default field of its size, whose generator is
//! the root of a Conway polynomial, and its own generator `F.1` is a root
//! of its defining polynomial there; so the maps between small fields act
//! on logarithms. Larger fields defined over the prime field use their own
//! polynomial, and larger extensions of non-prime fields the context of
//! the default field of their size.
//!
//! A field knows its subfields (with the image of the generator of their
//! context) and its overfields. Registering an embedding closes these
//! relations under composition and under inclusion among the subfields of
//! a field. Default fields are related through their Conway polynomials
//! without being registered, and a field embedded in a default field is
//! identified with the default field of its size when a field containing
//! elements of both is needed.

use std::cell::{OnceCell, RefCell};
use std::rc::{Rc, Weak};

use calyx_flint::gr::{Ctx, CtxKind, Elem, Truth};
use calyx_flint::{Integer, Nmod};

use super::fp::{Coords, LinMap};
use super::{FiniteField, Ring, RingKind, ZECH_LIMIT};
use crate::error::{RResult, RuntimeError};
use crate::interp::Interp;
use crate::value::{Struct, StructKind, Value};

/// The ground field of an extension of a non-prime field.
pub struct Ground {
    pub field: Rc<Struct>,
    /// The degree over the ground field.
    pub degree: u64,
    /// The defining polynomial over the ground field: monic, constant term
    /// first, with coefficients in the context of the ground field.
    pub poly: Vec<Elem>,
}

/// A known subfield, with the image of the generator of its context.
pub struct SubLink {
    pub field: Weak<Struct>,
    pub id: u64,
    pub image: Elem,
    /// Found between two subfields of a field rather than by creating,
    /// embedding or coercing: Magma does not search such links for a
    /// common overfield.
    pub side: bool,
}

/// The known relations of a field.
#[derive(Default)]
pub struct Links {
    pub subs: Vec<SubLink>,
    pub overs: Vec<Weak<Struct>>,
}

/// Data computed on demand.
#[derive(Default)]
pub struct Cache {
    pub primitive: RefCell<Option<Elem>>,
    /// Whether the primitive element was set or had to be found, so that
    /// `SetPrimitiveElement` cannot change it.
    pub primitive_fixed: std::cell::Cell<bool>,
    /// Context coordinates to coordinates over the ground field in the
    /// power basis of `F.1` (`None` when they are the same).
    basis: OnceCell<Option<LinMap>>,
    /// Embedding matrices and their left inverses, by subfield.
    restrict: RefCell<Vec<(u64, Rc<(LinMap, LinMap)>)>>,
    /// The factorisation of q - 1, and its primes.
    qm1_factors: OnceCell<Vec<(Integer, u64)>>,
    qm1_primes: OnceCell<Vec<Integer>>,
    /// Logarithms to the base of the primitive element found so far, by the
    /// coordinates of the element.
    pub logs: RefCell<rustc_hash::FxHashMap<Vec<Integer>, Integer>>,
    /// The image of the generator of the context in the default field of
    /// the same size, through a default overfield.
    anchor: OnceCell<Option<Elem>>,
    /// For square roots: the least non-square z (in counting order) to the
    /// power of the odd part of q - 1.
    pub non_square: OnceCell<Elem>,
}

pub fn field_of(st: &Struct) -> Option<(&Ring, &FiniteField)> {
    match &st.kind {
        StructKind::Ring(r) => match &r.kind {
            RingKind::Finite(f) => Some((r, f)),
            _ => None,
        },
        _ => None,
    }
}

fn ff(st: &Struct) -> (&Ring, &FiniteField) {
    field_of(st).expect("a finite field")
}

/// The finite field structure of a value.
pub fn field_struct(v: &Value) -> Option<&Rc<Struct>> {
    match v {
        Value::Struct(s) if field_of(s).is_some() => Some(s),
        _ => None,
    }
}

fn id(st: &Struct) -> u64 {
    ff(st).0.id
}

fn degree(st: &Struct) -> u64 {
    ff(st).1.degree
}

fn is_zech(ctx: &Ctx) -> bool {
    matches!(ctx.kind(), CtxKind::FqZech { .. })
}

fn mulmod(a: u64, b: u64, n: u64) -> u64 {
    ((a as u128 * b as u128) % n as u128) as u64
}

/// Whether the field of order `p^n` is small enough for Zech logarithms.
pub fn is_small(p: &Integer, n: u64) -> bool {
    p.pow(n).to_u64().is_some_and(|q| q <= ZECH_LIMIT)
}

/// `F.1`, the generator over the ground field.
pub fn gen1(r: &Ring, f: &FiniteField) -> Elem {
    if f.degree == 1 {
        return Elem::one(&r.ctx).unwrap();
    }
    match &f.generator {
        Some(g) => g.clone(),
        None => r.ctx.generator().unwrap(),
    }
}

/// The degree over the ground field.
pub fn rel_degree(f: &FiniteField) -> u64 {
    f.ground.as_ref().map_or(f.degree, |g| g.degree)
}

/// The logarithm of `x` to the base `F.1` in a small field (`None` for
/// zero or when `F.1` is not primitive).
pub fn log_gen1(f: &FiniteField, x: &Elem) -> Option<u64> {
    let k = x.zech_log()?;
    match &f.generator {
        None => Some(k),
        Some(g) => {
            let n = Elem::zech_order(x.ctx())?;
            Some(mulmod(k, Nmod::new(n).inv(g.zech_log()? % n)?, n))
        }
    }
}

/// Whether the FLINT context of a field is defined by a Conway polynomial.
fn ctx_conway(f: &FiniteField) -> bool {
    match &f.rep {
        Some(d) => ff(d).1.conway,
        None => f.conway,
    }
}

/// The polynomial defining the FLINT context of a field.
fn ctx_modulus(f: &FiniteField) -> &[Integer] {
    match &f.rep {
        Some(d) => &ff(d).1.modulus,
        None => &f.modulus,
    }
}

/// The polynomial with integer coefficients as one over a context.
pub fn int_poly_in(coeffs: &[Integer], ctx: &Rc<Ctx>) -> Vec<Elem> {
    coeffs.iter().map(|c| Elem::from_integer(ctx, c).unwrap()).collect()
}

/// The distinct roots in a finite field of a polynomial over it.
pub fn roots(coeffs: &[Elem], ctx: &Rc<Ctx>) -> Vec<Elem> {
    let px = Ctx::poly(ctx);
    let Ok(f) = Elem::poly_from_coeffs(&px, coeffs) else { return Vec::new() };
    if f.poly_len() < 2 {
        return Vec::new();
    }
    match f.poly_factor() {
        Ok((_, fs)) => fs.into_iter().filter(|(g, _)| g.poly_len() == 2).map(|(g, _)| g.poly_coeff(0).neg().unwrap()).collect(),
        Err(_) => Vec::new(),
    }
}

/// Magma's order on the elements of a field: by logarithm for small
/// fields, else by coordinates from the top.
pub fn elt_order(a: &Elem, b: &Elem) -> std::cmp::Ordering {
    if is_zech(a.ctx()) {
        a.zech_log().map_or(0, |k| k + 1).cmp(&b.zech_log().map_or(0, |k| k + 1))
    } else {
        a.fq_coords().iter().rev().cmp(b.fq_coords().iter().rev())
    }
}

fn smallest(v: Vec<Elem>) -> Option<Elem> {
    v.into_iter().min_by(elt_order)
}

/// The image of the generator of the Conway context of degree `d` in the
/// Conway context `to` of degree `n` (`d` divides `n`).
fn conway_image(p: &Integer, d: u64, to: &Rc<Ctx>, n: u64) -> Elem {
    let one = Integer::one();
    let c = (p.pow(n) - &one).divexact(&(p.pow(d) - &one));
    if is_zech(to) {
        let q1 = Elem::zech_order(to).unwrap();
        return Elem::fq_from_zech_log(to, c.to_u64().unwrap() % q1).unwrap();
    }
    to.generator().unwrap().pow(&c).unwrap()
}

// ----- maps between fields ---------------------------------------------------

/// The image of `x`, an element of a field of degree `d` (a prime field if
/// `d` is 1), under the embedding sending the generator of its context to
/// `image`.
pub fn embed_with(x: &Elem, d: u64, image: &Elem) -> Elem {
    let to = image.ctx();
    if d == 1 {
        let v = match x.ctx().kind() {
            CtxKind::Nmod(_) | CtxKind::FmpzMod(_) => x.to_integer().unwrap_or_default(),
            _ => x.fq_prime_value().unwrap_or_default(),
        };
        return Elem::from_integer(to, &v).unwrap();
    }
    if is_zech(x.ctx()) && is_zech(to) {
        let n = Elem::zech_order(to).unwrap();
        let s = image.zech_log().expect("the image of a generator is not zero");
        return match x.zech_log() {
            None => Elem::zero(to),
            Some(l) => Elem::fq_from_zech_log(to, mulmod(s, l, n)).unwrap(),
        };
    }
    let mut acc = Elem::zero(to);
    for c in x.fq_coords().iter().rev() {
        acc = acc.mul(image).unwrap();
        if !c.is_zero() {
            acc = acc.add(&Elem::from_integer(to, c).unwrap()).unwrap();
        }
    }
    acc
}

/// The element of the field `e` that the embedding into `f` given by
/// `image` sends to `y`, if there is one.
fn restrict_with(y: &Elem, e: &Struct, image: &Elem, f: &Struct) -> Option<Elem> {
    let (er, ef) = ff(e);
    if ef.degree == 1 {
        let v = match y.ctx().kind() {
            CtxKind::Nmod(_) | CtxKind::FmpzMod(_) => y.to_integer().ok()?,
            _ => y.fq_prime_value()?,
        };
        return Elem::from_integer(&er.ctx, &v).ok();
    }
    if is_zech(y.ctx()) && is_zech(&er.ctx) {
        let (nf, ne) = (Elem::zech_order(y.ctx())?, Elem::zech_order(&er.ctx)?);
        let c = nf / ne;
        let Some(t) = y.zech_log() else { return Some(Elem::zero(&er.ctx)) };
        if t % c != 0 {
            return None;
        }
        let u = (image.zech_log()? / c) % ne;
        let l = mulmod(t / c, Nmod::new(ne).inv(u)?, ne);
        return Elem::fq_from_zech_log(&er.ctx, l);
    }
    let (fr, fd) = ff(f);
    let key = er.id;
    let cached = fd.cache.restrict.borrow().iter().find(|(k, _)| *k == key).map(|(_, m)| m.clone());
    let mats = match cached {
        Some(m) => m,
        None => {
            let mut cols = Vec::with_capacity(ef.degree as usize);
            let mut pw = Elem::one(&fr.ctx).ok()?;
            for _ in 0..ef.degree {
                cols.push(Coords::of(&pw));
                pw = pw.mul(image).ok()?;
            }
            let m = LinMap::from_columns(&fd.p, &cols, fd.degree as usize);
            let l = m.left_inverse()?;
            let m = Rc::new((m, l));
            fd.cache.restrict.borrow_mut().push((key, m.clone()));
            m
        }
    };
    let v = Coords::of(y);
    let x = mats.1.apply(&v);
    if mats.0.apply(&x) != v {
        return None;
    }
    Some(x.to_elem(&er.ctx))
}

/// `restrict_with` for callers holding an embedding of their own.
pub fn restrict_by(y: &Elem, e: &Struct, image: &Elem, f: &Struct) -> Option<Elem> {
    restrict_with(y, e, image, f)
}

/// The image of the generator of the context of `e` under an isomorphism
/// onto `f` (of the same size): the known embedding, the identity of
/// Conway contexts, or the least root of the polynomial of the context of
/// `e`.
pub fn iso_image(e: &Rc<Struct>, f: &Rc<Struct>) -> Option<Elem> {
    if let Some(i) = find_emb(e, f) {
        return Some(i);
    }
    let ((_, ef), (fr, fd)) = (ff(e), ff(f));
    if ef.degree == 1 {
        return Elem::one(&fr.ctx).ok();
    }
    if ctx_conway(ef) && ctx_conway(fd) {
        return fr.ctx.generator().ok();
    }
    smallest(roots(&int_poly_in(ctx_modulus(ef), &fr.ctx), &fr.ctx))
}

/// The registered image of the generator of the context of `e` in `f`.
fn linked(e: u64, f: &Struct) -> Option<Elem> {
    linked_side(e, f).map(|(i, _)| i)
}

fn linked_side(e: u64, f: &Struct) -> Option<(Elem, bool)> {
    ff(f).1.links.borrow().subs.iter().find(|l| l.id == e && l.field.strong_count() > 0).map(|l| (l.image.clone(), l.side))
}

fn subs_of(f: &Struct) -> Vec<(Rc<Struct>, Elem)> {
    subs_side(f).into_iter().map(|(s, i, _)| (s, i)).collect()
}

fn subs_side(f: &Struct) -> Vec<(Rc<Struct>, Elem, bool)> {
    ff(f).1.links.borrow().subs.iter().filter_map(|l| Some((l.field.upgrade()?, l.image.clone(), l.side))).collect()
}

fn overs_of(f: &Struct) -> Vec<Rc<Struct>> {
    ff(f).1.links.borrow().overs.iter().filter_map(Weak::upgrade).collect()
}

/// The embedding of the default field `e` into the default field `f` of a
/// multiple degree.
fn default_emb(e: &Rc<Struct>, f: &Rc<Struct>) -> Option<Elem> {
    let ((er, ef), (fr, fd)) = (ff(e), ff(f));
    if ef.degree == 1 {
        return Elem::one(&fr.ctx).ok();
    }
    if er.id == fr.id {
        return fr.ctx.generator().ok();
    }
    if ef.conway && fd.conway {
        return Some(conway_image(&ef.p, ef.degree, &fr.ctx, fd.degree));
    }
    if let Some(img) = linked(er.id, f) {
        return Some(img);
    }
    // Default fields beyond the Conway range: through a default field
    // between them already embedded in f, or else the least root agreeing
    // with the embeddings fixed for the default subfields of e; fixed once
    // chosen.
    let de = ef.degree;
    let fixed: Vec<(Rc<Struct>, Elem)> = subs_of(f).into_iter().filter(|(d, _)| ff(d).1.default).collect();
    for (d, di) in fixed.iter().filter(|(d, _)| degree(d) > de && degree(d) % de == 0) {
        if let Some(c) = default_emb(e, d) {
            let img = embed_with(&c, degree(d), di);
            register(e, f, img.clone());
            return Some(img);
        }
    }
    let below: Vec<(Rc<Struct>, Elem, Elem)> = fixed
        .into_iter()
        .filter(|(s, _)| degree(s) < de && de % degree(s) == 0)
        .filter_map(|(s, si)| Some((s.clone(), default_emb(&s, e)?, si)))
        .collect();
    let mut rs = roots(&int_poly_in(ctx_modulus(ef), &fr.ctx), &fr.ctx);
    rs.sort_by(elt_order);
    let agrees = |r: &Elem| below.iter().all(|(s, c, si)| embed_with(c, degree(s), r).equal(si) == Truth::True);
    let img = rs.into_iter().find(agrees)?;
    register(e, f, img.clone());
    Some(img)
}

/// The image of the generator of the context of `e` under the known
/// embedding of `e` into `f`, if there is one: `e` is `f`, the prime
/// field, a registered subfield, a default field inside another, or
/// related to `f` through default fields.
pub fn find_emb(e: &Rc<Struct>, f: &Rc<Struct>) -> Option<Elem> {
    let ((er, ef), (fr, fd)) = (field_of(e)?, field_of(f)?);
    if ef.p != fd.p || fd.degree % ef.degree != 0 {
        return None;
    }
    if ef.degree == 1 {
        return Elem::one(&fr.ctx).ok();
    }
    if er.id == fr.id {
        return fr.ctx.generator().ok();
    }
    if let Some(img) = linked(er.id, f) {
        return Some(img);
    }
    if ef.default && fd.default {
        return default_emb(e, f);
    }
    // Through the default lattice: e inside a default d1, d1 inside a
    // default d2, d2 inside f.
    let mut ups: Vec<(Rc<Struct>, Elem)> = overs_of(e).into_iter().filter(|o| ff(o).1.default).filter_map(|o| Some((o.clone(), linked(er.id, &o)?))).collect();
    if ef.default {
        ups.push((e.clone(), er.ctx.generator().ok()?));
    }
    let mut downs: Vec<(Rc<Struct>, Elem)> = subs_of(f).into_iter().filter(|(s, _)| ff(s).1.default).collect();
    if fd.default {
        downs.push((f.clone(), fr.ctx.generator().ok()?));
    }
    for (d1, i1) in &ups {
        for (d2, i2) in &downs {
            if degree(d2) % degree(d1) == 0 {
                let c = default_emb(d1, d2)?;
                return Some(embed_with(&embed_with(i1, degree(d1), &c), degree(d2), i2));
            }
        }
    }
    None
}

/// Whether `e` is known to be a subfield of `f`.
pub fn is_subfield(e: &Rc<Struct>, f: &Rc<Struct>) -> bool {
    find_emb(e, f).is_some()
}

/// Register the embedding of `e` into `f` sending the generator of the
/// context of `e` to `image`, with everything it implies.
pub fn register(e: &Rc<Struct>, f: &Rc<Struct>, image: Elem) {
    link(e, f, image, false);
}

fn link(e: &Rc<Struct>, f: &Rc<Struct>, image: Elem, side: bool) {
    let (eid, fid) = (id(e), id(f));
    if eid == fid || degree(e) == 1 {
        return;
    }
    match linked_side(eid, f) {
        // A link found sideways first may also follow directly, which
        // then holds for what it implies as well.
        Some((_, true)) if !side => {
            let mut links = ff(f).1.links.borrow_mut();
            links.subs.iter_mut().filter(|l| l.id == eid).for_each(|l| l.side = false);
        }
        Some(_) => return,
        None => {
            ff(f).1.links.borrow_mut().subs.push(SubLink { field: Rc::downgrade(e), id: eid, image: image.clone(), side });
            ff(e).1.links.borrow_mut().overs.push(Rc::downgrade(f));
        }
    }
    let de = degree(e);
    // The subfields of e are subfields of f.
    for (s, si, ss) in subs_side(e) {
        link(&s, f, embed_with(&si, de, &image), side || ss);
    }
    // e is a subfield of the overfields of f.
    let df = degree(f);
    for g in overs_of(f) {
        if let Some((gi, gs)) = linked_side(fid, &g) {
            link(e, &g, embed_with(&image, df, &gi), side || gs);
        }
    }
    // Inclusions between e and the other subfields of f; as in Magma,
    // subfields of the same degree stay apart until a coercion relates them.
    for (s, si) in subs_of(f) {
        let (sid, ds) = (id(&s), degree(&s));
        if sid == eid || ds == de {
            continue;
        }
        if de % ds == 0 && linked(sid, e).is_none() {
            if let Some(r) = restrict_with(&si, e, &image, f) {
                link(&s, e, r, true);
            }
        }
        if ds % de == 0 && linked(eid, &s).is_none() {
            if let Some(r) = restrict_with(&image, &s, &si, f) {
                link(e, &s, r, true);
            }
        }
    }
}

/// `x` (an element of `e`) in `f`, if `e` is known to be a subfield.
pub fn embed(x: &Elem, e: &Rc<Struct>, f: &Rc<Struct>) -> Option<Elem> {
    let img = find_emb(e, f)?;
    Some(embed_with(x, degree(e), &img))
}

/// `y` (an element of `f`) as an element of its known subfield `e`: `None`
/// if `e` is not known to be a subfield, `Some(None)` if `y` is not in it.
pub fn restrict(y: &Elem, f: &Rc<Struct>, e: &Rc<Struct>) -> Option<Option<Elem>> {
    let img = find_emb(e, f)?;
    Some(restrict_with(y, e, &img, f))
}

/// `A eq B` for finite fields: equal when one is known to be a subfield of
/// the other, or both are registered subfields of a third, of the same
/// degree; default fields of different degrees are different; otherwise
/// the fields cannot be compared.
pub fn field_eq(a: &Rc<Struct>, b: &Rc<Struct>) -> Result<bool, &'static str> {
    let ((ar, af), (br, bf)) = (ff(a), ff(b));
    if ar.id == br.id {
        return Ok(true);
    }
    if af.p != bf.p {
        return Err("Arguments have no covering field");
    }
    if is_subfield(a, b) || is_subfield(b, a) || overs_of(a).iter().any(|o| linked(br.id, o).is_some()) {
        return Ok(af.degree == bf.degree);
    }
    if af.default && bf.default {
        return Ok(false);
    }
    Err("Arguments have no covering field")
}

/// Whether a field embeds in a default field (so that it can be identified
/// with the default field of its size).
fn anchored(e: &Rc<Struct>) -> bool {
    ff(e).1.default || overs_of(e).iter().any(|o| ff(o).1.default)
}

/// The image of the generator of the context of `e` in the default field
/// `d` of the same size, through a default field containing `e`.
fn anchor(e: &Rc<Struct>, d: &Rc<Struct>) -> Option<Elem> {
    let (er, ef) = ff(e);
    if ef.default {
        return er.ctx.generator().ok();
    }
    ef.cache
        .anchor
        .get_or_init(|| {
            for o in overs_of(e) {
                if ff(&o).1.default {
                    let img = linked(er.id, &o)?;
                    return restrict_with(&img, d, &default_emb(d, &o)?, &o);
                }
            }
            None
        })
        .clone()
}

// ----- coordinates -------------------------------------------------------------

/// Coordinates of `x` over the ground field in the power basis of `F.1`,
/// flattened: the context coordinates of the i-th coefficient are at
/// `[i*d, (i+1)*d)` where d is the degree of the ground field.
pub fn ground_coords(st: &Rc<Struct>, x: &Elem) -> Coords {
    let (r, f) = ff(st);
    let basis = f.cache.basis.get_or_init(|| {
        if f.generator.is_none() && f.ground.is_none() {
            return None;
        }
        let beta = gen1(r, f);
        let (kimg, d, m) = match &f.ground {
            None => (None, 1, f.degree),
            Some(g) => (find_emb(&g.field, st), degree(&g.field), g.degree),
        };
        let mut cols = Vec::with_capacity(f.degree as usize);
        let mut bi = Elem::one(&r.ctx).unwrap();
        for _ in 0..m {
            let mut t = bi.clone();
            for _ in 0..d {
                cols.push(Coords::of(&t));
                if let Some(k) = &kimg {
                    t = t.mul(k).unwrap();
                }
            }
            bi = bi.mul(&beta).unwrap();
        }
        LinMap::from_columns(&f.p, &cols, f.degree as usize).inverse()
    });
    let v = Coords::of(x);
    match basis {
        Some(b) => b.apply(&v),
        None => v,
    }
}

/// The coefficients of `x` over the ground field in the power basis of
/// `F.1`, as elements of the context of the ground field (`fp` for the
/// prime field).
pub fn ground_elems(st: &Rc<Struct>, x: &Elem, fp: &Rc<Ctx>) -> Vec<Elem> {
    let v = ground_coords(st, x);
    match &ff(st).1.ground {
        None => v.integers().iter().map(|c| Elem::from_integer(fp, c).unwrap()).collect(),
        Some(g) => {
            let (kr, kf) = ff(&g.field);
            (0..g.degree as usize).map(|i| v.chunk(i, kf.degree as usize).to_elem(&kr.ctx)).collect()
        }
    }
}

thread_local! {
    static PRIME_CTXS: RefCell<Vec<(Integer, Rc<Ctx>)>> = const { RefCell::new(Vec::new()) };
}

/// A context for the prime field of characteristic p.
fn prime_ctx(p: &Integer) -> Rc<Ctx> {
    PRIME_CTXS.with(|c| {
        if let Some((_, x)) = c.borrow().iter().find(|(q, _)| q == p) {
            return x.clone();
        }
        let x = Ctx::residue_ring(p);
        c.borrow_mut().push((p.clone(), x.clone()));
        x
    })
}

/// The element `sum c_i F.1^i` of `st` from coefficients in the context of
/// its ground field (integers for the prime field).
pub fn from_ground(st: &Rc<Struct>, cs: &[Elem]) -> Elem {
    let (r, f) = ff(st);
    let beta = gen1(r, f);
    let (dk, kimg) = match &f.ground {
        None => (1, Elem::one(&r.ctx).unwrap()),
        Some(g) => (degree(&g.field), find_emb(&g.field, st).expect("the ground field embeds")),
    };
    let mut acc = Elem::zero(&r.ctx);
    for c in cs.iter().rev() {
        acc = acc.mul(&beta).unwrap().add(&embed_with(c, dk, &kimg)).unwrap();
    }
    acc
}

// ----- element functions -------------------------------------------------------

/// The degree of `x` over the subfield of degree `e` (the number of its
/// conjugates), and the conjugates.
pub fn conjugates(x: &Elem, e: u64, n: u64) -> Vec<Elem> {
    let mut out = vec![x.clone()];
    if n == 1 {
        return out;
    }
    let mut y = x.fq_frobenius(e as i64).unwrap();
    while y.equal(x) != Truth::True && (out.len() as u64) < n {
        out.push(y.clone());
        y = y.fq_frobenius(e as i64).unwrap();
    }
    out
}

/// The monic polynomial with the given roots (coefficients, constant term
/// first).
pub fn poly_from_roots(rs: &[Elem], ctx: &Rc<Ctx>) -> Vec<Elem> {
    let mut c = vec![Elem::one(ctx).unwrap()];
    for r in rs {
        let mut next = vec![Elem::zero(ctx); c.len() + 1];
        for (i, a) in c.iter().enumerate() {
            next[i + 1] = next[i + 1].add(a).unwrap();
            next[i] = next[i].sub(&a.mul(r).unwrap()).unwrap();
        }
        c = next;
    }
    c
}

/// The minimal polynomial over GF(p), p a word, of an element x of a field
/// of degree d over it, as residues (constant term first): the first
/// linear dependency among the coordinates of 1, x, x^2, ..., found by
/// elimination over GF(p). This takes d products instead of d conjugates.
fn min_poly_prime(x: &Elem, p: u64, d: usize) -> Option<Vec<u64>> {
    let m = Nmod::new(p);
    // Rows in echelon form: the pivot, the coordinates and the combination
    // of powers of x that they are.
    let mut rows: Vec<(usize, Vec<u64>, Vec<u64>)> = Vec::with_capacity(d);
    let mut pw = Elem::one(x.ctx()).ok()?;
    for k in 0..=d {
        let mut v = pw.fq_coords_u64();
        let mut c = vec![0; k + 1];
        c[k] = 1;
        for (piv, rv, rc) in &rows {
            let a = v[*piv];
            if a != 0 {
                v.iter_mut().zip(rv).for_each(|(vi, &ri)| *vi = m.sub(*vi, m.mul(a, ri)));
                c.iter_mut().zip(rc).for_each(|(ci, &ri)| *ci = m.sub(*ci, m.mul(a, ri)));
            }
        }
        // A dependency: c is monic of degree k, as the rows have lower degrees.
        let Some(piv) = v.iter().position(|&a| a != 0) else { return Some(c) };
        let inv = m.inv(v[piv])?;
        v.iter_mut().for_each(|vi| *vi = m.mul(*vi, inv));
        c.iter_mut().for_each(|ci| *ci = m.mul(*ci, inv));
        rows.push((piv, v, c));
        pw = pw.mul(x).ok()?;
    }
    None
}

/// The minimal polynomial of `x` in `f` over the subfield `e`, with
/// coefficients in the context of `e`.
pub fn min_poly(x: &Elem, f: &Rc<Struct>, e: &Rc<Struct>) -> Option<Vec<Elem>> {
    if degree(e) == 1 && (2..=512).contains(&degree(f)) {
        if let Some(p) = ff(f).1.p.to_u64() {
            let cs = min_poly_prime(x, p, x.fq_coords_u64().len())?;
            let ectx = &ff(e).0.ctx;
            return Some(cs.into_iter().map(|c| Elem::from_word(ectx, c)).collect());
        }
    }
    let img = find_emb(e, f)?;
    let (fr, fd) = ff(f);
    let rs = conjugates(x, degree(e), fd.degree / degree(e));
    let cs = poly_from_roots(&rs, &fr.ctx);
    cs.iter().map(|c| restrict_with(c, e, &img, f)).collect()
}

/// The factorisation of q - 1 for the field `st`.
pub fn qm1_factors(st: &Struct) -> &[(Integer, u64)] {
    let f = ff(st).1;
    f.cache.qm1_factors.get_or_init(|| (&f.order() - &Integer::one()).factor().map(|fac| fac.factors).unwrap_or_default())
}

/// The primes dividing q - 1 for the field `st`.
pub fn qm1_primes(st: &Struct) -> &[Integer] {
    ff(st).1.cache.qm1_primes.get_or_init(|| qm1_factors(st).iter().map(|(p, _)| p.clone()).collect())
}

/// The product of some integers.
fn product(xs: &[Integer]) -> Integer {
    xs.iter().fold(Integer::one(), |a, b| &a * b)
}

/// Whether none of y^(P/r) is one, for P the product of the distinct
/// primes r of `rs`. The powers come from a product tree (raising y to the
/// product of one half of the primes gives the power for the other half),
/// which takes about log P log k squarings rather than k log P.
fn no_power_one(y: &Elem, rs: &[Integer]) -> bool {
    if rs.is_empty() {
        return true;
    }
    if y.is_one() == Truth::True {
        return false;
    }
    if rs.len() == 1 {
        return true;
    }
    let (l, r) = rs.split_at(rs.len() / 2);
    let pow = |e: &Integer| y.pow(e).expect("a power");
    no_power_one(&pow(&product(r)), l) && no_power_one(&pow(&product(l)), r)
}

/// The powers y^(P/m) for the pairwise coprime m of `ms`, P their product,
/// by the same product tree.
fn cofactor_powers(y: &Elem, ms: &[Integer], out: &mut Vec<Elem>) {
    if ms.len() <= 1 {
        out.extend(ms.iter().map(|_| y.clone()));
        return;
    }
    let (l, r) = ms.split_at(ms.len() / 2);
    cofactor_powers(&y.pow(&product(r)).expect("a power"), l, out);
    cofactor_powers(&y.pow(&product(l)).expect("a power"), r, out);
}

/// Whether `x` generates the multiplicative group of `st`.
pub fn is_primitive(st: &Struct, x: &Elem) -> bool {
    if x.is_zero() == Truth::True {
        return false;
    }
    if let (Some(k), Some(n)) = (x.zech_log(), Elem::zech_order(x.ctx())) {
        return calyx_flint::gcd_u64(k, n) == 1;
    }
    let q1 = &ff(st).1.order() - &Integer::one();
    let rs = qm1_primes(st);
    match x.pow(&q1.divexact(&product(rs))) {
        Ok(y) => no_power_one(&y, rs),
        Err(_) => false,
    }
}

/// The multiplicative order of a non-zero element: the product over the
/// prime powers r^e of q - 1 of the orders of x^((q - 1)/r^e).
pub fn mult_order(st: &Struct, x: &Elem) -> Integer {
    if let (Some(k), Some(n)) = (x.zech_log(), Elem::zech_order(x.ctx())) {
        return Integer::from_u64(n / calyx_flint::gcd_u64(k, n));
    }
    let fac = qm1_factors(st);
    let pps: Vec<Integer> = fac.iter().map(|(r, e)| r.pow(*e)).collect();
    let mut zs = Vec::with_capacity(pps.len());
    cofactor_powers(x, &pps, &mut zs);
    let mut ord = Integer::one();
    for ((r, _), mut z) in fac.iter().zip(zs) {
        while z.is_one() != Truth::True {
            z = z.pow(r).expect("a power");
            ord = &ord * r;
        }
    }
    ord
}

// ----- building fields -----------------------------------------------------------

fn coercion_map(domain: Value, codomain: Value) -> Value {
    use crate::value::{MapImpl, MapKind, MapObj};
    Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain, codomain, imp: MapImpl::Coercion }))
}

fn struct_of(v: &Value) -> Rc<Struct> {
    match v {
        Value::Struct(s) => s.clone(),
        _ => unreachable!("a structure"),
    }
}

impl Interp {
    /// The default field of order p^n as a structure.
    pub fn default_field(&mut self, p: &Integer, n: u64) -> RResult<Rc<Struct>> {
        Ok(struct_of(&self.finite_field(p, n)?))
    }

    fn new_field(&mut self, ff: FiniteField, ctx: Rc<Ctx>) -> Rc<Struct> {
        struct_of(&self.new_ring(RingKind::Finite(ff), ctx))
    }

    /// The field `F_p[x]/(f)` for a monic irreducible `f` of degree at least
    /// 2 (constant term first), with `F.1` a root of `f`.
    pub fn ff_from_poly(&mut self, p: &Integer, f: Vec<Integer>) -> RResult<Rc<Struct>> {
        let n = f.len() as u64 - 1;
        let conway = p.to_u64().and_then(|pw| calyx_flint::gr::conway_polynomial(pw, n)).is_some_and(|c| c == f);
        if !is_small(p, n) {
            return Ok(struct_of(&self.field_from_modulus(p, f, conway, false)?));
        }
        let d = self.default_field(p, n)?;
        let ctx = ff(&d).0.ctx.clone();
        let root = smallest(roots(&int_poly_in(&f, &ctx), &ctx)).ok_or_else(|| RuntimeError::runtime("Argument is not irreducible"))?;
        let g = (root.zech_log() != Some(1)).then_some(root);
        let pp = g.as_ref().is_none_or(|g| g.zech_log().is_some_and(|k| calyx_flint::gcd_u64(k, Elem::zech_order(&ctx).unwrap()) == 1));
        let mut field = FiniteField::new(p.clone(), n, f, conway, false, pp);
        field.generator = g;
        field.rep = Some(d);
        Ok(self.new_field(field, ctx))
    }

    /// The image of the generator of the context of `k` in the context of
    /// the default field `d` (whose degree is a multiple): the Conway
    /// embedding when both contexts are Conway, else a root.
    fn ctx_embedding(&mut self, k: &Rc<Struct>, d: &Rc<Struct>) -> RResult<Elem> {
        let ((kr, kf), (dr, df)) = (ff(k), ff(d));
        if kf.degree == 1 {
            return Ok(Elem::one(&dr.ctx)?);
        }
        if Rc::ptr_eq(&kr.ctx, &dr.ctx) {
            return Ok(dr.ctx.generator()?);
        }
        if ctx_conway(kf) && df.conway {
            return Ok(conway_image(&kf.p, kf.degree, &dr.ctx, df.degree));
        }
        smallest(roots(&int_poly_in(ctx_modulus(kf), &dr.ctx), &dr.ctx)).ok_or_else(|| RuntimeError::runtime("No embedding found"))
    }

    /// `ext<K | P>` for a monic irreducible polynomial P of degree at least
    /// 2 over a non-prime field K (coefficients in the context of K).
    pub fn ff_relative(&mut self, k: &Rc<Struct>, poly: Vec<Elem>) -> RResult<Rc<Struct>> {
        let (p, dk) = (ff(k).1.p.clone(), degree(k));
        let m = poly.len() as u64 - 1;
        let n = dk * m;
        let d = self.default_field(&p, n)?;
        let kimg = self.ctx_embedding(k, &d)?;
        let ctx = ff(&d).0.ctx.clone();
        let mapped: Vec<Elem> = poly.iter().map(|c| embed_with(c, dk, &kimg)).collect();
        let beta = smallest(roots(&mapped, &ctx)).ok_or_else(|| RuntimeError::runtime("Argument is not irreducible"))?;
        let pp = is_zech(&ctx) && is_primitive(&d, &beta);
        let mut field = FiniteField::new(p, n, Vec::new(), false, false, pp);
        field.generator = Some(beta);
        field.ground = Some(Ground { field: k.clone(), degree: m, poly });
        field.rep = Some(d);
        let l = self.new_field(field, ctx);
        register(k, &l, kimg);
        Ok(l)
    }

    /// `sub<F | d>`: the subfield of degree d (F itself, the prime field, a
    /// default field, or a new field generated by a power of the primitive
    /// element), and whether it is new.
    pub fn ff_sub_degree(&mut self, f: &Rc<Struct>, d: u64) -> RResult<Rc<Struct>> {
        let (r, fd) = ff(f);
        let (p, n) = (fd.p.clone(), fd.degree);
        if d == n {
            return Ok(f.clone());
        }
        if d == 1 || fd.default {
            return self.default_field(&p, d);
        }
        let _ = r;
        let pe = self.ff_primitive(f)?;
        let one = Integer::one();
        let c = (p.pow(n) - &one).divexact(&(p.pow(d) - &one));
        let g = pe.pow(&c)?;
        self.ff_sub_generated(f, &g, d)
    }

    /// The subfield of `f` generated by `x`, of degree `d` over the prime
    /// field, as a new field with `E.1` mapping to `x`.
    fn ff_sub_generated(&mut self, f: &Rc<Struct>, x: &Elem, d: u64) -> RResult<Rc<Struct>> {
        let p = ff(f).1.p.clone();
        let fp = self.default_field(&p, 1)?;
        let mp = min_poly(x, f, &fp).unwrap();
        let coeffs: Vec<Integer> = mp.iter().map(|c| c.to_integer().unwrap_or_default()).collect();
        debug_assert_eq!(coeffs.len() as u64, d + 1);
        let e = self.ff_from_poly(&p, coeffs)?;
        let img = gen_image_from(&e, x).ok_or_else(|| RuntimeError::runtime("No embedding found"))?;
        register(&e, f, img);
        Ok(e)
    }

    /// `sub<F | x>`: the subfield generated by x (F itself if x generates
    /// F, the prime field if x lies in it).
    pub fn ff_sub_elt(&mut self, f: &Rc<Struct>, x: &Elem) -> RResult<Rc<Struct>> {
        let fd = ff(f).1;
        let (p, n) = (fd.p.clone(), fd.degree);
        let k = conjugates(x, 1, n).len() as u64;
        if k == n {
            return Ok(f.clone());
        }
        if k == 1 {
            return self.default_field(&p, 1);
        }
        self.ff_sub_generated(f, x, k)
    }

    /// `ext<K | n>`: a default field for default K, else the extension by
    /// an irreducible polynomial of degree n over K.
    pub fn ff_ext_degree(&mut self, k: &Rc<Struct>, n: u64) -> RResult<Rc<Struct>> {
        let kf = ff(k).1;
        if n == 1 {
            return Ok(k.clone());
        }
        if kf.default {
            let (p, d) = (kf.p.clone(), kf.degree);
            return self.default_field(&p, d * n);
        }
        let poly = self.ff_irreducible(k, n)?;
        self.ff_relative(k, poly)
    }

    /// An irreducible polynomial of degree n over the non-prime field `k`:
    /// the first of the form `x^n + a x^t + b` for increasing t, with a and
    /// b in the order of the elements of `k`.
    pub fn ff_irreducible(&mut self, k: &Rc<Struct>, n: u64) -> RResult<Vec<Elem>> {
        let (kr, kf) = ff(k);
        let ctx = kr.ctx.clone();
        let size = kf.order().to_u64().unwrap_or(u64::MAX).min(1 << 12);
        let elems: Vec<Elem> = (0..size).map(|i| nth_elem(&ctx, kf, i)).collect();
        let px = Ctx::poly(&ctx);
        let one = Elem::one(&ctx)?;
        for t in 0..n {
            for a in &elems {
                if (t == 0) != (a.is_zero() == Truth::True) {
                    continue;
                }
                for b in elems.iter().skip(1) {
                    let mut cs = vec![Elem::zero(&ctx); n as usize + 1];
                    cs[n as usize] = one.clone();
                    cs[0] = b.clone();
                    if t > 0 {
                        cs[t as usize] = a.clone();
                    }
                    if Elem::poly_from_coeffs(&px, &cs)?.poly_is_irreducible()? {
                        return Ok(cs);
                    }
                }
            }
        }
        Err(RuntimeError::runtime("No irreducible polynomial found"))
    }

    /// `ext<K | n>` and `ext<K | P>`, with the embedding of K.
    pub fn ff_ext_constructor(&mut self, k: &Rc<Struct>, x: &Value) -> RResult<Vec<Value>> {
        let err = |m: &str| RuntimeError::runtime(m.to_string()).in_context("ext< ... >");
        let kv = Value::Struct(k.clone());
        let l = match x {
            Value::Int(n) => {
                let n = n.to_u64().filter(|&n| n > 0 && n < 1 << 30).ok_or_else(|| err("Extension degree should be a small integer greater than 0"))?;
                self.ff_ext_degree(k, n)?
            }
            Value::Elt(e) if matches!(e.ring().kind, RingKind::UPoly { .. }) => {
                let base = e.ring().base().unwrap().clone();
                let mut cs = Vec::with_capacity(e.x.poly_len());
                for i in 0..e.x.poly_len() {
                    let c = self.elem_to_value(&base, e.x.poly_coeff(i));
                    let c = self.to_structure_elem(&kv, &c, true)?.ok_or_else(|| err("Bad argument types"))?;
                    cs.push(c);
                }
                if cs.len() < 2 {
                    return Err(err("Degree of polynomial must be >= 2"));
                }
                if cs.last().unwrap().is_one() != Truth::True {
                    return Err(err("Argument 1 is not monic"));
                }
                if cs.len() == 2 {
                    k.clone()
                } else {
                    let px = Ctx::poly(&ff(k).0.ctx);
                    if !Elem::poly_from_coeffs(&px, &cs)?.poly_is_irreducible()? {
                        return Err(err("Argument is not irreducible"));
                    }
                    if degree(k) == 1 {
                        let p = ff(k).1.p.clone();
                        self.ff_from_poly(&p, cs.iter().map(|c| c.to_integer().unwrap_or_default()).collect())?
                    } else {
                        self.ff_relative(k, cs)?
                    }
                }
            }
            _ => return Err(err("Bad argument types")),
        };
        let lv = Value::Struct(l);
        Ok(vec![lv.clone(), coercion_map(kv, lv)])
    }

    /// `sub<F | d>` and `sub<F | x>`, with the embedding into F.
    pub fn ff_sub_constructor(&mut self, f: &Rc<Struct>, right: &[Value]) -> RResult<Vec<Value>> {
        let err = |m: String| RuntimeError::runtime(m).in_context("sub< ... >");
        let n = degree(f);
        let fv = Value::Struct(f.clone());
        let e = match right {
            [Value::Int(d)] => {
                if d.sign() <= 0 {
                    return Err(err("RHS argument 1 should be positive".into()));
                }
                let d = d.to_u64().filter(|d| n % d == 0).ok_or_else(|| err(format!("RHS argument 2 ({d}) is not a divisor of the degree of LHS ({n})")))?;
                self.ff_sub_degree(f, d)?
            }
            [x] => {
                let x = self.to_structure_elem(&fv, x, false)?.ok_or_else(|| err("Rhs argument 1 is invalid for this constructor".into()))?;
                self.ff_sub_elt(f, &x)?
            }
            _ => return Err(err("Bad argument types".into())),
        };
        let ev = Value::Struct(e);
        Ok(vec![ev.clone(), coercion_map(ev, fv)])
    }

    /// `Embed(E, F)` and `Embed(E, F, x)`.
    pub fn ff_embed_fields(&mut self, e: &Rc<Struct>, f: &Rc<Struct>, x: Option<&Value>) -> RResult<()> {
        let ((_, ef), (_, fd)) = (ff(e), ff(f));
        if ef.p != fd.p {
            return Err(RuntimeError::runtime("Arguments 1 and 2 have different characteristics"));
        }
        if fd.degree % ef.degree != 0 {
            return Err(RuntimeError::runtime("Degree of argument 1 does not divide degree of argument 2"));
        }
        if is_subfield(e, f) {
            if x.is_some() {
                return Err(RuntimeError::runtime("Argument 1 is already a subfield of argument 2"));
            }
            return Ok(());
        }
        let x = match x {
            Some(v) => {
                let fv = Value::Struct(f.clone());
                // Reported like a failed coercion, without the blank line.
                let failed = || RuntimeError::from(crate::error::ErrorInfo { style: crate::error::ErrStyle::Plain, ..crate::error::ErrorInfo::runtime("No embedding known into LHS field") });
                Some(self.to_structure_elem(&fv, v, false)?.ok_or_else(failed)?)
            }
            None => None,
        };
        let ((er, ef), (fr, fd)) = (ff(e), ff(f));
        let p = ef.p.clone();
        let fp = self.default_field(&p, 1)?;
        let g1 = gen1(er, ef);
        let def = min_poly(&g1, e, &fp).ok_or_else(|| RuntimeError::runtime("Argument 1 is not generated by its generator"))?;
        let def: Vec<Integer> = def.iter().map(|c| c.to_integer().unwrap_or_default()).collect();
        let image = match &x {
            Some(x) => {
                let mp: Vec<Integer> = min_poly(x, f, &fp).unwrap().iter().map(|c| c.to_integer().unwrap_or_default()).collect();
                if mp != def {
                    return Err(RuntimeError::runtime(
                        "Minimal polynomial of argument 3 over the prime field is not equal to the defining polynomial of argument 1 over the prime field",
                    ));
                }
                gen_image_from(e, x).ok_or_else(|| RuntimeError::runtime("Argument 1 is not generated by its generator"))?
            }
            None => {
                // Prefer the Conway embedding of the contexts; otherwise the
                // first root compatible with the known subfields.
                let fctx = fr.ctx.clone();
                let mut cands = Vec::new();
                if ctx_conway(ef) && ctx_conway(fd) {
                    cands.push(conway_image(&p, ef.degree, &fctx, fd.degree));
                }
                let mut rs = roots(&int_poly_in(&def, &fctx), &fctx);
                rs.sort_by(elt_order);
                cands.extend(rs.iter().filter_map(|r| gen_image_from(e, r)));
                cands.into_iter().find(|c| compatible(e, f, c)).ok_or_else(|| RuntimeError::runtime("No compatible embedding exists"))?
            }
        };
        register(e, f, image);
        Ok(())
    }

    /// `PrimitiveElement(F)`: `F.1` if it is primitive, else for small
    /// fields the generator of their context, else the first primitive
    /// element counting coordinates over the prime field from `F.1`.
    pub fn ff_primitive(&mut self, st: &Rc<Struct>) -> RResult<Elem> {
        let (r, f) = ff(st);
        if let Some(x) = f.cache.primitive.borrow().as_ref() {
            return Ok(x.clone());
        }
        let x = if f.degree == 1 {
            let root = crate::intrinsics::ints::primitive_root(&f.p).unwrap_or_default();
            Elem::from_integer(&r.ctx, &root)?
        } else {
            let g1 = gen1(r, f);
            if is_primitive(st, &g1) {
                g1
            } else if is_zech(&r.ctx) {
                r.ctx.generator()?
            } else {
                f.cache.primitive_fixed.set(true);
                let p = &f.p;
                let n = f.degree as usize;
                let mut counter = p.clone();
                let mut found = None;
                for _ in 0..1_000_000 {
                    let mut c = counter.clone();
                    let mut coords = Vec::with_capacity(n);
                    for _ in 0..n {
                        let (q, rem) = c.div_rem_euclid(p).unwrap();
                        coords.push(rem);
                        c = q;
                    }
                    let cand = self.ff_from_flat(st, &coords)?;
                    if is_primitive(st, &cand) {
                        found = Some(cand);
                        break;
                    }
                    counter = &counter + &Integer::one();
                }
                found.ok_or_else(|| RuntimeError::runtime("No primitive element found"))?
            }
        };
        *f.cache.primitive.borrow_mut() = Some(x.clone());
        Ok(x)
    }

    /// The element with the given flattened coordinates over the ground
    /// field (see `ground_coords`).
    pub fn ff_from_flat(&mut self, st: &Rc<Struct>, coords: &[Integer]) -> RResult<Elem> {
        let f = ff(st).1;
        let cs: Vec<Elem> = match &f.ground {
            None => {
                let fp = prime_ctx(&f.p);
                coords.iter().map(|c| Elem::from_integer(&fp, c).unwrap()).collect()
            }
            Some(g) => {
                let (kr, kf) = ff(&g.field);
                let d = kf.degree as usize;
                (0..g.degree as usize).map(|i| Coords::B(coords[i * d..(i + 1) * d].to_vec()).to_elem(&kr.ctx)).collect()
            }
        };
        Ok(from_ground(st, &cs))
    }

    /// A field containing both `a` and `b` for arithmetic between their
    /// elements: one of them, a known field containing both, or the default
    /// field of the combined degree when both lie in default fields.
    pub fn ff_cover(&mut self, a: &Rc<Struct>, b: &Rc<Struct>) -> RResult<Option<Rc<Struct>>> {
        let ((_, af), (_, bf)) = (ff(a), ff(b));
        if af.p != bf.p {
            return Ok(None);
        }
        if is_subfield(b, a) {
            return Ok(Some(a.clone()));
        }
        if is_subfield(a, b) {
            return Ok(Some(b.clone()));
        }
        // The smallest common overfield, not through links found between
        // subfields.
        let direct = |x: &Rc<Struct>, o: &Rc<Struct>| linked_side(id(x), o).map_or_else(|| is_subfield(x, o), |(_, side)| !side);
        let mut best: Option<Rc<Struct>> = None;
        for (x, y) in [(a, b), (b, a)] {
            for o in overs_of(x) {
                if direct(x, &o) && direct(y, &o) && best.as_ref().is_none_or(|c| degree(c) > degree(&o)) {
                    best = Some(o);
                }
            }
        }
        if best.is_some() {
            return Ok(best);
        }
        if anchored(a) && anchored(b) {
            let p = af.p.clone();
            let (da, db) = (af.degree, bf.degree);
            // The defaults of the sizes of a and b hold their anchors.
            self.default_field(&p, da)?;
            self.default_field(&p, db)?;
            let l = Integer::from_u64(da).lcm(&Integer::from_u64(db)).to_u64().unwrap();
            return Ok(Some(self.default_field(&p, l)?));
        }
        Ok(None)
    }

    /// The image of the generator of the context of `e` in `f`, through a
    /// known embedding or by identifying `e` with the default field of its
    /// size when `f` is a default field.
    pub fn ff_emb_image(&mut self, e: &Rc<Struct>, f: &Rc<Struct>) -> RResult<Option<Elem>> {
        if let Some(i) = find_emb(e, f) {
            return Ok(Some(i));
        }
        let ((_, ef), (_, fd)) = (ff(e), ff(f));
        if !fd.default || ef.p != fd.p || fd.degree % ef.degree != 0 || !anchored(e) {
            return Ok(None);
        }
        let p = ef.p.clone();
        let d = self.default_field(&p, ef.degree)?;
        let Some(a) = anchor(e, &d) else { return Ok(None) };
        let Some(c) = default_emb(&d, f) else { return Ok(None) };
        Ok(Some(embed_with(&a, ef.degree, &c)))
    }

    /// `x in F` for an element of a finite field.
    pub fn ff_contains(&mut self, f: &Rc<Struct>, x: &super::Elt) -> RResult<bool> {
        let g = x.parent.clone();
        if self.ff_cover(&g, f)?.is_none() {
            return Err(RuntimeError::runtime("Arguments have no covering structure"));
        }
        Ok(self.ff_convert(&x.x, &g, f)?.is_some())
    }

    /// `x` (an element of `e`) as an element of `f`: an embedding, a
    /// restriction, or both through a field containing both.
    /// `Ok(None)` when there is no such element.
    pub fn ff_convert(&mut self, x: &Elem, e: &Rc<Struct>, f: &Rc<Struct>) -> RResult<Option<Elem>> {
        if let Some(img) = self.ff_emb_image(e, f)? {
            return Ok(Some(embed_with(x, degree(e), &img)));
        }
        if let Some(img) = self.ff_emb_image(f, e)? {
            return Ok(restrict_with(x, f, &img, e));
        }
        let Some(c) = self.ff_cover(e, f)? else { return Ok(None) };
        let (Some(ie), Some(if_)) = (self.ff_emb_image(e, &c)?, self.ff_emb_image(f, &c)?) else { return Ok(None) };
        // A coercion between registered subfields of a field relates them.
        if degree(f) % degree(e) == 0 && linked(id(e), &c).is_some() && linked(id(f), &c).is_some() {
            if let Some(img) = restrict_with(&ie, f, &if_, &c) {
                register(e, f, img);
            }
        }
        let y = embed_with(x, degree(e), &ie);
        Ok(restrict_with(&y, f, &if_, &c))
    }
}

/// The i-th element of a field in Magma's order: zero, then the powers of
/// the primitive element for small fields, else by coordinates.
pub fn nth_elem(ctx: &Rc<Ctx>, f: &FiniteField, i: u64) -> Elem {
    if i == 0 {
        return Elem::zero(ctx);
    }
    if is_zech(ctx) {
        return Elem::fq_from_zech_log(ctx, i - 1).unwrap();
    }
    let p = f.p.to_u64().unwrap_or(u64::MAX);
    let mut c = i;
    let mut coords = Vec::with_capacity(f.degree as usize);
    for _ in 0..f.degree {
        coords.push(if p == u64::MAX { c } else { c % p });
        c = if p == u64::MAX { 0 } else { c / p };
    }
    Elem::fq_from_coords_u64(ctx, &coords)
}

/// The image of the generator of the context of `e` when `F.1` maps to
/// `x`, if `F.1` generates `e` over the prime field.
fn gen_image_from(e: &Rc<Struct>, x: &Elem) -> Option<Elem> {
    let (r, f) = ff(e);
    if f.generator.is_none() && f.ground.is_none() {
        return Some(x.clone());
    }
    // Coordinates of the context generator in the powers of F.1.
    let g1 = gen1(r, f);
    let n = f.degree as usize;
    let mut cols = Vec::with_capacity(n);
    let mut pw = Elem::one(&r.ctx).ok()?;
    for _ in 0..n {
        cols.push(Coords::of(&pw));
        pw = pw.mul(&g1).ok()?;
    }
    let m = LinMap::from_columns(&f.p, &cols, n).inverse()?;
    let h = m.apply(&Coords::of(&r.ctx.generator().ok()?)).integers();
    let to = x.ctx();
    let mut acc = Elem::zero(to);
    for c in h.iter().rev() {
        acc = acc.mul(x).ok()?.add(&Elem::from_integer(to, c).ok()?).ok()?;
    }
    Some(acc)
}

/// Whether sending the generator of the context of `e` to `image` in `f`
/// agrees with the known embeddings of the subfields of `e` into `f`.
fn compatible(e: &Rc<Struct>, f: &Rc<Struct>, image: &Elem) -> bool {
    let de = degree(e);
    let mut subs = subs_of(e);
    subs.extend(subs_of(f));
    subs.iter().all(|(s, _)| match (find_emb(s, e), find_emb(s, f)) {
        (Some(se), Some(sf)) => embed_with(&se, de, image).equal(&sf) == Truth::True,
        _ => true,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(n: u64) -> Integer {
        Integer::from_u64(n)
    }

    #[test]
    fn sibling_subfields_meet_in_their_field() {
        let mut it = Interp::new();
        let p = int(7);
        // x^4 + x + 1 is irreducible over GF(7).
        let g = it.ff_from_poly(&p, vec![int(1), int(1), int(0), int(0), int(1)]).unwrap();
        let (e1, e2) = (it.ff_sub_degree(&g, 2).unwrap(), it.ff_sub_degree(&g, 2).unwrap());
        assert_eq!(field_eq(&e1, &e2), Ok(true));
        assert!(!is_subfield(&e1, &e2));
        assert_eq!(id(&it.ff_cover(&e1, &e2).unwrap().unwrap()), id(&g));
        // A coercion relates them.
        let x = gen1(ff(&e1).0, ff(&e1).1);
        assert!(it.ff_convert(&x, &e1, &e2).unwrap().is_some());
        assert_eq!(id(&it.ff_cover(&e1, &e2).unwrap().unwrap()), id(&e2));
    }

    #[test]
    fn default_embeddings_beyond_conway_polynomials_commute() {
        let mut it = Interp::new();
        let p = int(7);
        let (a, b, c) = (it.default_field(&p, 72).unwrap(), it.default_field(&p, 24).unwrap(), it.default_field(&p, 12).unwrap());
        let x = ff(&c).0.ctx.generator().unwrap();
        let via = embed(&embed(&x, &c, &b).unwrap(), &b, &a).unwrap();
        assert_eq!(via.equal(&embed(&x, &c, &a).unwrap()), Truth::True);
    }
}
