//! Affine algebras (the handbook's Affine Algebras chapter): the quotients
//! P/J of a multivariate polynomial ring P by an ideal J, rings of type
//! RngMPolRes (`RingKind::MPolyRes`).
//!
//! An element is the normal form of a polynomial of P modulo the reduced
//! Gröbner basis of J in P's order, kept in P's context: sums need nothing
//! more, products and powers are reduced, inverses come from a Gröbner
//! basis with one more variable, and other quotients from linear algebra
//! on the monomial basis. J is the quotient's own copy of the ideal
//! given, whose basis Magma prints as the "quotient relations": as given
//! until an element needs the Gröbner basis, which then replaces it (so
//! naming the generators, which makes them, computes it).
//!
//! The ideals of an affine algebra Q have Q's type, RngMPolRes, as in Magma,
//! where Q is its own unit ideal. They keep their generating basis as given
//! and answer the rest through their preimages in P.

use std::cell::{OnceCell, RefCell};
use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{Elem, Truth};
use calyx_flint::mpoly as fm;
use calyx_groebner::{self as gb, Order, Terms};
use calyx_syntax::ast::BinOp;

use crate::intrinsics::groebner::{engine, shape, terms};
use super::{MPolIdeal, coercion_map, fmt_basis, generators, ideal_parts, ideal_subset, ideals_equal};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::{arg_ge, bare, boolv, intv, none, one, require};
use crate::print::{Level, Printer};
use crate::rings::{Ring, RingKind, make_elt, ring_of};
use crate::value::*;

/// The affine algebra P/J.
pub struct Affine {
    /// The polynomial ring P.
    pub preimage: Rc<Struct>,
    /// The ideal J of P, a structure of kind `MPolIdeal`.
    pub ideal: Rc<Struct>,
    /// The reduced Gröbner basis of J in P's order, as terms, once computed.
    basis: OnceCell<Rc<[Terms]>>,
}

impl Affine {
    /// P, as a ring.
    pub fn poly_ring(&self) -> &Ring {
        match &self.preimage.kind {
            StructKind::Ring(r) => r,
            _ => unreachable!("a polynomial ring"),
        }
    }

    /// The ideal J.
    pub fn divisor(&self) -> &Rc<MPolIdeal> {
        match &self.ideal.kind {
            StructKind::MPolIdeal(id) => id,
            _ => unreachable!("an ideal"),
        }
    }

    /// The monomial order of P.
    pub fn order(&self) -> &Order {
        shape(self.poly_ring()).2
    }

    /// The reduced Gröbner basis of J, computed once (it then becomes the
    /// basis of J).
    fn groebner(&self) -> RResult<Rc<[Terms]>> {
        if let Some(g) = self.basis.get() {
            return Ok(g.clone());
        }
        let g: Rc<[Terms]> = self.divisor().groebner()?.iter().map(terms).collect();
        Ok(self.basis.get_or_init(|| g).clone())
    }

    /// Whether J is the whole of P (P/J is the zero ring).
    fn is_zero_ring(&self) -> RResult<bool> {
        Ok(matches!(&*self.groebner()?, [t] if is_constant_terms(t)))
    }

    /// The normal form of `x`, a polynomial of P, modulo J.
    pub fn reduce(&self, x: Elem) -> RResult<Elem> {
        let g = self.groebner()?;
        if x.mpoly_len() == 0 || g.is_empty() {
            return Ok(x);
        }
        let r = self.poly_ring();
        let (base, n, order) = shape(r);
        let nf = engine(r, gb::normal_form(base, n, order, &terms(&x), &g))?;
        Ok(Elem::mpoly_from_terms(&r.ctx, &nf)?)
    }

    /// The constant `c` of the coefficient ring, reduced.
    fn constant(&self, c: &Elem) -> RResult<Elem> {
        let mut e = Elem::zero(&self.poly_ring().ctx);
        Elem::mpoly_set_scalar(&mut e, c)?;
        self.reduce(e)
    }

    /// Magma finds inverses and quotients by linear algebra, in algebras of
    /// finite dimension only.
    fn need_finite(&self) -> RResult<()> {
        match self.finite_dimensional()? {
            true => Ok(()),
            false => Err(RuntimeError::runtime("Quotient does not have finite dimension")),
        }
    }

    /// Whether P/J has finite dimension over the coefficient field: each
    /// variable has a pure power among the leading monomials of J (or J is
    /// P, whose leading monomial 1 counts for all).
    fn finite_dimensional(&self) -> RResult<bool> {
        let g = self.groebner()?;
        let n = shape(self.poly_ring()).1;
        let pure = |i: usize| g.iter().any(|t| t[0].1.iter().enumerate().all(|(j, &k)| k == 0 || j == i));
        Ok((0..n).all(pure))
    }

    /// The inverse of `x`, an element of P/J (of finite dimension), if it is
    /// a unit (in the zero ring, as in Magma, nothing is). When it is, the
    /// reduced Gröbner basis of J + (x t - 1) in P[t], for grevlex on t and
    /// then on the variables of P, has an element t - g, and g is the
    /// inverse modulo J; a unit modulo J : x^∞ only has one too, so the
    /// inverse is checked.
    pub fn inverse(&self, x: &Elem) -> RResult<Option<Elem>> {
        self.need_finite()?;
        if self.is_zero_ring()? || x.mpoly_len() == 0 {
            return Ok(None);
        }
        let r = self.poly_ring();
        let (base, n, _) = shape(r);
        if x.mpoly_len() == 1 {
            let (c, e) = x.mpoly_term(0);
            if e.iter().all(|&k| k == 0) {
                return match c.is_invertible() {
                    Truth::True => Ok(Some(self.constant(&c.inv()?)?)),
                    _ => Ok(None),
                };
            }
        }
        let lift = |t: &Terms, k: u64| -> Terms { t.iter().map(|(c, e)| (c.clone(), std::iter::once(k).chain(e.iter().copied()).collect())).collect() };
        let mut gens: Vec<Terms> = self.groebner()?.iter().map(|t| lift(t, 0)).collect();
        let mut xt = lift(&terms(x), 1);
        xt.push((Elem::one(base)?.neg()?, vec![0; n + 1]));
        gens.push(xt);
        let h = engine(r, gb::groebner(base, n + 1, &Order::ElimK(1), &gens))?;
        let t: Vec<u64> = std::iter::once(1).chain(std::iter::repeat_n(0, n)).collect();
        let Some(p) = h.iter().find(|p| p.first().is_some_and(|(_, e)| *e == t)) else { return Ok(None) };
        let g: Terms = p[1..].iter().map(|(c, e)| Ok((c.neg()?, e[1..].to_vec()))).collect::<RResult<_>>()?;
        let y = self.reduce(Elem::mpoly_from_terms(&r.ctx, &g)?)?;
        let check = self.reduce(x.mul(&y)?)?;
        Ok((check.is_one() == Truth::True).then_some(y))
    }

    /// `x^k` for an element x of P/J (`k < 0` for units).
    pub fn pow(&self, x: &Elem, k: &Integer) -> RResult<Elem> {
        let (mut b, k) = if k.sign() < 0 {
            match self.inverse(x).map_err(|e| e.in_context("^"))? {
                Some(y) => (y, -k),
                None => return Err(RuntimeError::runtime("Argument 1 is not invertible").in_context("^")),
            }
        } else {
            (x.clone(), k.clone())
        };
        let mut acc = self.constant(&Elem::one(self.poly_ring().ctx.base().expect("a polynomial ring"))?)?;
        let bits = k.bits();
        for i in 0..bits {
            if !k.bitand(&Integer::one().mul_2exp(i)).is_zero() {
                acc = self.reduce(acc.mul(&b)?)?;
            }
            if i + 1 < bits {
                b = self.reduce(b.mul(&b)?)?;
            }
        }
        Ok(acc)
    }

    /// `x / y` for elements of P/J, as Magma computes it (in an algebra of
    /// finite dimension): `x` times the inverse of `y`, or else the exact
    /// quotient of the polynomials, or else a solution of `q y = x`.
    pub fn divide(&self, x: &Elem, y: &Elem) -> RResult<Elem> {
        self.need_finite()?;
        if y.mpoly_len() == 0 {
            return Err(RuntimeError::runtime("Argument 2 is not a unit"));
        }
        if let Some(z) = self.inverse(y)? {
            return self.reduce(x.mul(&z)?);
        }
        if let Ok(Some(q)) = fm::divides(x, y) {
            return self.reduce(q);
        }
        self.solve(x, y)?.ok_or_else(|| RuntimeError::runtime("Element is not divisible by other element"))
    }

    /// A solution q of `q y = x` in P/J (of finite dimension), by linear
    /// algebra on the coordinates in the monomial basis: the images of the
    /// basis monomials, from the largest, that are independent of those
    /// before them carry the solution (as the quotients Magma gives show).
    fn solve(&self, x: &Elem, y: &Elem) -> RResult<Option<Elem>> {
        let r = self.poly_ring();
        let base = r.ctx.base().expect("a polynomial ring").clone();
        let Some(mut ms) = standard_monomials(self)? else { return Ok(None) };
        ms.reverse();
        let d = ms.len();
        let index: std::collections::HashMap<&[u64], usize> = ms.iter().enumerate().map(|(i, m)| (m.as_slice(), i)).collect();
        let coords = |f: &Elem| -> RResult<Vec<Elem>> {
            let mut v = vec![Elem::zero(&base); d];
            for (c, e) in terms(f) {
                v[index[e.as_slice()]] = c;
            }
            Ok(v)
        };
        let unit = Elem::one(&base)?;
        // Reduced columns, each with its pivot (a coordinate where it is 1
        // and the later columns 0) and the combination of the original
        // columns that makes it.
        let mut reduced: Vec<(usize, Vec<Elem>, Vec<Elem>)> = Vec::new();
        let axpy = |v: &mut [Elem], a: &Elem, w: &[Elem]| -> RResult<()> {
            for (x, y) in v.iter_mut().zip(w) {
                if y.is_zero() != Truth::True {
                    *x = x.sub(&a.mul(y)?)?;
                }
            }
            Ok(())
        };
        for (j, m) in ms.iter().enumerate() {
            let mono = Elem::mpoly_from_terms(&r.ctx, &[(unit.clone(), m.clone())])?;
            let mut v = coords(&self.reduce(y.mul(&mono)?)?)?;
            let mut combo = vec![Elem::zero(&base); d];
            combo[j] = unit.clone();
            for (p, w, c) in &reduced {
                let a = v[*p].clone();
                if a.is_zero() != Truth::True {
                    axpy(&mut v, &a, w)?;
                    axpy(&mut combo, &a, c)?;
                }
            }
            let Some(p) = v.iter().position(|c| c.is_zero() != Truth::True) else { continue };
            let inv = v[p].inv()?;
            let v: Vec<Elem> = v.iter().map(|c| c.mul(&inv)).collect::<Result<_, _>>()?;
            let combo: Vec<Elem> = combo.iter().map(|c| c.mul(&inv)).collect::<Result<_, _>>()?;
            reduced.push((p, v, combo));
        }
        let mut b = coords(x)?;
        let mut q = vec![Elem::zero(&base); d];
        for (p, w, c) in &reduced {
            let a = b[*p].clone();
            if a.is_zero() != Truth::True {
                axpy(&mut b, &a, w)?;
                let neg = a.neg()?;
                axpy(&mut q, &neg, c)?;
            }
        }
        if b.iter().any(|c| c.is_zero() != Truth::True) {
            return Ok(None);
        }
        let ts: Terms = q.into_iter().zip(ms).filter(|(c, _)| c.is_zero() != Truth::True).collect();
        Ok(Some(Elem::mpoly_from_terms(&r.ctx, &ts)?))
    }
}

/// Whether a polynomial as terms is a non-zero constant.
fn is_constant_terms(t: &Terms) -> bool {
    matches!(t.as_slice(), [(_, e)] if e.iter().all(|&k| k == 0))
}

/// The affine algebra of a ring.
pub fn affine_of(r: &Ring) -> Option<&Rc<Affine>> {
    match &r.kind {
        RingKind::MPolyRes { affine, .. } => Some(affine),
        _ => None,
    }
}

/// Argument `i`, an affine algebra or an ideal of one (which answers for the
/// algebra): the algebra and its data.
fn affine_arg(a: &CallArgs, i: usize) -> (Rc<Struct>, Rc<Affine>) {
    let (q, _) = aff_operand(&a.args[i]).expect("an affine algebra or ideal");
    let affine = algebra_affine(&q).clone();
    (q, affine)
}

fn elt_arg(a: &CallArgs, i: usize) -> Rc<crate::rings::Elt> {
    match &a.args[i] {
        Value::Elt(e) => e.clone(),
        _ => unreachable!("an element of an affine algebra"),
    }
}

// ----- construction ----------------------------------------------------------------

/// The quotient of the multivariate polynomial ring `p` by the ideal
/// generated by `gens`, with the names of the variables of `p`.
pub fn quotient(it: &mut Interp, p: &Rc<Struct>, gens: Vec<Elem>) -> Value {
    let ideal = Struct::new(StructKind::MPolIdeal(Rc::new(MPolIdeal::new(p.clone(), gens, false))));
    it.mpoly_res(p, Rc::new(Affine { preimage: p.clone(), ideal, basis: OnceCell::new() }))
}

/// `quo<P | ...>` for a multivariate polynomial ring P: the quotient by the
/// ideal generated as by `ideal<P | ...>`, and the quotient map. For an
/// affine algebra P/J, the quotient of P by J and the relations (ideals of
/// P/J bring their preimages), with the names of P, as Magma makes it.
pub fn quo_constructor(it: &mut Interp, base: &Value, right: &[Value], _map: bool) -> RResult<Option<Vec<Value>>> {
    if let Some((q, None)) = aff_operand(base) {
        let affine = algebra_affine(&q).clone();
        let mut gens = affine.divisor().basis();
        for item in aff_items(it, &q, right, "quo< ... >")? {
            match item {
                Item::Elt(f) => gens.push(f),
                Item::Ideal(Some(id)) => gens.extend(id.preimage_ideal().basis()),
                Item::Ideal(None) => gens.push(Elem::one(&affine.poly_ring().ctx)?),
            }
        }
        let x = quotient(it, &affine.preimage, gens);
        let map = MapObj { kind: MapKind::Map, domain: base.clone(), codomain: x.clone(), imp: MapImpl::Native(Rc::new(QuoMap)) };
        return Ok(Some(vec![x, Value::Map(Rc::new(map))]));
    }
    let Some((pst, _)) = ring_of(base).filter(|(_, r)| matches!(r.kind, RingKind::MPoly { .. })) else { return Ok(None) };
    let pst = pst.clone();
    let gens = generators(it, &pst, right, "quo< ... >")?;
    let q = quotient(it, &pst, gens);
    Ok(Some(vec![q.clone(), coercion_map(base.clone(), q)]))
}

/// The affine algebra of the multivariate polynomial ring `p` with the
/// relations `relations` (elements of `p`, ideals of it, and sets and
/// sequences of these, as in `quo<P | ...>`); the entry point of
/// `AffineAlgebra< R, X | L >`, whose names are those of `p`.
pub fn affine_algebra(it: &mut Interp, p: &Value, relations: &[Value]) -> RResult<Value> {
    let Some((pst, _)) = ring_of(p).filter(|(_, r)| matches!(r.kind, RingKind::MPoly { .. })) else {
        return Err(RuntimeError::runtime("A multivariate polynomial ring is needed").in_context("AffineAlgebra< ... >"));
    };
    let pst = pst.clone();
    let gens = generators(it, &pst, relations, "AffineAlgebra< ... >")?;
    Ok(quotient(it, &pst, gens))
}

/// `P / J` for an ideal J of P (or P itself).
pub fn quotient_of(it: &mut Interp, p: &Rc<Struct>, j: &Option<Rc<MPolIdeal>>) -> RResult<Value> {
    let gens = match j {
        Some(id) => id.basis(),
        None => vec![Elem::one(&shape_ring(p).ctx)?],
    };
    Ok(quotient(it, p, gens))
}

fn shape_ring(p: &Rc<Struct>) -> &Ring {
    match &p.kind {
        StructKind::Ring(r) => r,
        _ => unreachable!("a polynomial ring"),
    }
}

/// Whether two affine algebras are equal: quotients of one ring by equal
/// ideals.
pub fn algebras_equal(a: &Affine, b: &Affine) -> RResult<bool> {
    if Rc::ptr_eq(&a.ideal, &b.ideal) {
        return Ok(true);
    }
    if !struct_eq(&a.preimage, &b.preimage) {
        return Ok(false);
    }
    ideals_equal(&Some(a.divisor().clone()), &Some(b.divisor().clone()))
}

/// The map from an affine algebra onto a quotient of it.
struct QuoMap;

impl NativeMap for QuoMap {
    fn apply(&self, it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        let x = it.coerce(&m.domain, x).map_err(|_| RuntimeError::runtime("Element is not in the domain of the map").in_context("map application"))?;
        let (Value::Elt(e), Value::Struct(c)) = (&x, &m.codomain) else { unreachable!("an element and an affine algebra") };
        Ok(make_elt(c, algebra_affine(c).reduce(e.x.clone())?))
    }

    fn preimage(&self, it: &mut Interp, m: &MapObj, y: &Value) -> RResult<Value> {
        let y = it.coerce(&m.codomain, y).map_err(|_| RuntimeError::runtime("Element is not in the codomain of the map").in_context("map application"))?;
        let (Value::Elt(e), Value::Struct(d)) = (&y, &m.domain) else { unreachable!("an element and an affine algebra") };
        Ok(make_elt(d, algebra_affine(d).reduce(e.x.clone())?))
    }
}

// ----- ideals ----------------------------------------------------------------------

/// An ideal of an affine algebra Q = P/J, of type RngMPolRes like Q, which
/// is its own unit ideal (as in Magma, where the ideal is an algebra too).
pub struct AffIdeal {
    /// Q.
    pub algebra: Rc<Struct>,
    /// The generating basis: normal forms modulo J, none zero.
    pub gens: Vec<Elem>,
    /// A copy of Q naming the variables of the ideal, once they are renamed
    /// (until then they are those of Q).
    view: RefCell<Option<Rc<Struct>>>,
    /// The preimage in P, once needed: the ideal (a structure of kind
    /// `MPolIdeal`) of the representatives of the generators and the basis
    /// of J.
    preimage: OnceCell<Rc<Struct>>,
}

impl AffIdeal {
    fn affine(&self) -> &Rc<Affine> {
        algebra_affine(&self.algebra)
    }

    /// The algebra that names the variables of the ideal in printing.
    fn view(&self) -> Rc<Struct> {
        self.view.borrow().clone().unwrap_or_else(|| self.algebra.clone())
    }

    /// The preimage of the ideal in P.
    pub fn preimage(&self) -> &Rc<Struct> {
        self.preimage.get_or_init(|| {
            let affine = self.affine();
            let gens = self.gens.iter().cloned().chain(affine.divisor().basis()).collect();
            Struct::new(StructKind::MPolIdeal(Rc::new(MPolIdeal::new(affine.preimage.clone(), gens, false))))
        })
    }

    fn preimage_ideal(&self) -> Rc<MPolIdeal> {
        match &self.preimage().kind {
            StructKind::MPolIdeal(id) => id.clone(),
            _ => unreachable!("an ideal"),
        }
    }

    /// The basis the ideal brings to an ideal it generates: the images of
    /// the Gröbner basis of its preimage once that is known, else the
    /// generating basis.
    fn basis(&self) -> RResult<Vec<Elem>> {
        match self.preimage.get() {
            Some(_) if self.preimage_ideal().has_groebner() => reduced(self.affine(), self.preimage_ideal().basis()),
            _ => Ok(self.gens.clone()),
        }
    }

    /// Whether both are ideals of one algebra with one generating basis.
    pub fn same_as(&self, other: &AffIdeal) -> bool {
        Rc::ptr_eq(&self.algebra, &other.algebra) && self.gens.len() == other.gens.len() && self.gens.iter().zip(&other.gens).all(|(f, g)| f.equal(g) == Truth::True)
    }
}

/// The affine algebra of a structure that is one.
fn algebra_affine(st: &Struct) -> &Rc<Affine> {
    match &st.kind {
        StructKind::Ring(r) => affine_of(r).expect("an affine algebra"),
        _ => unreachable!("an affine algebra"),
    }
}

/// An affine algebra, or an ideal of one: the algebra and the ideal (`None`
/// for the algebra, its own unit ideal).
pub fn aff_operand(v: &Value) -> Option<(Rc<Struct>, Option<Rc<AffIdeal>>)> {
    match v.as_struct()? {
        StructKind::AffIdeal(id) => Some((id.algebra.clone(), Some(id.clone()))),
        StructKind::Ring(r) if matches!(r.kind, RingKind::MPolyRes { .. }) => {
            let Value::Struct(st) = v else { unreachable!() };
            Some((st.clone(), None))
        }
        _ => None,
    }
}

/// Whether two affine algebras are one quotient ring, whose ideals compare.
fn same_algebra(a: &Rc<Struct>, b: &Rc<Struct>) -> RResult<bool> {
    Ok(Rc::ptr_eq(a, b) || algebras_equal(algebra_affine(a), algebra_affine(b))?)
}

/// The normal forms of the polynomials `fs` modulo J, but zeros.
fn reduced(affine: &Affine, fs: Vec<Elem>) -> RResult<Vec<Elem>> {
    let mut out = Vec::with_capacity(fs.len());
    for f in fs {
        let g = affine.reduce(f)?;
        if g.mpoly_len() > 0 {
            out.push(g);
        }
    }
    Ok(out)
}

/// The generating basis of an ideal, [1] for the algebra.
fn generating(affine: &Affine, x: &Option<Rc<AffIdeal>>) -> RResult<Vec<Elem>> {
    match x {
        Some(id) => Ok(id.gens.clone()),
        None => reduced(affine, vec![Elem::one(&affine.poly_ring().ctx)?]),
    }
}

/// The preimage of an ideal in P (`None`, P itself, for the algebra).
fn preimage_of(x: &Option<Rc<AffIdeal>>) -> Option<Rc<MPolIdeal>> {
    x.as_ref().map(|id| id.preimage_ideal())
}

/// The ideal of the affine algebra `q` with the generating basis `gens`
/// (normal forms), zeros left out.
fn aff_ideal_value(q: &Rc<Struct>, gens: Vec<Elem>) -> Value {
    let gens = gens.into_iter().filter(|g| g.mpoly_len() > 0).collect();
    Value::structure(StructKind::AffIdeal(Rc::new(AffIdeal { algebra: q.clone(), gens, view: RefCell::new(None), preimage: OnceCell::new() })))
}

/// What the right-hand side of `ideal<Q | ...>` or `quo<Q | ...>` lists.
enum Item {
    /// An element of Q (a normal form).
    Elt(Elem),
    /// An ideal of Q (`None` for Q itself).
    Ideal(Option<Rc<AffIdeal>>),
}

/// The elements and ideals given for an ideal or quotient of the affine
/// algebra `q`, alone or in sets and sequences: elements of `q`, what
/// coerces into it (polynomials of P by force), and ideals of `q`.
fn aff_items(it: &mut Interp, q: &Rc<Struct>, right: &[Value], ctx: &str) -> RResult<Vec<Item>> {
    let invalid = |i: usize| RuntimeError::runtime(format!("Rhs argument {} is invalid for this constructor", i + 1)).in_context(ctx);
    let mut out = Vec::new();
    for (i, v) in right.iter().enumerate() {
        let items: Vec<Value> = match v {
            Value::Seq(s) => s.elems.clone(),
            Value::Set(s) => s.iter().collect(),
            _ => vec![v.clone()],
        };
        for x in &items {
            if let Some((r, id)) = aff_operand(x) {
                if !same_algebra(&r, q)? {
                    return Err(invalid(i));
                }
                out.push(Item::Ideal(id));
                continue;
            }
            let forced = matches!(x, Value::Elt(e) if matches!(e.ring().kind, RingKind::MPoly { .. } | RingKind::MPolyRes { .. }));
            out.push(Item::Elt(it.to_ring_elem(q, x, forced)?.ok_or_else(|| invalid(i))?));
        }
    }
    Ok(out)
}

/// `ideal<Q | ...>` for an affine algebra Q: the ideal with the generating
/// basis given (ideals bringing their bases, Q the unit), but zeros, and
/// its inclusion into Q.
pub fn ideal_constructor(it: &mut Interp, base: &Value, right: &[Value]) -> RResult<Option<Vec<Value>>> {
    let Some((q, None)) = aff_operand(base) else { return Ok(None) };
    let affine = algebra_affine(&q).clone();
    let mut gens = Vec::new();
    for item in aff_items(it, &q, right, "ideal< ... >")? {
        match item {
            Item::Elt(f) => gens.push(f),
            Item::Ideal(Some(id)) => gens.extend(id.basis()?),
            Item::Ideal(None) => gens.extend(generating(&affine, &None)?),
        }
    }
    let ideal = aff_ideal_value(&q, gens);
    Ok(Some(vec![ideal.clone(), coercion_map(ideal, base.clone())]))
}

/// Operators on the ideals of an affine algebra (the algebra itself among
/// them), as Magma computes them: comparisons through the preimages in P;
/// sums joining the generating bases (Magma lists them in the order of its
/// set of them); products of the representatives in P, as for ideals of
/// P, reduced; intersections of the preimages, reduced.
pub fn ideal_binop(it: &mut Interp, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
    use BinOp::*;
    let (Some((qa, x)), Some((qb, y))) = (aff_operand(a), aff_operand(b)) else { return Ok(None) };
    if !matches!(op, Eq | Ne | Cmpeq | Cmpne | Subset | Notsubset | Add | Mul | Meet) {
        return Ok(None);
    }
    let ctx = |e: RuntimeError| e.in_context(op.intrinsic_name());
    if !same_algebra(&qa, &qb).map_err(ctx)? {
        if matches!(op, Cmpeq | Cmpne) {
            return Ok(Some(Value::Bool(op == Cmpne)));
        }
        // Magma's eq reports it bare, other operators as a failed requirement.
        let e = RuntimeError::runtime("Ideals are not in the same quotient ring");
        return Err(if matches!(op, Eq | Ne) { bare(e) } else { require(e) });
    }
    let affine = algebra_affine(&qa).clone();
    Ok(Some(match op {
        Eq | Ne | Cmpeq | Cmpne => Value::Bool(ideals_equal(&preimage_of(&x), &preimage_of(&y)).map_err(ctx)? == matches!(op, Eq | Cmpeq)),
        Subset | Notsubset => Value::Bool(ideal_subset(&affine.preimage, &preimage_of(&x), &preimage_of(&y)).map_err(ctx)? == (op == Subset)),
        Add => {
            let mut gens: Vec<Elem> = Vec::new();
            for g in generating(&affine, &x)?.into_iter().chain(generating(&affine, &y)?) {
                if !gens.iter().any(|f| f.equal(&g) == Truth::True) {
                    gens.push(g);
                }
            }
            aff_ideal_value(&qa, gens)
        }
        Mul => {
            let ps = super::products(it, &affine.preimage, &generating(&affine, &x)?, &generating(&affine, &y)?)?;
            aff_ideal_value(&qa, reduced(&affine, ps)?)
        }
        _ => match (&x, &y) {
            (_, None) => a.clone(),
            (None, _) => b.clone(),
            (Some(i), Some(j)) => {
                let m = super::meet(&Value::Struct(i.preimage().clone()), &Value::Struct(j.preimage().clone())).map_err(ctx)?;
                let (_, basis) = ideal_parts(&m).expect("an ideal");
                aff_ideal_value(&qa, reduced(&affine, basis)?)
            }
        },
    }))
}

/// `I^k` for an ideal I of an affine algebra (or the algebra): the algebra
/// for k = 0, I for k = 1, else the power of the representatives of the
/// generators in P, as for ideals of P, reduced.
pub fn ideal_power(it: &mut Interp, a: &Value, k: &Integer) -> RResult<Option<Value>> {
    let Some((q, x)) = aff_operand(a) else { return Ok(None) };
    if k.sign() < 0 {
        return Err(arg_ge(2, k, 0).in_context("^"));
    }
    match k.to_u64() {
        Some(0) => return Ok(Some(Value::Struct(q))),
        Some(1) => return Ok(Some(a.clone())),
        _ => {}
    }
    let affine = algebra_affine(&q).clone();
    let p = super::ideal_pow(it, &super::ideal_value(&affine.preimage, generating(&affine, &x)?, false), k)?;
    let (_, basis) = ideal_parts(&p).expect("an ideal");
    Ok(Some(aff_ideal_value(&q, reduced(&affine, basis)?)))
}

/// `x in I` for an ideal I of an affine algebra: for elements of the
/// algebra, and constants such as rationals. Magma takes integers only when
/// I is the whole algebra.
pub fn aff_ideal_contains(it: &mut Interp, id: &AffIdeal, x: &Value) -> RResult<bool> {
    let fail = |msg: &str| Err(RuntimeError::runtime(msg).in_context("in"));
    let StructKind::Ring(q) = &id.algebra.kind else { unreachable!("an affine algebra") };
    let f = match x {
        Value::Elt(e) if e.ring().id == q.id => e.x.clone(),
        Value::Elt(e) if matches!(e.ring().kind, RingKind::MPolyRes { .. }) => return fail("Arguments have no covering structure"),
        Value::Elt(e) if matches!(e.ring().kind, RingKind::MPoly { .. }) => return fail("Bad argument types"),
        Value::Int(_) => {
            let unit = Elem::one(&id.affine().poly_ring().ctx)?;
            return match id.preimage_ideal().contains_all(&[unit]).map_err(|e| e.in_context("in"))? {
                true => Ok(true),
                false => fail("Bad argument types"),
            };
        }
        _ => match it.to_ring_elem(&id.algebra, x, false)? {
            Some(f) => f,
            None => return fail("Bad argument types"),
        },
    };
    id.preimage_ideal().contains_all(&[f]).map_err(|e| e.in_context("in"))
}

// ----- coercion --------------------------------------------------------------------

/// `x` as an element of the affine algebra `st`: elements of the coefficient
/// ring (and those coercing into it) as constants, and by force elements of
/// P and of quotients of P by the same ideal (and what else `P ! x` accepts
/// but polynomials of other rings and elements of other quotients),
/// reduced.
pub fn coerce_into(it: &mut Interp, st: &Rc<Struct>, x: &Value, forced: bool) -> RResult<Option<Elem>> {
    let StructKind::Ring(r) = &st.kind else { return Ok(None) };
    let (Some(affine), Some(base)) = (affine_of(r).cloned(), r.base().cloned()) else { return Ok(None) };
    let y = if !forced {
        match it.to_structure_elem(&base, x, false)? {
            Some(c) => {
                let mut e = Elem::zero(&r.ctx);
                Elem::mpoly_set_scalar(&mut e, &c)?;
                e
            }
            None => return Ok(None),
        }
    } else {
        if let Value::Elt(e) = x {
            let other = match &e.ring().kind {
                // Only a quotient of P by the same ideal passes its elements.
                RingKind::MPolyRes { affine: a, .. } => !algebras_equal(a, &affine)?,
                RingKind::MPoly { .. } => e.ring().id != affine.poly_ring().id,
                _ => false,
            };
            if other {
                return Ok(None);
            }
        }
        match it.to_ring_elem(&affine.preimage, x, true)? {
            Some(y) => y,
            None => return Ok(None),
        }
    };
    Ok(Some(affine.reduce(y)?))
}

// ----- printing --------------------------------------------------------------------

/// The order line of an affine algebra (`Lexicographical Order`).
fn order_line(affine: &Affine) -> String {
    format!("{} Order", affine.order().describe())
}

/// Print an affine algebra: at the minimal level `Affine Algebra of rank n
/// over R`, and otherwise (the Magma level too, as in Magma) also its
/// order, the names of its variables and the basis of its ideal (in those
/// names).
pub fn fmt_affine(it: &mut Interp, p: &mut Printer, s: &Rc<Struct>, indent: usize) -> RResult<()> {
    let StructKind::Ring(r) = &s.kind else { unreachable!("an affine algebra") };
    let RingKind::MPolyRes { base, rank, affine } = &r.kind else { unreachable!("an affine algebra") };
    let (base, rank, affine) = (base.clone(), *rank, affine.clone());
    let b = it.format_flat(&base, Level::Minimal)?;
    p.write(&format!("Affine Algebra of rank {rank} over {b}"));
    if p.level == Level::Minimal {
        return Ok(());
    }
    p.newline(indent);
    p.write(&order_line(&affine));
    p.newline(indent);
    let vars: Vec<String> = (1..=rank).map(|i| r.gen_name(i)).collect();
    p.write(&format!("Variables: {}", vars.join(", ")));
    if let RingKind::MPoly { grading: Some(w), .. } = &affine.poly_ring().kind {
        p.newline(indent);
        p.write(&format!("Variable weights: {}", w.iter().map(|k| k.to_string()).collect::<Vec<_>>().join(" ")));
    }
    p.newline(indent);
    p.write("Quotient relations:");
    fmt_basis(it, p, s, &affine.divisor().basis(), indent)
}

/// Print an ideal of an affine algebra: `Ideal of` and the algebra (only
/// its first line at the minimal level), then the generating basis.
pub fn fmt_aff_ideal(it: &mut Interp, p: &mut Printer, id: &AffIdeal, indent: usize) -> RResult<()> {
    let view = id.view();
    p.write("Ideal of ");
    fmt_affine(it, p, &view, indent)?;
    if p.level == Level::Minimal {
        return Ok(());
    }
    p.newline(indent);
    p.write("Generating basis:");
    fmt_basis(it, p, &view, &id.gens, indent)
}

// ----- finite dimension ------------------------------------------------------------

/// The monomials of P outside the ideal of the leading monomials of J (a
/// basis of P/J), in increasing order; `None` if there are infinitely many.
fn standard_monomials(affine: &Affine) -> RResult<Option<Vec<Vec<u64>>>> {
    if !affine.finite_dimensional()? {
        return Ok(None);
    }
    let g = affine.groebner()?;
    let n = shape(affine.poly_ring()).1;
    let lms: Vec<&[u64]> = g.iter().map(|t| t[0].1.as_slice()).collect();
    if affine.is_zero_ring()? {
        return Ok(Some(Vec::new()));
    }
    // The monomials outside the ideal form an order ideal: fill in the
    // exponents one variable at a time, stopping where the monomial so far
    // (the rest 0) is in the ideal.
    fn fill(i: usize, e: &mut Vec<u64>, lms: &[&[u64]], out: &mut Vec<Vec<u64>>) {
        if i == e.len() {
            out.push(e.clone());
            return;
        }
        loop {
            if lms.iter().any(|m| m.iter().zip(e.iter()).all(|(a, b)| a <= b)) {
                break;
            }
            fill(i + 1, e, lms, out);
            e[i] += 1;
        }
        e[i] = 0;
    }
    let mut out = Vec::new();
    fill(0, &mut vec![0; n], &lms, &mut out);
    let order = affine.order();
    out.sort_by(|a, b| order.cmp(a, b));
    Ok(Some(out))
}

/// The dimension of P/J over the coefficient field, if it is finite.
pub fn vector_dimension(affine: &Affine) -> RResult<Option<usize>> {
    Ok(standard_monomials(affine)?.map(|m| m.len()))
}

/// The minimal polynomial of `x` over the coefficient field, as its
/// coefficients (constant term first), in an algebra of finite dimension
/// (the only ones where Magma finds it): the element of the reduced
/// Gröbner basis of J + (T - x) in P[T] free of the variables of P, for
/// the elimination order on them.
fn minimal_polynomial(affine: &Affine, x: &Elem) -> RResult<Vec<Elem>> {
    affine.need_finite()?;
    let r = affine.poly_ring();
    let (base, n, _) = shape(r);
    let lift = |t: &Terms, k: u64| -> Terms { t.iter().map(|(c, e)| (c.clone(), e.iter().copied().chain(std::iter::once(k)).collect())).collect() };
    let mut gens: Vec<Terms> = affine.groebner()?.iter().map(|t| lift(t, 0)).collect();
    let mut tx: Terms = lift(&terms(x), 0).into_iter().map(|(c, e)| Ok((c.neg()?, e))).collect::<RResult<_>>()?;
    tx.push((Elem::one(base)?, std::iter::repeat_n(0, n).chain(std::iter::once(1)).collect()));
    gens.push(tx);
    let h = engine(r, gb::groebner(base, n + 1, &Order::ElimK(n), &gens))?;
    let p = h.iter().find(|p| p.iter().all(|(_, e)| e[..n].iter().all(|&k| k == 0))).expect("a minimal polynomial in finite dimension");
    let d = p[0].1[n] as usize;
    let mut cs = vec![Elem::zero(base); d + 1];
    for (c, e) in p {
        cs[e[n] as usize] = c.clone();
    }
    Ok(cs)
}

// ----- intrinsics ------------------------------------------------------------------

fn generator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, affine) = affine_arg(a, 0);
    let (k, n) = (a.int(1)?, shape(affine.poly_ring()).1);
    let Some(i) = k.to_i64().filter(|&k| k >= 1 && k as usize <= n).map(|k| k as usize) else {
        return Err(RuntimeError::runtime(format!("Value for name index ({k}) should be in the range [1..{n}]")));
    };
    let x = affine.poly_ring().ctx.mpoly_gen(i - 1)?;
    one(make_elt(&st, affine.reduce(x)?))
}

/// `AssignNames(~Q, N)`: the names given, and `$.i` for the others. An
/// ideal of an algebra has names of its own, as in Magma.
fn assign_names(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = match a.args[0].as_struct() {
        Some(StructKind::AffIdeal(id)) => {
            let affine = id.affine().clone();
            let Value::Struct(view) = it.mpoly_res(&affine.preimage.clone(), affine) else { unreachable!("an affine algebra") };
            *id.view.borrow_mut() = Some(view.clone());
            view
        }
        _ => affine_arg(a, 0).0,
    };
    let StructKind::Ring(r) = &st.kind else { unreachable!("an affine algebra") };
    let names = a.seq(1)?;
    let n = r.ngens();
    if names.elems.len() > n {
        return Err(RuntimeError::runtime(format!("Argument 2 should have length at most {n}")));
    }
    let mut out: Vec<Rc<str>> = Vec::with_capacity(n);
    for v in names.elems.iter() {
        match v {
            Value::Str(s) => out.push(Rc::from(s.as_str())),
            _ => return Err(RuntimeError::runtime("Names must be strings")),
        }
    }
    for i in out.len()..n {
        out.push(Rc::from(format!("$.{}", i + 1).as_str()));
    }
    *r.names.borrow_mut() = out;
    none()
}

fn ngens(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, affine) = affine_arg(a, 0);
    intv(Integer::from_u64(shape(affine.poly_ring()).1 as u64))
}

/// `Generators(Q)`: the set of the variables of Q, also for an ideal of Q
/// (as in Magma, which gives no generators of an ideal of an algebra).
fn algebra_generators(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, affine) = affine_arg(a, 0);
    let ctx = &affine.poly_ring().ctx;
    let gens = (0..shape(affine.poly_ring()).1).map(|i| Ok(make_elt(&st, affine.reduce(ctx.mpoly_gen(i)?)?))).collect::<RResult<_>>()?;
    one(Value::Set(Rc::new(SetEnum::new(Some(Value::Struct(st)), gens))))
}

fn original_ring(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, affine) = affine_arg(a, 0);
    one(Value::Struct(affine.preimage.clone()))
}

fn preimage_ring(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    if let Some(StructKind::AffIdeal(_)) = a.args[0].as_struct() {
        return Err(RuntimeError::runtime("Preimage is not a full polynomial ring"));
    }
    original_ring(it, a)
}

/// `PreimageIdeal(I)`: the ideal of P mapping onto I (P itself for the
/// algebra).
fn preimage_ideal(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match aff_operand(&a.args[0]).expect("an affine algebra or ideal") {
        (_, Some(id)) => one(Value::Struct(id.preimage().clone())),
        (_, None) => original_ring(it, a),
    }
}

fn generic(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::Struct(affine_arg(a, 0).0))
}

/// `IsZero(I)`: whether the ideal is zero (the algebra, only when it is the
/// zero ring).
fn is_zero_ideal(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match aff_operand(&a.args[0]).expect("an affine algebra or ideal") {
        (_, Some(id)) => boolv(id.gens.is_empty()),
        (q, None) => boolv(algebra_affine(&q).is_zero_ring()?),
    }
}

/// `IsProper(I)`: whether the ideal is not the whole algebra.
fn is_proper(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match aff_operand(&a.args[0]).expect("an affine algebra or ideal") {
        (_, Some(id)) => {
            let unit = Elem::one(&id.affine().poly_ring().ctx)?;
            boolv(!id.preimage_ideal().contains_all(&[unit])?)
        }
        (_, None) => boolv(false),
    }
}

fn divisor_ideal(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, affine) = affine_arg(a, 0);
    one(Value::Struct(affine.ideal.clone()))
}

fn is_finite(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, affine) = affine_arg(a, 0);
    match cardinality(&affine)? {
        Some(q) => Ok(vals![Value::Bool(true), Value::Int(q)]),
        None => boolv(false),
    }
}

/// The number of elements of P/J, if finite: q^d over a field of q
/// elements where P/J has dimension d.
pub fn cardinality(affine: &Affine) -> RResult<Option<Integer>> {
    let base = affine.poly_ring().base().expect("a coefficient ring");
    let Some(q) = crate::rings::props::ring_props(base).and_then(|p| p.cardinality) else {
        return Ok(if affine.is_zero_ring()? { Some(Integer::one()) } else { None });
    };
    Ok(vector_dimension(affine)?.map(|d| q.pow(d as u64)))
}

fn has_finite_dimension(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, affine) = affine_arg(a, 0);
    boolv(vector_dimension(&affine)?.is_some())
}

fn dimension(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, affine) = affine_arg(a, 0);
    match vector_dimension(&affine)? {
        Some(d) => intv(Integer::from_u64(d as u64)),
        None => Err(RuntimeError::runtime("Quotient does not have finite dimension")),
    }
}

fn monomial_basis(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, affine) = affine_arg(a, 0);
    let Some(ms) = standard_monomials(&affine)? else { return Err(RuntimeError::runtime("Quotient does not have finite dimension")) };
    let r = affine.poly_ring();
    let unit = Elem::one(r.ctx.base().expect("a polynomial ring"))?;
    let mut out = VSet::default();
    for e in ms {
        out.insert(make_elt(&st, Elem::mpoly_from_terms(&r.ctx, &[(unit.clone(), e)])?));
    }
    one(Value::ISet(Rc::new(SetIndx { universe: Some(Value::Struct(st)), elems: out, name: Default::default() })))
}

fn minimal_polynomial_of(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = elt_arg(a, 0);
    let affine = affine_of(f.ring()).expect("an affine algebra").clone();
    let cs = minimal_polynomial(&affine, &f.x)?;
    let base = f.ring().base().expect("a coefficient ring").clone();
    let u = it.poly_ring(&base, true)?;
    let Value::Struct(ust) = &u else { unreachable!("a polynomial ring") };
    let StructKind::Ring(ur) = &ust.kind else { unreachable!("a polynomial ring") };
    one(make_elt(ust, Elem::poly_from_coeffs(&ur.ctx, &cs)?))
}

fn is_nilpotent(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = elt_arg(a, 0);
    let affine = affine_of(f.ring()).expect("an affine algebra").clone();
    let cs = minimal_polynomial(&affine, &f.x)?;
    // x is nilpotent when its minimal polynomial is a power of T.
    let d = cs.len() - 1;
    if cs[..d].iter().all(|c| c.is_zero() == Truth::True) {
        return Ok(vals![Value::Bool(true), Value::int(d as i64)]);
    }
    boolv(false)
}

fn is_unit(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = elt_arg(a, 0);
    let affine = affine_of(f.ring()).expect("an affine algebra").clone();
    boolv(affine.inverse(&f.x)?.is_some())
}

fn is_zero(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(elt_arg(a, 0).x.is_zero() == Truth::True)
}

fn is_one(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(elt_arg(a, 0).x.is_one() == Truth::True)
}

fn is_minus_one(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(elt_arg(a, 0).x.is_neg_one() == Truth::True)
}

pub fn register(it: &mut Interp) {
    for name in [".", "Name"] {
        it.def(name, "Q::RngMPolRes, i::RngIntElt -> RngMPolResElt", "The i-th variable of Q.", generator);
    }
    it.def("AssignNames", "~Q::RngMPolRes, N::[MonStgElt]", "Name the variables of Q (for printing), $.i those not named.", assign_names);
    for name in ["Ngens", "Rank"] {
        it.def(name, "Q::RngMPolRes -> RngIntElt", "The number of variables of Q.", ngens);
    }
    it.def("Generators", "Q::RngMPolRes -> SetEnum", "The set of the variables of Q (or of the algebra of the ideal Q).", algebra_generators);
    it.def("PreimageRing", "Q::RngMPolRes -> RngMPol", "The polynomial ring P of which Q is the quotient P/J.", preimage_ring);
    it.def("OriginalRing", "Q::RngMPolRes -> RngMPol", "The polynomial ring P of which Q (or the algebra of the ideal Q) is the quotient P/J.", original_ring);
    it.def("DivisorIdeal", "Q::RngMPolRes -> RngMPol", "The ideal J of P with Q = P/J (for an ideal Q, of its algebra).", divisor_ideal);
    it.def("PreimageIdeal", "I::RngMPolRes -> RngMPol", "The ideal of P mapping onto the ideal I of P/J (P for P/J itself).", preimage_ideal);
    it.def("Generic", "I::RngMPolRes -> RngMPolRes", "The affine algebra of the ideal I.", generic);
    it.def("IsZero", "I::RngMPolRes -> BoolElt", "Whether I is the zero ideal.", is_zero_ideal);
    it.def("IsProper", "I::RngMPolRes -> BoolElt", "Whether the ideal I is not the whole algebra.", is_proper);
    it.def("IsFinite", "Q::RngMPolRes -> BoolElt, RngIntElt", "Whether Q is finite, and if so its cardinality.", is_finite);
    it.def("HasFiniteDimension", "Q::RngMPolRes -> BoolElt", "Whether Q has finite dimension over its coefficient field.", has_finite_dimension);
    it.def("Dimension", "Q::RngMPolRes -> RngIntElt", "The dimension of Q over its coefficient field.", dimension);
    it.def("MonomialBasis", "Q::RngMPolRes -> SetIndx", "The monomials forming a basis of Q over its coefficient field, increasing.", monomial_basis);
    it.def("MinimalPolynomial", "f::RngMPolResElt -> RngUPolElt", "The minimal polynomial of f over the coefficient field.", minimal_polynomial_of);
    it.def("IsNilpotent", "f::RngMPolResElt -> BoolElt, RngIntElt", "Whether f is nilpotent, and if so the least k with f^k = 0.", is_nilpotent);
    it.def("IsUnit", "f::RngMPolResElt -> BoolElt", "Whether f is a unit.", is_unit);
    it.def("IsZero", "f::RngMPolResElt -> BoolElt", "Whether f is zero.", is_zero);
    it.def("IsOne", "f::RngMPolResElt -> BoolElt", "Whether f is one.", is_one);
    it.def("IsMinusOne", "f::RngMPolResElt -> BoolElt", "Whether f is minus one.", is_minus_one);
}
