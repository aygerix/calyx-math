//! Ideals of multivariate polynomial rings (the handbook's Polynomial Rings
//! and Ideals: Creation of Ideals and Accessing their Bases, and the first
//! operations on ideals).
//!
//! An ideal of a polynomial ring P is a structure of type RngMPol, like P
//! (`StructKind::MPolIdeal`), with its basis: the generators as given,
//! duplicates and zeros included. The functions of the ring (Rank, Name,
//! MonomialOrder, BaseRing and so on) answer for P, and P acts as the ideal
//! with basis [1].

use std::cmp::Ordering;
use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{Elem, Truth};
use calyx_syntax::ast::BinOp;

use super::{arg_ge, boolv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::print::{Level, Printer};
use crate::rings::{Elt, Ring, RingKind, make_elt, ring_of};
use crate::value::*;

/// An ideal of a multivariate polynomial ring.
pub struct MPolIdeal {
    /// The polynomial ring (`Generic(I)`).
    pub ring: Rc<Struct>,
    /// The basis.
    pub gens: Vec<Elem>,
    /// Whether the basis is fixed (`IdealWithFixedBasis`).
    pub fixed: bool,
}

impl MPolIdeal {
    /// The polynomial ring.
    pub fn poly_ring(&self) -> &Rc<Ring> {
        match &self.ring.kind {
            StructKind::Ring(r) => r,
            _ => unreachable!("a polynomial ring"),
        }
    }

    /// Whether both ideals have one ring and one basis (the ideals are then
    /// equal).
    pub fn same_as(&self, other: &MPolIdeal) -> bool {
        self.poly_ring().id == other.poly_ring().id && self.gens.len() == other.gens.len() && self.gens.iter().zip(&other.gens).all(|(f, g)| f.equal(g) == Truth::True)
    }
}

fn ideal_value(ring: &Rc<Struct>, gens: Vec<Elem>, fixed: bool) -> Value {
    Value::structure(StructKind::MPolIdeal(Rc::new(MPolIdeal { ring: ring.clone(), gens, fixed })))
}

/// A multivariate polynomial ring or an ideal of one: the ring and the
/// basis ([1] for the ring).
fn ideal_parts(v: &Value) -> Option<(Rc<Struct>, Vec<Elem>)> {
    match v.as_struct()? {
        StructKind::MPolIdeal(id) => Some((id.ring.clone(), id.gens.clone())),
        StructKind::Ring(r) if matches!(r.kind, RingKind::MPoly { .. }) => {
            let Value::Struct(st) = v else { unreachable!() };
            Some((st.clone(), vec![Elem::one(&r.ctx).ok()?]))
        }
        _ => None,
    }
}

/// Argument `i`, which the signature makes a polynomial ring or an ideal of
/// one.
fn ideal_arg(a: &CallArgs, i: usize) -> (Rc<Struct>, Vec<Elem>) {
    ideal_parts(&a.args[i]).expect("a polynomial ring or ideal")
}

fn coercion_map(domain: Value, codomain: Value) -> Value {
    Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain, codomain, imp: MapImpl::Coercion }))
}

/// The basis of `ideal<P | ...>`: elements coercing into P, ideals of P,
/// and sets and sequences of these.
fn generators(it: &mut Interp, pst: &Rc<Struct>, right: &[Value]) -> RResult<Vec<Elem>> {
    let invalid = |i: usize| RuntimeError::runtime(format!("Rhs argument {} is invalid for this constructor", i + 1)).in_context("ideal< ... >");
    let mut out = Vec::new();
    for (i, v) in right.iter().enumerate() {
        let items: Vec<Value> = match v {
            Value::Seq(s) => s.elems.clone(),
            Value::Set(s) => s.iter().collect(),
            _ => vec![v.clone()],
        };
        for x in &items {
            if let Some((r, gs)) = ideal_parts(x) {
                if !struct_eq(&r, pst) {
                    return Err(invalid(i));
                }
                out.extend(gs);
                continue;
            }
            out.push(it.to_ring_elem(pst, x, false)?.ok_or_else(|| invalid(i))?);
        }
    }
    Ok(out)
}

/// `ideal<P | ...>` for a multivariate polynomial ring P: the ideal and its
/// inclusion into P.
pub fn ideal_constructor(it: &mut Interp, base: &Value, right: &[Value]) -> RResult<Option<Vec<Value>>> {
    let Some((pst, _)) = ring_of(base).filter(|(_, r)| matches!(r.kind, RingKind::MPoly { .. })) else { return Ok(None) };
    let pst = pst.clone();
    let gens = generators(it, &pst, right)?;
    let ideal = ideal_value(&pst, gens, false);
    Ok(Some(vec![ideal.clone(), coercion_map(ideal, base.clone())]))
}

/// The products of the elements of `xs` and `ys`, normalized, without
/// repetitions and in increasing order (as Magma builds the basis of a
/// product of ideals).
fn products(it: &mut Interp, pst: &Rc<Struct>, xs: &[Elem], ys: &[Elem]) -> RResult<Vec<Elem>> {
    let mut out = Vec::with_capacity(xs.len() * ys.len());
    for x in xs {
        for y in ys {
            out.push(x.mul(y)?);
        }
    }
    let out = normalized(it, pst, &out)?;
    sort_dedup(it, pst, out)
}

/// Polynomials of `pst` in increasing order (term by term in the monomial
/// order, then by coefficients), each once.
fn sort_dedup(it: &mut Interp, pst: &Rc<Struct>, mut xs: Vec<Elem>) -> RResult<Vec<Elem>> {
    let StructKind::Ring(r) = &pst.kind else { unreachable!("a polynomial ring") };
    let mut err = None;
    xs.sort_by(|x, y| match it.ring_elt_cmp(r, x, y) {
        Ok(o) => o.unwrap_or(Ordering::Equal),
        Err(e) => {
            err.get_or_insert(e);
            Ordering::Equal
        }
    });
    if let Some(e) = err {
        return Err(e);
    }
    xs.dedup_by(|x, y| x.equal(y) == Truth::True);
    Ok(xs)
}

/// The polynomials `xs` of `pst`, normalized.
fn normalized(it: &mut Interp, pst: &Rc<Struct>, xs: &[Elem]) -> RResult<Vec<Elem>> {
    xs.iter().map(|x| super::mpoly::normalized(it, &Elt { parent: pst.clone(), x: x.clone() })).collect()
}

/// `I^k`: the ring for k = 0, I for k = 1, else the products of k elements
/// of the basis.
fn ideal_pow(it: &mut Interp, a: &Value, k: &Integer) -> RResult<Value> {
    let (pst, gens) = ideal_parts(a).expect("a polynomial ring or ideal");
    if k.sign() < 0 {
        return Err(arg_ge(2, k, 0).in_context("^"));
    }
    let Some(k) = k.to_u64().filter(|&k| k < 1 << 30) else {
        return Err(RuntimeError::runtime(format!("Argument 2 ({k}) is too large")).in_context("^"));
    };
    match k {
        0 => return Ok(Value::Struct(pst)),
        1 => return Ok(a.clone()),
        _ => {}
    }
    // The products are those of the distinct normalized elements.
    let xs = normalized(it, &pst, &gens)?;
    let xs = sort_dedup(it, &pst, xs)?;
    let acc = match xs.as_slice() {
        [x] => normalized(it, &pst, &[x.pow(&Integer::from_u64(k))?])?,
        _ => {
            let mut acc = xs.clone();
            for _ in 1..k {
                acc = products(it, &pst, &acc, &xs)?;
            }
            acc
        }
    };
    Ok(ideal_value(&pst, acc, false))
}

/// Operators on ideals of multivariate polynomial rings (with an ideal
/// among the operands, or on the rings themselves as ideals).
pub fn ideal_binop(it: &mut Interp, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
    let is_ideal = |v: &Value| matches!(v.as_struct(), Some(StructKind::MPolIdeal(_)));
    if op == BinOp::Pow {
        return match (ideal_parts(a), b) {
            (Some(_), Value::Int(k)) => Ok(Some(ideal_pow(it, a, k)?)),
            _ => Ok(None),
        };
    }
    // The rings themselves have sums and products as ideals.
    let ring_op = matches!(op, BinOp::Add | BinOp::Mul);
    let compare = matches!(op, BinOp::Eq | BinOp::Ne | BinOp::Subset | BinOp::Notsubset | BinOp::Meet);
    if !(ring_op || compare && (is_ideal(a) || is_ideal(b))) {
        return Ok(None);
    }
    let (Some((r, f)), Some((s, g))) = (ideal_parts(a), ideal_parts(b)) else { return Ok(None) };
    if !struct_eq(&r, &s) {
        return Err(RuntimeError::runtime(format!("Arguments are not compatible\nArgument types given: {}, {}", it.type_name_ext(a), it.type_name_ext(b))).in_context(op.intrinsic_name()));
    }
    Ok(Some(match op {
        // The sum with the ring is the ring.
        BinOp::Add if !is_ideal(a) => a.clone(),
        BinOp::Add if !is_ideal(b) => b.clone(),
        BinOp::Add => ideal_value(&r, [f, g].concat(), false),
        BinOp::Mul => ideal_value(&r, products(it, &r, &f, &g)?, false),
        BinOp::Eq | BinOp::Ne if a == b => Value::Bool(op == BinOp::Eq),
        _ => return Err(RuntimeError::runtime("This operation on ideals needs Groebner bases, which calyx does not have yet").in_context(op.intrinsic_name())),
    }))
}

/// `x in I`, which needs a Gröbner basis.
pub fn ideal_contains(_it: &mut Interp, _id: &MPolIdeal, _x: &Value) -> RResult<bool> {
    Err(RuntimeError::runtime("Membership of ideals needs Groebner bases, which calyx does not have yet").in_context("in"))
}

/// `ChangeRing(I, S)`: the ideal of Q, the ring of I over S, generated by
/// the basis of I with its coefficients coerced into S.
pub fn change_ring(it: &mut Interp, id: &MPolIdeal, q: &Value) -> RResult<Value> {
    let Some((qst, _)) = ring_of(q) else { unreachable!("a polynomial ring") };
    let qst = qst.clone();
    let mut gens = Vec::with_capacity(id.gens.len());
    for g in &id.gens {
        match it.to_ring_elem(&qst, &make_elt(&id.ring, g.clone()), true)? {
            Some(x) => gens.push(x),
            None => return Err(RuntimeError::runtime("Cannot coerce element from source coefficent ring into the destination coefficient ring")),
        }
    }
    Ok(ideal_value(&qst, gens, false))
}

/// Whether the basis elements are homogeneous in the grading of the ring.
fn homogeneous_basis(r: &Ring, gens: &[Elem]) -> bool {
    gens.iter().all(|g| super::mpoly::homogeneous(r, g))
}

/// A basis, one element per line between brackets.
fn fmt_basis(it: &mut Interp, p: &mut Printer, ring: &Rc<Struct>, gens: &[Elem], indent: usize) -> RResult<()> {
    p.newline(indent);
    p.write("[");
    let saved = p.cont;
    p.cont = indent + 4;
    for (i, g) in gens.iter().enumerate() {
        p.newline(indent + 4);
        it.fmt(p, &make_elt(ring, g.clone()), indent + 4)?;
        if i + 1 < gens.len() {
            p.write(",");
        }
    }
    p.cont = saved;
    p.newline(indent);
    p.write("]");
    Ok(())
}

/// Print an ideal: at the Magma level `ideal<P | ...>` with an element of
/// the basis per line, at the minimal level `Ideal of P`, and otherwise the
/// ring, the fixed basis, whether the ideal is homogeneous and the basis.
pub fn fmt_ideal(it: &mut Interp, p: &mut Printer, id: &MPolIdeal, indent: usize) -> RResult<()> {
    let r = id.poly_ring().clone();
    if p.level == Level::Magma {
        let ring = it.format_ring(&r, Level::Magma)?.join("\n");
        p.write(&format!("ideal<{ring} |"));
        for (i, g) in id.gens.iter().enumerate() {
            p.newline(indent);
            it.fmt(p, &make_elt(&id.ring, g.clone()), indent)?;
            if i + 1 < id.gens.len() {
                p.write(",");
            }
        }
        p.newline(indent);
        p.write(">");
        return Ok(());
    }
    let minimal = p.level == Level::Minimal;
    let lines = it.format_ring(&r, if minimal { Level::Minimal } else { Level::Default })?;
    p.write("Ideal of ");
    for (i, line) in lines.iter().enumerate() {
        if i > 0 {
            p.newline(indent);
        }
        p.write(line);
    }
    if minimal {
        return Ok(());
    }
    if id.fixed {
        p.newline(indent);
        p.write("Fixed basis:");
        fmt_basis(it, p, &id.ring, &id.gens, indent)?;
    }
    if homogeneous_basis(&r, &id.gens) {
        p.newline(indent);
        p.write("Homogeneous");
    }
    p.newline(indent);
    p.write("Basis:");
    fmt_basis(it, p, &id.ring, &id.gens, indent)
}

// ----- intrinsics ------------------------------------------------------------------

/// `Ideal(B)` and `IdealWithFixedBasis(B)` for a set or sequence B of
/// polynomials.
fn ideal_of(a: &CallArgs, fixed: bool) -> RResult<Vals> {
    let (universe, elems): (Option<Value>, Vec<Value>) = match &a.args[0] {
        Value::Seq(s) => (s.universe.clone(), s.elems.clone()),
        Value::Set(s) => (s.universe.clone(), s.iter().collect()),
        _ => unreachable!("a set or sequence"),
    };
    let Some((pst, _)) = universe.as_ref().and_then(ring_of) else { return Err(RuntimeError::runtime("Illegal null sequence")) };
    let gens = elems.iter().map(|v| match v {
        Value::Elt(e) => e.x.clone(),
        _ => unreachable!("a polynomial"),
    });
    one(ideal_value(pst, gens.collect(), fixed))
}

fn ideal_from(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    ideal_of(a, false)
}

fn ideal_with_fixed_basis(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    ideal_of(a, true)
}

fn principal_ideal(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Elt(f) = &a.args[0] else { unreachable!("a polynomial") };
    one(ideal_value(&f.parent, vec![f.x.clone()], false))
}

fn basis(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (pst, gens) = ideal_arg(a, 0);
    let elems = gens.into_iter().map(|g| make_elt(&pst, g)).collect();
    one(Value::seq(Some(Value::Struct(pst)), elems))
}

fn basis_element(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (pst, gens) = ideal_arg(a, 0);
    let (k, n) = (a.int(1)?, gens.len());
    match k.to_u64().filter(|&k| k >= 1 && k as usize <= n) {
        Some(i) => one(make_elt(&pst, gens[i as usize - 1].clone())),
        None => Err(RuntimeError::runtime(format!("Argument 2 ({k}) should be in the range [1 .. {n}]"))),
    }
}

fn generic(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::Struct(ideal_arg(a, 0).0))
}

fn is_zero(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(ideal_arg(a, 0).1.iter().all(|g| g.mpoly_len() == 0))
}

/// `IsHomogeneous(I)`, decided here when the basis is homogeneous.
fn is_homogeneous(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (pst, gens) = ideal_arg(a, 0);
    let StructKind::Ring(r) = &pst.kind else { unreachable!("a polynomial ring") };
    if homogeneous_basis(r, &gens) {
        return boolv(true);
    }
    Err(RuntimeError::runtime("Deciding whether an ideal is homogeneous needs Groebner bases, which calyx does not have yet"))
}

pub fn register(it: &mut Interp) {
    it.def("Ideal", "B::[RngMPolElt] -> RngMPol", "The ideal generated by the polynomials B, with basis B.", ideal_from);
    it.def("Ideal", "B::{RngMPolElt} -> RngMPol", "The ideal generated by the polynomials B, with basis B.", ideal_from);
    it.def("Ideal", "f::RngMPolElt -> RngMPol", "The principal ideal generated by f.", principal_ideal);
    it.def("IdealWithFixedBasis", "B::[RngMPolElt] -> RngMPol", "The ideal generated by the polynomials B, with the fixed basis B.", ideal_with_fixed_basis);
    for name in ["Basis", "Generators"] {
        it.def(name, "I::RngMPol -> [RngMPolElt]", "The basis of the ideal I.", basis);
    }
    it.def("BasisElement", "I::RngMPol, i::RngIntElt -> RngMPolElt", "The i-th element of the basis of the ideal I.", basis_element);
    it.def("Generic", "I::RngMPol -> RngMPol", "The polynomial ring of the ideal I.", generic);
    it.def("IsZero", "I::RngMPol -> BoolElt", "Whether I is the zero ideal.", is_zero);
    it.def("IsHomogeneous", "I::RngMPol -> BoolElt", "Whether the ideal I is homogeneous in the grading of its ring.", is_homogeneous);
}
