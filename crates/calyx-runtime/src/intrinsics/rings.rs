//! Generic ring functions and the constructors of residue class rings,
//! polynomial rings and complex fields (finite fields are in
//! `finite_fields`).

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{Elem, Truth};

use super::{boolv, intv, none, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::rings::{Ring, RingKind, make_elt};
use crate::rings::props::{RingProps, ring_props};
use crate::value::*;

/// The ring and its structure from argument `i`.
fn ring_arg(a: &CallArgs, i: usize) -> RResult<(Rc<Struct>, Rc<Ring>)> {
    match &a.args[i] {
        Value::Struct(s) => match &s.kind {
            StructKind::Ring(r) => Ok((s.clone(), r.clone())),
            // An ideal of a polynomial ring answers for the ring, and one of an
            // affine algebra for the algebra.
            StructKind::MPolIdeal(id) => Ok((id.ring.clone(), id.poly_ring().clone())),
            StructKind::AffIdeal(id) => match &id.algebra.kind {
                StructKind::Ring(r) => Ok((id.algebra.clone(), r.clone())),
                _ => unreachable!("an affine algebra"),
            },
            _ => Err(RuntimeError::runtime("Bad argument types")),
        },
        _ => Err(RuntimeError::runtime("Bad argument types")),
    }
}

fn elt_arg(a: &CallArgs, i: usize) -> RResult<Rc<crate::rings::Elt>> {
    crate::rings::small::elt_of(&a.args[i]).ok_or_else(|| RuntimeError::runtime("Bad argument types"))
}

// ----- residue class rings ---------------------------------------------------

/// `GF(p)` with the reduction map from the integers.
fn residue_class_field(it: &mut Interp, p: Integer) -> RResult<Vals> {
    let f = it.finite_field(&p, 1)?;
    let map = Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain: Value::integers(), codomain: f.clone(), imp: MapImpl::Reduction(p) }));
    Ok(vals![f, map])
}

fn residue_ring(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = a.int(0)?.clone();
    if m.sign() <= 0 {
        return Err(RuntimeError::runtime("Argument 1 must be positive"));
    }
    let r = it.residue_ring(&m);
    let map = Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain: Value::integers(), codomain: r.clone(), imp: MapImpl::Reduction(m) }));
    Ok(vals![r, map])
}

fn modulus(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    if let Some((r, _)) = crate::rings::ideals::res_ideal_parts(&a.args[0]) {
        return intv(crate::rings::ideals::residue_modulus(&r));
    }
    let (_, r) = ring_arg(a, 0)?;
    match &r.kind {
        RingKind::Residue(m) => intv(m.clone()),
        _ => Err(RuntimeError::runtime("Bad argument types")),
    }
}

// ----- finite fields ---------------------------------------------------------

fn prime_field(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match &a.args[0] {
        Value::Struct(s) => match &s.kind {
            StructKind::Ring(r) => match &r.kind {
                RingKind::Finite(f) => {
                    let p = f.p.clone();
                    one(it.finite_field(&p, 1)?)
                }
                RingKind::Complex(_) => one(Value::rationals()),
                _ => Err(RuntimeError::runtime("Argument must be a field")),
            },
            StructKind::Rationals | StructKind::Reals(_) => one(Value::rationals()),
            _ => Err(RuntimeError::runtime("Argument must be a field")),
        },
        _ => Err(RuntimeError::runtime("Bad argument types")),
    }
}

fn is_prime_field(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    Ok(vals![Value::Bool(match &a.args[0] {
        Value::Struct(s) => match &s.kind {
            StructKind::Rationals => true,
            StructKind::Ring(r) => r.is_prime_field(),
            _ => false,
        },
        _ => false,
    })])
}

fn primitive_element(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, r) = ring_arg(a, 0)?;
    match &r.kind {
        RingKind::Residue(m) => {
            let root = crate::intrinsics::ints::primitive_root(m).unwrap_or_default();
            one(make_elt(&st, Elem::from_integer(&r.ctx, &root)?))
        }
        _ => Err(RuntimeError::runtime("Bad argument types")),
    }
}

// ----- polynomial rings ------------------------------------------------------

fn polynomial_ring(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let base = a.args[0].clone();
    let global = a.param_bool("Global")?;
    one(it.poly_ring(&base, global)?)
}

fn base_ring(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let r = match &a.args[0] {
        Value::Elt(e) => e.ring_rc(),
        _ => ring_arg(a, 0)?.1,
    };
    match r.base() {
        Some(b) => one(b.clone()),
        None => Err(RuntimeError::runtime("Bad argument types")),
    }
}

// ----- generic ring functions -------------------------------------------------

fn ngens(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    if matches!(a.args[0].as_struct(), Some(StructKind::ResIdeal(..))) {
        return Err(RuntimeError::runtime("Ngens not supported for this structure"));
    }
    let (_, r) = ring_arg(a, 0)?;
    intv(Integer::from_u64(r.ngens() as u64))
}

fn generator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, r) = ring_arg(a, 0)?;
    let (k, n) = (a.int(1)?, r.ngens());
    let Some(i) = k.to_i64().filter(|&k| k >= 1 && k as usize <= n).map(|k| k as usize) else {
        return Err(RuntimeError::runtime(match &r.kind {
            RingKind::UPoly { .. } | RingKind::MPoly { .. } => format!("Value for name index ({k}) should be in the range [1..{n}]"),
            RingKind::Finite(_) => format!("Argument 2 ({k}) should be in the range [1 .. {n}]"),
            _ => format!("Generator index must be in the range [1..{n}]"),
        }));
    };
    let g = match &r.kind {
        RingKind::MPoly { .. } => r.ctx.mpoly_gen(i - 1)?,
        RingKind::Residue(_) => Elem::one(&r.ctx)?,
        RingKind::Finite(f) => crate::rings::finite::gen1(&r, f),
        _ => r.ctx.generator()?,
    };
    one(make_elt(&st, g))
}

fn assign_names(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, r) = ring_arg(a, 0)?;
    let names = a.seq(1)?;
    let mut out = Vec::new();
    for v in names.elems.iter() {
        match v {
            Value::Str(s) => out.push(Rc::from(s.as_str())),
            _ => return Err(RuntimeError::runtime("Names must be strings")),
        }
    }
    let n = r.ngens();
    match &r.kind {
        RingKind::MPoly { .. } if out.len() > n => return Err(RuntimeError::runtime(format!("Argument 2 should have length at most {n}"))),
        RingKind::UPoly { .. } | RingKind::Finite(_) if out.len() != n => return Err(RuntimeError::runtime(format!("Argument 2 must have length {n}"))),
        _ if out.len() > n => return Err(RuntimeError::runtime(format!("Too many names ({} given, {n} generators)", out.len()))),
        _ => {}
    }
    // Names not given stay as they were.
    let mut names = r.names.borrow_mut();
    for (i, s) in out.into_iter().enumerate() {
        if i < names.len() { names[i] = s } else { names.push(s) }
    }
    none()
}

/// A ring argument, an ideal of a polynomial ring (or of an affine algebra)
/// standing for the ring.
fn ring_of_arg(v: &Value) -> Value {
    match v.as_struct() {
        Some(StructKind::MPolIdeal(id)) => Value::Struct(id.ring.clone()),
        Some(StructKind::AffIdeal(id)) => Value::Struct(id.algebra.clone()),
        _ => v.clone(),
    }
}

fn props(a: &CallArgs) -> RResult<RingProps> {
    ring_props(&ring_of_arg(&a.args[0])).ok_or_else(|| RuntimeError::runtime("Bad argument types"))
}

fn characteristic(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(props(a)?.characteristic)
}

/// `IsFinite(R)`: also the cardinality of a finite ring.
fn is_finite(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match props(a)?.cardinality {
        Some(n) => Ok(vals![Value::Bool(true), Value::Int(n)]),
        None => boolv(false),
    }
}

fn is_true(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    boolv(true)
}

fn is_unitary(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(!matches!(a.args[0].as_struct(), Some(StructKind::MPolIdeal(_))))
}

fn is_field(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(props(a)?.field)
}

fn is_ordered(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(props(a)?.ordered)
}

fn is_domain(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(props(a)?.domain)
}

fn is_ufd(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(props(a)?.ufd)
}

fn has_gcd(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(props(a)?.has_gcd)
}

fn is_magma_euclidean(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(props(a)?.magma_euclidean)
}

/// A property Magma cannot always decide; `algorithm` names it in the error.
fn undecided(v: Option<bool>, algorithm: &str) -> RResult<Vals> {
    match v {
        Some(b) => boolv(b),
        None => Err(RuntimeError::runtime(format!("Algorithm for '{algorithm}' not available for this object"))),
    }
}

fn is_euclidean_domain(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    undecided(props(a)?.euclidean, "IsEuclideanDomain")
}

fn is_euclidean_ring(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = props(a)?;
    // Residue class rings are Euclidean rings even when not domains.
    let v = if p.cardinality.is_some() && !p.field && p.magma_euclidean { Some(true) } else { p.euclidean };
    undecided(v, "IsEuclideanRing")
}

fn is_pid(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    undecided(props(a)?.pid, "IsPrincipalIdealDomain")
}

fn is_pir(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = props(a)?;
    let v = if p.cardinality.is_some() && !p.field && p.magma_euclidean { Some(true) } else { p.pid };
    undecided(v, "IsPrincipalIdealRing")
}

/// The smallest subring containing 1 (the prime field of a field).
fn prime_ring(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    fn of(it: &mut Interp, v: &Value) -> RResult<Value> {
        Ok(match v.as_struct() {
            Some(StructKind::Integers) => Value::integers(),
            Some(StructKind::Rationals | StructKind::Reals(_)) => Value::rationals(),
            Some(StructKind::ResIdeal(..)) => v.clone(),
            Some(StructKind::Ring(r)) => match &r.kind {
                RingKind::Complex(_) => Value::rationals(),
                RingKind::Residue(_) => v.clone(),
                RingKind::Finite(f) => {
                    let p = f.p.clone();
                    it.finite_field(&p, 1)?
                }
                RingKind::UPoly { base, .. } | RingKind::MPoly { base, .. } | RingKind::UPolyRes { base, .. } | RingKind::MPolyRes { base, .. } => {
                    let base = base.clone();
                    of(it, &base)?
                }
            },
            _ => return Err(RuntimeError::runtime("Bad argument types")),
        })
    }
    let r = of(it, &ring_of_arg(&a.args[0]))?;
    one(r)
}

fn centre(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(a.args[0].clone())
}

// ----- elements ----------------------------------------------------------------

fn elt_pred(a: &CallArgs, f: impl Fn(&Elem) -> Truth) -> RResult<Vals> {
    let e = elt_arg(a, 0)?;
    boolv(f(&e.x) == Truth::True)
}

fn is_zero(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    elt_pred(a, Elem::is_zero)
}

fn is_one(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    elt_pred(a, Elem::is_one)
}

fn is_minus_one(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    elt_pred(a, Elem::is_neg_one)
}

fn is_unit(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let e = elt_arg(a, 0)?;
    boolv(elt_is_unit(it, &e.ring_rc(), &e.x))
}

/// Units: constant polynomials whose constant is a unit of the coefficient
/// ring.
fn elt_is_unit(it: &mut Interp, ring: &Ring, x: &Elem) -> bool {
    let base_unit = |it: &mut Interp, base: &Value, c: Elem| match crate::rings::small::expand(&it.elem_to_value(base, c)) {
        Value::Int(n) => n.is_one() || (-&n).is_one(),
        Value::Rat(q) => q.sign() != 0,
        Value::Real(r) => !r.x.is_zero(),
        Value::Complex(c) => !c.is_zero(),
        Value::Elt(e) => elt_is_unit(it, &e.ring_rc(), &e.x),
        _ => false,
    };
    match &ring.kind {
        RingKind::UPoly { base, .. } => x.poly_len() == 1 && base_unit(it, base, x.poly_coeff(0)),
        RingKind::MPoly { base, .. } => {
            if x.mpoly_len() != 1 {
                return false;
            }
            let (c, exps) = x.mpoly_term(0);
            exps.iter().all(|&k| k == 0) && base_unit(it, base, c)
        }
        _ => x.is_invertible() == Truth::True,
    }
}

fn multiplicative_order(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let e = elt_arg(a, 0)?;
    match &e.ring().kind {
        RingKind::Finite(_) => {
            if e.x.is_zero() == Truth::True {
                return Err(RuntimeError::runtime("Can not take order of zero element"));
            }
            intv(crate::rings::finite::mult_order(&e.parent, &e.x))
        }
        RingKind::Residue(m) => {
            let x = e.residue().unwrap();
            if x.is_zero() {
                return Err(RuntimeError::runtime("Can not take order of zero element"));
            }
            intv(crate::intrinsics::ints::modorder(&x, m))
        }
        _ => Err(RuntimeError::runtime("Bad argument types")),
    }
}

pub fn register(it: &mut Interp) {
    for name in ["Integers", "IntegerRing", "RingOfIntegers", "ResidueClassRing"] {
        it.def(name, "m::RngIntElt -> RngIntRes, Map", "The ring of integers modulo m.", residue_ring);
    }
    it.def("Modulus", "R::RngIntRes -> RngIntElt", "The modulus of the residue class ring R.", modulus);

    it.def("ResidueClassField", "p::RngIntElt -> FldFin, Map", "The finite field of prime order p.", |it, a| {
        let p = a.int(0)?.clone();
        if !p.is_prime() {
            return Err(RuntimeError::runtime("Argument must be prime"));
        }
        residue_class_field(it, p)
    });
    it.def("ResidueClassField", "I::RngInt -> FldFin, Map", "The residue class field of the maximal ideal I of the integers.", |it, a| {
        let p = crate::rings::ideals::int_ideal_gen(&a.args[0]).unwrap_or_default();
        if !p.is_prime() {
            return Err(RuntimeError::runtime("Ideal is not maximal"));
        }
        residue_class_field(it, p)
    });
    it.def("PrimeField", "F::Fld -> Fld", "The prime field of F.", prime_field);
    it.def("IsPrimeField", "F::Fld -> BoolElt", "Whether F is a prime field.", is_prime_field);
    it.def("PrimitiveElement", "R::RngIntRes -> RngIntResElt", "A generator of the unit group of R, or 0.", primitive_element);
    it.def("PrimitiveRoot", "R::RngIntRes -> RngIntResElt", "A generator of the unit group of R, or 0.", primitive_element);

    for name in ["PolynomialRing", "PolynomialAlgebra"] {
        it.def_params(name, "R::Rng -> RngUPol", &[("Global", Value::Bool(true))], "The univariate polynomial ring over R.", polynomial_ring);
    }
    for name in ["BaseRing", "CoefficientRing"] {
        it.def(name, "P::RngUPol -> Rng", "The coefficient ring of P.", base_ring);
        it.def(name, "P::RngMPol -> Rng", "The coefficient ring of P.", base_ring);
        it.def(name, "f::RngUPolElt -> Rng", "The coefficient ring of the parent of f.", base_ring);
        it.def(name, "f::RngMPolElt -> Rng", "The coefficient ring of the parent of f.", base_ring);
        it.def(name, "Q::RngMPolRes -> Rng", "The coefficient ring of Q.", base_ring);
    }

    for t in ["FldFin", "RngUPol", "RngMPol"] {
        it.def("Ngens", &format!("R::{t} -> RngIntElt"), "The number of generators of R.", ngens);
        it.def(".", &format!("R::{t}, i::RngIntElt -> RngElt"), "The i-th generator of R.", generator);
        it.def("Name", &format!("R::{t}, i::RngIntElt -> RngElt"), "The i-th generator of R.", generator);
        it.def("AssignNames", &format!("~R::{t}, N::[MonStgElt]"), "Set the names used to print the generators of R.", assign_names);
    }
    it.def("Ngens", "R::RngIntRes -> RngIntElt", "The number of generators of R.", ngens);
    for t in ["RngUPol", "RngMPol"] {
        it.def("Rank", &format!("R::{t} -> RngIntElt"), "The number of variables of R.", ngens);
    }

    // Properties of any ring.
    it.def("Characteristic", "R::Rng -> RngIntElt", "The characteristic of R.", characteristic);
    it.def("IsFinite", "R::Rng -> BoolElt, RngIntElt", "Whether R is finite, and if so its cardinality.", is_finite);
    it.def("IsCommutative", "R::Rng -> BoolElt", "True for the rings of this kind.", is_true);
    it.def("IsUnitary", "R::Rng -> BoolElt", "Whether R has an identity: true but for ideals of polynomial rings.", is_unitary);
    it.def("IsOrdered", "R::Rng -> BoolElt", "Whether R is ordered.", is_ordered);
    for name in ["IsField", "IsDivisionRing"] {
        it.def(name, "R::Rng -> BoolElt", "Whether R is a field.", is_field);
    }
    it.def("IsEuclideanDomain", "R::Rng -> BoolElt", "Whether R is a Euclidean domain.", is_euclidean_domain);
    it.def("IsEuclideanRing", "R::Rng -> BoolElt", "Whether R is a Euclidean ring.", is_euclidean_ring);
    it.def("IsMagmaEuclideanRing", "R::Rng -> BoolElt", "Whether Magma's Euclidean algorithms (div, mod, Gcd) apply to R.", is_magma_euclidean);
    for name in ["IsPID", "IsPrincipalIdealDomain"] {
        it.def(name, "R::Rng -> BoolElt", "Whether R is a principal ideal domain.", is_pid);
    }
    for name in ["IsPIR", "IsPrincipalIdealRing"] {
        it.def(name, "R::Rng -> BoolElt", "Whether R is a principal ideal ring.", is_pir);
    }
    it.def("IsUFD", "R::Rng -> BoolElt", "Whether R is a unique factorization domain.", is_ufd);
    for name in ["IsDomain", "IsIntegralDomain"] {
        it.def(name, "R::Rng -> BoolElt", "Whether R is an integral domain.", is_domain);
    }
    it.def("HasGCD", "R::Rng -> BoolElt", "Whether greatest common divisors can be computed in R.", has_gcd);
    it.def("PrimeRing", "R::Rng -> Rng", "The prime ring of R (its prime field if R is a field).", prime_ring);
    for name in ["Centre", "Center"] {
        it.def(name, "R::Rng -> Rng", "The centre of R (R itself: these rings are commutative).", centre);
    }

    for t in ["RngIntResElt", "FldFinElt", "RngUPolElt", "RngMPolElt"] {
        it.def("IsZero", &format!("x::{t} -> BoolElt"), "Whether x is zero.", is_zero);
        it.def("IsOne", &format!("x::{t} -> BoolElt"), "Whether x is one.", is_one);
        it.def("IsMinusOne", &format!("x::{t} -> BoolElt"), "Whether x is minus one.", is_minus_one);
        it.def("IsUnit", &format!("x::{t} -> BoolElt"), "Whether x is a unit.", is_unit);
    }
    it.def("Order", "x::FldFinElt -> RngIntElt", "The multiplicative order of x.", multiplicative_order);
    it.def("Order", "x::RngIntResElt -> RngIntElt", "The multiplicative order of x (0 if x is not a unit).", multiplicative_order);
}
