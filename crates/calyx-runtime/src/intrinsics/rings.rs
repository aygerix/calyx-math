//! Generic ring functions and the constructors of residue class rings,
//! finite fields, polynomial rings and complex fields.

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{Elem, MonomialOrder, Truth};

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
            _ => Err(RuntimeError::runtime("Bad argument types")),
        },
        _ => Err(RuntimeError::runtime("Bad argument types")),
    }
}

fn elt_arg(a: &CallArgs, i: usize) -> RResult<Rc<crate::rings::Elt>> {
    match &a.args[i] {
        Value::Elt(e) => Ok(e.clone()),
        _ => Err(RuntimeError::runtime("Bad argument types")),
    }
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
    let (_, r) = ring_arg(a, 0)?;
    match &r.kind {
        RingKind::Residue(m) => intv(m.clone()),
        _ => Err(RuntimeError::runtime("Bad argument types")),
    }
}

// ----- finite fields ---------------------------------------------------------

fn finite_field_q(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let q = a.int(0)?.clone();
    let err = || RuntimeError::runtime("Argument must be a prime power");
    if q.sign() <= 0 {
        return Err(err());
    }
    let f = q.factor().ok_or_else(err)?;
    if f.factors.len() != 1 {
        return Err(err());
    }
    let (p, n) = f.factors[0].clone();
    one(it.finite_field(&p, n)?)
}

fn finite_field_pn(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = a.int(0)?.clone();
    let n = a.int(1)?.clone();
    let check = a.param_bool("Check")?;
    if n.sign() <= 0 {
        return Err(RuntimeError::runtime("Argument 2 must be positive"));
    }
    if p.sign() <= 0 || (check && !p.is_probable_prime()) {
        return Err(RuntimeError::runtime("Argument 1 must be prime"));
    }
    let n = n.to_u64().ok_or_else(|| RuntimeError::runtime("Degree is too large"))?;
    one(it.finite_field(&p, n)?)
}

fn degree_ff(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, r) = ring_arg(a, 0)?;
    match &r.kind {
        RingKind::Finite(f) => intv(Integer::from_u64(f.degree)),
        _ => Err(RuntimeError::runtime("Bad argument types")),
    }
}

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

fn is_conway(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, r) = ring_arg(a, 0)?;
    boolv(r.finite_field().is_some_and(|f| f.conway))
}

fn is_default(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, r) = ring_arg(a, 0)?;
    boolv(r.finite_field().is_some_and(|f| f.default))
}

fn defining_polynomial_ff(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, r) = ring_arg(a, 0)?;
    let f = r.finite_field().ok_or_else(|| RuntimeError::runtime("Bad argument types"))?;
    let p = f.p.clone();
    let modulus = if f.degree == 1 { vec![Integer::zero(), Integer::one()] } else { f.modulus.clone() };
    let fp = it.finite_field(&p, 1)?;
    let px = it.poly_ring(&fp, true)?;
    let coeffs: Vec<Value> = modulus.into_iter().map(Value::Int).collect();
    one(it.coerce(&px, &Value::seq(Some(Value::integers()), coeffs))?)
}

fn conway_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = a.int(0)?.clone();
    let n = a.int(1)?.clone();
    let c = p.to_u64().zip(n.to_u64()).and_then(|(p, n)| calyx_flint::gr::conway_polynomial(p, n));
    let Some(c) = c else {
        return Err(RuntimeError::runtime("Conway polynomial not known for these parameters"));
    };
    let fp = it.finite_field(&p, 1)?;
    let px = it.poly_ring(&fp, true)?;
    one(it.coerce(&px, &Value::seq(Some(Value::integers()), c.into_iter().map(Value::Int).collect()))?)
}

fn set_power_printing(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, r) = ring_arg(a, 0)?;
    let on = a.bool(1)?;
    let f = r.finite_field().ok_or_else(|| RuntimeError::runtime("Bad argument types"))?;
    if on && !matches!(r.ctx.kind(), calyx_flint::gr::CtxKind::FqZech { .. }) {
        return Err(RuntimeError::runtime("Power printing is only possible for small fields defined by a primitive polynomial"));
    }
    f.power_printing.set(on);
    none()
}

fn primitive_element(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, r) = ring_arg(a, 0)?;
    match &r.kind {
        RingKind::Finite(f) => {
            if f.degree > 1 && matches!(r.ctx.kind(), calyx_flint::gr::CtxKind::FqZech { .. }) {
                return one(make_elt(&st, r.ctx.generator()?));
            }
            // Search for a primitive element among small polynomials in
            // the generator (the generator itself first).
            let q1 = &f.order() - &Integer::one();
            let primes: Vec<Integer> = q1.factor().map(|fac| fac.factors.into_iter().map(|(p, _)| p).collect()).unwrap_or_default();
            let g0 = if f.degree == 1 { Elem::from_i64(&r.ctx, 1)? } else { r.ctx.generator()? };
            let mut k: i64 = if f.degree == 1 { 2 } else { 0 };
            loop {
                let cand = if f.degree == 1 { Elem::from_i64(&r.ctx, k)? } else { g0.add(&Elem::from_i64(&r.ctx, k)?)? };
                if cand.is_zero() != Truth::True && primes.iter().all(|p| cand.pow(&(&q1).div_rem_euclid(p).unwrap().0).map(|x| x.is_one() != Truth::True).unwrap_or(false)) {
                    return one(make_elt(&st, cand));
                }
                k += 1;
                if k > 1_000_000 {
                    return Err(RuntimeError::runtime("No primitive element found"));
                }
                let _ = it;
            }
        }
        RingKind::Residue(m) => {
            let m = m.clone();
            let root = crate::intrinsics::ints::primitive_root(&m).unwrap_or_default();
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

fn parse_order(s: &str) -> RResult<MonomialOrder> {
    Ok(match s {
        "lex" => MonomialOrder::Lex,
        "glex" => MonomialOrder::DegLex,
        "grevlex" => MonomialOrder::DegRevLex,
        _ => return Err(RuntimeError::runtime(format!("Unsupported monomial order \"{s}\""))),
    })
}

fn mpolynomial_ring(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let base = a.args[0].clone();
    let n = a.usize(1)?;
    if n == 0 {
        return Err(RuntimeError::runtime("The rank must be positive"));
    }
    let order = if a.args.len() > 2 { parse_order(&a.str(2)?)? } else { MonomialOrder::Lex };
    one(it.mpoly_ring(&base, n, order)?)
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

// ----- complex fields --------------------------------------------------------

fn complex_field(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let d = if a.args.is_empty() {
        crate::intrinsics::reals::DEFAULT_DIGITS
    } else {
        match &a.args[0] {
            Value::Struct(s) => match &s.kind {
                StructKind::Reals(d) => *d,
                _ => return Err(RuntimeError::runtime("Bad argument types")),
            },
            _ => a.usize(0)? as u32,
        }
    };
    if d == 0 {
        return Err(RuntimeError::runtime("Precision must be positive"));
    }
    one(it.complex_field(d))
}

// ----- generic ring functions -------------------------------------------------

fn ngens(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, r) = ring_arg(a, 0)?;
    intv(Integer::from_u64(r.ngens() as u64))
}

fn generator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, r) = ring_arg(a, 0)?;
    let i = a.usize(1)?;
    if i == 0 || i > r.ngens() {
        return Err(RuntimeError::runtime(format!("Generator index must be in the range [1..{}]", r.ngens())));
    }
    let g = match &r.kind {
        RingKind::MPoly { .. } => r.ctx.mpoly_gen(i - 1)?,
        RingKind::Residue(_) => Elem::one(&r.ctx)?,
        RingKind::Finite(f) if f.degree == 1 => Elem::one(&r.ctx)?,
        RingKind::Complex(_) => {
            let d = calyx_flint::bits_for_digits(0);
            let _ = d;
            let zero = calyx_flint::Real::zero(64);
            let onef = calyx_flint::Real::from_integer(&Integer::one(), 64);
            Elem::from_complex_parts(&r.ctx, &zero, &onef)?
        }
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
    if out.len() > r.ngens() {
        return Err(RuntimeError::runtime(format!("Too many names ({} given, {} generators)", out.len(), r.ngens())));
    }
    *r.names.borrow_mut() = out;
    none()
}

fn props(a: &CallArgs) -> RResult<RingProps> {
    ring_props(&a.args[0]).ok_or_else(|| RuntimeError::runtime("Bad argument types"))
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
            Some(StructKind::Ring(r)) => match &r.kind {
                RingKind::Complex(_) => Value::rationals(),
                RingKind::Residue(_) => v.clone(),
                RingKind::Finite(f) => {
                    let p = f.p.clone();
                    it.finite_field(&p, 1)?
                }
                RingKind::UPoly { base, .. } | RingKind::MPoly { base, .. } => {
                    let base = base.clone();
                    of(it, &base)?
                }
            },
            _ => return Err(RuntimeError::runtime("Bad argument types")),
        })
    }
    let r = of(it, &a.args[0])?;
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

/// Units: non-zero complex numbers, and constant polynomials whose constant
/// is a unit of the coefficient ring.
fn elt_is_unit(it: &mut Interp, ring: &Ring, x: &Elem) -> bool {
    let base_unit = |it: &mut Interp, base: &Value, c: Elem| match it.elem_to_value(base, c) {
        Value::Int(n) => n.is_one() || (-&n).is_one(),
        Value::Rat(q) => q.sign() != 0,
        Value::Real(r) => r.x.sign() != 0,
        Value::Elt(e) => elt_is_unit(it, &e.ring_rc(), &e.x),
        _ => false,
    };
    match &ring.kind {
        RingKind::Complex(_) => x.is_zero() != Truth::True,
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
        RingKind::Finite(f) => {
            if e.x.is_zero() == Truth::True {
                return Err(RuntimeError::runtime("Argument must be non-zero"));
            }
            if f.degree == 1 {
                let x = e.residue().unwrap();
                return intv(crate::intrinsics::ints::modorder(&x, &f.p));
            }
            intv(e.x.fq_multiplicative_order()?)
        }
        RingKind::Residue(m) => {
            let x = e.residue().unwrap();
            intv(crate::intrinsics::ints::modorder(&x, m))
        }
        _ => Err(RuntimeError::runtime("Bad argument types")),
    }
}

fn eltseq_ff(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let e = elt_arg(a, 0)?;
    let f = e.ring().finite_field().ok_or_else(|| RuntimeError::runtime("Bad argument types"))?;
    let p = f.p.clone();
    let fp = it.finite_field(&p, 1)?;
    let Value::Struct(fps) = &fp else { unreachable!() };
    let StructKind::Ring(fr) = &fps.kind else { unreachable!() };
    let coords = if f.degree == 1 { vec![e.residue().unwrap()] } else { e.x.fq_coords() };
    let mut out = Vec::with_capacity(coords.len());
    for c in coords {
        out.push(make_elt(fps, Elem::from_integer(&fr.ctx, &c)?));
    }
    one(Value::seq(Some(fp.clone()), out))
}

pub fn register(it: &mut Interp) {
    for name in ["Integers", "IntegerRing", "RingOfIntegers", "ResidueClassRing"] {
        it.def(name, "m::RngIntElt -> RngIntRes, Map", "The ring of integers modulo m.", residue_ring);
    }
    it.def("Modulus", "R::RngIntRes -> RngIntElt", "The modulus of the residue class ring R.", modulus);

    for name in ["FiniteField", "GaloisField", "GF"] {
        it.def_params(name, "q::RngIntElt -> FldFin", &[("Optimize", Value::Bool(true)), ("Sparse", Value::Bool(false))], "The finite field with q elements.", finite_field_q);
        it.def_params(
            name,
            "p::RngIntElt, n::RngIntElt -> FldFin",
            &[("Check", Value::Bool(true)), ("Optimize", Value::Bool(true)), ("Sparse", Value::Bool(false))],
            "The finite field with p^n elements.",
            finite_field_pn,
        );
    }
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
    it.def("Degree", "F::FldFin -> RngIntElt", "The degree of F over its prime field.", degree_ff);
    it.def("PrimeField", "F::Fld -> Fld", "The prime field of F.", prime_field);
    it.def("IsPrimeField", "F::Fld -> BoolElt", "Whether F is a prime field.", is_prime_field);
    it.def("IsConway", "F::FldFin -> BoolElt", "Whether F is defined by a Conway polynomial.", is_conway);
    it.def("IsDefault", "F::FldFin -> BoolElt", "Whether F is a default field.", is_default);
    it.def("DefiningPolynomial", "F::FldFin -> RngUPolElt", "The polynomial defining F over its prime field.", defining_polynomial_ff);
    it.def("ConwayPolynomial", "p::RngIntElt, n::RngIntElt -> RngUPolElt", "The Conway polynomial of degree n over GF(p).", conway_polynomial);
    it.def("SetPowerPrinting", "F::FldFin, l::BoolElt", "Print elements of F as powers of the primitive element (or not).", set_power_printing);
    it.def("PrimitiveElement", "F::FldFin -> FldFinElt", "A primitive element of F.", primitive_element);
    it.def("PrimitiveElement", "R::RngIntRes -> RngIntResElt", "A generator of the unit group of R, or 0.", primitive_element);
    it.def("PrimitiveRoot", "R::RngIntRes -> RngIntResElt", "A generator of the unit group of R, or 0.", primitive_element);
    for name in ["ElementToSequence", "Eltseq"] {
        it.def(name, "a::FldFinElt -> [FldFinElt]", "The coefficients of a in terms of the generator of its field.", eltseq_ff);
    }

    for name in ["PolynomialRing", "PolynomialAlgebra"] {
        it.def_params(name, "R::Rng -> RngUPol", &[("Global", Value::Bool(true))], "The univariate polynomial ring over R.", polynomial_ring);
    }
    it.def_params("PolynomialRing", "R::Rng, n::RngIntElt -> RngMPol", &[("Global", Value::Bool(false))], "The polynomial ring in n variables over R.", mpolynomial_ring);
    it.def_params("PolynomialRing", "R::Rng, n::RngIntElt, order::MonStgElt -> RngMPol", &[("Global", Value::Bool(false))], "The polynomial ring in n variables over R with the given monomial order.", mpolynomial_ring);
    for name in ["BaseRing", "CoefficientRing"] {
        it.def(name, "P::RngUPol -> Rng", "The coefficient ring of P.", base_ring);
        it.def(name, "P::RngMPol -> Rng", "The coefficient ring of P.", base_ring);
        it.def(name, "f::RngUPolElt -> Rng", "The coefficient ring of the parent of f.", base_ring);
        it.def(name, "f::RngMPolElt -> Rng", "The coefficient ring of the parent of f.", base_ring);
    }

    it.def_params("ComplexField", "-> FldCom", &[("Bits", Value::Bool(false))], "The default complex field.", complex_field);
    it.def_params("ComplexField", "p::RngIntElt -> FldCom", &[("Bits", Value::Bool(false))], "The complex field with p decimal digits of precision.", complex_field);
    it.def("ComplexField", "R::FldRe -> FldCom", "The complex field containing R.", complex_field);

    for t in ["FldFin", "RngUPol", "RngMPol", "FldCom"] {
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
    for name in ["IsCommutative", "IsUnitary"] {
        it.def(name, "R::Rng -> BoolElt", "True for the rings of this kind.", is_true);
    }
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

    for t in ["RngIntResElt", "FldFinElt", "RngUPolElt", "RngMPolElt", "FldComElt"] {
        it.def("IsZero", &format!("x::{t} -> BoolElt"), "Whether x is zero.", is_zero);
        it.def("IsOne", &format!("x::{t} -> BoolElt"), "Whether x is one.", is_one);
        it.def("IsMinusOne", &format!("x::{t} -> BoolElt"), "Whether x is minus one.", is_minus_one);
        it.def("IsUnit", &format!("x::{t} -> BoolElt"), "Whether x is a unit.", is_unit);
    }
    it.def("Order", "x::FldFinElt -> RngIntElt", "The multiplicative order of x.", multiplicative_order);
    it.def("Order", "x::RngIntResElt -> RngIntElt", "The multiplicative order of x (0 if x is not a unit).", multiplicative_order);
}
