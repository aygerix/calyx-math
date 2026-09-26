//! Predicates on ring elements that apply to every kind of ring: integers,
//! rationals and reals as well as the elements of FLINT-backed rings.

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::Truth;

use super::boolv;
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::rings::{Elt, RingKind};
use crate::value::*;

fn not_possible() -> RuntimeError {
    RuntimeError::runtime("Algorithm not possible for this type of element")
}

fn truth(t: Truth) -> bool {
    t == Truth::True
}

fn is_unit(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(match &a.args[0] {
        Value::Int(n) => n.is_one() || (-n).is_one(),
        Value::Rat(q) => q.sign() != 0,
        Value::Real(r) => r.x.sign() != 0,
        _ => unreachable!(),
    })
}

fn is_one(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Real(r) = &a.args[0] else { unreachable!() };
    boolv(r.x.to_rational().is_some_and(|q| q.is_integral() && q.numerator().is_one()))
}

fn is_minus_one(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Real(r) = &a.args[0] else { unreachable!() };
    boolv(r.x.to_rational().is_some_and(|q| q.is_integral() && (-&q.numerator()).is_one()))
}

/// `x^2 = x`
fn is_idempotent(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let arg = crate::rings::small::expand(&a.args[0]);
    let zero_or_one = |q: Option<calyx_flint::Rational>| q.is_some_and(|q| q.sign() == 0 || (q.is_integral() && q.numerator().is_one()));
    boolv(match &arg {
        Value::Int(n) => n.is_zero() || n.is_one(),
        Value::Rat(q) => zero_or_one(Some((**q).clone())),
        Value::Real(r) => zero_or_one(r.x.to_rational()),
        Value::Elt(e) => e.x.sqr().is_ok_and(|s| truth(s.equal(&e.x))),
        _ => unreachable!(),
    })
}

/// Whether some power of x is zero, and if so the least such power.
fn is_nilpotent(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let arg = crate::rings::small::expand(&a.args[0]);
    let yes = |k: u64| Ok(vals![Value::Bool(true), Value::Int(Integer::from_u64(k))]);
    let zero = match &arg {
        Value::Int(n) => n.is_zero(),
        Value::Rat(q) => q.sign() == 0,
        Value::Real(r) => r.x.sign() == 0,
        Value::Elt(e) => {
            if truth(e.x.is_zero()) {
                return yes(1);
            }
            return match &e.ring().kind {
                RingKind::Residue(m) => {
                    // The exponent needed is at most the largest exponent in
                    // the factorisation of m, which is at most log2(m).
                    let mut y = e.x.clone();
                    for k in 2..=m.bits() + 1 {
                        y = y.mul(&e.x).map_err(|_| not_possible())?;
                        if truth(y.is_zero()) {
                            return yes(k);
                        }
                    }
                    boolv(false)
                }
                RingKind::UPoly { .. } | RingKind::MPoly { .. } => Err(RuntimeError::runtime("Operation not supported for this type of element")),
                _ => boolv(false),
            };
        }
        _ => unreachable!(),
    };
    if zero { yes(1) } else { boolv(false) }
}

/// Whether x is a non-zero element with a non-zero multiple equal to zero.
fn is_zero_divisor(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let arg = crate::rings::small::expand(&a.args[0]);
    let Value::Elt(e) = &arg else { return boolv(false) };
    boolv(match &e.ring().kind {
        RingKind::Residue(m) => !truth(e.x.is_zero()) && e.residue().is_some_and(|r| !r.gcd(m).is_one()),
        RingKind::UPoly { base, .. } | RingKind::MPoly { base, .. } => {
            if !crate::rings::props::ring_props(base).is_some_and(|p| p.domain) {
                return Err(not_possible());
            }
            false
        }
        _ => false,
    })
}

/// Irreducibility and primality agree in the rings calyx has so far: an
/// integer is irreducible when its absolute value is prime, and field
/// elements never are.
fn irreducible(e: &Value) -> RResult<bool> {
    Ok(match e {
        Value::Int(n) => n.abs().is_prime(),
        Value::Rat(_) | Value::Real(_) => false,
        Value::Elt(e) => elt_irreducible(e)?,
        _ => unreachable!(),
    })
}

fn elt_irreducible(e: &Rc<Elt>) -> RResult<bool> {
    match &e.ring().kind {
        RingKind::Residue(_) => Err(not_possible()),
        RingKind::Finite(_) | RingKind::Complex(_) => Ok(false),
        RingKind::UPoly { .. } | RingKind::MPoly { .. } => {
            if truth(e.x.is_zero()) {
                return Err(RuntimeError::runtime("Argument 1 is not non-zero"));
            }
            Err(RuntimeError::runtime("Polynomial factorization is not available yet"))
        }
    }
}

fn is_irreducible(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let arg = crate::rings::small::expand(&a.args[0]);
    boolv(irreducible(&arg)?)
}

fn is_prime_elt(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let arg = crate::rings::small::expand(&a.args[0]);
    if let Value::Elt(e) = &arg {
        if matches!(e.ring().kind, RingKind::Residue(_)) {
            return Err(RuntimeError::runtime("Algorithm not possible for this type of element"));
        }
    }
    boolv(irreducible(&arg)?)
}

pub fn register(it: &mut Interp) {
    for t in ["RngIntElt", "FldRatElt", "FldReElt"] {
        it.def("IsUnit", &format!("x::{t} -> BoolElt"), "Whether x is a unit.", is_unit);
    }
    it.def("IsOne", "x::FldReElt -> BoolElt", "Whether x is one.", is_one);
    it.def("IsMinusOne", "x::FldReElt -> BoolElt", "Whether x is minus one.", is_minus_one);
    it.def("IsIdempotent", "x::RngElt -> BoolElt", "Whether x^2 = x.", is_idempotent);
    it.def("IsNilpotent", "x::RngElt -> BoolElt, RngIntElt", "Whether some power of x is zero, and if so the least such power.", is_nilpotent);
    it.def("IsZeroDivisor", "x::RngElt -> BoolElt", "Whether x is a non-zero zero divisor.", is_zero_divisor);
    it.def("IsIrreducible", "x::RngElt -> BoolElt", "Whether x is irreducible (a non-unit with no proper factorisation).", is_irreducible);
    it.def("IsPrime", "x::RngElt -> BoolElt", "Whether x is a prime element.", is_prime_elt);
}
