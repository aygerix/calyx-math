//! Multivariate polynomial rings (the handbook chapter of that name):
//! creating rings and polynomials, structure operations, the functions of
//! polynomials, greatest common divisors, factorization, resultants and
//! the functions for integer polynomials.
//!
//! Polynomials are `gr_mpoly`s, whose generic arithmetic is fast enough
//! (it beats Magma on Fateman's benchmark). The algorithms beyond it run
//! on FLINT's specialised types through `calyx_flint::mpoly`.

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{Elem, MonomialOrder, Truth};

use super::{none, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::rings::{Elt, Ring, RingKind, make_elt};
use crate::value::*;

// ----- helpers ---------------------------------------------------------------

/// Argument `i`, which the signature makes a multivariate polynomial.
fn mpol(a: &CallArgs, i: usize) -> Rc<Elt> {
    match &a.args[i] {
        Value::Elt(e) => e.clone(),
        _ => unreachable!("a polynomial argument"),
    }
}

/// Argument `i`, a multivariate polynomial ring.
fn ring_arg(a: &CallArgs, i: usize) -> (Rc<Struct>, Rc<Ring>) {
    match &a.args[i] {
        Value::Struct(s) => match &s.kind {
            StructKind::Ring(r) => (s.clone(), r.clone()),
            _ => unreachable!("a polynomial ring argument"),
        },
        _ => unreachable!("a polynomial ring argument"),
    }
}

/// The rank of a multivariate polynomial ring.
fn rank(r: &Ring) -> usize {
    match &r.kind {
        RingKind::MPoly { rank, .. } => *rank,
        _ => unreachable!("a multivariate polynomial ring"),
    }
}

/// The index of `v` among the variables of the ring of `f` (from 0), if
/// it is one of them.
fn var_index(f: &Elt, v: &Value) -> Option<usize> {
    let Value::Elt(v) = v else { return None };
    if v.ring().id != f.ring().id || v.x.mpoly_len() != 1 {
        return None;
    }
    let (c, exps) = v.x.mpoly_term(0);
    if c.is_one() != Truth::True || exps.iter().sum::<u64>() != 1 {
        return None;
    }
    exps.iter().position(|&e| e == 1)
}

/// Argument `i` naming a variable of `P` of rank `n`, by number (1 to n) or
/// as the variable itself, as an index from 0. `what` words the error for a
/// number out of range ("variable number", "name index").
fn var_arg(a: &CallArgs, i: usize, f: &Elt, what: &str) -> RResult<usize> {
    let n = rank(f.ring());
    match &a.args[i] {
        Value::Int(k) => match k.to_i64() {
            Some(k) if k >= 1 && k as usize <= n => Ok(k as usize - 1),
            _ => Err(RuntimeError::runtime(format!("Value for {what} ({k}) should be in the range [1..{n}]"))),
        },
        v => var_index(f, v).ok_or_else(|| RuntimeError::runtime(format!("Argument {} is not a variable", i + 1))),
    }
}

// ----- creation --------------------------------------------------------------

/// The monomial order named `s`.
fn parse_order(s: &str) -> RResult<MonomialOrder> {
    Ok(match s {
        "lex" => MonomialOrder::Lex,
        "glex" => MonomialOrder::DegLex,
        "grevlex" => MonomialOrder::DegRevLex,
        _ => return Err(RuntimeError::runtime(format!("Bad order \"{s}\""))),
    })
}

/// `PolynomialRing(R, n)` (global with the parameter Global) and
/// `PolynomialRing(R, n, order)`.
fn polynomial_ring(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let base = a.args[0].clone();
    let n = a.int(1)?;
    let Some(n) = n.to_i64().filter(|n| (0..1 << 29).contains(n)) else {
        return Err(RuntimeError::runtime(format!("Argument 2 ({n}) should be in the range [0 .. 536870911]")));
    };
    let order = if a.args.len() > 2 { parse_order(&a.str(2)?)? } else { MonomialOrder::Lex };
    let global = a.args.len() == 2 && a.param_bool("Global")?;
    one(it.mpoly_ring(&base, n as usize, order, global)?)
}

fn identity(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, r) = ring_arg(a, 0);
    one(make_elt(&st, Elem::one(&r.ctx)?))
}

/// `MultivariatePolynomial(P, f, v)`: the univariate `f` in the variable v
/// of P (given by number or as the variable).
fn multivariate_polynomial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, r) = ring_arg(a, 0);
    let Value::Elt(f) = &a.args[1] else { unreachable!("a polynomial argument") };
    let base = r.base().expect("a polynomial ring");
    if f.ring().base() != Some(base) {
        return Err(RuntimeError::runtime("Arguments have incompatible coefficient rings"));
    }
    let n = rank(&r);
    let i = match &a.args[2] {
        Value::Int(k) => match k.to_i64() {
            Some(k) if k >= 1 && k as usize <= n => k as usize - 1,
            _ => return Err(RuntimeError::runtime(format!("Value for variable number ({k}) should be in the range [1..{n}]"))),
        },
        v => {
            let p = Elt { parent: st.clone(), x: Elem::zero(&r.ctx) };
            var_index(&p, v).ok_or_else(|| RuntimeError::runtime("Argument 3 is not a variable"))?
        }
    };
    let mut terms = Vec::with_capacity(f.x.poly_len());
    for k in 0..f.x.poly_len() {
        let c = f.x.poly_coeff(k);
        if c.is_zero() != Truth::True {
            let mut exps = vec![0u64; n];
            exps[i] = k as u64;
            terms.push((c, exps));
        }
    }
    one(make_elt(&st, Elem::mpoly_from_terms(&r.ctx, &terms)?))
}

pub fn register(it: &mut Interp) {
    for name in ["PolynomialRing", "PolynomialAlgebra"] {
        it.def_params(name, "R::Rng, n::RngIntElt -> RngMPol", &[("Global", Value::Bool(false))], "The polynomial ring in n variables over R (the global one with Global).", polynomial_ring);
        it.def(name, "R::Rng, n::RngIntElt, order::MonStgElt -> RngMPol", "The polynomial ring in n variables over R with the given monomial order.", polynomial_ring);
    }
    it.def("Identity", "P::RngMPol -> RngMPolElt", "The identity of P.", identity);
    it.def("MultivariatePolynomial", "P::RngMPol, f::RngUPolElt, i::RngIntElt -> RngMPolElt", "The univariate polynomial f in the i-th variable of P.", multivariate_polynomial);
    it.def("MultivariatePolynomial", "P::RngMPol, f::RngUPolElt, v::RngMPolElt -> RngMPolElt", "The univariate polynomial f in the variable v of P.", multivariate_polynomial);
}
