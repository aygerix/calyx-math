//! Arithmetic and comparison of ring elements.

use std::borrow::Cow;
use std::cmp::Ordering;
use std::rc::Rc;

use calyx_flint::gr::{CtxKind, Elem, GrError, Truth};
use calyx_syntax::ast::BinOp;

use super::finite;
use super::small::{self, SmallRing};
use super::{Elt, Ring, RingKind, make_elt};
use crate::error::{RResult, RuntimeError};
use crate::interp::Interp;
use crate::ops::div_by_zero;
use crate::value::{Struct, StructKind, Value};

/// Arithmetic and comparison of inline ring elements with each other and
/// with integers. `None` leaves the operation to the generic path, which
/// also reports errors (a non-invertible divisor, say).
#[inline]
pub fn small_binop(op: BinOp, a: &Value, b: &Value) -> Option<Value> {
    use BinOp::*;
    let (r, x, y) = match (a, b) {
        (Value::Small(r, x), Value::Small(s, y)) if r == s => (*r, *x, *y),
        (Value::Small(r, x), Value::Int(k)) if op == Pow => return small_pow(*r, *x, k),
        (Value::Small(r, x), Value::Int(i)) => (*r, *x, r.modulus().reduce_integer(i)),
        (Value::Int(i), Value::Small(r, y)) if op != Pow => (*r, r.modulus().reduce_integer(i), *y),
        _ => return None,
    };
    let m = r.modulus();
    Some(match op {
        Add => Value::Small(r, m.add(x, y)),
        Sub => Value::Small(r, m.sub(x, y)),
        Mul => Value::Small(r, m.mul(x, y)),
        Div if m.modulus() > 1 => Value::Small(r, m.mul(x, m.inv(y)?)),
        IntDiv if y != 0 && r.info().kind == small::SmallKind::Residue => Value::Small(r, residue_div(m, x, y)),
        Eq | Cmpeq => Value::Bool(x == y),
        Ne | Cmpne => Value::Bool(x != y),
        Lt => Value::Bool(x < y),
        Le => Value::Bool(x <= y),
        Gt => Value::Bool(x > y),
        Ge => Value::Bool(x >= y),
        _ => return None,
    })
}

/// `x div y` in `Z/nZ` for `y ≠ 0`, as Magma computes it: with `s y = g`
/// from the textbook extended Euclidean algorithm on `(y, n)`, the quotient
/// is `floor(x / g) * s` (`x / y` for a unit `y`).
fn residue_div(m: calyx_flint::Nmod, x: u64, y: u64) -> u64 {
    let n = m.modulus();
    let (mut r0, mut r1) = (y as i128, n as i128);
    let (mut s0, mut s1) = (1i128, 0i128);
    while r1 != 0 {
        let q = r0 / r1;
        (r0, r1) = (r1, r0 - q * r1);
        (s0, s1) = (s1, s0 - q * s1);
    }
    m.mul(x / r0 as u64, s0.rem_euclid(n as i128) as u64)
}

/// `x^k` for an inline element (`None` for a non-invertible `x` and `k < 0`).
fn small_pow(r: SmallRing, x: u64, k: &calyx_flint::Integer) -> Option<Value> {
    let m = r.modulus();
    if k.sign() >= 0 {
        return Some(Value::Small(r, m.pow_integer(x, k)));
    }
    if m.modulus() == 1 {
        return None;
    }
    Some(Value::Small(r, m.pow_integer(m.inv(x)?, &-k)))
}

/// A finite field, or a polynomial ring over one.
fn over_finite_field(v: &Value) -> bool {
    match v.as_struct() {
        Some(StructKind::Ring(r)) => match &r.kind {
            RingKind::Finite(_) => true,
            RingKind::UPoly { base, .. } | RingKind::MPoly { base, .. } => over_finite_field(base),
            _ => false,
        },
        _ => false,
    }
}

fn arith_err(e: GrError, op: &str) -> RuntimeError {
    match e {
        GrError::Domain => RuntimeError::runtime("Arguments are not compatible").in_context(op),
        GrError::Unable => RuntimeError::runtime("Operation not supported for this ring").in_context(op),
    }
}

impl Interp {
    /// Binary operators with at least one ring element operand. Returns
    /// `None` when the operator does not apply (so user operators and the
    /// usual error can take over).
    pub fn ring_binop(&mut self, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
        use BinOp::*;
        // Sums and products of two elements of the same ring.
        if let (Value::Elt(x), Value::Elt(y)) = (a, b) {
            if matches!(op, Add | Sub | Mul) && x.ring().id == y.ring().id {
                let r = match op {
                    Add => x.x.add(&y.x),
                    Sub => x.x.sub(&y.x),
                    _ => x.x.mul(&y.x),
                };
                let mut r = r.map_err(|e| arith_err(e, op.intrinsic_name()))?;
                // Products in a polynomial quotient ring are reduced.
                if let (Mul, RingKind::UPolyRes { modulus, .. }) = (op, &x.ring().kind) {
                    r = crate::intrinsics::upoly::res_reduce(modulus, r).map_err(|e| arith_err(e, "*"))?;
                }
                if let (Mul, RingKind::MPolyRes { affine, .. }) = (op, &x.ring().kind) {
                    r = affine.reduce(r).map_err(|e| e.in_context("*"))?;
                }
                return Ok(Some(make_elt(&x.parent, r)));
            }
        }
        let (a, b) = (&small::expand(a), &small::expand(b));
        if op == Pow {
            return self.ring_pow(a, b);
        }
        if !matches!(op, Add | Sub | Mul | Div | IntDiv | Mod | Eq | Ne | Cmpeq | Cmpne | Lt | Le | Gt | Ge) {
            return Ok(None);
        }
        let pa = self.parent_of(a)?;
        let pb = self.parent_of(b)?;
        // Rationals coerce into finite fields (and polynomial rings over them)
        // in arithmetic, though not when choosing a universe.
        let r = match self.common_ring(&pa, &pb)? {
            None if matches!(pb.as_struct(), Some(StructKind::Rationals)) && over_finite_field(&pa) => Some(pa.clone()),
            None if matches!(pa.as_struct(), Some(StructKind::Rationals)) && over_finite_field(&pb) => Some(pb.clone()),
            r => r,
        };
        let Some(r) = r else {
            if matches!(op, Cmpeq | Cmpne) {
                return Ok(Some(Value::Bool(op == Cmpne)));
            }
            // Elements of distinct multivariate polynomial rings, or of
            // unrelated finite fields, are incompatible; multivariate elements
            // and those of a polynomial quotient compare only within their ring.
            let kind = |v: &Value| match v {
                Value::Elt(e) => match e.ring().kind {
                    RingKind::MPoly { .. } => 2,
                    RingKind::UPolyRes { .. } => 1,
                    RingKind::MPolyRes { .. } => 3,
                    _ => 0,
                },
                _ => 0,
            };
            let msg = match (kind(a), kind(b)) {
                (3, 3) => "Arguments are not compatible",
                (3, _) | (_, 3) => "Bad argument types",
                (2, 2) if op != Mod => "Arguments are not compatible",
                (1 | 2, _) | (_, 1 | 2) if matches!(op, Eq | Ne) => "Bad argument types",
                _ if finite::field_struct(&pa).is_some() && finite::field_struct(&pb).is_some() => {
                    let msg = "Arguments are not compatible\nArgument types given: FldFinElt, FldFinElt";
                    return Err(RuntimeError::runtime(msg).in_context(op.intrinsic_name()));
                }
                _ => return Ok(None),
            };
            let types = format!("Argument types given: {}, {}", self.type_name_ext(a), self.type_name_ext(b));
            return Err(RuntimeError::runtime(format!("{msg}\n{types}")).in_context(op.intrinsic_name()));
        };
        let Value::Struct(st) = &r else { return Ok(None) };
        if !matches!(st.kind, StructKind::Ring(_)) {
            // Both operands coerce into the integers, rationals or reals.
            let x = self.coerce(&r, a)?;
            let y = self.coerce(&r, b)?;
            return self.binop(op, x, y).map(Some);
        }
        let StructKind::Ring(ring) = &st.kind else { unreachable!() };
        let Some(x) = self.ring_operand(st, ring, a)? else { return Ok(None) };
        let Some(y) = self.ring_operand(st, ring, b)? else { return Ok(None) };
        let name = op.intrinsic_name();
        let v = match op {
            Add => x.add(&y).map_err(|e| arith_err(e, name))?,
            Sub => x.sub(&y).map_err(|e| arith_err(e, name))?,
            Mul => {
                let r = x.mul(&y).map_err(|e| arith_err(e, name))?;
                match &ring.kind {
                    RingKind::UPolyRes { modulus, .. } => crate::intrinsics::upoly::res_reduce(modulus, r).map_err(|e| arith_err(e, name))?,
                    RingKind::MPolyRes { affine, .. } => affine.reduce(r).map_err(|e| e.in_context(name))?,
                    _ => r,
                }
            }
            Div if matches!(ring.kind, RingKind::MPolyRes { .. }) => {
                let RingKind::MPolyRes { affine, .. } = &ring.kind else { unreachable!() };
                affine.divide(&x, &y).map_err(|e| e.in_context("/"))?
            }
            IntDiv | Mod if matches!(ring.kind, RingKind::MPolyRes { .. }) => return Ok(None),
            Div if matches!(ring.kind, RingKind::UPolyRes { .. }) => crate::intrinsics::upoly::res_div(crate::intrinsics::upoly::res_modulus(ring), &x, &y)?,
            IntDiv | Mod if matches!(ring.kind, RingKind::UPolyRes { .. }) => return Ok(None),
            Div => {
                // Magma reports a polynomial divided by zero or another
                // non-unit constant in one way.
                let upoly = matches!(ring.kind, RingKind::UPoly { .. });
                if y.is_zero() == Truth::True {
                    let e = if upoly { RuntimeError::runtime("Argument 2 is not a unit") } else { div_by_zero() };
                    return Err(e.in_context("/"));
                }
                // Division of a polynomial by a unit of the coefficient ring.
                let by_constant = match &ring.kind {
                    RingKind::UPoly { .. } if y.poly_len() == 1 => Some(y.poly_coeff(0)),
                    RingKind::MPoly { .. } if y.mpoly_len() == 1 && y.mpoly_term(0).1.iter().all(|&e| e == 0) => Some(y.mpoly_term(0).0),
                    _ => None,
                };
                if let Some(c) = by_constant {
                    let msg = if upoly { "Argument 2 is not a unit" } else { "Argument 2 is not invertible" };
                    let inv = c.inv().map_err(|_| RuntimeError::runtime(msg).in_context("/"))?;
                    let v = match &ring.kind {
                        RingKind::UPoly { .. } => x.poly_mul_scalar(&inv),
                        _ => x.mpoly_mul_scalar(&inv),
                    };
                    return Ok(Some(make_elt(st, v.map_err(|e| arith_err(e, "/"))?)));
                }
                match x.div(&y) {
                    Ok(q) => q,
                    Err(GrError::Domain) => {
                        let msg = match &ring.kind {
                            RingKind::UPoly { .. } | RingKind::MPoly { .. } => "Division is not exact",
                            _ => "Argument 2 is not invertible",
                        };
                        return Err(RuntimeError::runtime(msg).in_context("/"));
                    }
                    Err(e) => return Err(arith_err(e, "/")),
                }
            }
            IntDiv | Mod => {
                if let RingKind::Residue(m) = &ring.kind {
                    // Residues have a quotient but no remainder.
                    if op == Mod {
                        return Ok(None);
                    }
                    let (x, y) = (x.to_integer().unwrap_or_default(), y.to_integer().unwrap_or_default());
                    let q = crate::intrinsics::residue::residue_div(&x, &y, m).ok_or_else(|| div_by_zero().in_context(name))?;
                    return Ok(Some(crate::intrinsics::residue::residue_value(st, ring, &q)?));
                }
                // Multivariate polynomials divide only exactly, by zero only over
                // a field, and have no remainder.
                if let RingKind::MPoly { base, .. } = &ring.kind {
                    if op == Mod {
                        return Ok(None);
                    }
                    if y.is_zero() == Truth::True {
                        let field = super::props::ring_props(base).is_some_and(|p| p.field);
                        let e = if field { div_by_zero() } else { RuntimeError::runtime("Operation not available for this base ring") };
                        return Err(e.in_context(name));
                    }
                    return match crate::intrinsics::mpoly::exact_div(&x, &y).map_err(|e| e.in_context(name))? {
                        Some(q) => Ok(Some(make_elt(st, q))),
                        None => Err(RuntimeError::runtime("Argument 2 does not divide argument 1").in_context(name)),
                    };
                }
                if y.is_zero() == Truth::True {
                    return Err(div_by_zero().in_context(name));
                }
                let (q, rem) = match &ring.kind {
                    RingKind::UPoly { .. } => crate::intrinsics::upoly::quotrem(self, ring, &x, &y).map_err(|e| e.in_context(name))?,
                    _ => x.euclidean_divrem(&y).map_err(|e| arith_err(e, name))?,
                };
                if op == IntDiv { q } else { rem }
            }
            Eq | Ne | Cmpeq | Cmpne => {
                let e = x.equal(&y) == Truth::True;
                return Ok(Some(Value::Bool(if matches!(op, Eq | Cmpeq) { e } else { !e })));
            }
            Lt | Le | Gt | Ge => {
                let Some(c) = self.ring_elt_cmp(ring, &x, &y)? else {
                    return Err(RuntimeError::runtime("No comparison algorithm exists for given objects").in_context(name));
                };
                return Ok(Some(Value::Bool(match op {
                    Lt => c == Ordering::Less,
                    Le => c != Ordering::Greater,
                    Gt => c == Ordering::Greater,
                    _ => c != Ordering::Less,
                })));
            }
            _ => unreachable!(),
        };
        Ok(Some(make_elt(st, v)))
    }

    /// An operand as an element of `ring`, borrowed when it already is one.
    fn ring_operand<'v>(&mut self, st: &Rc<Struct>, ring: &Ring, v: &'v Value) -> RResult<Option<Cow<'v, Elem>>> {
        if let Value::Elt(e) = v {
            if e.ring().id == ring.id {
                return Ok(Some(Cow::Borrowed(&e.x)));
            }
        }
        Ok(self.to_ring_elem(st, v, false)?.map(Cow::Owned))
    }

    /// Magma's order on the elements of a ring, where it has one: residues
    /// and prime field elements by value, other finite field elements by
    /// their representation (powers of the primitive element, or
    /// coordinates), polynomials by degree and then coefficients from the
    /// top, multivariate polynomials term by term in the monomial order.
    pub fn ring_elt_cmp(&mut self, ring: &Ring, x: &Elem, y: &Elem) -> RResult<Option<Ordering>> {
        Ok(Some(match &ring.kind {
            RingKind::Residue(_) => x.to_integer().ok().cmp(&y.to_integer().ok()),
            RingKind::Finite(f) if f.degree == 1 => x.to_integer().ok().cmp(&y.to_integer().ok()),
            RingKind::Finite(_) => match x.ctx().kind() {
                // Zero, then the powers of the primitive element.
                CtxKind::FqZech { .. } => x.zech_log().map(|k| k + 1).unwrap_or(0).cmp(&y.zech_log().map(|k| k + 1).unwrap_or(0)),
                _ => x.fq_coords().iter().rev().cmp(y.fq_coords().iter().rev()),
            },
            RingKind::UPoly { base, .. } | RingKind::UPolyRes { base, .. } => {
                let (m, n) = (x.poly_len(), y.poly_len());
                if m != n {
                    return Ok(Some(m.cmp(&n)));
                }
                for k in (0..m).rev() {
                    let a = self.elem_to_value(base, x.poly_coeff(k));
                    let b = self.elem_to_value(base, y.poly_coeff(k));
                    match self.compare_ord(&a, &b)? {
                        Some(Ordering::Equal) => {}
                        other => return Ok(other),
                    }
                }
                Ordering::Equal
            }
            RingKind::MPoly { base, .. } | RingKind::MPolyRes { base, .. } => {
                let order = crate::intrinsics::mpoly::order_of(ring);
                let (m, n) = (x.mpoly_len(), y.mpoly_len());
                let (xs, ys) = (crate::intrinsics::mpoly::ordered_terms(ring, &x), crate::intrinsics::mpoly::ordered_terms(ring, &y));
                for ((a, ea), (b, eb)) in xs.into_iter().zip(ys) {
                    match order.cmp(&ea, &eb) {
                        Ordering::Equal => {}
                        o => return Ok(Some(o)),
                    }
                    let a = self.elem_to_value(base, a);
                    let b = self.elem_to_value(base, b);
                    match self.compare_ord(&a, &b)? {
                        Some(Ordering::Equal) => {}
                        other => return Ok(other),
                    }
                }
                m.cmp(&n)
            }
            RingKind::Complex(_) => return Ok(None),
        }))
    }

    /// `a ^ k` for a ring element `a` and an integer `k`.
    fn ring_pow(&mut self, a: &Value, b: &Value) -> RResult<Option<Value>> {
        let (Value::Elt(x), Value::Int(k)) = (a, b) else { return Ok(None) };
        if let RingKind::UPolyRes { modulus, .. } = &x.ring().kind {
            return Ok(Some(make_elt(&x.parent, crate::intrinsics::upoly::res_pow(modulus, &x.x, k)?)));
        }
        if let RingKind::MPolyRes { affine, .. } = &x.ring().kind {
            return Ok(Some(make_elt(&x.parent, affine.pow(&x.x, k)?)));
        }
        if k.sign() < 0 && matches!(x.ring().kind, RingKind::UPoly { .. }) {
            return Err(crate::intrinsics::arg_ge(2, k, 0).in_context("^"));
        }
        if k.sign() < 0 && x.x.is_zero() == Truth::True {
            if finite::field_of(&x.parent).is_some() {
                return Err(RuntimeError::runtime("Illegal negative power of zero element").in_context("^"));
            }
            return Err(div_by_zero().in_context("^"));
        }
        // Guard against runaway polynomial powers.
        if matches!(x.x.ctx().kind(), CtxKind::Poly | CtxKind::MPoly { .. }) && k.to_u64().is_none_or(|k| k > 1 << 32) && k.sign() > 0 {
            let trivial = x.x.is_zero() == Truth::True || x.x.is_one() == Truth::True;
            if !trivial {
                return Err(RuntimeError::runtime("Exponent is too large").in_context("^"));
            }
        }
        let r = x.x.pow(k).map_err(|e| match e {
            GrError::Domain => RuntimeError::runtime("Element is not invertible").in_context("^"),
            GrError::Unable => RuntimeError::runtime("Operation not supported for this ring").in_context("^"),
        })?;
        Ok(Some(make_elt(&x.parent, r)))
    }

    pub fn ring_negate(&mut self, x: &Rc<Elt>) -> RResult<Value> {
        let r = x.x.neg().map_err(|e| arith_err(e, "-"))?;
        Ok(make_elt(&x.parent, r))
    }

    /// Make a value of the ring `parent` from a FLINT element.
    pub fn ring_value(parent: &Value, e: Elem) -> Value {
        match parent {
            Value::Struct(st) => make_elt(st, e),
            _ => Value::Undef,
        }
    }
}
