//! Arithmetic and comparison of ring elements.

use std::rc::Rc;

use calyx_flint::gr::{CtxKind, Elem, GrError, Truth};
use calyx_syntax::ast::BinOp;

use super::{Elt, RingKind, make_elt};
use crate::error::{RResult, RuntimeError};
use crate::interp::Interp;
use crate::ops::div_by_zero;
use crate::value::{StructKind, Value};

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
        if op == Pow {
            return self.ring_pow(a, b);
        }
        if !matches!(op, Add | Sub | Mul | Div | IntDiv | Mod | Eq | Ne | Cmpeq | Cmpne | Lt | Le | Gt | Ge) {
            return Ok(None);
        }
        let pa = self.parent_of(a)?;
        let pb = self.parent_of(b)?;
        let Some(r) = self.common_ring(&pa, &pb)? else {
            if matches!(op, Cmpeq | Cmpne) {
                return Ok(Some(Value::Bool(op == Cmpne)));
            }
            return Ok(None);
        };
        let Value::Struct(st) = &r else { return Ok(None) };
        if !matches!(st.kind, StructKind::Ring(_)) {
            // Both operands coerce into the integers, rationals or reals.
            let x = self.coerce(&r, a)?;
            let y = self.coerce(&r, b)?;
            return self.binop(op, x, y).map(Some);
        }
        let Some(x) = self.to_ring_elem(st, a, false)? else { return Ok(None) };
        let Some(y) = self.to_ring_elem(st, b, false)? else { return Ok(None) };
        let StructKind::Ring(ring) = &st.kind else { unreachable!() };
        let name = op.intrinsic_name();
        let v = match op {
            Add => x.add(&y).map_err(|e| arith_err(e, name))?,
            Sub => x.sub(&y).map_err(|e| arith_err(e, name))?,
            Mul => x.mul(&y).map_err(|e| arith_err(e, name))?,
            Div => {
                if y.is_zero() == Truth::True {
                    return Err(div_by_zero().in_context("/"));
                }
                // Division of a polynomial by a unit of the coefficient ring.
                let by_constant = match &ring.kind {
                    RingKind::UPoly { .. } if y.poly_len() == 1 => Some(y.poly_coeff(0)),
                    RingKind::MPoly { .. } if y.mpoly_len() == 1 && y.mpoly_term(0).1.iter().all(|&e| e == 0) => Some(y.mpoly_term(0).0),
                    _ => None,
                };
                if let Some(c) = by_constant {
                    let inv = c.inv().map_err(|_| RuntimeError::runtime("Argument 2 is not invertible").in_context("/"))?;
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
                if y.is_zero() == Truth::True {
                    return Err(div_by_zero().in_context(name));
                }
                let (q, rem) = match &ring.kind {
                    RingKind::UPoly { .. } => x.poly_divrem(&y).map_err(|_| RuntimeError::runtime("The leading coefficient of the divisor is not a unit").in_context(name))?,
                    _ => x.euclidean_divrem(&y).map_err(|e| arith_err(e, name))?,
                };
                if op == IntDiv { q } else { rem }
            }
            Eq | Ne | Cmpeq | Cmpne => {
                let e = x.equal(&y) == Truth::True;
                return Ok(Some(Value::Bool(if matches!(op, Eq | Cmpeq) { e } else { !e })));
            }
            Lt | Le | Gt | Ge => {
                let c = x.cmp(&y).map_err(|_| RuntimeError::runtime("The ring is not ordered").in_context(name))?;
                return Ok(Some(Value::Bool(match op {
                    Lt => c < 0,
                    Le => c <= 0,
                    Gt => c > 0,
                    _ => c >= 0,
                })));
            }
            _ => unreachable!(),
        };
        Ok(Some(make_elt(st, v)))
    }

    /// `a ^ k` for a ring element `a` and an integer `k`.
    fn ring_pow(&mut self, a: &Value, b: &Value) -> RResult<Option<Value>> {
        let (Value::Elt(x), Value::Int(k)) = (a, b) else { return Ok(None) };
        if k.sign() < 0 && x.x.is_zero() == Truth::True {
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
