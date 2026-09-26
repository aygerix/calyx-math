//! Complex fields and their elements (pairs of MPFR numbers), with `reals`:
//! the Real and Complex Fields chapter.
//!
//! A complex field is a ring (`RingKind::Complex`, so that polynomial
//! rings can be built over it) determined by its precision in bits; its
//! elements are `Value::Complex`. Operations are rounded correctly in each
//! part, as with MPC, which Magma uses.

use std::rc::Rc;

use calyx_flint::Real;
use calyx_syntax::ast::BinOp;

use super::reals::{self, default_bits, field_bits, to_real};
use super::{boolv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::ops::div_by_zero;
use crate::print::Level;
use crate::rings::{RingKind, ring_of};
use crate::value::*;

/// An integer, rational, real or complex number as a complex number of the
/// given precision.
pub fn to_complex(v: &Value, bits: u64) -> Option<ComplexV> {
    match v {
        Value::Complex(c) if c.prec() == bits => Some((**c).clone()),
        Value::Complex(c) => Some(c.round_to(bits)),
        _ => Some(ComplexV::from_real(to_real(v, bits)?)),
    }
}

/// `C ! x` for the complex field of the given precision: numbers, and
/// sequences `[re, im]`.
pub fn coerce_complex(x: &Value, bits: u64) -> Result<Value, Option<String>> {
    match x {
        Value::Seq(s) if s.elems.len() != 2 => Err(Some("Sequence must have length 2 to lift into this ring".into())),
        Value::Seq(s) => match (to_real(&s.elems[0], bits), to_real(&s.elems[1], bits)) {
            (Some(re), Some(im)) => Ok(cv(ComplexV::new(re, im))),
            _ => Err(None),
        },
        _ => to_complex(x, bits).map(cv).ok_or(None),
    }
}

pub fn cv(c: ComplexV) -> Value {
    Value::Complex(Rc::new(c))
}

/// Binary operators with a complex operand.
pub fn complex_binop(op: BinOp, a: &Value, b: &Value, bits: u64) -> RResult<Option<Value>> {
    use BinOp::*;
    let (Some(x), Some(y)) = (to_complex(a, bits), to_complex(b, bits)) else { return Ok(None) };
    Ok(Some(match op {
        Add => cv(x.add(&y)),
        Sub => cv(x.sub(&y)),
        Mul => cv(x.mul(&y)),
        Div => cv(x.div(&y).ok_or_else(|| div_by_zero().in_context("/"))?),
        Pow => match b {
            Value::Int(n) => {
                if x.is_zero() && n.sign() < 0 {
                    return Err(RuntimeError::runtime("Illegal negative power of zero element").in_context("^"));
                }
                cv(x.pow_integer(n))
            }
            _ => cv(x.pow(&y)),
        },
        Eq | Cmpeq => Value::Bool(reals::num_eq(a, b).unwrap_or(false)),
        Ne | Cmpne => Value::Bool(!reals::num_eq(a, b).unwrap_or(false)),
        _ => return Ok(None),
    }))
}

pub fn negate(c: &ComplexV) -> Value {
    Value::complex(c.re.neg(), c.im.neg())
}

// ----- printing ------------------------------------------------------------------

impl Interp {
    /// How the imaginary unit of the complex field of the given precision
    /// prints: its assigned name, else `C.1` for a field assigned to `C`,
    /// else `$.1`.
    pub fn complex_gen_name(&mut self, bits: u64) -> String {
        let c = self.complex_field(bits);
        let Some((st, r)) = ring_of(&c) else { unreachable!() };
        if r.has_names() {
            return r.gen_name(1);
        }
        match *st.name.borrow() {
            Some(n) => format!("{n}.1"),
            None => "$.1".to_string(),
        }
    }
}

/// A complex number as Magma prints it: zero parts are left out (the real
/// part is shown if both are zero).
pub fn format_complex(it: &mut Interp, c: &ComplexV, level: Level) -> String {
    let d = c.re.digits();
    let f = |x: &Real| {
        let s = x.format(d);
        if level == Level::Magma { format!("{s}p{d}") } else { s }
    };
    if c.im.is_zero() {
        return f(&c.re);
    }
    let name = it.complex_gen_name(c.prec());
    if c.re.is_zero() {
        return format!("{}*{name}", f(&c.im));
    }
    let neg = c.im.is_sign_negative() && !c.im.is_nan();
    format!("{} {} {}*{name}", f(&c.re), if neg { "-" } else { "+" }, f(&if neg { c.im.neg() } else { c.im.clone() }))
}

// ----- complex fields ----------------------------------------------------------

/// The complex field and precision of argument `i`.
fn field_arg(a: &CallArgs, i: usize) -> RResult<u64> {
    match ring_of(&a.args[i]) {
        Some((_, r)) => match r.kind {
            RingKind::Complex(bits) => Ok(bits),
            _ => Err(RuntimeError::runtime("Bad argument types")),
        },
        None => Err(RuntimeError::runtime("Bad argument types")),
    }
}

fn complex_field(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bits = match a.args.first() {
        None => default_bits(),
        Some(Value::Struct(s)) => match &s.kind {
            StructKind::Reals(b) => *b,
            _ => return Err(RuntimeError::runtime("Bad argument types")),
        },
        Some(_) => field_bits(a, 0)?,
    };
    one(it.complex_field(bits))
}

fn ngens(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int(1))
}

fn generator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bits = field_arg(a, 0)?;
    if a.i64(1)? != 1 {
        return Err(RuntimeError::runtime("Generator index must be in the range [1..1]"));
    }
    one(Value::complex(Real::zero(bits), Real::from_i64(1, bits)))
}

fn assign_names(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Some((_, r)) = ring_of(&a.args[0]) else { unreachable!() };
    let names = a.seq(1)?;
    let mut out = Vec::new();
    for v in names.elems.iter() {
        match v {
            Value::Str(s) => out.push(Rc::from(s.as_str())),
            _ => return Err(RuntimeError::runtime("Names must be strings")),
        }
    }
    if out.len() > 1 {
        return Err(RuntimeError::runtime("Too many names given"));
    }
    *r.names.borrow_mut() = out;
    super::none()
}

fn is_zero(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Complex(c) = &a.args[0] else { unreachable!() };
    boolv(c.re.is_zero() && c.im.is_zero())
}

pub fn register(it: &mut Interp) {
    it.def_params("ComplexField", "-> FldCom", &[("Bits", Value::Bool(false))], "The default complex field.", complex_field);
    it.def_params("ComplexField", "p::RngIntElt -> FldCom", &[("Bits", Value::Bool(false))], "The complex field with p decimal digits of precision (or p bits with Bits).", complex_field);
    it.def("ComplexField", "R::FldRe -> FldCom", "The complex field containing R.", complex_field);
    it.def("Ngens", "C::FldCom -> RngIntElt", "The number of generators of C (1).", ngens);
    it.def(".", "C::FldCom, i::RngIntElt -> FldComElt", "The square root of -1 in C.", generator);
    it.def("Name", "C::FldCom, i::RngIntElt -> FldComElt", "The square root of -1 in C.", generator);
    it.def("AssignNames", "~C::FldCom, N::[MonStgElt]", "Set the name used to print the square root of -1 in C.", assign_names);
    it.def("IsZero", "x::FldComElt -> BoolElt", "Whether x is zero.", is_zero);
}
