//! Real fields and their elements (MPFR numbers), with `complex`: the Real
//! and Complex Fields chapter.
//!
//! A real field is determined by its precision in bits, `⌈p·log2(10)⌉` for
//! `p` decimal digits, and every real carries its precision. Arithmetic
//! mixing precisions first rounds the more precise operand to the smaller
//! precision, as Magma does; integers and rationals are first rounded into
//! the field of the other operand.

use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::rc::Rc;

use calyx_flint::{Integer, Real, bits_for_digits};
use calyx_syntax::ast::BinOp;
use rustc_hash::FxHashMap;

use super::one;
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::ops::div_by_zero;
use crate::print::Level;
use crate::value::*;

/// The precision of the default real field at startup.
pub const DEFAULT_DIGITS: u32 = 30;

thread_local! {
    /// The precision in bits of the default real field (the parent of real
    /// literals, `RealField()`, ...).
    static DEFAULT_BITS: Cell<u64> = const { Cell::new(100) };
    /// Real literals by source text (the constant's address) and precision.
    static LITERALS: RefCell<FxHashMap<(usize, u64), (Rc<Text>, Value)>> = RefCell::default();
}

pub fn default_bits() -> u64 {
    DEFAULT_BITS.with(|b| b.get())
}

pub fn set_default_bits(bits: u64) {
    DEFAULT_BITS.with(|b| b.set(bits));
}

/// A real literal such as `1.5`, `2e-3` or `1.5p10` (precision 10) in the
/// default real field.
pub fn real_literal(s: &Rc<Text>) -> RResult<Value> {
    let bits = default_bits();
    let key = (Rc::as_ptr(s) as usize, bits);
    if let Some(v) = LITERALS.with(|m| m.borrow().get(&key).map(|e| e.1.clone())) {
        return Ok(v);
    }
    let (num, bits) = match s.find(['p', 'P']) {
        Some(i) => {
            let d: u64 = s[i + 1..].parse().map_err(|_| RuntimeError::runtime(format!("Bad real literal '{s}'")))?;
            (&s[..i], bits_for_digits(d))
        }
        None => (s.as_str(), bits),
    };
    let x = Real::parse(num, bits).ok_or_else(|| RuntimeError::runtime(format!("Bad real literal '{s}'")))?;
    let v = Value::real(x);
    LITERALS.with(|m| {
        let mut m = m.borrow_mut();
        if m.len() > 4096 {
            m.clear();
        }
        m.insert(key, (s.clone(), v.clone()));
    });
    Ok(v)
}

/// Format a real with a fixed number of decimals (for `%.No`).
pub fn format_with_digits(v: &Value, decimals: usize) -> Option<String> {
    match v {
        Value::Real(r) => Some(r.x.format_decimals(decimals, r.x.digits())),
        _ => None,
    }
}

/// A real as Magma prints it; at the Magma level followed by `p` and the
/// precision.
pub fn format_real(r: &RealV, level: Level) -> String {
    if let Some(d) = r.fixed {
        return r.x.to_string_fixed(d as usize);
    }
    let d = r.x.digits();
    let s = r.x.format(d);
    if level == Level::Magma { format!("{s}p{d}") } else { s }
}

/// An integer, rational or real as a real of the given precision.
pub fn to_real(v: &Value, bits: u64) -> Option<Real> {
    Some(match v {
        Value::Int(i) => Real::from_integer(i, bits),
        Value::Rat(q) => Real::from_rational(q, bits),
        Value::Real(r) if r.x.prec() == bits => r.x.clone(),
        Value::Real(r) => r.x.round_to(bits),
        _ => return None,
    })
}

/// A real with the precision of its argument (or the default precision for
/// integers and rationals).
pub fn real_arg(v: &Value) -> Option<Real> {
    match v {
        Value::Real(r) => Some(r.x.clone()),
        _ => to_real(v, default_bits()),
    }
}

/// The precision in bits of a real or complex number.
pub fn prec_of(v: &Value) -> Option<u64> {
    match v {
        Value::Real(r) => Some(r.x.prec()),
        Value::Complex(c) => Some(c.prec()),
        _ => None,
    }
}

/// 0 for integers and rationals, 1 for reals, 2 for complex numbers.
fn num_kind(v: &Value) -> Option<u8> {
    match v {
        Value::Int(_) | Value::Rat(_) => Some(0),
        Value::Real(_) => Some(1),
        Value::Complex(_) => Some(2),
        _ => None,
    }
}

/// The precision of an operation on `a` and `b`, at least one of which is
/// real or complex: the smaller precision.
fn common_bits(a: &Value, b: &Value) -> u64 {
    match (prec_of(a), prec_of(b)) {
        (Some(x), Some(y)) => x.min(y),
        (Some(x), None) | (None, Some(x)) => x,
        _ => default_bits(),
    }
}

/// Timings print with a fixed number of decimals, and so do results
/// computed from them.
fn fixed_of(a: &Value, b: &Value) -> Option<u32> {
    let f = |v: &Value| if let Value::Real(r) = v { r.fixed } else { None };
    match (f(a), f(b)) {
        (Some(x), Some(y)) => Some(x.min(y)),
        (x, y) => x.or(y),
    }
}

/// Binary operators with a real or complex operand and the other an
/// integer, rational, real or complex number; `None` for other operands.
pub fn num_binop(op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
    let (Some(ka), Some(kb)) = (num_kind(a), num_kind(b)) else { return Ok(None) };
    if ka == 0 && kb == 0 {
        return Ok(None);
    }
    let bits = common_bits(a, b);
    if ka == 2 || kb == 2 {
        return super::complex::complex_binop(op, a, b, bits);
    }
    use BinOp::*;
    Ok(Some(match op {
        Add | Sub | Mul | Div => {
            let (x, y) = (to_real(a, bits).unwrap(), to_real(b, bits).unwrap());
            let r = match op {
                Add => x.add(&y),
                Sub => x.sub(&y),
                Mul => x.mul(&y),
                _ => x.div(&y).ok_or_else(|| div_by_zero().in_context("/"))?,
            };
            Value::Real(Rc::new(RealV { x: r, fixed: fixed_of(a, b) }))
        }
        Pow => return real_pow(a, b, bits).map(Some),
        Eq | Cmpeq => Value::Bool(num_eq(a, b).unwrap_or(false)),
        Ne | Cmpne => Value::Bool(!num_eq(a, b).unwrap_or(false)),
        Lt | Le | Gt | Ge => {
            let o = num_cmp(a, b).unwrap_or(Ordering::Equal);
            Value::Bool(match op {
                Lt => o.is_lt(),
                Le => o.is_le(),
                Gt => o.is_gt(),
                _ => o.is_ge(),
            })
        }
        _ => return Ok(None),
    }))
}

/// `a^b` with a real operand and no complex one.
fn real_pow(a: &Value, b: &Value, bits: u64) -> RResult<Value> {
    let r = match (a, b) {
        (Value::Real(x), Value::Int(e)) => {
            if x.x.is_zero() && e.sign() < 0 {
                return Err(RuntimeError::runtime("Illegal negative power of zero element").in_context("^"));
            }
            return Ok(Value::Real(Rc::new(RealV { x: x.x.pow_integer(e), fixed: x.fixed })));
        }
        _ => to_real(a, bits).unwrap().pow(&to_real(b, bits).unwrap()),
    };
    Ok(Value::real(r))
}

/// Equality of numbers at least one of which is real or complex (after
/// rounding to the smaller precision; NaN equals everything, as with
/// MPFR's comparison).
pub fn num_eq(a: &Value, b: &Value) -> Option<bool> {
    let (ka, kb) = (num_kind(a)?, num_kind(b)?);
    if ka == 0 && kb == 0 {
        return None;
    }
    let bits = common_bits(a, b);
    if ka == 2 || kb == 2 {
        let (x, y) = (super::complex::to_complex(a, bits)?, super::complex::to_complex(b, bits)?);
        return Some(x.re.cmp_magma(&y.re) == Ordering::Equal && x.im.cmp_magma(&y.im) == Ordering::Equal);
    }
    Some(to_real(a, bits)?.cmp_magma(&to_real(b, bits)?) == Ordering::Equal)
}

/// The order of real numbers (with integers and rationals).
pub fn num_cmp(a: &Value, b: &Value) -> Option<Ordering> {
    let (ka, kb) = (num_kind(a)?, num_kind(b)?);
    if ka == 2 || kb == 2 || (ka == 0 && kb == 0) {
        return None;
    }
    let bits = common_bits(a, b);
    Some(to_real(a, bits)?.cmp_magma(&to_real(b, bits)?))
}

/// A real with fixed-decimal printing (for timings).
pub fn timing_value(secs: f64) -> Value {
    let x = Real::from_f64(secs, default_bits());
    Value::Real(Rc::new(RealV { x, fixed: Some(3) }))
}

// ----- real fields -------------------------------------------------------------

/// The precision in bits of `RealField(p)` or `ComplexField(p)`, with the
/// `Bits` parameter.
pub fn field_bits(a: &CallArgs, i: usize) -> RResult<u64> {
    let p = a.int(i)?;
    if a.param_bool("Bits")? {
        if *p < Integer::from_i64(2) {
            return Err(super::arg_ge(i + 1, p, 2));
        }
        return p.to_u64().filter(|&b| b < 1 << 40).ok_or_else(|| RuntimeError::runtime("Precision is too large"));
    }
    if p.sign() <= 0 {
        return Err(super::arg_not(i + 1, "positive"));
    }
    p.to_u64().filter(|&d| d < 1 << 38).map(bits_for_digits).ok_or_else(|| RuntimeError::runtime("Precision is too large"))
}

fn real_field(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bits = if a.args.is_empty() { default_bits() } else { field_bits(a, 0)? };
    one(Value::reals(bits))
}

fn sqrt(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = real_arg(&a.args[0]).unwrap();
    if x.sign() < 0 {
        let z = Real::zero(x.prec());
        return one(Value::complex(z, x.neg().sqrt()));
    }
    one(Value::real(x.sqrt()))
}

fn precision(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match &a.args[0] {
        Value::Struct(s) => match &s.kind {
            StructKind::Reals(b) => one(Value::int(calyx_flint::digits_for_bits(*b) as i64)),
            _ => Err(RuntimeError::runtime("Argument must be a real field")),
        },
        Value::Real(r) => one(Value::int(r.digits() as i64)),
        _ => unreachable!(),
    }
}

fn extended_reals(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::extended_reals())
}

fn infinity(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::Infinity(true))
}

fn minus_infinity(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::Infinity(false))
}

fn infinity_abs(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::Infinity(true))
}

fn infinity_sign(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int(if matches!(a.args[0], Value::Infinity(true)) { 1 } else { -1 }))
}

fn infinity_is_finite(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::Bool(false))
}

pub fn register(it: &mut Interp) {
    it.def("Infinity", "-> Infty", "Positive infinity.", infinity);
    it.def("ExtendedReals", "-> ExtRe", "The real numbers together with plus and minus infinity.", extended_reals);
    it.def("MinusInfinity", "-> Infty", "Negative infinity.", minus_infinity);
    it.def("Abs", "x::Infty -> Infty", "Positive infinity.", infinity_abs);
    it.def("Sign", "x::Infty -> RngIntElt", "The sign of x.", infinity_sign);
    it.def("IsFinite", "x::Infty -> BoolElt", "False: x is infinite.", infinity_is_finite);
    it.def("RealField", "-> FldRe", "The default real field.", real_field);
    it.def_params("RealField", "p::RngIntElt -> FldRe", &[("Bits", Value::Bool(false))], "The real field with p decimal digits of precision (or p bits with Bits).", real_field);
    for t in ["RngIntElt", "FldRatElt", "FldReElt"] {
        it.def("Sqrt", &format!("x::{t} -> FldReElt"), "The real square root of x.", sqrt);
    }
    it.def("Precision", "R::FldRe -> RngIntElt", "The decimal precision of R.", precision);
    it.def("Precision", "x::FldReElt -> RngIntElt", "The decimal precision of x.", precision);
}
