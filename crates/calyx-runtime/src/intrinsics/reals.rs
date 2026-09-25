//! A minimal real field (multiprecision floats from FLINT).

use calyx_flint::{Real, bits_for_digits};

use super::one;
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

pub const DEFAULT_DIGITS: u32 = 30;

pub fn real_literal(s: &str) -> RResult<Value> {
    let x = Real::parse(s, bits_for_digits(DEFAULT_DIGITS as u64)).ok_or_else(|| RuntimeError::runtime(format!("Bad real literal '{s}'")))?;
    Ok(Value::real(x, DEFAULT_DIGITS))
}

/// Format a real with a fixed number of decimals (for `%.No`).
pub fn format_with_digits(v: &Value, decimals: usize) -> Option<String> {
    match v {
        Value::Real(r) => Some(r.x.to_string_fixed(decimals)),
        _ => None,
    }
}

pub fn to_real(v: &Value, digits: u32) -> Option<Real> {
    let bits = bits_for_digits(digits as u64);
    match v {
        Value::Int(i) => Some(Real::from_integer(i, bits)),
        Value::Rat(q) => Some(Real::from_rational(q, bits)),
        Value::Real(r) => Some(r.x.round_to(bits)),
        _ => None,
    }
}

/// A real with fixed-decimal printing (for timings).
pub fn timing_value(secs: f64) -> Value {
    let x = Real::from_f64(secs, bits_for_digits(DEFAULT_DIGITS as u64));
    Value::Real(std::rc::Rc::new(RealV { x, digits: DEFAULT_DIGITS, fixed: Some(3) }))
}

fn real_field(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let d = if a.args.is_empty() { DEFAULT_DIGITS } else { a.int(0)?.to_u64().filter(|&d| d >= 1 && d <= 1_000_000).ok_or_else(|| RuntimeError::runtime("Precision must be positive"))? as u32 };
    one(Value::reals(d))
}

fn sqrt(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let digits = match &a.args[0] {
        Value::Real(r) => r.digits,
        _ => DEFAULT_DIGITS,
    };
    let x = to_real(&a.args[0], digits).unwrap();
    match x.sqrt() {
        Some(r) => one(Value::real(r, digits)),
        None => Err(RuntimeError::runtime("Square root of a negative number is not real")),
    }
}

fn precision(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    match &a.args[0] {
        Value::Struct(s) => match &s.kind {
            StructKind::Reals(d) => one(Value::int(*d as i64)),
            _ => Err(RuntimeError::runtime("Argument must be a real field")),
        },
        Value::Real(r) => one(Value::int(r.digits as i64)),
        _ => unreachable!(),
    }
}

pub fn register(it: &mut Interp) {
    it.def("RealField", "-> FldRe", "The real field of default precision (30 digits).", real_field);
    it.def("RealField", "p::RngIntElt -> FldRe", "The real field with p decimal digits of precision.", real_field);
    for t in ["RngIntElt", "FldRatElt", "FldReElt"] {
        it.def("Sqrt", &format!("x::{t} -> FldReElt"), "The real square root of x.", sqrt);
    }
    it.def("Precision", "R::FldRe -> RngIntElt", "The decimal precision of R.", precision);
    it.def("Precision", "x::FldReElt -> RngIntElt", "The decimal precision of x.", precision);
}
