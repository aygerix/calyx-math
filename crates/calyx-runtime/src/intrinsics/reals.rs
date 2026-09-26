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

/// An integer exponent of a real or complex number: `|e| < 2^30`.
pub fn small_exponent(e: &Integer) -> RResult<i64> {
    e.to_i64().filter(|k| k.unsigned_abs() < 1 << 30).ok_or_else(|| RuntimeError::runtime(format!("Argument 2 ({e}) is too large")).in_context("^"))
}

/// `a^b` with a real operand and no complex one.
fn real_pow(a: &Value, b: &Value, bits: u64) -> RResult<Value> {
    let r = match (a, b) {
        (Value::Real(x), Value::Int(e)) => {
            let e = small_exponent(e)?;
            if x.x.is_zero() && e < 0 {
                return Err(RuntimeError::runtime("Illegal negative power of zero element").in_context("^"));
            }
            return Ok(Value::Real(Rc::new(RealV { x: x.x.pow_i64(e), fixed: x.fixed })));
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
    let bits = match a.args.first() {
        None => default_bits(),
        Some(v @ Value::Struct(_)) => bits_of(v).unwrap(),
        Some(_) => field_bits(a, 0)?,
    };
    one(Value::reals(bits))
}

fn get_default_real_field(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::reals(default_bits()))
}

fn set_default_real_field(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    set_default_bits(bits_of(&a.args[0]).unwrap());
    super::none()
}

fn identity(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bits = bits_of(&a.args[0]).unwrap();
    let x = Real::from_i64(1, bits);
    one(if matches!(a.args[0], Value::Struct(ref s) if matches!(s.kind, StructKind::Reals(_))) { Value::real(x) } else { Value::complex(x, Real::zero(bits)) })
}

/// The precision in bits of a real or complex field or number, or of the
/// universe of a sequence of them.
pub fn bits_of(v: &Value) -> Option<u64> {
    match v {
        Value::Real(r) => Some(r.x.prec()),
        Value::Complex(c) => Some(c.prec()),
        Value::Struct(s) => match &s.kind {
            StructKind::Reals(b) => Some(*b),
            StructKind::Ring(r) => match r.kind {
                crate::rings::RingKind::Complex(b) => Some(b),
                _ => None,
            },
            _ => None,
        },
        Value::Seq(s) => s.universe.as_ref().and_then(bits_of),
        _ => None,
    }
}

fn precision(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bits = bits_of(&a.args[0]).ok_or_else(|| RuntimeError::runtime("Bad argument types"))?;
    one(Value::int(calyx_flint::digits_for_bits(bits) as i64))
}

fn bit_precision(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int(bits_of(&a.args[0]).unwrap() as i64))
}

/// `ChangePrecision(x, n)`: x in the field of precision n.
fn change_precision(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(1)?;
    if n.sign() <= 0 {
        return Err(super::arg_not(1, "positive").in_context("RealField"));
    }
    let bits = n.to_u64().filter(|&d| d < 1 << 38).map(bits_for_digits).ok_or_else(|| RuntimeError::runtime("Precision is too large"))?;
    one(match &a.args[0] {
        Value::Complex(c) => super::complex::cv(c.round_to(bits)),
        v => Value::real(to_real(v, bits).unwrap()),
    })
}

fn mantissa_exponent(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Real(r) = &a.args[0] else { unreachable!() };
    if !r.x.is_regular() {
        return Ok(vals![Value::int(0), Value::Infinity(false)]);
    }
    let (m, e) = r.x.mantissa_exponent();
    Ok(vals![Value::Int(m), Value::int(e)])
}

/// Argument `i` as a real number, with integers and rationals in the
/// default field.
fn real_at(a: &CallArgs, i: usize) -> Real {
    real_arg(&a.args[i]).unwrap()
}

fn sqrt(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = real_at(a, 0);
    if x.sign() < 0 {
        let z = Real::zero(x.prec());
        return one(Value::complex(z, x.neg().sqrt()));
    }
    one(Value::real(x.sqrt()))
}

/// The real n-th root (NaN for n < 1); even roots of negative integers
/// and rationals are complex.
fn root(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = real_at(a, 0);
    let n = a.int(1)?;
    let Some(k) = n.to_u64().filter(|&k| k > 0) else { return one(Value::real(Real::nan(x.prec()))) };
    if k % 2 == 0 && x.sign() < 0 {
        if !matches!(a.args[0], Value::Real(_)) {
            let c = super::complex::magma_root(&calyx_flint::Complex::from_real(x), n);
            return one(super::complex::cv(c));
        }
        return Err(RuntimeError::runtime("Illegal even root of negative number"));
    }
    one(Value::real(x.root(k)))
}

fn real_part(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::real(real_at(a, 0)))
}

fn imaginary_part(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::real(Real::zero(real_at(a, 0).prec())))
}

/// The argument of a real: 0, or pi for negative numbers.
fn arg(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = real_at(a, 0);
    one(Value::real(Real::zero(x.prec()).binary(&x, calyx_flint::mpfr::mpfr_atan2)))
}

fn abs(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::real(real_at(a, 0).abs()))
}

fn conjugate(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(a.args[0].clone())
}

fn is_integral(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    super::boolv(real_at(a, 0).is_integer())
}

fn constant(a: &CallArgs, f: calyx_flint::mpfr::Constant) -> RResult<Vals> {
    let bits = bits_of(&a.args[0]).unwrap();
    let x = Real::constant(f, bits);
    one(match &a.args[0] {
        Value::Struct(s) if matches!(s.kind, StructKind::Reals(_)) => Value::real(x),
        _ => Value::complex(x, Real::zero(bits)),
    })
}

fn pi(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    constant(a, calyx_flint::mpfr::mpfr_const_pi)
}

fn euler_gamma(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    constant(a, calyx_flint::mpfr::mpfr_const_euler)
}

fn catalan(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    constant(a, calyx_flint::mpfr::mpfr_const_catalan)
}

/// `|x - y|` for real or complex numbers.
fn distance_between(x: &Value, y: &Value) -> RResult<Value> {
    Ok(match num_binop(BinOp::Sub, x, y)? {
        Some(Value::Real(r)) => Value::real(r.x.abs()),
        Some(Value::Complex(c)) => Value::real(c.abs()),
        _ => return Err(RuntimeError::runtime("Bad argument types")),
    })
}

/// Whether a distance is below the bound `Max` (none by default).
fn below(d: &Value, max: &Value) -> bool {
    match max {
        Value::Infinity(pos) => *pos,
        _ => num_cmp(d, max).is_some_and(|o| o.is_lt()),
    }
}

/// `Distance(x, L)`: the least distance from x to an element of L, and the
/// index of such an element (`Max` and 0 if every distance is at least
/// `Max`).
fn distance(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = a.args[0].clone();
    let Value::Seq(l) = &a.args[1] else { unreachable!() };
    if l.elems.is_empty() {
        return Err(RuntimeError::runtime("Array must be nonempty").in_context(""));
    }
    let max = a.param("Max").cloned().unwrap_or(Value::Infinity(true));
    let mut best = (max.clone(), 0);
    for (i, y) in l.elems.iter().enumerate() {
        let d = distance_between(&x, y)?;
        if below(&d, &best.0) {
            best = (d, i + 1);
        }
    }
    if best.1 == 0 && matches!(best.0, Value::Infinity(_)) {
        best.0 = Value::int(0);
    }
    Ok(vals![best.0, Value::int(best.1 as i64)])
}

/// `Diameter(L)`: the least distance between distinct elements of L (0, or
/// `Max`, if there is none below `Max`).
fn diameter(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Seq(l) = &a.args[0] else { unreachable!() };
    let l = l.clone();
    let max = a.param("Max").cloned().unwrap_or(Value::Infinity(true));
    let mut best = max;
    for (i, x) in l.elems.iter().enumerate() {
        for y in &l.elems[i + 1..] {
            let d = distance_between(x, y)?;
            if !matches!(&d, Value::Real(r) if r.x.is_zero()) && below(&d, &best) {
                best = d;
            }
        }
    }
    one(if matches!(best, Value::Infinity(_)) { Value::int(0) } else { best })
}

// ----- transcendental functions ------------------------------------------------

/// The error for an argument outside the domain of a real function.
type Domain = fn(&Real) -> Option<&'static str>;

/// A real function as Magma computes it: MPFR's function (of `1/x` for
/// `recip`), after a check of the domain; for `finite`, a value that is
/// not finite (a pole, an overflow, or NaN) is an error.
struct RealFn {
    f: calyx_flint::mpfr::Unary,
    recip: bool,
    domain: Domain,
    finite: bool,
}

/// The real functions with their Magma names, and their descriptions.
pub const REAL_FUNCTIONS: [(&str, &str); 27] = [
    ("Exp", "The exponential of x."),
    ("Log", "The natural logarithm of x > 0."),
    ("Dilog", "The dilogarithm of x (its real part for x > 1)."),
    ("Sin", "The sine of x."),
    ("Cos", "The cosine of x."),
    ("Tan", "The tangent of x."),
    ("Cot", "The cotangent of x."),
    ("Sec", "The secant of x."),
    ("Cosec", "The cosecant of x."),
    ("Arcsin", "The inverse sine of x, in [-pi/2, pi/2]."),
    ("Arccos", "The inverse cosine of x, in [0, pi]."),
    ("Arctan", "The inverse tangent of x, in (-pi/2, pi/2)."),
    ("Arccot", "The inverse cotangent of x, the inverse tangent of 1/x."),
    ("Arcsec", "The inverse secant of x, the inverse cosine of 1/x."),
    ("Arccosec", "The inverse cosecant of x, the inverse sine of 1/x."),
    ("Sinh", "The hyperbolic sine of x."),
    ("Cosh", "The hyperbolic cosine of x."),
    ("Tanh", "The hyperbolic tangent of x."),
    ("Coth", "The hyperbolic cotangent of x."),
    ("Sech", "The hyperbolic secant of x."),
    ("Cosech", "The hyperbolic cosecant of x."),
    ("Argsinh", "The inverse hyperbolic sine of x."),
    ("Argcosh", "The inverse hyperbolic cosine of x >= 1."),
    ("Argtanh", "The inverse hyperbolic tangent of x, |x| < 1."),
    ("Argsech", "The inverse hyperbolic secant of x, the inverse hyperbolic cosine of 1/x."),
    ("Argcosech", "The inverse hyperbolic cosecant of x, the inverse hyperbolic sine of 1/x."),
    ("Argcoth", "The inverse hyperbolic cotangent of x, the inverse hyperbolic tangent of 1/x."),
];

fn cmp_one(x: &Real) -> Ordering {
    x.cmp_magma(&Real::from_i64(1, 2))
}

fn abs_cmp_one(x: &Real) -> Ordering {
    x.cmp_abs(&Real::from_i64(1, 2))
}

fn real_fn(name: &str) -> RealFn {
    use calyx_flint::mpfr::*;
    let any: Domain = |_| None;
    let (f, recip, domain, finite): (Unary, bool, Domain, bool) = match name {
        "Exp" => (mpfr_exp, false, any, false),
        "Log" => (mpfr_log, false, |x| (x.is_zero() || x.sign() < 0).then_some("Argument 1 is not positive"), false),
        "Dilog" => (mpfr_li2, false, any, false),
        "Sin" => (mpfr_sin, false, any, true),
        "Cos" => (mpfr_cos, false, any, true),
        "Tan" => (mpfr_tan, false, any, true),
        "Cot" => (mpfr_cot, false, any, true),
        "Sec" => (mpfr_sec, false, any, true),
        "Cosec" => (mpfr_csc, false, any, true),
        "Arcsin" | "Arccos" => {
            let f: Unary = if name == "Arcsin" { mpfr_asin } else { mpfr_acos };
            (f, false, |x| abs_cmp_one(x).is_gt().then_some("Argument must have absolute value <= 1"), true)
        }
        "Arctan" => (mpfr_atan, false, any, true),
        "Arccot" => (mpfr_atan, true, any, false),
        "Arcsec" | "Arccosec" => {
            let f: Unary = if name == "Arcsec" { mpfr_acos } else { mpfr_asin };
            (f, true, |x| abs_cmp_one(x).is_lt().then_some("Argument must have absolute value >= 1"), false)
        }
        "Sinh" => (mpfr_sinh, false, any, true),
        "Cosh" => (mpfr_cosh, false, any, true),
        "Tanh" => (mpfr_tanh, false, any, true),
        "Coth" => (mpfr_coth, false, |x| x.is_zero().then_some("Argument 1 is not non-zero"), true),
        "Sech" => (mpfr_sech, false, any, true),
        "Cosech" => (mpfr_csch, false, |x| x.is_zero().then_some("Argument 1 is not non-zero"), true),
        "Argsinh" => (mpfr_asinh, false, any, true),
        "Argcosh" => (mpfr_acosh, false, |x| cmp_one(x).is_lt().then_some("Argument must be at least 1"), true),
        "Argtanh" => (mpfr_atanh, false, |x| (x.is_nan() || !abs_cmp_one(x).is_lt()).then_some("Argument must have absolute value < 1"), true),
        "Argsech" => (
            mpfr_acosh,
            true,
            |x| {
                if x.is_zero() || x.sign() < 0 {
                    Some("Argument must be positive")
                } else {
                    cmp_one(x).is_gt().then_some("Argument must be no more than 1")
                }
            },
            false,
        ),
        "Argcosech" => (mpfr_asinh, true, |x| x.is_zero().then_some("Argument 1 is not non-zero"), false),
        "Argcoth" => (mpfr_atanh, true, |x| (x.is_nan() || !abs_cmp_one(x).is_gt()).then_some("Argument must have absolute value > 1"), false),
        _ => unreachable!("{name}"),
    };
    RealFn { f, recip, domain, finite }
}

/// The real functions of `REAL_FUNCTIONS`, by the name called.
fn real_function(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let spec = real_fn(&a.name.as_rc());
    let x = real_at(a, 0);
    if let Some(msg) = (spec.domain)(&x) {
        return Err(RuntimeError::runtime(msg));
    }
    let x = if spec.recip { Real::from_i64(1, x.prec()).binary(&x, calyx_flint::mpfr::mpfr_div) } else { x };
    let y = x.unary(spec.f);
    if spec.finite && !y.is_finite() {
        return Err(RuntimeError::runtime("Function not defined for this argument"));
    }
    one(Value::real(y))
}

fn sincos(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (s, c) = real_at(a, 0).sin_cos();
    Ok(vals![Value::real(s), Value::real(c)])
}

/// The precision of a function of two real arguments: the smaller
/// precision; the default one if neither is real.
fn common_real_bits(a: &CallArgs) -> u64 {
    let (x, y) = (prec_of(&a.args[0]), prec_of(&a.args[1]));
    x.zip(y).map(|(x, y)| x.min(y)).or(x).or(y).unwrap_or_else(default_bits)
}

/// `Log(b, x)`: the logarithm of x to the base b, the quotient of the two
/// logarithms, in the field of b and x if they are the same, else in the
/// default real field.
fn log_base(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bits = shared_bits(&a.args);
    let (b, x) = (to_real(&a.args[0], bits).unwrap(), to_real(&a.args[1], bits).unwrap());
    if b.sign() <= 0 {
        return Err(super::arg_not(1, "positive"));
    }
    if x.sign() <= 0 {
        return Err(super::arg_not(2, "positive"));
    }
    if cmp_one(&b).is_eq() {
        return Err(RuntimeError::runtime("Base for logarithm should not be 1"));
    }
    let log = |v: &Real| v.unary(calyx_flint::mpfr::mpfr_log);
    one(Value::real(log(&x).div(&log(&b)).unwrap()))
}

/// `Arctan(x, y)`: the angle of the point (x, y), in (-pi, pi]. Magma
/// computes it with PARI, whose zeros have no sign: `Arctan(-1, -0)` is pi.
fn arctan2(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bits = common_real_bits(a);
    let unsigned = |v: &Value| to_real(v, bits).map(|r| if r.is_zero() { Real::zero(bits) } else { r }).unwrap();
    let (x, y) = (unsigned(&a.args[0]), unsigned(&a.args[1]));
    if x.is_zero() && y.is_zero() {
        return Err(RuntimeError::runtime("Arguments cannot both be zero"));
    }
    one(Value::real(y.binary(&x, calyx_flint::mpfr::mpfr_atan2)))
}

// ----- gamma, Bessel and associated functions ------------------------------------------------

/// Magma's errors at the poles of the gamma function on the real line: 0
/// (of either sign) and the negative integers.
fn real_pole(x: &Real) -> RResult<()> {
    if x.is_zero() {
        return Err(RuntimeError::runtime("Argument must be non zero"));
    }
    if x.sign() < 0 && x.is_integer() {
        return Err(RuntimeError::runtime("Argument must not be a negative integer"));
    }
    Ok(())
}

/// `Gamma(x)`, `LogGamma(x)` and `Psi(x)` (also `LogDerivative(x)`) of a
/// real or complex number, integers and rationals in the default field.
/// The real Gamma and LogGamma are MPFR's, and an error where their value
/// is not finite (so where Gamma is negative for LogGamma). The complex
/// LogGamma is the principal branch, log(Gamma(x)).
fn gamma_function(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let name = a.name.as_rc();
    if let Value::Complex(z) = &a.args[0] {
        if z.im.is_zero() && (z.re.is_zero() || z.re.sign() < 0 && z.re.is_integer()) {
            return Err(RuntimeError::runtime(match &*name {
                "Gamma" if z.re.is_zero() => "Argument 1 is not non-zero",
                "Gamma" => "Argument must not be a negative integer",
                _ => "Argument 1 must not be a non positive integer",
            }));
        }
        let w = match &*name {
            "Gamma" => z.gamma(),
            "LogGamma" => z.log_gamma(),
            _ => z.digamma(),
        };
        return one(super::complex::cv(w));
    }
    let x = real_at(a, 0);
    real_pole(&x)?;
    use calyx_flint::mpfr::*;
    let y = match &*name {
        "Gamma" => x.unary(mpfr_gamma),
        "LogGamma" => x.unary(mpfr_lngamma),
        _ => return one(Value::real(x.unary(mpfr_digamma))),
    };
    if !y.is_finite() {
        return Err(RuntimeError::runtime("Function not defined for this argument"));
    }
    one(Value::real(y))
}

/// Magma's error for a parameter of the wrong type.
fn bad_param(it: &Interp, a: &CallArgs, p: &str) -> RuntimeError {
    let types: Vec<String> = a.args.iter().map(|v| it.type_name_ext(v)).collect();
    RuntimeError::runtime(format!("Bad type for parameter '{p}'\nArgument types given: {}", types.join(", ")))
}

/// The precision of a function computed by PARI in Magma: that of its
/// arguments if they are reals of the same precision, else the default one.
fn shared_bits(v: &[Value]) -> u64 {
    match prec_of(&v[0]) {
        Some(p) if v.iter().all(|x| matches!(x, Value::Real(r) if r.x.prec() == p)) => p,
        _ => default_bits(),
    }
}

/// `Gamma(s, t)`: the incomplete gamma function `∫_0^t u^(s-1) e^-u du`,
/// or with `Complementary` `∫_t^∞ u^(s-1) e^-u du`. Given the value `g` of
/// `Γ(s)` as `Gamma`, the lower one is `g` minus the upper one.
fn incomplete_gamma(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let upper = match a.param("Complementary") {
        Some(Value::Bool(b)) => *b,
        _ => return Err(bad_param(it, a, "Complementary")),
    };
    let g = match a.param("Gamma") {
        None | Some(Value::Undef) => None,
        Some(Value::Real(g)) => Some(g.x.clone()),
        _ => return Err(bad_param(it, a, "Gamma")),
    };
    if upper && g.is_some() {
        return Err(RuntimeError::runtime("Parameter Gamma cannot be given when parameter Complementary is true"));
    }
    let bits = shared_bits(&a.args);
    let (s, t) = (to_real(&a.args[0], bits).unwrap(), to_real(&a.args[1], bits).unwrap());
    // The lower function at a pole of Γ(s), and the integrals from 0 that
    // diverge.
    let pole = s.sign() <= 0 && s.is_integer();
    if pole && !upper && g.is_none() || t.is_zero() && s.sign() <= 0 {
        return Err(RuntimeError::runtime("Division by zero in (possibly) real or complex division. Maybe loss of precision?"));
    }
    one(Value::real(match g {
        Some(g) => g.round_to(bits).sub(&Real::incomplete_gamma(&s, &t, true, bits)),
        None => Real::incomplete_gamma(&s, &t, upper, bits),
    }))
}

/// `GammaD(s)`: `Γ(s + 1/2)`.
fn gamma_d(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = real_at(a, 0);
    // s + 1/2 is a pole when 2s is an odd integer, s < 0.
    let twice = x.add(&x);
    if x.sign() < 0 && twice.is_integer() && !x.is_integer() {
        real_pole(&twice.add(&Real::from_i64(1, x.prec())))?;
    }
    one(Value::real(x.gamma_half()))
}

/// A Bessel function's order: a small non-negative integer.
fn bessel_order(a: &CallArgs) -> RResult<i64> {
    let n = a.int(0)?;
    n.to_i64().filter(|n| (0..1 << 30).contains(n)).ok_or_else(|| RuntimeError::runtime(format!("Argument 1 ({n}) is not small and non-negative")))
}

/// `BesselFunction(n, x)` and `BesselFunctionSecondKind(n, x)`: `J_n(x)`
/// and `Y_n(x)` (MPFR's, so `Y_n(x)` is NaN for x < 0).
fn bessel_function(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = bessel_order(a)?;
    let x = real_at(a, 1);
    one(Value::real(if &*a.name.as_rc() == "BesselFunction" { Real::bessel_jn(n, &x) } else { Real::bessel_yn(n, &x) }))
}

/// `JBessel(n, x)`: the Bessel function of the first kind of half-integral
/// order `J_(n+1/2)(x)`, x ≥ 0 (by the same formula for a real n).
fn j_bessel(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = real_at(a, 1);
    let n = match &a.args[0] {
        Value::Real(r) => r.x.clone(),
        _ => Real::from_i64(bessel_order(a)?, 64),
    };
    if x.sign() < 0 {
        return Err(RuntimeError::runtime("Argument 2 must be non-negative"));
    }
    one(Value::real(Real::bessel_j_half(&n, &x, x.prec())))
}

/// `KBessel(nu, x)` and `KBessel2(nu, x)`: the modified Bessel function of
/// the second kind `K_nu(x)`, x > 0. For a real order in the smaller
/// precision of nu and x, for a complex one in that of nu, which x must
/// have.
fn k_bessel(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let complex = match &a.args[0] {
        Value::Complex(nu) => Some(nu.clone()),
        _ => None,
    };
    let bits = complex.as_ref().map_or_else(|| common_real_bits(a), |nu| nu.prec());
    if complex.is_some() && prec_of(&a.args[1]) < Some(bits) {
        return Err(RuntimeError::runtime("Argument 2 must have at least the precision of argument 1"));
    }
    let x = to_real(&a.args[1], bits).unwrap();
    if x.sign() <= 0 {
        return Err(RuntimeError::runtime("Argument must be positive"));
    }
    if let Some(nu) = complex {
        return one(super::complex::cv(calyx_flint::Complex::bessel_k(&nu, &calyx_flint::Complex::from_real(x), bits)));
    }
    let nu = to_real(&a.args[0], bits).unwrap();
    one(Value::real(Real::bessel_k(&nu, &x, bits)))
}

/// `HypergeometricU(a, b, x)`: the confluent hypergeometric function
/// `U(a, b, x)`, x > 0. Reals a and b of the same precision need x in their
/// field.
fn hypergeometric_u(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    if let (Some(p), Some(q), Some(r)) = (prec_of(&a.args[0]), prec_of(&a.args[1]), prec_of(&a.args[2])) {
        if p == q && q != r {
            return Err(RuntimeError::runtime("Arguments are not compatible"));
        }
    }
    let bits = shared_bits(&a.args);
    let r = |i: usize| to_real(&a.args[i], bits).unwrap();
    let x = r(2);
    if x.sign() <= 0 {
        return Err(RuntimeError::runtime("Argument 3 must be positive"));
    }
    one(Value::real(Real::hypergeometric_u(&r(0), &r(1), &x, bits)))
}

fn mpfr_version(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::str(&calyx_flint::mpfr::version()))
}

fn gmp_version(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::str(&calyx_flint::mpfr::gmp_version()))
}

/// calyx computes complex functions with FLINT's ball arithmetic instead
/// of MPC.
fn mpc_version(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::str("none"))
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

fn infinity_itself(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(a.args[0].clone())
}

pub fn register(it: &mut Interp) {
    it.def("Infinity", "-> Infty", "Positive infinity.", infinity);
    it.def("ExtendedReals", "-> ExtRe", "The real numbers together with plus and minus infinity.", extended_reals);
    it.def("MinusInfinity", "-> Infty", "Negative infinity.", minus_infinity);
    it.def("Abs", "x::Infty -> Infty", "Positive infinity.", infinity_abs);
    it.def("Sign", "x::Infty -> RngIntElt", "The sign of x.", infinity_sign);
    it.def("IsFinite", "x::Infty -> BoolElt", "False: x is infinite.", infinity_is_finite);
    for name in ["Floor", "Ceiling", "Round"] {
        it.def(name, "x::Infty -> Infty", "x itself.", infinity_itself);
    }

    // Fields.
    it.def("RealField", "-> FldRe", "The default real field.", real_field);
    it.def_params("RealField", "p::RngIntElt -> FldRe", &[("Bits", Value::Bool(false))], "The real field with p decimal digits of precision (or p bits with Bits).", real_field);
    it.def("RealField", "C::FldCom -> FldRe", "The real field of the precision of C.", real_field);
    it.def("GetDefaultRealField", "-> FldRe", "The parent of real literals.", get_default_real_field);
    it.def("SetDefaultRealField", "R::FldRe", "Make R the parent of real literals and the default real field.", set_default_real_field);
    it.def("GetMPFRVersion", "-> MonStgElt", "The version of MPFR used.", mpfr_version);
    it.def("GetGMPVersion", "-> MonStgElt", "The version of GMP used.", gmp_version);
    it.def("GetMPCVersion", "-> MonStgElt", "\"none\": calyx computes with FLINT's complex balls instead of MPC.", mpc_version);
    for t in ["FldRe", "FldCom"] {
        it.def("Identity", &format!("R::{t} -> {t}Elt"), "The one of R.", identity);
        it.def("Precision", &format!("R::{t} -> RngIntElt"), "The decimal precision of R.", precision);
        it.def("BitPrecision", &format!("R::{t} -> RngIntElt"), "The precision of R in bits.", bit_precision);
        it.def("Pi", &format!("R::{t} -> {t}Elt"), "Pi in R.", pi);
        it.def("EulerGamma", &format!("R::{t} -> {t}Elt"), "Euler's constant in R.", euler_gamma);
        it.def("Catalan", &format!("R::{t} -> {t}Elt"), "Catalan's constant in R.", catalan);
    }
    for t in ["FldReElt", "FldComElt"] {
        it.def("Precision", &format!("x::{t} -> RngIntElt"), "The decimal precision of the parent of x.", precision);
        it.def("BitPrecision", &format!("x::{t} -> RngIntElt"), "The precision in bits of the parent of x.", bit_precision);
        it.def("Precision", &format!("L::[{t}] -> RngIntElt"), "The decimal precision of the universe of L.", precision);
        it.def("ChangePrecision", &format!("x::{t}, n::RngIntElt -> {t}"), "x in the field of precision n.", change_precision);
        for u in ["FldReElt", "FldComElt"] {
            it.def_params("Distance", &format!("x::{t}, L::[{u}] -> FldReElt, RngIntElt"), &[("Max", Value::Infinity(true))], "The least distance from x to an element of L, and its index.", distance);
        }
        it.def_params("Diameter", &format!("L::[{t}] -> FldReElt"), &[("Max", Value::Infinity(true))], "The least distance between distinct elements of L.", diameter);
    }

    // Elements.
    it.def("MantissaExponent", "x::FldReElt -> RngIntElt, RngIntElt", "Integers m, e with x = m*2^e, m of the precision of x.", mantissa_exponent);
    it.def("IsIntegral", "x::FldReElt -> BoolElt", "Whether x is an integer.", is_integral);
    it.def("ComplexConjugate", "x::FldReElt -> FldReElt", "x itself.", conjugate);
    it.def("Norm", "x::FldReElt -> FldReElt", "The absolute value of x.", abs);
    for t in ["RngIntElt", "FldRatElt", "FldReElt"] {
        it.def("Modulus", &format!("x::{t} -> FldReElt"), "The absolute value of x as a real number.", abs);
        for name in ["Arg", "Argument"] {
            it.def(name, &format!("x::{t} -> FldReElt"), "The argument of x (0, or pi if x is negative).", arg);
        }
        for name in ["Sqrt", "SquareRoot"] {
            it.def(name, &format!("x::{t} -> FldReElt"), "The square root of x (a complex number if x < 0).", sqrt);
        }
        it.def("Root", &format!("x::{t}, n::RngIntElt -> FldReElt"), "The real n-th root of x.", root);
        for name in ["Real", "Re"] {
            it.def(name, &format!("x::{t} -> FldReElt"), "The real part of x.", real_part);
        }
        for name in ["Imaginary", "Im"] {
            it.def(name, &format!("x::{t} -> FldReElt"), "The imaginary part of x (zero).", imaginary_part);
        }
    }

    // Transcendental functions; integers and rationals are in the default
    // field (and their dilogarithm is complex, as in Magma).
    for (name, doc) in REAL_FUNCTIONS {
        for t in ["RngIntElt", "FldRatElt", "FldReElt"] {
            if name != "Dilog" || t == "FldReElt" {
                it.def(name, &format!("x::{t} -> FldReElt"), doc, real_function);
            }
        }
    }
    for t in ["RngIntElt", "FldRatElt", "FldReElt"] {
        it.def("Sincos", &format!("x::{t} -> FldReElt, FldReElt"), "The sine and the cosine of x.", sincos);
        for u in ["RngIntElt", "FldRatElt", "FldReElt"] {
            it.def("Log", &format!("b::{t}, x::{u} -> FldReElt"), "The logarithm of x to the base b.", log_base);
            for name in ["Arctan", "Arctan2"] {
                it.def(name, &format!("x::{t}, y::{u} -> FldReElt"), "The angle of the point (x, y) in (-pi, pi], the inverse tangent of y/x.", arctan2);
            }
        }
    }

    // Gamma, Bessel and associated functions; integers and rationals are in
    // the default field.
    const REAL_ARGS: [&str; 3] = ["RngIntElt", "FldRatElt", "FldReElt"];
    for t in ["RngIntElt", "FldRatElt", "FldReElt", "FldComElt"] {
        let r = if t == "FldComElt" { t } else { "FldReElt" };
        it.def("Gamma", &format!("x::{t} -> {r}"), "The gamma function of x.", gamma_function);
        it.def("LogGamma", &format!("x::{t} -> {r}"), "The logarithm of the gamma function of x (its principal branch).", gamma_function);
        for name in ["Psi", "LogDerivative"] {
            it.def(name, &format!("x::{t} -> {r}"), "The logarithmic derivative of the gamma function at x.", gamma_function);
        }
    }
    let incomplete = [("Complementary", Value::Bool(false)), ("Gamma", Value::Undef)];
    for t in REAL_ARGS {
        for u in REAL_ARGS {
            it.def_params("Gamma", &format!("s::{t}, t::{u} -> FldReElt"), &incomplete, "The incomplete gamma function: the integral of u^(s-1) e^-u from 0 to t (from t to infinity with Complementary).", incomplete_gamma);
        }
        it.def("GammaD", &format!("s::{t} -> FldReElt"), "The gamma function of s + 1/2.", gamma_d);
        it.def("BesselFunction", &format!("n::RngIntElt, x::{t} -> FldReElt"), "The Bessel function of the first kind J_n(x).", bessel_function);
        it.def("BesselFunctionSecondKind", &format!("n::RngIntElt, x::{t} -> FldReElt"), "The Bessel function of the second kind Y_n(x).", bessel_function);
    }
    for t in ["RngIntElt", "FldReElt"] {
        it.def("JBessel", &format!("n::{t}, x::FldReElt -> FldReElt"), "The Bessel function of the first kind of half-integral order J_(n+1/2)(x).", j_bessel);
    }
    for name in ["KBessel", "KBessel2"] {
        for (t, u) in [("FldReElt", "FldReElt"), ("RngIntElt", "FldReElt"), ("FldRatElt", "FldReElt"), ("FldReElt", "RngIntElt"), ("FldReElt", "FldRatElt"), ("FldComElt", "FldReElt")] {
            let r = if t == "FldComElt" { t } else { "FldReElt" };
            it.def(name, &format!("n::{t}, x::{u} -> {r}"), "The modified Bessel function of the second kind K_n(x), x > 0.", k_bessel);
        }
    }
    for t in REAL_ARGS {
        for u in REAL_ARGS {
            for v in REAL_ARGS {
                it.def("HypergeometricU", &format!("a::{t}, b::{u}, x::{v} -> FldReElt"), "The confluent hypergeometric function U(a, b, x), x > 0.", hypergeometric_u);
            }
        }
    }
}
