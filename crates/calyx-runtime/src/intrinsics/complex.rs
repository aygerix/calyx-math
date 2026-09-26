//! Complex fields and their elements (pairs of MPFR numbers), with `reals`:
//! the Real and Complex Fields chapter.
//!
//! A complex field is a ring (`RingKind::Complex`, so that polynomial
//! rings can be built over it) determined by its precision in bits; its
//! elements are `Value::Complex`. Operations are rounded correctly in each
//! part, as with MPC, which Magma uses.

use std::rc::Rc;

use calyx_flint::{Elementary, ModifiedPolylog, Real};
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
            _ => Err(Some("Illegal coercion\n".into())),
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
                let n = reals::small_exponent(n)?;
                if x.is_zero() && n < 0 {
                    return Err(RuntimeError::runtime("Illegal negative power of zero element").in_context("^"));
                }
                cv(x.pow_i64(n))
            }
            _ => cv(x.pow(&y)),
        },
        Eq | Cmpeq => Value::Bool(reals::num_eq(a, b).unwrap_or(false)),
        Ne | Cmpne => Value::Bool(!reals::num_eq(a, b).unwrap_or(false)),
        Lt | Le | Gt | Ge => {
            let name = match op { Lt => "lt", Le => "le", Gt => "gt", _ => "ge" };
            return Err(RuntimeError::runtime("No comparison algorithm exists for given objects").in_context(name));
        }
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
    boolv(arg_c(a, 0).is_zero())
}

// ----- elements ------------------------------------------------------------------

fn arg_c(a: &CallArgs, i: usize) -> &ComplexV {
    let Value::Complex(c) = &a.args[i] else { unreachable!() };
    c
}

fn is_real(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(arg_c(a, 0).im.is_zero())
}

fn is_integral(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let c = arg_c(a, 0);
    boolv(c.im.is_zero() && c.re.is_integer())
}

fn real_part(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::real(arg_c(a, 0).re.clone()))
}

fn imaginary_part(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::real(arg_c(a, 0).im.clone()))
}

fn modulus(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::real(arg_c(a, 0).abs()))
}

fn argument(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::real(arg_c(a, 0).arg()))
}

fn norm(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::real(arg_c(a, 0).norm()))
}

fn conjugate(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(cv(arg_c(a, 0).conj()))
}

/// The modulus and the argument. (Magma 2.22 returns the arccosine of
/// `Re(c)/|c|` as the argument, which loses its sign; this follows the
/// handbook.)
fn complex_to_polar(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let c = arg_c(a, 0);
    Ok(vals![Value::real(c.abs()), Value::real(c.arg())])
}

/// `m·e^(ia)`, at the smaller precision of the real arguments (the default
/// precision if neither is real).
fn polar_to_complex(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bits = match (reals::prec_of(&a.args[0]), reals::prec_of(&a.args[1])) {
        (Some(x), Some(y)) => x.min(y),
        (Some(x), None) | (None, Some(x)) => x,
        _ => default_bits(),
    };
    let (m, t) = (to_real(&a.args[0], bits).unwrap(), to_real(&a.args[1], bits).unwrap());
    one(cv(ComplexV::polar(&m, &t)))
}

fn sqrt(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(cv(arg_c(a, 0).sqrt()))
}

/// The n-th root that Magma returns (NaN for n < 1). Magma computes it by
/// Newton's method and does not document which root it finds: for n = 2
/// it is the negative of the principal square root, on the negative real
/// axis the conjugate of the principal root (the real root for n = 3), and
/// otherwise usually the principal root. The sign of a zero imaginary part
/// does not matter.
pub fn magma_root(c: &ComplexV, n: &calyx_flint::Integer) -> ComplexV {
    let bits = c.prec();
    let c = &if c.im.is_zero() { ComplexV::from_real(c.re.clone()) } else { c.clone() };
    match n.to_u64().filter(|&k| k > 0) {
        Some(2) => c.sqrt().neg(),
        Some(3) if c.im.is_zero() && c.re.sign() < 0 => ComplexV::from_real(c.re.root(3)),
        Some(k) if c.im.is_zero() && c.re.sign() < 0 => c.root(k).conj(),
        Some(k) => c.root(k),
        None => ComplexV::new(Real::nan(bits), Real::nan(bits)),
    }
}

fn root(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(1)?;
    one(cv(magma_root(arg_c(a, 0), n)))
}

// ----- transcendental functions ------------------------------------------------

/// Magma's error for complex functions at a pole: raised without a
/// position (and so reported without the source line).
fn pole() -> RuntimeError {
    crate::error::ErrorInfo { style: crate::error::ErrStyle::Bare, ..crate::error::ErrorInfo::runtime("Division by zero") }.into()
}

/// `1/z`, as `z^-1`.
fn recip(z: &ComplexV) -> RResult<ComplexV> {
    ComplexV::from_real(Real::from_i64(1, z.prec())).div(z).ok_or_else(pole)
}

/// The inverse tangent; Magma excludes `i` (but not `-i`).
fn arctan(z: &ComplexV) -> RResult<ComplexV> {
    if z.re.is_zero() && z.im == Real::from_i64(1, z.prec()) {
        return Err(RuntimeError::runtime("Cannot take Arctan of Sqrt(-1)").in_context("Arctan"));
    }
    Ok(z.elementary(Elementary::Atan))
}

/// A transcendental function of a complex number, by its Magma name (the
/// names of `reals::REAL_FUNCTIONS`). The reciprocal functions divide by
/// the value of the function (cotangent: the cosine by the sine), and the
/// inverse ones apply the inverse function to `1/z`, as Magma does.
pub fn complex_function_of(name: &str, z: &ComplexV) -> RResult<ComplexV> {
    use Elementary::*;
    let f = |g: Elementary| z.elementary(g);
    Ok(match name {
        "Exp" => f(Exp),
        "Log" if z.is_zero() => return Err(RuntimeError::runtime("Can not take log of zero element")),
        "Log" => f(Log),
        "Dilog" => z.polylog(2),
        "Sin" => f(Sin),
        "Cos" => f(Cos),
        "Tan" => f(Tan),
        "Cot" => f(Cos).div(&f(Sin)).ok_or_else(pole)?,
        "Sec" => recip(&f(Cos))?,
        "Cosec" => recip(&f(Sin))?,
        "Arcsin" => f(Asin),
        "Arccos" => f(Acos),
        "Arctan" => arctan(z)?,
        "Arccot" => arctan(&recip(z)?)?,
        "Arcsec" => recip(z)?.elementary(Acos),
        "Arccosec" => recip(z)?.elementary(Asin),
        "Sinh" => f(Sinh),
        "Cosh" => f(Cosh),
        "Tanh" => f(Tanh),
        "Coth" => recip(&f(Tanh))?,
        "Sech" => recip(&f(Cosh))?,
        "Cosech" => recip(&f(Sinh))?,
        "Argsinh" => f(Asinh),
        "Argcosh" => f(Acosh),
        "Argtanh" => f(Atanh),
        "Argsech" => recip(z)?.elementary(Acosh),
        "Argcosech" => recip(z)?.elementary(Asinh),
        "Argcoth" => recip(z)?.elementary(Atanh),
        _ => unreachable!("{name}"),
    })
}

fn complex_function(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let z = match &a.args[0] {
        Value::Complex(c) => (**c).clone(),
        v => to_complex(v, default_bits()).unwrap(),
    };
    one(cv(complex_function_of(&a.name.as_rc(), &z)?))
}

fn sincos(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let z = arg_c(a, 0);
    Ok(vals![cv(z.elementary(Elementary::Sin)), cv(z.elementary(Elementary::Cos))])
}

/// The index m >= 1 of a polylogarithm.
fn polylog_index(a: &CallArgs) -> RResult<u64> {
    let m = a.int(0)?;
    if m.sign() <= 0 {
        return Err(super::arg_not(1, "positive"));
    }
    m.to_u64().filter(|&m| m < 1 << 24).ok_or_else(|| RuntimeError::runtime("Argument 1 is too large"))
}

/// The argument of a polylogarithm as a complex number (integers and
/// rationals in the default field).
fn polylog_arg(a: &CallArgs) -> ComplexV {
    let v = &a.args[1];
    to_complex(v, reals::prec_of(v).unwrap_or_else(default_bits)).unwrap()
}

/// `Polylog(m, x)`: the m-th polylogarithm (computed like PARI's for real
/// x > 1: the limit from below the cut).
fn polylog(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = polylog_index(a)?;
    let z = polylog_arg(a);
    if m == 1 && z.im.is_zero() && z.re == Real::from_i64(1, z.prec()) {
        return Err(RuntimeError::runtime("Arguments cannot both be 1"));
    }
    one(cv(z.polylog(m as i64)))
}

/// Zagier's modified polylogarithms (PARI's `polylog` with flag 1, 2 and
/// 3): real numbers, complex for a complex argument.
fn modified_polylog(a: &CallArgs, f: ModifiedPolylog) -> RResult<Vals> {
    let m = polylog_index(a)?;
    let z = polylog_arg(a);
    let v = z.modified_polylog(m, f);
    one(if matches!(a.args[1], Value::Complex(_)) { cv(ComplexV::from_real(v)) } else { Value::real(v) })
}

fn polylog_d(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    modified_polylog(a, ModifiedPolylog::DTilde)
}

fn polylog_d_old(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    modified_polylog(a, ModifiedPolylog::D)
}

fn polylog_p(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    modified_polylog(a, ModifiedPolylog::P)
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
    it.def("IsReal", "x::FldComElt -> BoolElt", "Whether the imaginary part of x is zero.", is_real);
    it.def("IsIntegral", "x::FldComElt -> BoolElt", "Whether x is an integer.", is_integral);
    for name in ["Real", "Re"] {
        it.def(name, "x::FldComElt -> FldReElt", "The real part of x.", real_part);
    }
    for name in ["Imaginary", "Im"] {
        it.def(name, "x::FldComElt -> FldReElt", "The imaginary part of x.", imaginary_part);
    }
    for name in ["Modulus", "Abs", "AbsoluteValue"] {
        it.def(name, "x::FldComElt -> FldReElt", "The modulus of x.", modulus);
    }
    for name in ["Arg", "Argument"] {
        it.def(name, "x::FldComElt -> FldReElt", "The argument of x, in [-pi, pi].", argument);
    }
    it.def("Norm", "x::FldComElt -> FldReElt", "The norm Re(x)^2 + Im(x)^2 of x.", norm);
    for name in ["ComplexConjugate", "Conjugate"] {
        it.def(name, "x::FldComElt -> FldComElt", "The complex conjugate of x.", conjugate);
    }
    it.def("ComplexToPolar", "x::FldComElt -> FldReElt, FldReElt", "The modulus and the argument of x.", complex_to_polar);
    for s in ["RngIntElt", "FldRatElt", "FldReElt"] {
        for t in ["RngIntElt", "FldRatElt", "FldReElt"] {
            it.def("PolarToComplex", &format!("m::{s}, a::{t} -> FldComElt"), "The complex number m*e^(i*a).", polar_to_complex);
        }
    }
    for name in ["Sqrt", "SquareRoot"] {
        it.def(name, "x::FldComElt -> FldComElt", "The principal square root of x.", sqrt);
    }
    it.def("Root", "x::FldComElt, n::RngIntElt -> FldComElt", "An n-th root of x.", root);

    // Transcendental functions.
    for (name, _) in reals::REAL_FUNCTIONS {
        it.def(name, "z::FldComElt -> FldComElt", &format!("The {} of z, on the principal branch.", complex_doc(name)), complex_function);
    }
    for t in ["RngIntElt", "FldRatElt"] {
        it.def("Dilog", &format!("x::{t} -> FldComElt"), "The dilogarithm of x, in the default complex field.", complex_function);
    }
    it.def("Sincos", "z::FldComElt -> FldComElt, FldComElt", "The sine and the cosine of z.", sincos);
    for t in ["RngIntElt", "FldRatElt", "FldReElt", "FldComElt"] {
        it.def("Polylog", &format!("m::RngIntElt, x::{t} -> FldComElt"), "The m-th polylogarithm of x (m >= 1).", polylog);
        let r = if t == "FldComElt" { "FldComElt" } else { "FldReElt" };
        it.def("PolylogD", &format!("m::RngIntElt, x::{t} -> {r}"), "Zagier's modified m-th polylogarithm D~_m(x) (m >= 1).", polylog_d);
        it.def("PolylogDold", &format!("m::RngIntElt, x::{t} -> {r}"), "Zagier's modified m-th polylogarithm D_m(x) (m >= 1).", polylog_d_old);
        it.def("PolylogP", &format!("m::RngIntElt, x::{t} -> {r}"), "Zagier's modified m-th polylogarithm P_m(x) (m >= 1).", polylog_p);
    }
}

/// What a function of `REAL_FUNCTIONS` computes, for its description.
fn complex_doc(name: &str) -> &'static str {
    match name {
        "Exp" => "exponential",
        "Log" => "natural logarithm",
        "Dilog" => "dilogarithm",
        "Sin" => "sine",
        "Cos" => "cosine",
        "Tan" => "tangent",
        "Cot" => "cotangent",
        "Sec" => "secant",
        "Cosec" => "cosecant",
        "Arcsin" => "inverse sine",
        "Arccos" => "inverse cosine",
        "Arctan" => "inverse tangent",
        "Arccot" => "inverse cotangent",
        "Arcsec" => "inverse secant",
        "Arccosec" => "inverse cosecant",
        "Sinh" => "hyperbolic sine",
        "Cosh" => "hyperbolic cosine",
        "Tanh" => "hyperbolic tangent",
        "Coth" => "hyperbolic cotangent",
        "Sech" => "hyperbolic secant",
        "Cosech" => "hyperbolic cosecant",
        "Argsinh" => "inverse hyperbolic sine",
        "Argcosh" => "inverse hyperbolic cosine",
        "Argtanh" => "inverse hyperbolic tangent",
        "Argsech" => "inverse hyperbolic secant",
        "Argcosech" => "inverse hyperbolic cosecant",
        _ => "inverse hyperbolic cotangent",
    }
}
