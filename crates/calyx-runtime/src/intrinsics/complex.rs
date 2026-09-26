//! Complex fields and their elements (pairs of MPFR numbers), with `reals`:
//! the Real and Complex Fields chapter.
//!
//! A complex field is a ring (`RingKind::Complex`, so that polynomial
//! rings can be built over it) determined by its precision in bits; its
//! elements are `Value::Complex`. Operations are rounded correctly in each
//! part, as with MPC, which Magma uses.

use std::rc::Rc;

use calyx_flint::approx::{self, ApproxError};
use calyx_flint::gr::CtxKind;
use calyx_flint::polroots;
use calyx_flint::{Elementary, Integer, ModifiedPolylog, Modular, Rational, Real, ThetaCost};
use calyx_syntax::ast::BinOp;

use super::reals::{self, default_bits, field_bits, to_real};
use super::{arg_not, boolv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::ops::div_by_zero;
use crate::print::Level;
use crate::rings::{Elt, RingKind, ring_of};
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
    let n = a.int(1)?;
    if n.to_i64() != Some(1) {
        return Err(RuntimeError::runtime(format!("Value for generator index ({n}) should be in the range [1..1]")));
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

// ----- elliptic and modular functions ------------------------------------------------

/// A point of the upper half plane; `numbered`: the error names the
/// argument.
fn upper_half_plane(z: &ComplexV, numbered: bool) -> RResult<()> {
    if z.im.sign() > 0 {
        return Ok(());
    }
    Err(RuntimeError::runtime(if numbered { "Argument 1 must have positive imaginary part" } else { "Argument must have positive imaginary part" }))
}

/// The point `tau` of the lattice `[a, b]`: `a/b`, or `1/(a/b)` if that is
/// in the upper half plane.
fn lattice_point(l: &SeqEnum) -> RResult<ComplexV> {
    if l.elems.len() != 2 {
        return Err(RuntimeError::runtime("Lattice must have two basis elements"));
    }
    let bits = l.universe.as_ref().and_then(reals::bits_of).unwrap_or_else(default_bits);
    let (Some(x), Some(y)) = (to_complex(&l.elems[0], bits), to_complex(&l.elems[1], bits)) else {
        return Err(RuntimeError::runtime("Bad argument types"));
    };
    let degenerate = || RuntimeError::runtime("Lattice is degenerate");
    let w = x.div(&y).ok_or_else(degenerate)?;
    if w.im.sign() > 0 {
        return Ok(w);
    }
    let w = ComplexV::from_real(Real::from_i64(1, bits)).div(&w).ok_or_else(degenerate)?;
    if w.im.sign() > 0 { Ok(w) } else { Err(degenerate()) }
}

/// The point of the upper half plane given as argument `i`: a complex
/// number, or a lattice. `numbered`: the error names the argument.
fn point_arg(it: &Interp, a: &CallArgs, i: usize, numbered: bool) -> RResult<ComplexV> {
    let s = match &a.args[i] {
        Value::Complex(c) => {
            upper_half_plane(c, numbered)?;
            return Ok((**c).clone());
        }
        Value::Seq(s) => s,
        _ => unreachable!(),
    };
    // jInvariant takes a sequence of integers or rationals as the complex
    // number C![a, b], as Magma does.
    if &*a.name.as_rc() == "jInvariant" && s.universe.as_ref().is_some_and(|u| u.is_integers() || u.is_rationals()) {
        let bits = default_bits();
        return match (s.elems.len(), s.elems.first().and_then(|x| to_real(x, bits)), s.elems.last().and_then(|x| to_real(x, bits))) {
            (2, Some(re), Some(im)) => {
                let c = ComplexV::new(re, im);
                upper_half_plane(&c, true)?;
                Ok(c)
            }
            _ => Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}", it.type_name_ext(&a.args[i])))),
        };
    }
    lattice_point(s)
}

/// The weight of an Eisenstein series: even, and positive and below 2^30.
fn eisenstein_weight(a: &CallArgs) -> RResult<u64> {
    let k = a.int(0)?;
    let Some(k) = k.to_u64().filter(|&k| k > 0 && k < 1 << 30) else {
        return Err(RuntimeError::runtime(format!("Argument 1 ({k}) is not small and positive")));
    };
    if k % 2 == 1 {
        return Err(RuntimeError::runtime("Argument 1 (= 2 * k) must be even"));
    }
    Ok(k)
}

/// `Eisenstein(k, t)`: the normalized Eisenstein series E_k at t (or at the
/// point of a lattice).
fn eisenstein(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = eisenstein_weight(a)?;
    let t = point_arg(it, a, 1, false)?;
    one(cv(t.eisenstein(k)))
}

/// Dedekind's eta, j, the discriminant and Weber's functions at a point of
/// the upper half plane (or, for j and the discriminant, of a lattice).
fn modular_function(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let name = a.name.as_rc();
    let f = match &*name {
        "DedekindEta" => Modular::Eta,
        "jInvariant" => Modular::J,
        "Delta" => Modular::Delta,
        "WeberF" => Modular::WeberF,
        "WeberF1" => Modular::WeberF1,
        _ => Modular::WeberF2,
    };
    let t = point_arg(it, a, 0, f != Modular::Delta)?;
    one(cv(t.modular(f)))
}

/// Check the nome q of a theta function: |q| < 1.
fn nome(q: &ComplexV, msg: &'static str) -> RResult<()> {
    let r = q.abs();
    if !r.is_nan() && r < Real::from_i64(1, 2) { Ok(()) } else { Err(RuntimeError::runtime(msg)) }
}

/// A real value as a real number, and a complex one (from a negative nome)
/// as a complex number.
fn real_or_complex(v: ComplexV, real: bool) -> Value {
    if real && v.im.is_zero() { Value::real(v.re) } else { cv(v) }
}

/// `JacobiTheta(q, z)`: Jacobi's first theta function with nome q. The
/// result is in the field of q and z if they are both real or both complex
/// numbers of the same precision. Other arguments are taken (as by Magma,
/// which makes z a power series) in the default precision.
fn jacobi_theta(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (x, y) = (&a.args[0], &a.args[1]);
    let (bits, msg, real) = match (x, y) {
        (Value::Real(p), Value::Real(q)) if p.x.prec() == q.x.prec() => (p.x.prec(), "Argument must have absolute value < 1", true),
        (Value::Complex(p), Value::Complex(q)) if p.prec() == q.prec() => (p.prec(), "First argument must have absolute values less \nthan 1", false),
        _ => (default_bits(), "First argument must have absolute value less \nthan 1", !matches!(x, Value::Complex(_)) && !matches!(y, Value::Complex(_))),
    };
    let (q, z) = (to_complex(x, bits).unwrap(), to_complex(y, bits).unwrap());
    nome(&q, msg)?;
    one(real_or_complex(ComplexV::jacobi_theta(&q, &z, bits), real))
}

/// `JacobiThetaNullK(q, k)`: the k-th derivative of Jacobi's theta function
/// at z = 0. A complex q must be real, as with Magma.
fn jacobi_theta_null(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let v = &a.args[0];
    if matches!(v, Value::Complex(c) if !c.im.is_zero()) {
        let types = format!("{}, {}", it.type_name_ext(v), it.type_name_ext(&a.args[1]));
        return Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {types}")));
    }
    let q = to_complex(v, reals::prec_of(v).unwrap_or_else(default_bits)).unwrap();
    nome(&q, "Argument must have absolute value < 1")?;
    let k = a.int(1)?;
    let Some(k) = k.to_i64() else {
        // Beyond a machine word, Magma gives 0 for even k.
        if k.is_even() {
            return one(Value::real(Real::zero(q.prec())));
        }
        return Err(RuntimeError::runtime("Argument 2 is too large"));
    };
    match ComplexV::jacobi_theta_null(&q, k, q.prec()) {
        Ok(t) => one(real_or_complex(t, true)),
        Err(ThetaCost::Nome) => Err(RuntimeError::runtime("Argument 1 is too close to 1")),
        Err(ThetaCost::Order) => Err(RuntimeError::runtime("Argument 2 is too large")),
    }
}

// ----- roots of polynomials -----------------------------------------------------

/// The coefficients of `f`, constant term first, as the real and imaginary
/// parts of Gaussian integers after clearing denominators, if its
/// coefficient ring is the integers, the rationals or a real or complex
/// field. Roots are those of the exact coefficients (as in Magma, which
/// does not round the coefficients of `f` into the field of the roots).
fn exact_coefficients(f: &Elt) -> Option<(Vec<Integer>, Vec<Integer>)> {
    let kind = f.x.ctx().base()?.kind().clone();
    let mut parts = Vec::new();
    for k in 0..f.x.poly_len() {
        let c = f.x.poly_coeff(k);
        parts.push(match kind {
            CtxKind::Integers => (Rational::from_integer(&c.to_integer().ok()?), Rational::zero()),
            CtxKind::Rationals => (c.to_rational().ok()?, Rational::zero()),
            CtxKind::RealFloat(_) => (c.to_real()?.to_rational()?, Rational::zero()),
            CtxKind::ComplexFloat(_) => {
                let (x, y) = c.to_complex_parts()?;
                (x.to_rational()?, y.to_rational()?)
            }
            _ => return None,
        });
    }
    let den = parts.iter().fold(Integer::one(), |d, (x, y)| d.lcm(&x.denominator()).lcm(&y.denominator()));
    let den = Rational::from_integer(&den);
    Some(parts.iter().map(|(x, y)| ((x * &den).numerator(), (y * &den).numerator())).unzip())
}

/// Checks the parameters of Roots over a real or complex field. Al and
/// Digits choose Magma's algorithm and its accuracy, but the roots here are
/// always rounded correctly, so like Max (which Magma ignores here) they
/// are not used.
fn root_params(it: &Interp, a: &CallArgs) -> RResult<()> {
    let types = || a.args.iter().map(|v| it.type_name_ext(v)).collect::<Vec<_>>().join(", ");
    let bad_type = |p: &str| RuntimeError::runtime(format!("Bad type for parameter '{p}'\nArgument types given: {}", types()));
    match a.param("Al") {
        Some(Value::Str(s)) if !["Schonhage", "Laguerre", "NewtonRaphson", "Combination"].contains(&s.as_str()) => {
            return Err(RuntimeError::runtime(format!("Bad value for parameter 'Al' ({})\nArgument types given: {}", s.as_str(), types())));
        }
        None | Some(Value::Str(_)) => {}
        Some(_) => return Err(bad_type("Al")),
    }
    match a.param("Digits") {
        Some(Value::Int(n)) if n.sign() <= 0 => return Err(RuntimeError::runtime("Bad value for parameter 'Digits': value not positive")),
        None | Some(Value::Undef | Value::Int(_)) => {}
        Some(_) => return Err(bad_type("Digits")),
    }
    match a.param("Max") {
        Some(Value::Int(m)) if !m.to_i64().is_some_and(|v| (0..1 << 30).contains(&v)) => Err(RuntimeError::runtime("Bad value for parameter 'Max': value not small non-negative")),
        None | Some(Value::Undef | Value::Int(_)) => Ok(()),
        Some(_) => Err(bad_type("Max")),
    }
}

/// The precision of a real or complex field, and whether it is complex.
fn root_field(s: &Value) -> (u64, bool) {
    match s {
        Value::Struct(st) => match &st.kind {
            StructKind::Reals(bits) => (*bits, false),
            StructKind::Ring(r) => match r.kind {
                RingKind::Complex(bits) => (bits, true),
                _ => unreachable!("a real or complex field"),
            },
            _ => unreachable!("a real or complex field"),
        },
        _ => unreachable!("a real or complex field"),
    }
}

/// The polynomial argument of Roots or HasRoot, and the field `S` to find
/// its roots in (argument 2, or its coefficient field), with its exact
/// coefficients if they lie in `S`.
fn root_args(a: &CallArgs, verb: &str) -> RResult<(Value, u64, bool, Vec<Integer>, Vec<Integer>)> {
    let Value::Elt(f) = &a.args[0] else { unreachable!("a polynomial argument") };
    let s = a.args.get(1).cloned().unwrap_or_else(|| f.ring().base().expect("a polynomial").clone());
    let (bits, complex) = root_field(&s);
    match exact_coefficients(f).filter(|(_, im)| complex || im.iter().all(Integer::is_zero)) {
        Some((re, im)) => Ok((s, bits, complex, re, im)),
        None => Err(RuntimeError::runtime(format!("Argument 1 cannot be {verb} to be over argument 2"))),
    }
}

/// The roots in `S` of the nonzero polynomial with Gaussian integer
/// coefficients `re + i·im`: in ascending order in a real field, and in a
/// complex field in the order of `polroots::complex_roots` (Magma lists them
/// in the order PARI finds them).
fn field_roots(bits: u64, complex: bool, re: &[Integer], im: &[Integer]) -> RResult<Vec<(Value, u64)>> {
    if !complex {
        return Ok(polroots::real_roots(re, bits).into_iter().map(|(r, e)| (Value::real(r), e)).collect());
    }
    let rs = polroots::complex_roots(re, im, bits).ok_or_else(|| RuntimeError::runtime("Roots could not be computed"))?;
    Ok(rs.into_iter().map(|(z, e)| (cv(z), e)).collect())
}

fn roots(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    root_params(it, a)?;
    let (s, bits, complex, re, im) = root_args(a, "coerced")?;
    if re.iter().chain(&im).all(Integer::is_zero) {
        return Err(arg_not(1, "non-zero"));
    }
    let rs = field_roots(bits, complex, &re, &im)?;
    let universe = Value::structure(StructKind::Cartesian(vec![s, Value::integers()]));
    one(Value::seq(Some(universe), rs.into_iter().map(|(r, e)| Value::tuple(vec![r, Value::int(e as i64)])).collect()))
}

/// Whether the polynomial has a root in `S`, and a root: zero if it is one,
/// else the first of its roots.
fn has_root(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, bits, complex, re, im) = root_args(a, "changed")?;
    if re.first().is_none_or(Integer::is_zero) && im.first().is_none_or(Integer::is_zero) {
        let zero = if complex { cv(ComplexV::new(Real::zero(bits), Real::zero(bits))) } else { Value::real(Real::zero(bits)) };
        return Ok(vals![Value::Bool(true), zero]);
    }
    match field_roots(bits, complex, &re, &im)?.into_iter().next() {
        Some((r, _)) => Ok(vals![Value::Bool(true), r]),
        None => Ok(vals![Value::Bool(false), Value::Undef]),
    }
}

/// Argument i, a real number or a complex one that is real, as Magma's
/// real intrinsics take it.
fn real_valued(it: &Interp, a: &CallArgs, i: usize) -> RResult<Real> {
    match &a.args[i] {
        Value::Real(r) => Ok(r.x.clone()),
        Value::Complex(c) if c.im.is_zero() => Ok(c.re.clone()),
        _ => {
            let types: Vec<String> = a.args.iter().map(|v| it.type_name_ext(v)).collect();
            Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}", types.join(", "))))
        }
    }
}

/// `ContinuedFraction(x : Bound)`: the continued fraction of x up to its
/// precision (see `calyx_flint::approx`).
fn continued_fraction(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bound = match a.param("Bound") {
        None | Some(Value::Undef) => None,
        Some(Value::Int(n)) if n.sign() < 0 => return Err(RuntimeError::runtime("Bad value for parameter 'Bound'")),
        Some(Value::Int(n)) => Some(n.clone()),
        Some(_) => return Err(reals::bad_param(it, a, "Bound")),
    };
    let x = real_valued(it, a, 0)?;
    let terms = approx::continued_fraction(&x, bound.as_ref()).ok_or_else(|| RuntimeError::runtime("Undefined sequence element"))?;
    one(Value::int_seq(terms))
}

/// `BestApproximation(x, k)`: PARI's best approximation of x by a rational
/// of denominator at most k (see `calyx_flint::approx`).
fn best_approximation(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = real_valued(it, a, 0)?;
    match approx::best_approximation(&x, a.int(1)?) {
        Ok(q) => one(Value::rat(q)),
        Err(ApproxError::DivisionByZero) => Err(RuntimeError::runtime("Division by zero in (possibly) real or complex division. Maybe loss of precision?")),
        Err(ApproxError::PrecisionLoss) => Err(RuntimeError::runtime("Overflow or precision loss in truncation")),
    }
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

    // Elliptic and modular functions.
    it.def("Eisenstein", "k::RngIntElt, t::FldComElt -> FldComElt", "The normalized Eisenstein series E_k at t in the upper half plane (k even).", eisenstein);
    it.def("Eisenstein", "k::RngIntElt, L::SeqEnum -> FldComElt", "E_k at the point a/b (or b/a) of the upper half plane, for the lattice L = [a, b].", eisenstein);
    for (name, doc) in [
        ("DedekindEta", "Dedekind's eta function at s in the upper half plane."),
        ("jInvariant", "The elliptic j-invariant at s in the upper half plane."),
        ("Delta", "The discriminant Delta = eta^24 at s in the upper half plane."),
        ("WeberF", "Weber's function f at s in the upper half plane."),
        ("WeberF1", "Weber's function f1 at s in the upper half plane."),
        ("WeberF2", "Weber's function f2 at s in the upper half plane."),
    ] {
        it.def(name, "s::FldComElt -> FldComElt", doc, modular_function);
    }
    for name in ["jInvariant", "Delta"] {
        it.def(name, "L::SeqEnum -> FldComElt", "The value at the point a/b (or b/a) of the upper half plane, for the lattice L = [a, b].", modular_function);
    }
    for s in ["RngIntElt", "FldRatElt", "FldReElt", "FldComElt"] {
        for t in ["RngIntElt", "FldRatElt", "FldReElt", "FldComElt"] {
            let r = if s == "FldComElt" || t == "FldComElt" { "FldComElt" } else { "FldReElt" };
            it.def("JacobiTheta", &format!("q::{s}, z::{t} -> {r}"), "Jacobi's first theta function with nome q (|q| < 1) at z.", jacobi_theta);
        }
    }
    // Roots of polynomials.
    let params = [("Al", Value::str("Schonhage")), ("Digits", Value::Undef), ("Max", Value::Undef)];
    for t in ["FldRe", "FldCom"] {
        it.def_params("Roots", &format!("p::RngUPolElt[{t}] -> [Tup]"), &params, "The roots of p in its coefficient field with their multiplicities, rounded correctly.", roots);
        it.def_params("Roots", &format!("p::RngUPolElt, S::{t} -> [Tup]"), &params, "The roots of p in S with their multiplicities, rounded correctly.", roots);
        it.def("HasRoot", &format!("p::RngUPolElt[{t}] -> BoolElt, {t}Elt"), "Whether p has a root in its coefficient field, and a root (0 if it is one, else the first of its roots).", has_root);
        it.def("HasRoot", &format!("p::RngUPolElt, S::{t} -> BoolElt, {t}Elt"), "Whether p has a root in S, and a root (0 if it is one, else the first of its roots).", has_root);
    }
    // Continued fractions, of real numbers and of complex numbers that are
    // real.
    for t in ["FldReElt", "FldComElt"] {
        let doc = "The partial quotients of the continued fraction of x, as far as the precision of x determines them (at most Bound of them).";
        it.def_params("ContinuedFraction", &format!("x::{t} -> [RngIntElt]"), &[("Bound", Value::Undef)], doc, continued_fraction);
        let doc = "A rational approximation to x of denominator at most k, at least as close as the convergents of such denominators (PARI's bestappr).";
        it.def("BestApproximation", &format!("x::{t}, k::RngIntElt -> FldRatElt"), doc, best_approximation);
    }
    for s in ["RngIntElt", "FldRatElt", "FldReElt", "FldComElt"] {
        it.def("JacobiThetaNullK", &format!("q::{s}, k::RngIntElt -> FldReElt"), "The k-th derivative at 0 of Jacobi's first theta function with nome q (real).", jacobi_theta_null);
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
