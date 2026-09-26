//! Linear and algebraic dependencies among real and complex numbers.
//! IntegerRelation and MinimalPolynomial reduce the lattices Magma builds
//! with the L² algorithm and the parameters of Magma's LLL; the deprecated
//! LinearRelation and PowerRelation follow PARI's lindep and algdep, which
//! Magma calls for them.

use std::rc::Rc;

use calyx_flint::gr::{Ctx, Elem};
use calyx_flint::upoly as fu;
use calyx_flint::{Complex, Integer, Real, digits_for_bits, lll_l2};

use super::{bad_param_value, bits_of, default_bits};
use crate::error::{RResult, RuntimeError, TraceFrame};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::{arg_ge, hidden, hidden_inner, one, require};
use crate::rings::RingKind;
use crate::sym::Sym;
use crate::value::*;

/// The size-reduction bound of Magma's LLL, (Eta + 1/2)/2 for its default
/// Eta = 0.501.
const ETA: f64 = 0.5005;

/// A real or complex number with its precision, as the relations take
/// them: reals as complex numbers with imaginary part zero.
struct Nums {
    z: Vec<Complex>,
    complex: bool,
    bits: u64,
}

impl Nums {
    fn value(&self, x: &Complex) -> Value {
        if self.complex { Value::Complex(Rc::new(x.clone())) } else { Value::real(x.re.clone()) }
    }

    /// The numbers `z` as a sequence over their field.
    fn seq(&self, it: &mut Interp, z: &[Complex]) -> Value {
        let field = if self.complex { it.complex_field(self.bits) } else { Value::reals(self.bits) };
        let elems = z.iter().map(|x| self.value(x)).collect();
        Value::seq(Some(field), elems)
    }

    /// `x^k`: correctly rounded for reals, by Magma's binary powering for
    /// complex numbers.
    fn pow(&self, x: &Complex, k: usize) -> Complex {
        if self.complex { x.pow_i64(k as i64) } else { Complex::from_real(x.re.pow_i64(k as i64)) }
    }
}

fn is_complex_field(v: &Value) -> bool {
    matches!(v, Value::Struct(s) if matches!(&s.kind, StructKind::Ring(r) if matches!(r.kind, RingKind::Complex(_))))
}

/// The entries of a sequence of reals or complex numbers.
fn seq_nums(s: &SeqEnum) -> Nums {
    let bits = s.universe.as_ref().and_then(bits_of).unwrap_or_else(default_bits);
    let complex = s.universe.as_ref().is_some_and(is_complex_field);
    let z = s.elems.iter().map(|v| num(v, bits)).collect();
    Nums { z, complex, bits }
}

fn num(v: &Value, bits: u64) -> Complex {
    match v {
        Value::Real(r) => Complex::from_real(r.x.round_to(bits)),
        Value::Complex(c) => c.round_to(bits),
        _ => unreachable!("a real or complex number"),
    }
}

/// A real or complex number argument.
fn arg_num(v: &Value) -> Nums {
    let bits = bits_of(v).expect("a real or complex number");
    Nums { z: vec![num(v, bits)], complex: matches!(v, Value::Complex(_)), bits }
}

fn mul_int(x: &Complex, n: &Integer) -> Complex {
    Complex::new(x.re.mul_integer(n), x.im.mul_integer(n))
}

/// The smallest `n >= 1` with `n^k >= 10^p` (Ceiling(10^(p/k))), for the
/// decimal precision `p` of a field of `bits` bits.
fn default_bound(bits: u64, k: usize) -> Integer {
    let t = Integer::from_i64(10).pow(digits_for_bits(bits));
    let (r, exact) = t.root(k as u64).expect("a positive number");
    if exact { r } else { &r + &Integer::one() }
}

/// The Lovász constant of the LLL IntegerRelation calls with `Delta`, or
/// the error of Magma's LLL: Delta + 0.01, at most halfway to 1.
fn lovasz(delta: &Value) -> RResult<f64> {
    let bad = |m: &str| Err(RuntimeError::runtime(m).in_context("LLL"));
    let d = match delta {
        Value::Real(r) => &r.x,
        Value::Int(_) | Value::Rat(_) | Value::Complex(_) => return bad("Bad value for parameter 'Delta'"),
        _ => return bad("Bad type for parameter 'Delta'\nArgument types given: ModMatFldElt[FldRe]"),
    };
    let p = d.prec();
    if !(*d > Real::from_f64(0.25, p) && *d <= Real::from_i64(1, p)) {
        return bad("Bad value for parameter 'Delta' (should be in range (0.25, 1])");
    }
    let f = d.to_f64();
    if f >= 1.0 || 0.501 >= f.sqrt() {
        return bad(&format!("Bad LLL parameters Delta, Eta {f:.6} 0.501000"));
    }
    Ok((f + 0.01).min((f + 1.0) / 2.0))
}

/// The relation IntegerRelation returns for `q`, not all zero, with bound
/// `h`: the first row of the reduced lattice spanned by the rows of
/// `[I | re c | im c]`, `c = W (q / m)`, where `m` is the largest `|q_i|`,
/// `W = h^d` and each step is rounded in the field of `q`. Magma reduces
/// that real lattice exactly, as the integer lattice `2^s` times it.
fn relation(q: &Nums, z: &[Complex], h: &Integer, delta: f64) -> Vec<Integer> {
    let d = z.len();
    let m = z.iter().map(Complex::abs).max().expect("a number");
    let w = Real::from_integer(&h.pow(d as u64), q.bits);
    let mut cols = vec![z.iter().map(|x| w.mul(&x.re.div(&m).expect("m > 0"))).collect::<Vec<_>>()];
    if q.complex {
        cols.push(z.iter().map(|x| w.mul(&x.im.div(&m).expect("m > 0"))).collect());
    }
    let me: Vec<Vec<(Integer, i64)>> = cols.iter().map(|c| c.iter().map(Real::mantissa_exponent).collect()).collect();
    let s = me.iter().flatten().filter(|(m, _)| !m.is_zero()).map(|&(_, e)| -e).max().unwrap_or(0).max(0);
    let unit = Integer::one().mul_2exp(s as u64);
    let mut rows: Vec<Vec<Integer>> = (0..d)
        .map(|i| {
            let mut r: Vec<Integer> = (0..d).map(|j| if i == j { unit.clone() } else { Integer::zero() }).collect();
            r.extend(me.iter().map(|c| c[i].0.mul_2exp((c[i].1 + s) as u64)));
            r
        })
        .collect();
    lll_l2(&mut rows, delta, ETA);
    rows.swap_remove(0).into_iter().take(d).map(|x| x.fdiv_2exp(s as u64)).collect()
}

/// `|x_1 q_1 + ... + x_d q_d|`, each step rounded: IntegerRelation's
/// measure of fit, summed as `&+` sums a sequence (each half first, the
/// first the shorter).
fn residual(z: &[Complex], x: &[Integer]) -> Real {
    fn sum(t: &[Complex]) -> Complex {
        if let [a] = t {
            return a.clone();
        }
        let (l, r) = t.split_at(t.len() / 2);
        sum(l).add(&sum(r))
    }
    let t: Vec<Complex> = z.iter().zip(x).map(|(y, n)| mul_int(y, n)).collect();
    sum(&t).abs()
}

/// `|f(x)|` for an integer polynomial `f` (constant term first), as Magma
/// evaluates it: Horner's rule over the non-zero coefficients, each run of
/// zeros spanned by a power of `x`.
fn eval_abs(q: &Nums, f: &[Integer], x: &Complex) -> Real {
    let nz: Vec<usize> = (0..f.len()).filter(|&i| !f[i].is_zero()).collect();
    let Some(&top) = nz.last() else { return Real::zero(q.bits) };
    // The leading coefficient stays exact until it is first multiplied.
    let mut acc: Option<Complex> = None;
    let mut prev = top;
    for &i in nz.iter().rev().skip(1).chain(std::iter::once(&0)) {
        if i == prev {
            continue;
        }
        let p = q.pow(x, prev - i);
        let t = match acc {
            None => mul_int(&p, &f[top]),
            Some(a) => a.mul(&p),
        };
        acc = Some(if f[i].is_zero() { t } else { Complex::new(t.re.add_integer(&f[i]), t.im) });
        prev = i;
    }
    acc.unwrap_or_else(|| Complex::from_real(Real::from_integer(&f[top], q.bits))).abs()
}

fn zx() -> Rc<Ctx> {
    thread_local! {
        static ZX: Rc<Ctx> = Ctx::poly(&Ctx::integers());
    }
    ZX.with(Rc::clone)
}

fn zx_elem(f: &[Integer]) -> Elem {
    let zz = Ctx::integers();
    let cs: Vec<Elem> = f.iter().map(|c| Elem::from_integer(&zz, c).expect("an integer")).collect();
    Elem::poly_from_coeffs(&zx(), &cs).expect("an integer polynomial")
}

fn coeffs(f: &Elem) -> Vec<Integer> {
    (0..f.poly_len()).map(|i| f.poly_coeff(i).to_integer().expect("an integer")).collect()
}

/// `f` without leading zeros, with a positive leading coefficient.
fn normalized(mut f: Vec<Integer>) -> Vec<Integer> {
    while f.len() > 1 && f.last().is_some_and(Integer::is_zero) {
        f.pop();
    }
    if f.last().is_some_and(|c| c.sign() < 0) {
        f.iter_mut().for_each(Integer::neg_assign);
    }
    f
}

fn zx_value(it: &mut Interp, f: Vec<Integer>) -> RResult<Value> {
    let px = it.poly_ring(&Value::integers(), true)?;
    it.coerce(&px, &Value::int_seq(f))
}

// ----- IntegerRelation and MinimalPolynomial -------------------------------------

/// `IntegerRelation(A[, H] : Delta)`: integers `x_i` of size about `H` or
/// less with `x_1 A_1 + ... + x_d A_d` small, found by LLL, and the size of
/// that sum. `H` defaults to `Ceiling(10^(p/d))` for the precision `p` of
/// `A`. For `A` all zero Magma returns the polynomial 1 without `H` (with
/// the value 1 of MinimalPolynomial's failure here; 2.22 returns only one
/// value), and fails with it.
fn integer_relation(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Seq(s) = &a.args[0] else { unreachable!("a sequence") };
    let q = seq_nums(s);
    if q.z.is_empty() {
        return Err(require(RuntimeError::runtime("A must have at least one element")));
    }
    let h = match a.args.get(1) {
        Some(Value::Int(h)) if h.sign() <= 0 => return Err(require(RuntimeError::runtime("H must be at least 1"))),
        Some(Value::Int(h)) => h.clone(),
        _ => default_bound(q.bits, q.z.len()),
    };
    if q.z.iter().all(Complex::is_zero) {
        if a.args.len() > 1 {
            return Err(hidden_inner(RuntimeError::runtime("Bad argument types").in_context("[]")));
        }
        return Ok(vals![zx_value(it, vec![Integer::one()])?, Value::real(Real::from_i64(1, default_bits()))]);
    }
    let delta = lovasz(a.param("Delta").expect("Delta")).map_err(hidden)?;
    let x = relation(&q, &q.z, &h, delta);
    let r = residual(&q.z, &x);
    Ok(vals![Value::int_seq(x), Value::real(r)])
}

/// `MinimalPolynomial(a, d[, H] : Delta, ExactDegree, Squarefree)`: an
/// irreducible integer polynomial of degree at most `d` with coefficients
/// of size about `H` that nearly vanishes at `a`, and `|f(a)|`. Magma finds
/// the integer relation among `1, a, ..., a^k` for each `k <= d` (with `H`
/// defaulting to `Ceiling(10^(p/(d+1)))`) and keeps the first irreducible
/// one with the smallest value at `a`, or 1 with the value 1 in the default
/// real field if none is irreducible. With ExactDegree it takes the one of
/// `k = d`, the product of its distinct irreducible factors if Squarefree.
fn minimal_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let q = arg_num(&a.args[0]);
    let x = &q.z[0];
    let d = a.int(1)?.clone();
    if d.sign() <= 0 {
        return Err(require(RuntimeError::runtime("The degree must be at least 1")));
    }
    let d = d.to_u64().filter(|&d| d < 1 << 20).ok_or_else(|| RuntimeError::runtime("Degree too large"))? as usize;
    let logical = || hidden(RuntimeError::statement("if", "Logical expected"));
    let exact = match a.param("ExactDegree") {
        Some(Value::Bool(b)) => *b,
        _ => return Err(logical()),
    };
    let h = match a.args.get(2) {
        Some(Value::Int(h)) if h.sign() <= 0 => return Err(hidden(RuntimeError::runtime("H must be at least 1").in_context("IntegerRelation"))),
        Some(Value::Int(h)) => h.clone(),
        _ => default_bound(q.bits, d + 1),
    };
    let sqfree = a.param("Squarefree").cloned().unwrap_or(Value::Bool(true));
    let powers: Vec<Complex> = (0..=d).map(|i| q.pow(x, i)).collect();
    let delta_value = a.param("Delta").cloned().expect("Delta");
    let delta = match lovasz(&delta_value) {
        Ok(v) => v,
        Err(e) => {
            // The frames of the package function algdep and of the first
            // IntegerRelation it calls.
            let k = if exact { d } else { 1 };
            let mut e = hidden(e);
            let a_seq = q.seq(it, &powers[..=k]);
            let args = vec![("A".to_string(), it.frame_arg(&a_seq)), ("H".to_string(), it.frame_arg(&Value::Int(h.clone())))];
            e.trace.push(TraceFrame { name: Sym::new("IntegerRelation"), span: None, args });
            let vals = [a.args[0].clone(), Value::int(d as i64), Value::Int(h.clone()), delta_value, Value::Bool(exact), sqfree];
            let args = ["a", "d", "H", "DELTA", "exact", "sqfree"].iter().zip(vals.iter()).map(|(n, v)| (n.to_string(), it.frame_arg(v))).collect();
            e.trace.push(TraceFrame { name: Sym::new("algdep"), span: None, args });
            return Err(e);
        }
    };
    if exact {
        let mut f = relation(&q, &powers, &h, delta);
        match sqfree {
            Value::Bool(true) => {
                let fac = fu::factor(&zx_elem(&f)).map_err(|_| RuntimeError::runtime("Factorization failed"))?;
                if fac.factors.is_empty() {
                    return Err(hidden(RuntimeError::runtime("Illegal null sequence").in_context("&*")));
                }
                let one = zx_elem(&[Integer::one()]);
                let p = fac.factors.iter().try_fold(one, |p, (g, _)| p.mul(g)).map_err(|_| RuntimeError::runtime("Factorization failed"))?;
                f = coeffs(&p);
            }
            Value::Bool(false) => {}
            _ => return Err(logical()),
        }
        let f = normalized(f);
        let g = eval_abs(&q, &f, x);
        return Ok(vals![zx_value(it, f)?, Value::real(g)]);
    }
    let mut best: Option<(Vec<Integer>, Real)> = None;
    let one = Real::from_i64(1, default_bits());
    for k in 1..=d {
        let f = relation(&q, &powers[..=k], &h, delta);
        let g = eval_abs(&q, &f, x);
        if g.cmp_magma(best.as_ref().map_or(&one, |b| &b.1)).is_lt() && fu::is_irreducible(&zx_elem(&f)).unwrap_or(false) {
            best = Some((f, g));
        }
    }
    let (f, g) = best.unwrap_or_else(|| (vec![Integer::one()], one));
    Ok(vals![zx_value(it, normalized(f))?, Value::real(g)])
}

// ----- LinearRelation and PowerRelation ------------------------------------------

/// PARI's lindep with the given number of decimal digits: the first row of
/// the lattice spanned by the rows `[I | trunc(2^b re q) | trunc(2^b im q)]`,
/// `b = floor(digits log2(10))`, reduced by LLL (δ = 0.99, η = 0.51), the
/// imaginary parts only if one is non-zero. `None` for two numbers that are
/// independent over the reals, however nearly dependent.
fn lindep(z: &[Complex], digits: u64) -> Option<Vec<Integer>> {
    let d = z.len();
    let b = (digits as f64 * std::f64::consts::LOG2_10).floor() as i64;
    if d == 2 && !Real::fmma(&z[0].re, &z[1].im, &z[1].re, &z[0].im, true).is_zero() {
        return None;
    }
    let im = z.iter().any(|x| !x.im.is_zero());
    let mut rows: Vec<Vec<Integer>> = (0..d)
        .map(|i| {
            let mut r: Vec<Integer> = (0..d).map(|j| Integer::from_i64((i == j) as i64)).collect();
            r.push(z[i].re.mul_2exp(b).trunc());
            if im {
                r.push(z[i].im.mul_2exp(b).trunc());
            }
            r
        })
        .collect();
    lll_l2(&mut rows, 0.99, 0.51);
    Some(rows.swap_remove(0).into_iter().take(d).collect())
}

/// The Al parameter of LinearRelation and PowerRelation: "LLL" or "Hastad",
/// which Magma no longer distinguishes.
fn check_al(it: &Interp, a: &CallArgs) -> RResult<()> {
    match a.param("Al") {
        Some(Value::Str(s)) if !["LLL", "Hastad"].contains(&s.as_str()) => Err(bad_param_value(it, a, "Al", s.as_str())),
        None | Some(Value::Str(_)) => Ok(()),
        Some(_) => {
            let types: Vec<String> = a.args.iter().map(|v| it.type_name_ext(v)).collect();
            Err(RuntimeError::runtime(format!("Bad type for parameter 'Al'\nArgument types given: {}", types.join(", "))))
        }
    }
}

/// `LinearRelation(q : Al)` (deprecated): a small integer relation among
/// the complex numbers `q`, by PARI's lindep to half the precision of `q`,
/// with its first non-zero entry positive.
fn linear_relation(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    check_al(it, a)?;
    let Value::Seq(s) = &a.args[0] else { unreachable!("a sequence") };
    let q = seq_nums(s);
    if q.z.len() <= 1 {
        return Err(RuntimeError::runtime(format!("Sequence must have length > 1.  Illegal length {}", q.z.len())));
    }
    let digits = digits_for_bits(q.bits).div_ceil(2);
    let mut x = lindep(&q.z, digits).ok_or_else(|| RuntimeError::runtime("No linear dependency exists"))?;
    if x.iter().find(|c| !c.is_zero()).is_some_and(|c| c.sign() < 0) {
        x.iter_mut().for_each(Integer::neg_assign);
    }
    one(Value::int_seq(x))
}

/// `PowerRelation(r, k : Al, Precision)` (deprecated): an integer
/// polynomial of degree at most `k` with `r` as an approximate root, by
/// PARI's algdep: lindep among `1, r, ..., r^k` (successive products),
/// without factors x. Magma passes PARI the precision of complex `r`
/// halved, and for real `r` the decimal digits of its precision in 32-bit
/// words less two words: none below 20 digits, where the integer parts of
/// the powers give 1. An integer or rational `r` is taken in the default
/// real field. The Precision parameter, which 2.22 lacks, is taken as the
/// digits.
fn power_relation(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    if let Some(q) = match &a.args[0] {
        Value::Int(n) => Some(calyx_flint::Rational::from_integer(n)),
        Value::Rat(q) => Some((**q).clone()),
        _ => None,
    } {
        a.args[0] = Value::real(Real::from_rational(&q, default_bits()));
    }
    check_al(it, a)?;
    let precision = match a.param("Precision") {
        None | Some(Value::Undef) => None,
        Some(Value::Int(n)) if n.sign() > 0 => Some(n.to_u64().filter(|&n| n < 1 << 32).ok_or_else(|| RuntimeError::runtime("Precision is too large"))?),
        Some(Value::Int(_)) => return Err(RuntimeError::runtime("Bad value for parameter 'Precision'")),
        Some(_) => {
            let types: Vec<String> = a.args.iter().map(|v| it.type_name_ext(v)).collect();
            return Err(RuntimeError::runtime(format!("Bad type for parameter 'Precision'\nArgument types given: {}", types.join(", "))));
        }
    };
    let k = a.int(1)?;
    if k.sign() <= 0 {
        return Err(arg_ge(2, k, 1));
    }
    let k = k.to_u64().filter(|&k| k < 1 << 16).ok_or_else(|| RuntimeError::runtime("Degree too large"))? as usize;
    let q = arg_num(&a.args[0]);
    let r = &q.z[0];
    if r.is_zero() {
        return one(zx_value(it, Vec::new())?);
    }
    let digits = precision.unwrap_or_else(|| {
        if q.complex {
            digits_for_bits(q.bits).div_ceil(2)
        } else {
            let words = q.bits.div_ceil(32);
            (32.0 * words.saturating_sub(2) as f64 * std::f64::consts::LOG10_2).floor() as u64
        }
    });
    let mut pw = vec![Complex::from_real(Real::from_i64(1, q.bits))];
    for i in 0..k {
        let p = pw[i].mul(r);
        pw.push(p);
    }
    let mut x = lindep(&pw, digits).ok_or_else(|| RuntimeError::runtime("No algebraic dependency exists"))?;
    let v = x.iter().take_while(|c| c.is_zero()).count().min(x.len() - 1);
    x.drain(..v);
    one(zx_value(it, normalized(x))?)
}

pub fn register(it: &mut Interp) {
    let delta = || ("Delta", Value::real(Real::from_f64(0.75, default_bits())));
    for t in ["FldReElt", "FldComElt"] {
        let doc = "Integers x with |x[i]| about H or less and |&+[x[i]*A[i]]| small (found by LLL), and that sum's size.";
        it.def_params("IntegerRelation", &format!("A::[{t}] -> [RngIntElt], FldReElt"), &[delta()], doc, integer_relation).package = true;
        it.def_params("IntegerRelation", &format!("A::[{t}], H::RngIntElt -> [RngIntElt], FldReElt"), &[delta()], doc, integer_relation).package = true;
        let params = [delta(), ("ExactDegree", Value::Bool(false)), ("Squarefree", Value::Bool(true))];
        let doc = "An irreducible integer polynomial of degree at most d, with coefficients about H or less, of a number close to a (found by LLL), and its value's size at a.";
        it.def_params("MinimalPolynomial", &format!("a::{t}, d::RngIntElt -> RngUPolElt, FldReElt"), &params, doc, minimal_polynomial).package = true;
        it.def_params("MinimalPolynomial", &format!("a::{t}, d::RngIntElt, H::RngIntElt -> RngUPolElt, FldReElt"), &params, doc, minimal_polynomial).package = true;
        let params = [("Al", Value::str("LLL")), ("Precision", Value::Undef)];
        it.def_params("PowerRelation", &format!("r::{t}, k::RngIntElt -> RngUPolElt"), &params, "(Deprecated) An integer polynomial of degree at most k with r as an approximate root (PARI's algdep).", power_relation);
    }
    for t in ["RngIntElt", "FldRatElt"] {
        let params = [("Al", Value::str("LLL")), ("Precision", Value::Undef)];
        it.def_params("PowerRelation", &format!("r::{t}, k::RngIntElt -> RngUPolElt"), &params, "(Deprecated) PowerRelation of r in the default real field.", power_relation);
    }
    let doc = "(Deprecated) A small integer relation among the entries of q (PARI's lindep).";
    it.def_params("LinearRelation", "q::[FldComElt] -> [RngIntElt]", &[("Al", Value::str("LLL"))], doc, linear_relation);
}

#[cfg(test)]
mod tests {
    use super::*;

    const BITS: u64 = 67; // RealField(20)

    fn real(n: i64) -> Complex {
        Complex::from_real(Real::from_i64(n, BITS))
    }

    fn sqrt(n: i64) -> Complex {
        Complex::from_real(Real::from_i64(n, BITS).sqrt())
    }

    fn nums(z: Vec<Complex>) -> Nums {
        Nums { z, complex: false, bits: BITS }
    }

    fn ints(v: &[i64]) -> Vec<Integer> {
        v.iter().map(|&x| Integer::from_i64(x)).collect()
    }

    #[test]
    fn default_bounds() {
        let b = |k| default_bound(BITS, k).to_i64().unwrap();
        assert_eq!((b(2), b(3), b(4)), (10_000_000_000, 4641589, 100000));
        assert_eq!(default_bound(BITS, 1), Integer::from_i64(10).pow(20));
    }

    #[test]
    fn relations_as_magma_finds_them() {
        // IntegerRelation([Sqrt(2), 1], H) in RealField(20), from Magma.
        let q = nums(vec![sqrt(2), real(1)]);
        for (h, x) in [(1, [0, 1]), (3, [-1, 1]), (22, [-5, 7]), (135, [-70, 99]), (1000, [-408, 577]), (10_000_000_000, [-3166815962, 4478554083])] {
            assert_eq!(relation(&q, &q.z, &Integer::from_i64(h), 0.76), ints(&x), "H = {h}");
        }
        // Sqrt(2) + Sqrt(3) is a root of x^4 - 10x^2 + 1.
        let r = sqrt(2).add(&sqrt(3));
        let q = nums((0..=4).map(|k| q_pow(&r, k)).collect());
        assert_eq!(relation(&q, &q.z, &Integer::from_i64(100), 0.76), ints(&[1, 0, -10, 0, 1]));
    }

    fn q_pow(x: &Complex, k: usize) -> Complex {
        nums(Vec::new()).pow(x, k)
    }

    #[test]
    fn measures_of_fit() {
        // The terms are summed in halves; the polynomial is evaluated by
        // powers across its zero coefficients (95/2^67, where Horner's rule
        // step by step gives 96/2^67). The values are Magma's.
        let r = sqrt(2).add(&sqrt(3));
        let q = nums((0..=4).map(|k| q_pow(&r, k)).collect());
        let y = residual(&q.z, &ints(&[-6, 0, -3, -2, 1]));
        assert_eq!(y.format(20), "0.0032434905166110182019");
        // [r^3, r^2, r, 1] with r = 3 Pi/7, from the first term or the last
        // gives 0.0014454164706141991808.
        let t = Complex::from_real(Real::constant(calyx_flint::mpfr::mpfr_const_pi, BITS).mul(&Real::from_i64(3, BITS)).div(&Real::from_i64(7, BITS)).unwrap());
        let z: Vec<Complex> = (0..4).rev().map(|k| q_pow(&t, k)).collect();
        assert_eq!(residual(&z, &ints(&[-2, -1, 2, 4])).format(20), "0.0014454164706141991266");
        let g = eval_abs(&q, &ints(&[1, 0, -10, 0, 1]), &r);
        assert_eq!(g, Real::from_integer_2exp(&Integer::from_i64(95), -67, BITS));
        assert!(eval_abs(&q, &ints(&[0, 1]), &real(0)).is_zero());
    }

    #[test]
    fn lindep_to_half_the_precision() {
        // LinearRelation([Sqrt(2), 1]) in ComplexField(20), before its sign
        // is fixed: 10 digits.
        let x = lindep(&[sqrt(2), real(1)], 10).unwrap();
        assert_eq!(x, ints(&[-33461, 47321]));
        let i = Complex::new(Real::zero(BITS), Real::from_i64(1, BITS));
        assert!(lindep(&[i, real(1)], 10).is_none());
    }
}
