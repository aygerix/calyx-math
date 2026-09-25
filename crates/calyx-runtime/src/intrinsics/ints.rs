//! Integer and rational number intrinsics (FLINT-backed).

use std::rc::Rc;

use calyx_flint::{Integer, Rational};

use super::{boolv, intv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

fn int_arg(a: &CallArgs, i: usize) -> RResult<Integer> {
    match &a.args[i] {
        Value::Int(n) => Ok(n.clone()),
        Value::Rat(q) if q.is_integral() => Ok(q.numerator()),
        other => Err(RuntimeError::runtime(format!("Argument {} must be an integer (got {})", i + 1, crate::value_kind(other)))),
    }
}

fn rat_arg(a: &CallArgs, i: usize) -> RResult<Rational> {
    match &a.args[i] {
        Value::Int(n) => Ok(Rational::from_integer(n)),
        Value::Rat(q) => Ok((**q).clone()),
        other => Err(RuntimeError::runtime(format!("Argument {} must be rational (got {})", i + 1, crate::value_kind(other)))),
    }
}

fn int_seq(v: Vec<Integer>) -> Value {
    Value::int_seq(v)
}

fn int_pair_parent() -> Value {
    Value::structure(StructKind::Cartesian(vec![Value::integers(), Value::integers()]))
}

/// A factorization as a sequence of `<p, e>` tuples.
pub fn factorization_value(factors: &[(Integer, u64)]) -> Value {
    let parent = int_pair_parent();
    let elems = factors
        .iter()
        .map(|(p, e)| Value::Tuple(Rc::new(Tuple { elems: vec![Value::Int(p.clone()), Value::Int(Integer::from_u64(*e))], parent: Some(parent.clone()) })))
        .collect();
    Value::seq(Some(parent), elems)
}

fn abs(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    one(match &a.args[0] {
        Value::Int(n) => Value::Int(n.abs()),
        Value::Rat(q) => Value::rat(q.abs()),
        Value::Real(r) => Value::Real(Rc::new(RealV { x: r.x.abs(), digits: r.digits, fixed: r.fixed })),
        _ => unreachable!(),
    })
}

fn sign(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let s = match &a.args[0] {
        Value::Int(n) => n.sign(),
        Value::Rat(q) => q.sign(),
        Value::Real(r) => r.x.sign(),
        _ => unreachable!(),
    };
    one(Value::int(s as i64))
}

fn is_zero(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    boolv(match &a.args[0] {
        Value::Int(n) => n.is_zero(),
        Value::Rat(q) => q.is_zero(),
        Value::Real(r) => r.x.is_zero(),
        _ => false,
    })
}

fn is_one(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    boolv(match &a.args[0] {
        Value::Int(n) => n.is_one(),
        Value::Rat(q) => q.is_one(),
        _ => false,
    })
}

fn is_minus_one(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    boolv(match &a.args[0] {
        Value::Int(n) => n.to_i64() == Some(-1),
        Value::Rat(q) => q.is_integral() && q.numerator().to_i64() == Some(-1),
        _ => false,
    })
}

fn is_even(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    boolv(a.int(0)?.is_even())
}

fn is_odd(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    boolv(a.int(0)?.is_odd())
}

fn is_prime(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?;
    let proof = a.param("Proof").map(|v| matches!(v, Value::Bool(true))).unwrap_or(true);
    // Negatives of primes are prime elements of the integers too.
    let n = n.abs();
    boolv(if proof { n.is_prime() } else { n.is_probable_prime() })
}

fn is_probable_prime(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?;
    boolv(n.sign() > 0 && n.is_probable_prime())
}

fn next_prime(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    intv(a.int(0)?.next_prime())
}

fn previous_prime(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    match a.int(0)?.previous_prime() {
        Some(p) => intv(p),
        None => Err(RuntimeError::runtime("There is no prime smaller than the argument")),
    }
}

fn nth_prime(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.usize(0)?;
    if n == 0 {
        return Err(RuntimeError::runtime("Argument must be positive"));
    }
    let mut p = Integer::from_i64(2);
    for _ in 1..n {
        p = p.next_prime();
    }
    intv(p)
}

fn factorization(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?;
    let Some(f) = n.factor() else {
        return Err(RuntimeError::runtime("Cannot factorize zero"));
    };
    // The sign is an optional second result, not shown when printing.
    if a.nresults >= 2 {
        return Ok(vec![factorization_value(&f.factors), Value::int(f.sign as i64)]);
    }
    one(factorization_value(&f.factors))
}

fn prime_divisors(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?;
    let Some(f) = n.factor() else {
        return Err(RuntimeError::runtime("Argument must be non-zero"));
    };
    one(int_seq(f.factors.into_iter().map(|(p, _)| p).collect()))
}

fn divisor_list(n: &Integer) -> RResult<Vec<Integer>> {
    let Some(f) = n.factor() else {
        return Err(RuntimeError::runtime("Argument must be non-zero"));
    };
    let mut divs = vec![Integer::one()];
    for (p, e) in &f.factors {
        let mut next = Vec::with_capacity(divs.len() * (*e as usize + 1));
        for d in &divs {
            let mut pk = Integer::one();
            for _ in 0..=*e {
                next.push(d * &pk);
                pk = &pk * p;
            }
        }
        divs = next;
    }
    divs.sort();
    Ok(divs)
}

fn divisors(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    one(int_seq(divisor_list(a.int(0)?)?))
}

fn number_of_divisors(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    intv(a.int(0)?.abs().divisor_sigma(0))
}

fn sum_of_divisors(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    intv(a.int(0)?.abs().divisor_sigma(1))
}

fn divisor_sigma(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let k = a.usize(0)? as u64;
    intv(a.int(1)?.abs().divisor_sigma(k))
}

fn euler_phi(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?;
    if n.sign() <= 0 {
        return Err(RuntimeError::runtime("Argument must be positive"));
    }
    intv(n.euler_phi())
}

fn moebius_mu(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?;
    if n.sign() <= 0 {
        return Err(RuntimeError::runtime("Argument must be positive"));
    }
    one(Value::int(n.moebius_mu() as i64))
}

fn gcd(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (x, y) = (rat_arg(a, 0)?, rat_arg(a, 1)?);
    if x.is_integral() && y.is_integral() {
        return intv(x.numerator().gcd(&y.numerator()));
    }
    // gcd of rationals: gcd of numerators over lcm of denominators.
    let n = x.numerator().gcd(&y.numerator());
    let d = x.denominator().lcm(&y.denominator());
    one(Value::rat(Rational::new(&n, &d).unwrap()))
}

fn gcd_seq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let s = a.seq(0)?;
    let mut g = Integer::zero();
    for v in &s.elems {
        match v {
            Value::Int(n) => g = g.gcd(n),
            _ => return Err(RuntimeError::runtime("Sequence must contain integers")),
        }
    }
    intv(g)
}

fn lcm(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    intv(int_arg(a, 0)?.lcm(&int_arg(a, 1)?))
}

fn lcm_seq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let s = a.seq(0)?;
    let mut l = Integer::one();
    for v in &s.elems {
        match v {
            Value::Int(n) => l = l.lcm(n),
            _ => return Err(RuntimeError::runtime("Sequence must contain integers")),
        }
    }
    intv(l)
}

fn xgcd(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (g, s, t) = a.int(0)?.xgcd(a.int(1)?);
    Ok(vec![Value::Int(g), Value::Int(s), Value::Int(t)])
}

fn quotrem(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (q, r) = a.int(0)?.div_rem_euclid(a.int(1)?).ok_or_else(|| RuntimeError::runtime("Division by zero"))?;
    Ok(vec![Value::Int(q), Value::Int(r)])
}

fn modexp(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let m = a.int(2)?;
    if m.sign() <= 0 {
        return Err(RuntimeError::runtime("Modulus must be positive"));
    }
    match a.int(0)?.powm(a.int(1)?, m) {
        Some(r) => intv(r),
        None => Err(RuntimeError::runtime("Base is not invertible modulo the modulus")),
    }
}

fn modinv(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    match a.int(0)?.invmod(a.int(1)?) {
        Some(r) => intv(r),
        None => Err(RuntimeError::runtime("Argument is not invertible modulo the modulus")),
    }
}

fn isqrt(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    match a.int(0)?.isqrt() {
        Some(r) => intv(r),
        None => Err(RuntimeError::runtime("Argument must be non-negative")),
    }
}

fn iroot(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let k = a.usize(1)? as u64;
    match a.int(0)?.root(k) {
        Some((r, _)) => intv(r),
        None => Err(RuntimeError::runtime("No real root exists")),
    }
}

fn is_square(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    match &a.args[0] {
        Value::Int(n) => {
            if n.sign() >= 0 && n.is_square() {
                Ok(vec![Value::Bool(true), Value::Int(n.isqrt().unwrap())])
            } else {
                Ok(vec![Value::Bool(false), Value::Undef])
            }
        }
        Value::Rat(q) => {
            let (n, d) = (q.numerator(), q.denominator());
            if n.sign() >= 0 && n.is_square() && d.is_square() {
                Ok(vec![Value::Bool(true), Value::rat(Rational::new(&n.isqrt().unwrap(), &d.isqrt().unwrap()).unwrap())])
            } else {
                Ok(vec![Value::Bool(false), Value::Undef])
            }
        }
        _ => unreachable!(),
    }
}

fn is_power(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?;
    if a.args.len() == 2 {
        let k = a.usize(1)? as u64;
        return match n.root(k) {
            Some((r, true)) => Ok(vec![Value::Bool(true), Value::Int(r)]),
            _ => Ok(vec![Value::Bool(false), Value::Undef]),
        };
    }
    match n.perfect_power() {
        Some((b, e)) => Ok(vec![Value::Bool(true), Value::Int(b), Value::Int(Integer::from_u64(e))]),
        None => Ok(vec![Value::Bool(false), Value::Undef, Value::Undef]),
    }
}

fn is_prime_power(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?;
    if n.sign() <= 0 || n.is_one() {
        return Ok(vec![Value::Bool(false), Value::Undef, Value::Undef]);
    }
    let f = n.factor().unwrap();
    if f.factors.len() == 1 {
        let (p, e) = &f.factors[0];
        return Ok(vec![Value::Bool(true), Value::Int(p.clone()), Value::Int(Integer::from_u64(*e))]);
    }
    Ok(vec![Value::Bool(false), Value::Undef, Value::Undef])
}

fn factorial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?;
    if n.sign() < 0 {
        return Err(RuntimeError::runtime("Argument must be non-negative"));
    }
    let n = n.to_u64().filter(|&n| n < 100_000_000).ok_or_else(|| RuntimeError::runtime("Argument is too large"))?;
    intv(Integer::factorial(n))
}

fn binomial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (n, k) = (a.int(0)?.clone(), a.int(1)?.clone());
    if k.sign() < 0 {
        return intv(Integer::zero());
    }
    let k = k.to_u64().ok_or_else(|| RuntimeError::runtime("Argument 2 is too large"))?;
    if let Some(nn) = n.to_u64() {
        if n.sign() >= 0 {
            return intv(if k > nn { Integer::zero() } else { Integer::binomial_u64(nn, k) });
        }
    }
    // General n: product formula.
    let mut num = Integer::one();
    for i in 0..k {
        num = &num * &(&n - &Integer::from_u64(i));
    }
    intv(num.divexact(&Integer::factorial(k)))
}

fn fibonacci(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.i64(0)?;
    if n >= 0 {
        return intv(Integer::fibonacci(n as u64));
    }
    let f = Integer::fibonacci((-n) as u64);
    intv(if n % 2 == 0 { -f } else { f })
}

fn lucas(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.usize(0)? as u64;
    if n == 0 {
        return intv(Integer::from_i64(2));
    }
    intv(&Integer::fibonacci(n - 1) + &Integer::fibonacci(n + 1))
}

fn numerator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    intv(rat_arg(a, 0)?.numerator())
}

fn denominator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    intv(rat_arg(a, 0)?.denominator())
}

fn floor(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    intv(match &a.args[0] {
        Value::Int(n) => n.clone(),
        Value::Rat(q) => q.floor(),
        Value::Real(r) => r.x.floor(),
        _ => unreachable!(),
    })
}

fn ceiling(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    intv(match &a.args[0] {
        Value::Int(n) => n.clone(),
        Value::Rat(q) => q.ceil(),
        Value::Real(r) => r.x.ceil(),
        _ => unreachable!(),
    })
}

fn round(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    intv(match &a.args[0] {
        Value::Int(n) => n.clone(),
        Value::Rat(q) => q.round(),
        Value::Real(r) => r.x.round(),
        _ => unreachable!(),
    })
}

fn truncate(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    intv(match &a.args[0] {
        Value::Int(n) => n.clone(),
        Value::Rat(q) => q.trunc(),
        Value::Real(r) => r.x.trunc(),
        _ => unreachable!(),
    })
}

fn intseq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?.clone();
    let b = a.int(1)?.clone();
    if n.sign() < 0 || b.to_i64().is_none_or(|b| b < 2) {
        return Err(RuntimeError::runtime("Arguments must be a non-negative integer and a base of at least 2"));
    }
    let mut digits = Vec::new();
    let mut m = n;
    while !m.is_zero() {
        let (q, r) = m.div_rem_euclid(&b).unwrap();
        digits.push(r);
        m = q;
    }
    if a.args.len() > 2 {
        let k = a.usize(2)?;
        if digits.len() > k {
            return Err(RuntimeError::runtime("The number has more digits than requested"));
        }
        digits.resize(k, Integer::zero());
    }
    one(int_seq(digits))
}

fn seqint(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let s = a.seq(0)?.clone();
    let b = if a.args.len() > 1 { a.int(1)?.clone() } else { Integer::from_i64(2) };
    let mut n = Integer::zero();
    for v in s.elems.iter().rev() {
        let Value::Int(d) = v else {
            return Err(RuntimeError::runtime("Sequence must contain integers"));
        };
        n = &(&n * &b) + d;
    }
    intv(n)
}

/// Maximum and Minimum of two values are not defined on ring elements, even
/// where `lt` is.
fn check_max_args(it: &Interp, x: &Value, y: &Value) -> RResult<()> {
    if matches!(x, Value::Elt(_)) || matches!(y, Value::Elt(_)) {
        return Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}, {}", it.type_name_ext(x), it.type_name_ext(y))));
    }
    Ok(())
}

fn max2(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (x, y) = (a.args[0].clone(), a.args[1].clone());
    check_max_args(it, &x, &y)?;
    let o = it.compare_for_sort(&x, &y)?;
    let r = if o == std::cmp::Ordering::Less { y.clone() } else { x.clone() };
    one(in_common_structure(it, &x, &y, r)?)
}

/// `r` (one of x and y) in the structure containing both, as Maximum and
/// Minimum return it (so `Max(1.5, 2)` is a real).
fn in_common_structure(it: &mut Interp, x: &Value, y: &Value, r: Value) -> RResult<Value> {
    let (px, py) = (it.parent_of(x)?, it.parent_of(y)?);
    match it.common_universe(&px, &py) {
        Some(u) => Ok(it.try_coerce(&u, &r)?.unwrap_or(r)),
        None => Ok(r),
    }
}

fn min2(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (x, y) = (a.args[0].clone(), a.args[1].clone());
    check_max_args(it, &x, &y)?;
    let o = it.compare_for_sort(&x, &y)?;
    let r = if o == std::cmp::Ordering::Greater { y.clone() } else { x.clone() };
    one(in_common_structure(it, &x, &y, r)?)
}

fn valuation(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (n, p) = (a.int(0)?, a.int(1)?);
    if n.is_zero() {
        return Err(RuntimeError::runtime("The valuation of zero is infinite"));
    }
    if p.cmp_abs(&Integer::one()) != std::cmp::Ordering::Greater {
        return Err(RuntimeError::runtime("Argument 2 must have absolute value at least 2"));
    }
    let (v, rest) = n.remove(p);
    Ok(vec![Value::Int(Integer::from_u64(v)), Value::Int(rest)])
}

fn ilog(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let b = a.int(0)?.to_u64().filter(|&b| b >= 2).ok_or_else(|| RuntimeError::runtime("Base must be at least 2"))?;
    match a.int(1)?.ilog(b) {
        Some(k) => intv(Integer::from_u64(k)),
        None => Err(RuntimeError::runtime("Argument must be positive")),
    }
}

fn ilog2(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?;
    if n.sign() <= 0 {
        return Err(RuntimeError::runtime("Argument must be positive"));
    }
    intv(Integer::from_u64(n.bits() - 1))
}

fn is_divisible_by(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (n, d) = (a.int(0)?, a.int(1)?);
    if d.is_zero() {
        return Err(RuntimeError::runtime("Division by zero"));
    }
    if n.is_divisible_by(d) { Ok(vec![Value::Bool(true), Value::Int(n.divexact(d))]) } else { Ok(vec![Value::Bool(false), Value::Undef]) }
}

fn crt(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (xs, ms) = (a.seq(0)?.clone(), a.seq(1)?.clone());
    if xs.elems.len() != ms.elems.len() {
        return Err(RuntimeError::runtime("Sequences must have the same length"));
    }
    let mut x = Integer::zero();
    let mut m = Integer::one();
    for (xv, mv) in xs.elems.iter().zip(&ms.elems) {
        let (Value::Int(xi), Value::Int(mi)) = (xv, mv) else {
            return Err(RuntimeError::runtime("Sequences must contain integers"));
        };
        let (g, s, _) = m.xgcd(mi);
        let diff = xi - &x;
        if !diff.is_divisible_by(&g) {
            return Err(RuntimeError::runtime("The congruences are inconsistent"));
        }
        let l = m.lcm(mi);
        let step = &(&m * &s) * &diff.divexact(&g);
        x = (&x + &step).div_rem_euclid(&l).unwrap().1;
        m = l;
    }
    intv(x)
}

fn is_integral(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    boolv(match &a.args[0] {
        Value::Int(_) => true,
        Value::Rat(q) => q.is_integral(),
        _ => false,
    })
}

fn legendre(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    one(Value::int(a.int(0)?.kronecker(a.int(1)?) as i64))
}

fn primes_up_to(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?.clone();
    let mut out = Vec::new();
    let mut p = Integer::from_i64(2);
    while p <= n {
        out.push(p.clone());
        p = p.next_prime();
    }
    one(int_seq(out))
}

pub fn register(it: &mut Interp) {
    for t in ["RngIntElt", "FldRatElt", "FldReElt"] {
        it.def("Abs", &format!("x::{t} -> {t}"), "The absolute value of x.", abs);
        it.def("Sign", &format!("x::{t} -> RngIntElt"), "The sign of x (-1, 0 or 1).", sign);
        it.def("IsZero", &format!("x::{t} -> BoolElt"), "Whether x is zero.", is_zero);
        it.def("Floor", &format!("x::{t} -> RngIntElt"), "The largest integer not exceeding x.", floor);
        it.def("Ceiling", &format!("x::{t} -> RngIntElt"), "The smallest integer not less than x.", ceiling);
        it.def("Round", &format!("x::{t} -> RngIntElt"), "The integer nearest to x (halves away from zero).", round);
        it.def("Truncate", &format!("x::{t} -> RngIntElt"), "The integer part of x.", truncate);
    }
    for t in ["RngIntElt", "FldRatElt"] {
        it.def("IsOne", &format!("x::{t} -> BoolElt"), "Whether x is one.", is_one);
        it.def("IsMinusOne", &format!("x::{t} -> BoolElt"), "Whether x is minus one.", is_minus_one);
        it.def("Numerator", &format!("x::{t} -> RngIntElt"), "The numerator of x.", numerator);
        it.def("Denominator", &format!("x::{t} -> RngIntElt"), "The denominator of x.", denominator);
        it.def("IsSquare", &format!("x::{t} -> BoolElt, {t}"), "Whether x is a square, and a square root.", is_square);
        it.def("IsIntegral", &format!("x::{t} -> BoolElt"), "Whether x is an integer.", is_integral);
    }
    it.def("IsEven", "n::RngIntElt -> BoolElt", "Whether n is even.", is_even);
    it.def("IsOdd", "n::RngIntElt -> BoolElt", "Whether n is odd.", is_odd);
    it.def_params("IsPrime", "n::RngIntElt -> BoolElt", &[("Proof", Value::Bool(true))], "Whether n is a prime number.", is_prime);
    it.def("IsProbablePrime", "n::RngIntElt -> BoolElt", "Whether n passes a strong probable-prime test.", is_probable_prime);
    it.def("IsProbablyPrime", "n::RngIntElt -> BoolElt", "Whether n passes a strong probable-prime test.", is_probable_prime);
    it.def_params("NextPrime", "n::RngIntElt -> RngIntElt", &[("Proof", Value::Bool(true))], "The least prime greater than n.", next_prime);
    it.def_params("PreviousPrime", "n::RngIntElt -> RngIntElt", &[("Proof", Value::Bool(true))], "The greatest prime less than n.", previous_prime);
    it.def("NthPrime", "n::RngIntElt -> RngIntElt", "The n-th prime.", nth_prime);
    it.def("PrimesUpTo", "n::RngIntElt -> [RngIntElt]", "The primes up to n.", primes_up_to);
    for name in ["Factorization", "Factorisation", "Factorisation"] {
        it.def(name, "n::RngIntElt -> SeqEnum, RngIntElt", "The prime factorization of n as a sequence of <p, e> pairs, and the sign of n.", factorization);
    }
    it.def("PrimeDivisors", "n::RngIntElt -> [RngIntElt]", "The prime divisors of n.", prime_divisors);
    it.def("PrimeFactors", "n::RngIntElt -> [RngIntElt]", "The prime divisors of n.", prime_divisors);
    it.def("Divisors", "n::RngIntElt -> [RngIntElt]", "The positive divisors of n.", divisors);
    it.def("NumberOfDivisors", "n::RngIntElt -> RngIntElt", "The number of positive divisors of n.", number_of_divisors);
    it.def("NumberOfDivisors", "n::RngIntElt -> RngIntElt", "The number of positive divisors of n.", number_of_divisors);
    it.def("SumOfDivisors", "n::RngIntElt -> RngIntElt", "The sum of the positive divisors of n.", sum_of_divisors);
    it.def("DivisorSigma", "k::RngIntElt, n::RngIntElt -> RngIntElt", "The sum of the k-th powers of the divisors of n.", divisor_sigma);
    it.def("EulerPhi", "n::RngIntElt -> RngIntElt", "Euler's totient of n.", euler_phi);
    it.def("MoebiusMu", "n::RngIntElt -> RngIntElt", "The Moebius function of n.", moebius_mu);
    for name in ["Gcd", "GCD", "GreatestCommonDivisor"] {
        it.def(name, "x::RngIntElt, y::RngIntElt -> RngIntElt", "The greatest common divisor of x and y.", gcd);
        it.def(name, "x::FldRatElt, y::FldRatElt -> FldRatElt", "The greatest common divisor of x and y.", gcd);
        it.def(name, "x::RngIntElt, y::FldRatElt -> FldRatElt", "The greatest common divisor of x and y.", gcd);
        it.def(name, "x::FldRatElt, y::RngIntElt -> FldRatElt", "The greatest common divisor of x and y.", gcd);
        it.def(name, "S::[RngIntElt] -> RngIntElt", "The greatest common divisor of the integers in S.", gcd_seq);
    }
    for name in ["Lcm", "LCM", "LeastCommonMultiple"] {
        it.def(name, "x::RngIntElt, y::RngIntElt -> RngIntElt", "The least common multiple of x and y.", lcm);
        it.def(name, "S::[RngIntElt] -> RngIntElt", "The least common multiple of the integers in S.", lcm_seq);
    }
    for name in ["Xgcd", "XGCD", "ExtendedGreatestCommonDivisor"] {
        it.def(name, "x::RngIntElt, y::RngIntElt -> RngIntElt, RngIntElt, RngIntElt", "The gcd d of x and y, with a and b such that d = a*x + b*y.", xgcd);
    }
    it.def("Quotrem", "a::RngIntElt, b::RngIntElt -> RngIntElt, RngIntElt", "The quotient and remainder of a on division by b (0 <= r < |b|).", quotrem);
    it.def("Modexp", "a::RngIntElt, e::RngIntElt, n::RngIntElt -> RngIntElt", "a^e mod n.", modexp);
    it.def("Modinv", "a::RngIntElt, n::RngIntElt -> RngIntElt", "The inverse of a modulo n.", modinv);
    it.def("InverseMod", "a::RngIntElt, n::RngIntElt -> RngIntElt", "The inverse of a modulo n.", modinv);
    it.def("Isqrt", "n::RngIntElt -> RngIntElt", "The integer part of the square root of n.", isqrt);
    it.def("Iroot", "n::RngIntElt, k::RngIntElt -> RngIntElt", "The integer part of the k-th root of n.", iroot);
    it.def("IsPower", "n::RngIntElt -> BoolElt, RngIntElt, RngIntElt", "Whether n is a perfect power b^e with e > 1, and b and e.", is_power);
    it.def("IsPower", "n::RngIntElt, k::RngIntElt -> BoolElt, RngIntElt", "Whether n is a k-th power, and a k-th root.", is_power);
    it.def("IsPrimePower", "n::RngIntElt -> BoolElt, RngIntElt, RngIntElt", "Whether n is a prime power p^k, and p and k.", is_prime_power);
    it.def("Factorial", "n::RngIntElt -> RngIntElt", "n factorial.", factorial);
    it.def("Binomial", "n::RngIntElt, k::RngIntElt -> RngIntElt", "The binomial coefficient n choose k.", binomial);
    it.def("Fibonacci", "n::RngIntElt -> RngIntElt", "The n-th Fibonacci number.", fibonacci);
    it.def("Lucas", "n::RngIntElt -> RngIntElt", "The n-th Lucas number.", lucas);
    it.def("Intseq", "n::RngIntElt, b::RngIntElt -> [RngIntElt]", "The base b digits of n, least significant first.", intseq);
    it.def("Intseq", "n::RngIntElt, b::RngIntElt, k::RngIntElt -> [RngIntElt]", "The base b digits of n padded to length k.", intseq);
    it.def("Seqint", "s::[RngIntElt] -> RngIntElt", "The integer with base 2 digits s.", seqint);
    it.def("Seqint", "s::[RngIntElt], b::RngIntElt -> RngIntElt", "The integer with base b digits s (least significant first).", seqint);
    it.def("Max", "x::., y::. -> .", "The larger of x and y.", max2);
    it.def("Min", "x::., y::. -> .", "The smaller of x and y.", min2);
    it.def("Maximum", "x::., y::. -> .", "The larger of x and y.", max2);
    it.def("Minimum", "x::., y::. -> .", "The smaller of x and y.", min2);
    it.def("Valuation", "n::RngIntElt, p::RngIntElt -> RngIntElt, RngIntElt", "The largest k with p^k dividing n, and n/p^k.", valuation);
    it.def("Ilog", "b::RngIntElt, n::RngIntElt -> RngIntElt", "The integer part of the logarithm of n to base b.", ilog);
    it.def("Ilog2", "n::RngIntElt -> RngIntElt", "The integer part of the base 2 logarithm of n.", ilog2);
    it.def("IsDivisibleBy", "n::RngIntElt, d::RngIntElt -> BoolElt, RngIntElt", "Whether d divides n, and the quotient.", is_divisible_by);
    it.def("CRT", "x::[RngIntElt], m::[RngIntElt] -> RngIntElt", "The solution of the congruences x[i] mod m[i].", crt);
    it.def("ChineseRemainderTheorem", "x::[RngIntElt], m::[RngIntElt] -> RngIntElt", "The solution of the congruences x[i] mod m[i].", crt);
    it.def("LegendreSymbol", "a::RngIntElt, p::RngIntElt -> RngIntElt", "The Legendre symbol (a/p).", legendre);
    it.def("JacobiSymbol", "a::RngIntElt, n::RngIntElt -> RngIntElt", "The Jacobi symbol (a/n).", legendre);
    it.def("KroneckerSymbol", "a::RngIntElt, n::RngIntElt -> RngIntElt", "The Kronecker symbol (a/n).", legendre);
}

// ----- modular helpers shared with residue class rings --------------------------

/// Euler's totient of a positive integer.
pub fn totient(m: &Integer) -> Integer {
    m.euler_phi()
}

/// The multiplicative order of `x` modulo `m > 1`, or 0 if `x` is not a
/// unit modulo `m`.
pub fn modorder(x: &Integer, m: &Integer) -> Integer {
    if m.is_one() {
        return Integer::one();
    }
    let x = x.div_rem_euclid(m).unwrap().1;
    if !x.gcd(m).is_one() {
        return Integer::zero();
    }
    let mut order = totient(m);
    let f = order.factor().expect("factorisation of a positive integer");
    for (p, e) in &f.factors {
        for _ in 0..*e {
            let cand = order.div_rem_euclid(p).unwrap().0;
            if x.powm(&cand, m).is_some_and(|r| r.is_one()) {
                order = cand;
            } else {
                break;
            }
        }
    }
    order
}

/// The least primitive root modulo `m`, if the unit group is cyclic.
pub fn primitive_root(m: &Integer) -> Option<Integer> {
    if m.sign() <= 0 {
        return None;
    }
    if m.is_one() {
        return Some(Integer::zero());
    }
    let two = Integer::from_i64(2);
    if *m == two {
        return Some(Integer::one());
    }
    if *m == Integer::from_i64(4) {
        return Some(Integer::from_i64(3));
    }
    // m must be p^k or 2p^k for an odd prime p.
    let odd = if m.div_rem_euclid(&two).unwrap().1.is_zero() { m.div_rem_euclid(&two).unwrap().0 } else { m.clone() };
    let f = odd.factor()?;
    if f.factors.len() != 1 || f.factors[0].0 == two {
        return None;
    }
    let phi = totient(m);
    let primes: Vec<Integer> = phi.factor()?.factors.into_iter().map(|(p, _)| p).collect();
    let mut g = two.clone();
    while &g < m {
        if g.gcd(m).is_one() && primes.iter().all(|p| !g.powm(&phi.div_rem_euclid(p).unwrap().0, m).is_some_and(|r| r.is_one())) {
            return Some(g);
        }
        g = &g + &Integer::one();
    }
    None
}
