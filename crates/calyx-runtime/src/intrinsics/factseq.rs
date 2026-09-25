//! Factorization sequences (`RngIntEltFact`): sequences of `<p, k>` pairs
//! of increasing primes and positive exponents that stand for the integer
//! prod p^k, with their own arithmetic, and the divisor functions and
//! predicates that accept them in place of the integer.

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_syntax::ast::BinOp;

use super::{arg_ge, arg_not, boolv, intv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

/// Prime-exponent pairs, increasing in the prime.
pub type Fact = Vec<(Integer, u64)>;

fn pair_parent() -> Value {
    Value::structure(StructKind::Cartesian(vec![Value::integers(), Value::integers()]))
}

fn pairs_value(factors: &[(Integer, u64)], fact: bool) -> Value {
    let parent = pair_parent();
    let elems = factors
        .iter()
        .map(|(p, e)| Value::Tuple(Rc::new(Tuple { elems: vec![Value::Int(p.clone()), Value::Int(Integer::from_u64(*e))], parent: Some(parent.clone()) })))
        .collect();
    let mut s = SeqEnum::new(Some(parent), elems);
    s.fact = fact;
    Value::Seq(Rc::new(s))
}

/// A factorization sequence.
pub fn fact_value(factors: &[(Integer, u64)]) -> Value {
    pairs_value(factors, true)
}

/// A plain sequence of `<a, k>` pairs (not a factorization sequence).
pub fn pair_seq_value(factors: &[(Integer, u64)]) -> Value {
    pairs_value(factors, false)
}

pub fn is_fact(v: &Value) -> bool {
    matches!(v, Value::Seq(s) if s.fact)
}

/// The pairs of a sequence of `<a, k>` tuples of integers (a factorization
/// sequence or a plain sequence of tuples). Exponents must be non-negative.
pub fn pairs_of(v: &Value) -> Option<Vec<(Integer, Integer)>> {
    let Value::Seq(s) = v else { return None };
    let mut out = Vec::with_capacity(s.elems.len());
    for e in &s.elems {
        let Value::Tuple(t) = e else { return None };
        match t.elems.as_slice() {
            [Value::Int(p), Value::Int(k)] => out.push((p.clone(), k.clone())),
            _ => return None,
        }
    }
    Some(out)
}

/// The factorization held by a sequence of pairs, pair by pair (a
/// factorization sequence changed by assignment keeps its order and any
/// repeated primes, as in Magma).
pub fn fact_of(v: &Value) -> Fact {
    pairs_of(v).unwrap_or_default().into_iter().filter_map(|(p, k)| Some((p, k.to_u64()?))).collect()
}

/// The integer a factorization stands for.
pub fn fact_int(f: &[(Integer, u64)]) -> Integer {
    let mut n = Integer::one();
    for (p, k) in f {
        n = &n * &p.pow(*k);
    }
    n
}

/// The factorization of a non-zero integer (of its absolute value).
pub fn factor(n: &Integer) -> Fact {
    n.factor().map(|f| f.factors).unwrap_or_default()
}

/// `a * b` as factorizations: the two sequences are merged in order,
/// adding exponents where their primes meet.
pub fn fact_mul(a: &Fact, b: &Fact) -> Fact {
    let (mut i, mut j) = (0, 0);
    let mut out = Fact::with_capacity(a.len() + b.len());
    while i < a.len() && j < b.len() {
        match a[i].0.cmp(&b[j].0) {
            std::cmp::Ordering::Less => {
                out.push(a[i].clone());
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                out.push(b[j].clone());
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                out.push((a[i].0.clone(), a[i].1 + b[j].1));
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}

/// Combine exponents prime by prime (`max` for lcm, `min` for gcd).
fn fact_merge(a: &Fact, b: &Fact, pick: fn(u64, u64) -> u64) -> Fact {
    let mut primes: Vec<Integer> = a.iter().chain(b).map(|(p, _)| p.clone()).collect();
    primes.sort();
    primes.dedup();
    let exp = |f: &Fact, p: &Integer| f.iter().find(|(q, _)| q == p).map(|(_, k)| *k).unwrap_or(0);
    primes
        .into_iter()
        .filter_map(|p| {
            let k = pick(exp(a, &p), exp(b, &p));
            (k > 0).then_some((p, k))
        })
        .collect()
}

impl Interp {
    /// Arithmetic on factorization sequences.
    pub fn fact_binop(&mut self, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
        if op == BinOp::Pow && is_fact(a) {
            let Value::Int(k) = b else { return Ok(None) };
            if k.sign() < 0 {
                return Err(RuntimeError::runtime("Exponent must be non-negative").in_context("^"));
            }
            let k = k.to_u64().ok_or_else(|| RuntimeError::runtime("Exponent is too large").in_context("^"))?;
            let f: Fact = if k == 0 { Vec::new() } else { fact_of(a).into_iter().map(|(p, e)| (p, e * k)).collect() };
            return Ok(Some(fact_value(&f)));
        }
        if !(is_fact(a) && is_fact(b)) {
            return Ok(None);
        }
        let (f, g) = (fact_of(a), fact_of(b));
        Ok(Some(match op {
            BinOp::Mul => fact_value(&fact_mul(&f, &g)),
            BinOp::Div => {
                let mut out = Fact::new();
                for (p, k) in &f {
                    let e = g.iter().find(|(q, _)| q == p).map(|(_, e)| *e).unwrap_or(0);
                    if e > *k {
                        return Err(RuntimeError::runtime("Division was not exact").in_context("/"));
                    }
                    if e < *k {
                        out.push((p.clone(), k - e));
                    }
                }
                if g.iter().any(|(q, _)| !f.iter().any(|(p, _)| p == q)) {
                    return Err(RuntimeError::runtime("Division was not exact").in_context("/"));
                }
                fact_value(&out)
            }
            BinOp::Add | BinOp::Sub => {
                let (x, y) = (fact_int(&f), fact_int(&g));
                let n = if op == BinOp::Add { &x + &y } else { &x - &y };
                if n.is_zero() {
                    return Err(RuntimeError::runtime("Result is 0").in_context(op.intrinsic_name()));
                }
                // A negative difference gives the factorization of its
                // absolute value.
                fact_value(&factor(&n))
            }
            _ => return Ok(None),
        }))
    }
}

// ----- conversions -------------------------------------------------------------

fn facint(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(fact_int(&fact_of(&a.args[0])))
}

fn seqfact(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bad = || RuntimeError::runtime("Sequence not a factorization list (must be a sequence of ordered <prime, exponent> tuples)");
    let pairs = pairs_of(&a.args[0]).ok_or_else(bad)?;
    let mut f = Fact::with_capacity(pairs.len());
    for (p, k) in pairs {
        let ok_prev = f.last().is_none_or(|(q, _): &(Integer, u64)| *q < p);
        if !ok_prev || k.sign() <= 0 || !p.is_prime() || p.sign() < 0 {
            return Err(bad());
        }
        f.push((p, k.to_u64().ok_or_else(bad)?));
    }
    one(fact_value(&f))
}

// ----- divisors --------------------------------------------------------------

/// The positive divisors of the integer with factorization `f`, in
/// increasing order.
pub fn divisors_of(f: &Fact) -> Vec<Integer> {
    let mut divs = vec![Integer::one()];
    for (p, e) in f {
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
    divs
}

/// The factorization of an integer argument (which must be positive) or of
/// a factorization sequence.
fn fact_arg(a: &CallArgs, i: usize, check: fn(usize, &Integer) -> RResult<()>) -> RResult<Fact> {
    match &a.args[i] {
        Value::Int(n) => {
            check(i + 1, n)?;
            Ok(factor(n))
        }
        v => Ok(fact_of(v)),
    }
}

fn positive(i: usize, n: &Integer) -> RResult<()> {
    if n.sign() <= 0 { Err(arg_not(i, "positive")) } else { Ok(()) }
}

fn at_least_one(i: usize, n: &Integer) -> RResult<()> {
    if n.sign() <= 0 { Err(arg_ge(i, n, 1)) } else { Ok(()) }
}

fn at_least_two(i: usize, n: &Integer) -> RResult<()> {
    if *n < Integer::from_i64(2) { Err(arg_ge(i, n, 2)) } else { Ok(()) }
}

fn divisors(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int_seq(divisors_of(&fact_arg(a, 0, at_least_one)?)))
}

fn prime_divisors(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = match &a.args[0] {
        Value::Int(n) if n.is_zero() => return Err(arg_not(1, "non-zero")),
        Value::Int(n) => factor(n),
        v => fact_of(v),
    };
    one(Value::int_seq(f.into_iter().map(|(p, _)| p)))
}

fn sigma(f: &Fact, k: u64) -> Integer {
    let mut s = Integer::one();
    for (p, e) in f {
        let mut t = Integer::zero();
        let pk = p.pow(k);
        let mut x = Integer::one();
        for _ in 0..=*e {
            t = &t + &x;
            x = &x * &pk;
        }
        s = &s * &t;
    }
    s
}

fn number_of_divisors(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(sigma(&fact_arg(a, 0, positive)?, 0))
}

fn sum_of_divisors(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(sigma(&fact_arg(a, 0, positive)?, 1))
}

fn divisor_sigma(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = a.small_ge(0, 0)?;
    intv(sigma(&fact_arg(a, 1, at_least_one)?, k))
}

pub fn phi(f: &Fact) -> Integer {
    let mut r = Integer::one();
    for (p, e) in f {
        r = &(&r * &p.pow(e - 1)) * &(p - &Integer::one());
    }
    r
}

fn euler_phi(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(phi(&fact_arg(a, 0, positive)?))
}

/// The factorization of phi(n) from that of n.
pub fn factored_phi(f: &Fact) -> Fact {
    let mut out = Fact::new();
    for (p, e) in f {
        if *e > 1 {
            out.push((p.clone(), e - 1));
        }
        out = fact_mul(&out, &factor(&(p - &Integer::one())));
    }
    out.retain(|(p, _)| !p.is_one());
    out
}

fn factored_euler_phi(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(fact_value(&factored_phi(&fact_arg(a, 0, positive)?)))
}

/// The factorization of the Carmichael function of the integer with
/// factorization `f`.
fn factored_lambda(f: &Fact) -> Fact {
    let two = Integer::from_i64(2);
    let mut out = Fact::new();
    for (p, e) in f {
        let l: Fact = if *p == two {
            match e {
                1 => Vec::new(),
                2 => vec![(two.clone(), 1)],
                _ => vec![(two.clone(), e - 2)],
            }
        } else {
            let mut l = factor(&(p - &Integer::one()));
            if *e > 1 {
                l = fact_mul(&l, &vec![(p.clone(), e - 1)]);
            }
            l
        };
        out = fact_merge(&out, &l, u64::max);
    }
    out
}

fn carmichael_lambda(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(fact_int(&factored_lambda(&fact_arg(a, 0, at_least_two)?)))
}

fn factored_carmichael_lambda(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(fact_value(&factored_lambda(&fact_arg(a, 0, positive)?)))
}

fn moebius_mu(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = fact_arg(a, 0, at_least_one)?;
    let mu = if f.iter().any(|(_, e)| *e > 1) {
        0
    } else if f.len() % 2 == 0 {
        1
    } else {
        -1
    };
    one(Value::int(mu))
}

/// All n with phi(n) = m, in increasing order.
pub fn phi_inverse(m: &Integer) -> Vec<Integer> {
    // Choose the prime powers p^k exactly dividing n, largest prime first:
    // p - 1 must divide what is left of m.
    fn search(m: &Integer, primes: &[Integer], acc: &Integer, out: &mut Vec<Integer>) {
        if m.is_one() {
            out.push(acc.clone());
        }
        for (i, p) in primes.iter().enumerate() {
            let p1 = p - &Integer::one();
            if !m.is_divisible_by(&p1) {
                continue;
            }
            let mut rest = m.divexact(&p1);
            let mut pk = p.clone();
            loop {
                search(&rest, &primes[i + 1..], &(acc * &pk), out);
                if !rest.is_divisible_by(p) {
                    break;
                }
                rest = rest.divexact(p);
                pk = &pk * p;
            }
        }
    }
    if m.sign() <= 0 || (m.is_odd() && !m.is_one()) {
        return Vec::new();
    }
    let mut primes: Vec<Integer> = divisors_of(&factor(m)).into_iter().map(|d| &d + &Integer::one()).filter(|p| p.is_prime()).collect();
    primes.sort_by(|a, b| b.cmp(a));
    let mut out = Vec::new();
    search(m, &primes, &Integer::one(), &mut out);
    out.sort();
    out
}

fn euler_phi_inverse(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = match &a.args[0] {
        Value::Int(n) => {
            if n.sign() <= 0 {
                return Err(super::bare(arg_ge(1, n, 1)));
            }
            n.clone()
        }
        v => fact_int(&fact_of(v)),
    };
    one(Value::int_seq(phi_inverse(&m)))
}

fn factored_euler_phi_inverse(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = match &a.args[0] {
        Value::Int(n) => {
            if n.sign() <= 0 {
                return Err(super::bare(arg_ge(1, n, 1)));
            }
            n.clone()
        }
        v => fact_int(&fact_of(v)),
    };
    if m.is_odd() && !m.is_one() {
        // Magma returns an empty set here, not a sequence.
        return one(Value::Set(Rc::new(SetEnum::new(None, VSet::default()))));
    }
    let sols = phi_inverse(&m);
    let mut facts: Vec<Fact> = sols.iter().map(factor).collect();
    facts.sort_by(|a, b| cmp_fact(a, b));
    one(Value::seq(None, facts.iter().map(|f| fact_value(f)).collect()))
}

/// Magma's order on factorization sequences: pair by pair.
fn cmp_fact(a: &Fact, b: &Fact) -> std::cmp::Ordering {
    for (x, y) in a.iter().zip(b) {
        let o = x.0.cmp(&y.0).then(x.1.cmp(&y.1));
        if o.is_ne() {
            return o;
        }
    }
    a.len().cmp(&b.len())
}

fn gcd_fact(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(fact_value(&fact_merge(&fact_of(&a.args[0]), &fact_of(&a.args[1]), u64::min)))
}

fn lcm_fact(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(fact_value(&fact_merge(&fact_of(&a.args[0]), &fact_of(&a.args[1]), u64::max)))
}

/// `n = x * y^2` with `x` squarefree.
pub fn squarefree_split(f: &Fact) -> (Fact, Fact) {
    let x = f.iter().filter(|(_, e)| e % 2 == 1).map(|(p, _)| (p.clone(), 1)).collect();
    let y = f.iter().filter(|(_, e)| *e >= 2).map(|(p, e)| (p.clone(), e / 2)).collect();
    (x, y)
}

fn squarefree_factorization_fact(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (x, y) = squarefree_split(&fact_of(&a.args[0]));
    Ok(vals![fact_value(&x), fact_value(&y)])
}

// ----- predicates --------------------------------------------------------------

fn fact_is_one(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(fact_of(&a.args[0]).is_empty())
}

fn fact_is_even(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let two = Integer::from_i64(2);
    boolv(fact_of(&a.args[0]).iter().any(|(p, _)| *p == two))
}

fn fact_is_odd(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let two = Integer::from_i64(2);
    boolv(!fact_of(&a.args[0]).iter().any(|(p, _)| *p == two))
}

fn fact_is_prime(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = fact_of(&a.args[0]);
    boolv(f.len() == 1 && f[0].1 == 1)
}

fn fact_is_prime_power(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(fact_of(&a.args[0]).len() <= 1)
}

fn fact_is_square(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = fact_of(&a.args[0]);
    if f.iter().any(|(_, e)| e % 2 == 1) {
        return boolv(false);
    }
    Ok(vals![Value::Bool(true), fact_value(&f.iter().map(|(p, e)| (p.clone(), e / 2)).collect::<Fact>())])
}

fn fact_is_squarefree(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(fact_of(&a.args[0]).iter().all(|(_, e)| *e == 1))
}

pub fn register(it: &mut Interp) {
    const F: &str = "RngIntEltFact";
    for name in ["Facint", "FactorizationToInteger", "FactorisationToInteger"] {
        it.def(name, &format!("f::{F} -> RngIntElt"), "The integer the factorization sequence f stands for.", facint);
    }
    for name in ["SeqFact", "SequenceToFactorization"] {
        it.def(name, &format!("s::[Tup] -> {F}"), "The factorization sequence with the <prime, exponent> pairs of s.", seqfact);
    }
    for t in ["n::RngIntElt", "f::RngIntEltFact"] {
        it.def("Divisors", &format!("{t} -> [RngIntElt]"), "The positive divisors, in increasing order.", divisors);
        for name in ["PrimeDivisors", "PrimeBasis", "PrimeFactors"] {
            it.def(name, &format!("{t} -> [RngIntElt]"), "The distinct prime divisors, in increasing order.", prime_divisors);
        }
        it.def("NumberOfDivisors", &format!("{t} -> RngIntElt"), "The number of positive divisors.", number_of_divisors);
        it.def("SumOfDivisors", &format!("{t} -> RngIntElt"), "The sum of the positive divisors.", sum_of_divisors);
        it.def("DivisorSigma", &format!("i::RngIntElt, {t} -> RngIntElt"), "The sum of the i-th powers of the divisors.", divisor_sigma);
        it.def("MoebiusMu", &format!("{t} -> RngIntElt"), "The Moebius function.", moebius_mu);
        it.def("EulerPhiInverse", &format!("{t} -> [RngIntElt]"), "The integers n with EulerPhi(n) = m, in increasing order.", euler_phi_inverse);
        it.def("FactoredEulerPhiInverse", &format!("{t} -> [{F}]"), "The factorizations of the integers n with EulerPhi(n) = m.", factored_euler_phi_inverse);
    }
    for t in ["n::RngIntElt", "f::RngIntEltFact", "f::[Tup]"] {
        it.def("EulerPhi", &format!("{t} -> RngIntElt"), "Euler's totient function.", euler_phi);
        it.def("FactoredEulerPhi", &format!("{t} -> {F}"), "Euler's totient function, as a factorization sequence.", factored_euler_phi);
        it.def("CarmichaelLambda", &format!("{t} -> RngIntElt"), "The Carmichael function (the exponent of the unit group modulo n).", carmichael_lambda);
        it.def("FactoredCarmichaelLambda", &format!("{t} -> {F}"), "The Carmichael function, as a factorization sequence.", factored_carmichael_lambda);
    }
    for name in ["Gcd", "GCD", "GreatestCommonDivisor"] {
        it.def(name, &format!("f::{F}, g::{F} -> {F}"), "The greatest common divisor, as a factorization sequence.", gcd_fact);
    }
    for name in ["Lcm", "LCM", "LeastCommonMultiple"] {
        it.def(name, &format!("f::{F}, g::{F} -> {F}"), "The least common multiple, as a factorization sequence.", lcm_fact);
    }
    it.def("SquarefreeFactorization", &format!("f::{F} -> {F}, {F}"), "Factorizations of x squarefree and y with n = x*y^2.", squarefree_factorization_fact);
    it.def("IsOne", &format!("f::{F} -> BoolElt"), "Whether f stands for 1.", fact_is_one);
    it.def("IsUnit", &format!("f::{F} -> BoolElt"), "Whether f stands for 1.", fact_is_one);
    it.def("IsEven", &format!("f::{F} -> BoolElt"), "Whether f stands for an even integer.", fact_is_even);
    it.def("IsOdd", &format!("f::{F} -> BoolElt"), "Whether f stands for an odd integer.", fact_is_odd);
    it.def("IsPrime", &format!("f::{F} -> BoolElt"), "Whether f stands for a prime.", fact_is_prime);
    it.def("IsPrimePower", &format!("f::{F} -> BoolElt"), "Whether f stands for a prime power (or 1).", fact_is_prime_power);
    it.def("IsSquare", &format!("f::{F} -> BoolElt, {F}"), "Whether f stands for a square, and its square root.", fact_is_square);
    it.def("IsSquarefree", &format!("f::{F} -> BoolElt"), "Whether f stands for a squarefree integer.", fact_is_squarefree);
}
