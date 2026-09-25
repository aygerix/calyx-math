//! Integer factorization: `Factorization` and the individual methods
//! (trial division, Pollard rho, SQUFOF, p - 1, p + 1, ECM, the quadratic
//! sieve), coprime bases, partial factorizations and Cunningham numbers.

use std::collections::HashMap;

use calyx_flint::Integer;

use super::factseq::{Fact, fact_mul, fact_value, factor};
use super::numtheory::{modp, modsqrt, primes_up_to};
use super::{arg_not, arg_range, intv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

fn int(v: i64) -> Integer {
    Integer::from_i64(v)
}

/// A factorization sequence and the composites left unfactored.
fn fact_and_rest(f: &Fact, rest: Vec<Integer>) -> Vec<Value> {
    vec![fact_value(f), Value::int_seq(rest)]
}

fn sorted_fact(mut f: Fact) -> Fact {
    f.sort_by(|a, b| a.0.cmp(&b.0));
    let mut out: Fact = Vec::with_capacity(f.len());
    for (p, e) in f {
        match out.last_mut() {
            Some((q, k)) if *q == p => *k += e,
            _ => out.push((p, e)),
        }
    }
    out
}

fn param_int(a: &CallArgs, name: &str) -> Option<Integer> {
    match a.param(name) {
        Some(Value::Int(n)) => Some(n.clone()),
        _ => None,
    }
}

// ----- Factorization ------------------------------------------------------------------

/// Split `n` with one method until every part is prime or the method
/// gives up. `method` returns a proper divisor of a composite, if it finds
/// one. Powers of 2 and 3 and perfect powers are taken out first.
fn split_with(n: &Integer, method: &mut dyn FnMut(&Integer) -> Option<Integer>) -> (Fact, Vec<Integer>) {
    let mut fact = Fact::new();
    let mut rest = Vec::new();
    let mut stack = vec![(n.abs(), 1u64)];
    while let Some((m, e)) = stack.pop() {
        if m.is_one() {
            continue;
        }
        if m.is_prime() {
            fact.push((m, e));
            continue;
        }
        let mut m = m;
        let mut found_small = false;
        for p in [int(2), int(3)] {
            let (k, r) = m.remove(&p);
            if k > 0 {
                fact.push((p, k * e));
                m = r;
                found_small = true;
            }
        }
        if found_small {
            stack.push((m, e));
            continue;
        }
        if let Some((b, k)) = m.perfect_power() {
            stack.push((b, e * k));
            continue;
        }
        match method(&m) {
            Some(d) if !d.is_one() && d != m => {
                let q = m.divexact(&d);
                stack.push((d, e));
                stack.push((q, e));
            }
            _ => rest.push(m),
        }
    }
    rest.sort();
    (sorted_fact(fact), rest)
}

fn factorization(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?.clone();
    if n.is_zero() {
        return Err(arg_not(1, "non-zero"));
    }
    let sign = Value::int(n.sign() as i64);
    let mut m = n.abs();
    // Stored factors are tried first.
    let mut fact = Fact::new();
    for p in &it.stored_factors {
        let (k, r) = m.remove(p);
        if k > 0 {
            fact.push((p.clone(), k));
            m = r;
        }
    }
    let ecm = param_int(a, "ECMLimit");
    let mpqs = param_int(a, "MPQSLimit");
    let limited = ecm.is_some() && mpqs.as_ref().is_some_and(|l| *l < int(25));
    let mut rest = Vec::new();
    if limited {
        // Only trial division, SQUFOF, Pollard rho and the given number of
        // ECM curves may be used.
        let td = param_int(a, "TrialDivisionLimit").and_then(|b| b.to_u64()).unwrap_or(10000);
        let (f, r) = trial_division(&m, td);
        fact.extend(f);
        let rho = param_int(a, "PollardRhoLimit").and_then(|b| b.to_u64()).unwrap_or(8191);
        let sq = param_int(a, "SQUFOFLimit").and_then(|b| b.to_u64()).unwrap_or(24);
        let curves = ecm.and_then(|c| c.to_u64()).unwrap_or(0);
        let rng = &mut it.rng;
        let (f, r) = split_with(&r, &mut |x: &Integer| {
            if (x.to_string().len() as u64) <= sq {
                if let Some(d) = squfof(x, 200_000) {
                    return Some(d);
                }
            }
            if let Some(d) = pollard_rho(x, &int(1), &int(1), rho) {
                return Some(d);
            }
            let mut b1 = 500u64;
            for _ in 0..curves {
                let sigma = Integer::from_u64(6 + rng.below_u64((1 << 32) - 6));
                if let Some(d) = ecm_curve(x, b1, 100 * b1, &sigma, None).found() {
                    return Some(d);
                }
                b1 += 100;
            }
            None
        });
        fact.extend(f);
        rest = r;
    } else if !m.is_one() {
        fact.extend(factor(&m));
    }
    let fact = sorted_fact(fact);
    // The sign and the unfactored part are returned only when asked for;
    // the latter stays unassigned when the factorization is complete.
    let mut out = vec![fact_value(&fact), sign, if rest.is_empty() { Value::Undef } else { Value::int_seq(rest) }];
    out.truncate(a.nresults.max(1));
    Ok(out)
}

fn store_factor(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let ps = match &a.args[0] {
        Value::Int(n) => vec![n.clone()],
        v => super::ints::ints_of(v)?,
    };
    for p in &ps {
        if p.sign() <= 0 {
            return Err(arg_not(1, "positive"));
        }
        if !p.is_prime() {
            return Err(super::arg_prime(1, p));
        }
    }
    for p in ps {
        if !it.stored_factors.contains(&p) {
            it.stored_factors.push(p);
        }
    }
    Ok(Vec::new())
}

fn get_stored_factors(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vec<Value>> {
    one(Value::int_seq(it.stored_factors.clone()))
}

fn clear_stored_factors(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vec<Value>> {
    it.stored_factors.clear();
    Ok(Vec::new())
}

// ----- trial division ---------------------------------------------------------------------

/// The primes up to `bound` dividing `n`, and the part of |n| left.
fn trial_division(n: &Integer, bound: u64) -> (Fact, Integer) {
    let mut m = n.abs();
    let mut fact = Fact::new();
    let limit = bound.min(1 << 32);
    let mut p = 2u64;
    while p <= limit && !m.is_one() {
        let pi = Integer::from_u64(p);
        if &pi * &pi > m {
            // What is left is prime; keep it only if it is within the bound.
            if m <= Integer::from_u64(bound) {
                fact.push((m.clone(), 1));
                m = Integer::one();
            }
            break;
        }
        let (k, r) = m.remove(&pi);
        if k > 0 {
            fact.push((pi, k));
            m = r;
        }
        p = if p == 2 { 3 } else { p + 2 };
    }
    (fact, m)
}

fn trial_division_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?.clone();
    if n.is_zero() {
        return Err(arg_not(1, "non-zero"));
    }
    let bound = if a.args.len() > 1 {
        let b = a.int(1)?;
        if b.sign() <= 0 {
            return Err(RuntimeError::runtime("Argument 2 must be greater than 0"));
        }
        b.to_u64().unwrap_or(u64::MAX)
    } else {
        10000
    };
    let (f, r) = trial_division(&n, bound);
    Ok(vec![fact_value(&f), Value::Int(r)])
}

// ----- Pollard rho --------------------------------------------------------------------------

/// Brent's variant of Pollard's rho with x -> x^2 + c from x = s, for at
/// most `k` iterations.
fn pollard_rho(n: &Integer, c: &Integer, s: &Integer, k: u64) -> Option<Integer> {
    let f = |x: &Integer| modp(&(&(x * x) + c), n);
    let (mut y, mut r, mut q) = (modp(s, n), 1u64, Integer::one());
    let mut x = y.clone();
    let mut ys = y.clone();
    let mut g = Integer::one();
    let mut iters = 0u64;
    let batch = 32u64;
    while g.is_one() {
        x = y.clone();
        for _ in 0..r {
            y = f(&y);
        }
        let mut done = 0u64;
        while done < r && g.is_one() {
            ys = y.clone();
            for _ in 0..batch.min(r - done) {
                y = f(&y);
                q = modp(&(&q * &(&x - &y).abs()), n);
                iters += 1;
            }
            g = q.gcd(n);
            done += batch;
            if iters >= k && g.is_one() {
                return None;
            }
        }
        r *= 2;
    }
    if g == *n {
        // Step back one iteration at a time.
        loop {
            ys = f(&ys);
            g = (&x - &ys).abs().gcd(n);
            if !g.is_one() {
                break;
            }
        }
    }
    if g == *n { None } else { Some(g) }
}

fn pollard_rho_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?.clone();
    if n <= Integer::one() {
        return Err(RuntimeError::runtime("Argument 1 must be greater than 1"));
    }
    let (c, s, k) = if a.args.len() == 4 { (a.int(1)?.clone(), a.int(2)?.clone(), a.int(3)?.to_u64().unwrap_or(0)) } else { (int(1), int(1), 8191) };
    let (f, r) = split_with(&n, &mut |m: &Integer| pollard_rho(m, &c, &s, k));
    Ok(fact_and_rest(&f, r))
}

// ----- SQUFOF ----------------------------------------------------------------------------------

/// Shanks's square form factorization, with small multipliers.
fn squfof(n: &Integer, limit: u64) -> Option<Integer> {
    if n.is_square() {
        return n.isqrt();
    }
    for k in [1i64, 3, 5, 7, 11, 15, 21, 33, 35, 55, 77, 105, 165, 231, 385, 1155] {
        let kn = n * &int(k);
        let p0 = kn.isqrt()?;
        let (mut qprev, mut q) = (Integer::one(), &kn - &(&p0 * &p0));
        if q.is_zero() {
            continue;
        }
        let mut p = p0.clone();
        let mut found = false;
        for i in 1..=limit {
            let b = (&p0 + &p).fdiv_qr(&q)?.0;
            let pn = &(&b * &q) - &p;
            let qn = &qprev + &(&b * &(&p - &pn));
            qprev = q;
            q = qn;
            p = pn;
            // q is now Q_(i+1), which must be a square with even index.
            if i % 2 == 1 && q.is_square() {
                found = true;
                break;
            }
        }
        if !found {
            continue;
        }
        let r = q.isqrt()?;
        let b = (&p0 - &p).fdiv_qr(&r)?.0;
        p = &(&b * &r) + &p;
        qprev = r;
        q = (&kn - &(&p * &p)).divexact(&qprev);
        if q.is_zero() {
            continue;
        }
        for _ in 0..limit {
            let b = (&p0 + &p).fdiv_qr(&q)?.0;
            let pn = &(&b * &q) - &p;
            let qn = &qprev + &(&b * &(&p - &pn));
            if pn == p {
                break;
            }
            qprev = q;
            q = qn;
            p = pn;
        }
        let f = n.gcd(&p);
        if !f.is_one() && f != *n {
            return Some(f);
        }
    }
    None
}

fn squfof_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?.clone();
    if n <= Integer::one() {
        return Err(RuntimeError::runtime("Argument 1 must be greater than 1"));
    }
    if n.bits() > 126 {
        return Err(RuntimeError::runtime(format!("Argument 1 ({n}) is too large")));
    }
    let limit = if a.args.len() > 1 { a.int(1)?.to_u64().unwrap_or(0) } else { 200_000 };
    let (f, r) = split_with(&n, &mut |m: &Integer| squfof(m, limit));
    Ok(fact_and_rest(&f, r))
}

// ----- p - 1 and p + 1 ---------------------------------------------------------------------------

fn b1_primes(b1: u64) -> Vec<u64> {
    primes_up_to(b1.min(1 << 32))
}

/// The outcome of a factoring attempt with a single base or curve.
enum Attempt {
    Found(Integer),
    Failed,
}

impl Attempt {
    fn found(self) -> Option<Integer> {
        match self {
            Attempt::Found(d) => Some(d),
            Attempt::Failed => None,
        }
    }
}

/// A proper divisor of n from g = gcd(..., n), if g is one.
fn proper(g: &Integer, n: &Integer) -> Option<Integer> {
    (!g.is_one() && g != n && !g.is_zero()).then(|| g.clone())
}

/// Stage 1 of a power-based method: `step(x, q)` raises the element x to
/// the q-th power, `test(x)` the value whose gcd with n reveals a factor.
/// The gcd is taken after each prime, and when all of n appears the prime's
/// powers are applied one at a time.
fn stage1<T: Clone>(n: &Integer, b1: u64, x: &mut T, step: &dyn Fn(&T, u64) -> T, test: &dyn Fn(&T) -> Integer) -> Option<Attempt> {
    for p in b1_primes(b1) {
        let mut q = p;
        while q <= b1 / p {
            q *= p;
        }
        let saved = x.clone();
        *x = step(x, q);
        let g = test(x).gcd(n);
        if let Some(d) = proper(&g, n) {
            return Some(Attempt::Found(d));
        }
        if g == *n {
            let mut y = saved;
            let mut pk = 1;
            while pk <= q / p {
                y = step(&y, p);
                pk *= p;
                let g = test(&y).gcd(n);
                if let Some(d) = proper(&g, n) {
                    return Some(Attempt::Found(d));
                }
                if g == *n {
                    return Some(Attempt::Failed);
                }
            }
            return Some(Attempt::Failed);
        }
    }
    None
}

/// Stage 2 over the primes in (B1, B2]: `at(q)` is the value to test for
/// the prime q.
fn stage2(n: &Integer, b1: u64, b2: u64, at: &mut dyn FnMut(u64) -> Integer) -> Attempt {
    let primes: Vec<u64> = primes_up_to(b2.min(1 << 32)).into_iter().filter(|&q| q > b1).collect();
    for block in primes.chunks(64) {
        let mut acc = Integer::one();
        let vals: Vec<Integer> = block.iter().map(|&q| at(q)).collect();
        for v in &vals {
            acc = modp(&(&acc * v), n);
        }
        let g = acc.gcd(n);
        if let Some(d) = proper(&g, n) {
            return Attempt::Found(d);
        }
        if g == *n {
            for v in &vals {
                if let Some(d) = proper(&v.gcd(n), n) {
                    return Attempt::Found(d);
                }
            }
            return Attempt::Failed;
        }
    }
    Attempt::Failed
}

fn p_minus_1(n: &Integer, b1: u64, b2: u64, x0: &Integer) -> Attempt {
    let mut x = modp(x0, n);
    let step = |x: &Integer, q: u64| x.powm(&Integer::from_u64(q), n).unwrap();
    let test = |x: &Integer| x - &Integer::one();
    if let Some(r) = stage1(n, b1, &mut x, &step, &test) {
        return r;
    }
    stage2(n, b1, b2, &mut |q| &x.powm(&Integer::from_u64(q), n).unwrap() - &Integer::one())
}

/// V_k(v) of the Lucas sequence V_0 = 2, V_1 = v, V_(i+1) = v V_i - V_(i-1).
fn lucas_v(v: &Integer, k: u64, n: &Integer) -> Integer {
    if k == 0 {
        return modp(&int(2), n);
    }
    let (mut a, mut b) = (v.clone(), modp(&(&(v * v) - &int(2)), n));
    for i in (0..63 - k.leading_zeros()).rev() {
        if (k >> i) & 1 == 1 {
            a = modp(&(&(&a * &b) - v), n);
            b = modp(&(&(&b * &b) - &int(2)), n);
        } else {
            b = modp(&(&(&a * &b) - v), n);
            a = modp(&(&(&a * &a) - &int(2)), n);
        }
    }
    a
}

fn p_plus_1(n: &Integer, b1: u64, b2: u64, x0: &Integer) -> Attempt {
    let mut v = modp(x0, n);
    let step = |v: &Integer, q: u64| lucas_v(v, q, n);
    let test = |v: &Integer| v - &int(2);
    if let Some(r) = stage1(n, b1, &mut v, &step, &test) {
        return r;
    }
    stage2(n, b1, b2, &mut |q| &lucas_v(&v, q, n) - &int(2))
}

fn pm1_args(it: &mut Interp, a: &CallArgs) -> RResult<(Integer, u64, u64, Integer)> {
    let n = a.int(0)?.clone();
    if n <= Integer::one() {
        return Err(RuntimeError::runtime("Argument 1 should be greater than 1"));
    }
    let b1 = a.int(1)?.to_u64().unwrap_or(0);
    // Without B2 only stage 1 is run.
    let b2 = param_int(a, "B2").and_then(|b| b.to_u64()).unwrap_or(b1);
    let x0 = match param_int(a, "x0") {
        Some(x) => x,
        None => &int(2) + &it.rng.below(&(&n.clone().max(int(5)) - &int(3))),
    };
    Ok((n, b1, b2, x0))
}

fn p_minus_1_fn(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (n, b1, b2, x0) = pm1_args(it, a)?;
    match p_minus_1(&n, b1, b2, &x0) {
        Attempt::Found(d) => Ok(vec![Value::Int(d), Value::Int(x0)]),
        Attempt::Failed => intv(Integer::zero()),
    }
}

fn p_plus_1_fn(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (n, b1, b2, x0) = pm1_args(it, a)?;
    match p_plus_1(&n, b1, b2, &x0) {
        Attempt::Found(d) => Ok(vec![Value::Int(d), Value::Int(x0)]),
        Attempt::Failed => intv(Integer::zero()),
    }
}

// ----- ECM ------------------------------------------------------------------------------------------

/// Points (X : Z) on a Montgomery curve B y^2 = x^3 + A x^2 + x modulo n,
/// with a24 = (A + 2)/4.
#[derive(Clone)]
struct MPoint {
    x: Integer,
    z: Integer,
}

fn xdbl(p: &MPoint, a24: &Integer, n: &Integer) -> MPoint {
    let s = modp(&(&(&p.x + &p.z) * &(&p.x + &p.z)), n);
    let d = modp(&(&(&p.x - &p.z) * &(&p.x - &p.z)), n);
    let t = &s - &d;
    MPoint { x: modp(&(&s * &d), n), z: modp(&(&t * &(&d + &(a24 * &t))), n) }
}

fn xadd(p: &MPoint, q: &MPoint, diff: &MPoint, n: &Integer) -> MPoint {
    let u = &(&p.x - &p.z) * &(&q.x + &q.z);
    let v = &(&p.x + &p.z) * &(&q.x - &q.z);
    let s = &u + &v;
    let d = &u - &v;
    MPoint { x: modp(&(&diff.z * &modp(&(&s * &s), n)), n), z: modp(&(&diff.x * &modp(&(&d * &d), n)), n) }
}

/// [k]P by the Montgomery ladder.
fn ladder(p: &MPoint, k: u64, a24: &Integer, n: &Integer) -> MPoint {
    if k == 0 {
        return MPoint { x: Integer::zero(), z: Integer::zero() };
    }
    let (mut r0, mut r1) = (p.clone(), xdbl(p, a24, n));
    for i in (0..63 - k.leading_zeros()).rev() {
        if (k >> i) & 1 == 1 {
            r0 = xadd(&r1, &r0, p, n);
            r1 = xdbl(&r1, a24, n);
        } else {
            r1 = xadd(&r1, &r0, p, n);
            r0 = xdbl(&r0, a24, n);
        }
    }
    r0
}

/// Suyama's curve for sigma: u = sigma^2 - 5, v = 4 sigma,
/// A + 2 = (v - u)^3 (3u + v) / (4 u^3 v), starting point (u^3 : v^3).
/// Returns (a24 numerator, a24 denominator, x0 numerator, x0 denominator).
fn suyama(sigma: &Integer) -> (Integer, Integer, Integer, Integer) {
    let u = &(sigma * sigma) - &int(5);
    let v = sigma * &int(4);
    let vu = &v - &u;
    let num = &(&(&vu * &vu) * &vu) * &(&(&u * &int(3)) + &v);
    let den = &(&(&(&u * &u) * &u) * &v) * &int(16);
    (num, den, &(&u * &u) * &u, &(&v * &v) * &v)
}

fn ecm_curve(n: &Integer, b1: u64, b2: u64, sigma: &Integer, x0: Option<&Integer>) -> Attempt {
    let (num, den, xn, xd) = suyama(sigma);
    let inv = match modp(&den, n).invmod(n) {
        Some(i) => i,
        None => {
            return match proper(&den.gcd(n), n) {
                Some(d) => Attempt::Found(d),
                None => Attempt::Failed,
            };
        }
    };
    let a24 = modp(&(&num * &inv), n);
    let mut p = match x0 {
        Some(x) => MPoint { x: modp(x, n), z: Integer::one() },
        None => MPoint { x: modp(&xn, n), z: modp(&xd, n) },
    };
    let step = |p: &MPoint, q: u64| ladder(p, q, &a24, n);
    let test = |p: &MPoint| p.z.clone();
    if let Some(r) = stage1(n, b1, &mut p, &step, &test) {
        return r;
    }
    // Stage 2: odd multiples of the stage 1 point by differential addition.
    let q2 = xdbl(&p, &a24, n);
    let start = (b1 + 1) | 1;
    let mut prev = ladder(&p, start.saturating_sub(2).max(1), &a24, n);
    let mut cur = ladder(&p, start, &a24, n);
    let mut at_m = start;
    stage2(n, b1, b2, &mut |q| {
        while at_m < q {
            let next = if at_m == 1 { ladder(&p, 3, &a24, n) } else { xadd(&cur, &q2, &prev, n) };
            prev = std::mem::replace(&mut cur, next);
            at_m += 2;
        }
        cur.z.clone()
    })
}

fn ecm_fn(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?.clone();
    if n <= Integer::one() {
        return Err(RuntimeError::runtime("Argument 1 should be greater than 1"));
    }
    let b1 = a.int(1)?.to_u64().unwrap_or(0);
    let b2 = param_int(a, "B2").and_then(|b| b.to_u64()).unwrap_or(b1);
    let sigma = param_int(a, "Sigma").unwrap_or_else(|| Integer::from_u64(6 + it.rng.below_u64((1 << 32) - 6)));
    let x0 = param_int(a, "x0");
    match ecm_curve(&n, b1, b2, &sigma, x0.as_ref()) {
        Attempt::Found(d) => Ok(vec![Value::Int(d), Value::Int(sigma)]),
        Attempt::Failed => intv(Integer::zero()),
    }
}

fn ecm_steps(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?.clone();
    if n <= Integer::one() {
        return Err(RuntimeError::runtime("Argument 1 should be greater than 1"));
    }
    let mut b1 = a.int(1)?.to_u64().unwrap_or(0).max(1);
    let hi = a.int(2)?.to_u64().unwrap_or(u64::MAX);
    while b1 <= hi {
        let sigma = Integer::from_u64(6 + it.rng.below_u64((1 << 32) - 6));
        if let Attempt::Found(d) = ecm_curve(&n, b1, 100 * b1, &sigma, None) {
            return Ok(vec![Value::Int(d), Value::Int(sigma)]);
        }
        b1 += (b1 as f64).sqrt() as u64;
    }
    intv(Integer::zero())
}

fn mpqs(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?.clone();
    if n <= Integer::one() {
        return Err(RuntimeError::runtime("Argument 1 must be greater than 1"));
    }
    Ok(fact_and_rest(&factor(&n), Vec::new()))
}

// ----- ECM curve orders ---------------------------------------------------------------------------------

/// Affine points on y^2 = x^3 + a2 x^2 + a4 x over GF(p); `None` is the
/// point at infinity.
type Pt = Option<(Integer, Integer)>;

struct Curve {
    p: Integer,
    a2: Integer,
    a4: Integer,
}

impl Curve {
    fn add(&self, s: &Pt, t: &Pt) -> Pt {
        let p = &self.p;
        let (Some((x1, y1)), Some((x2, y2))) = (s, t) else {
            return if s.is_none() { t.clone() } else { s.clone() };
        };
        let lam = if x1 == x2 {
            if modp(&(y1 + y2), p).is_zero() {
                return None;
            }
            let num = &(&(&(&(x1 * x1) * &int(3)) + &(&(&self.a2 * x1) * &int(2))) + &self.a4);
            modp(&(num * &modp(&(y1 * &int(2)), p).invmod(p)?), p)
        } else {
            modp(&(&(y2 - y1) * &modp(&(x2 - x1), p).invmod(p)?), p)
        };
        let x3 = modp(&(&(&(&(&lam * &lam) - &self.a2) - x1) - x2), p);
        let y3 = modp(&(&(&lam * &(x1 - &x3)) - y1), p);
        Some((x3, y3))
    }

    fn mul(&self, s: &Pt, k: &Integer) -> Pt {
        let mut r: Pt = None;
        let mut base = s.clone();
        let mut k = k.clone();
        while !k.is_zero() {
            if k.is_odd() {
                r = self.add(&r, &base);
            }
            base = self.add(&base, &base);
            k = k.fdiv_2exp(1);
        }
        r
    }

    fn rhs(&self, x: &Integer) -> Integer {
        modp(&(&(&(&(x * x) * x) + &(&(&self.a2 * x) * x)) + &(&self.a4 * x)), &self.p)
    }

    fn random_point(&self, rng: &mut crate::random::Rng) -> Pt {
        loop {
            let x = rng.below(&self.p);
            let r = self.rhs(&x);
            if r.is_zero() {
                return Some((x, r));
            }
            if r.kronecker(&self.p) == 1 {
                return Some((x, modsqrt(&r, &self.p)?));
            }
        }
    }

    /// The number of points over GF(p).
    fn order(&self, rng: &mut crate::random::Rng) -> Integer {
        let p = &self.p;
        if p.to_u64().is_some_and(|p| p < 5000) {
            let mut n = p + 1;
            let mut x = Integer::zero();
            while x < *p {
                n = &n + &Integer::from_i64(self.rhs(&x).kronecker(p) as i64);
                x = &x + 1;
            }
            return n;
        }
        // The order lies in [p + 1 - 2 sqrt p, p + 1 + 2 sqrt p]; find the
        // multiples of the orders of random points there.
        let s = &(p.isqrt().unwrap() * &int(2)) + 2;
        let (lo, hi) = (&(p + 1) - &s, &(p + 1) + &s);
        let width = &hi - &lo;
        let m = &width.isqrt().unwrap() + 1;
        let mut lcm = Integer::one();
        for _ in 0..64 {
            let pt = self.random_point(rng);
            let mut baby: std::collections::HashMap<Integer, Vec<(u64, Integer)>> = std::collections::HashMap::new();
            let mut q: Pt = None;
            let mm = m.to_u64().unwrap();
            for j in 0..=mm {
                if let Some((x, y)) = &q {
                    baby.entry(x.clone()).or_default().push((j, y.clone()));
                }
                q = self.add(&q, &pt);
            }
            let giant = self.mul(&pt, &m);
            let mut r = self.mul(&pt, &lo);
            let mut base = lo.clone();
            let mut cands = Vec::new();
            while base <= &hi + &m {
                match &r {
                    None => cands.push(base.clone()),
                    Some((x, y)) => {
                        for (j, yj) in baby.get(x).into_iter().flatten() {
                            let j = Integer::from_u64(*j);
                            cands.push(if yj == y { &base - &j } else { &base + &j });
                        }
                    }
                }
                r = self.add(&r, &giant);
                base = &base + &m;
            }
            // The order of this point divides every candidate that kills it.
            let Some(nn) = cands.into_iter().find(|c| c.sign() > 0 && self.mul(&pt, c).is_none()) else {
                continue;
            };
            let mut ord = nn;
            for (q, _) in factor(&ord) {
                while ord.is_divisible_by(&q) && self.mul(&pt, &ord.divexact(&q)).is_none() {
                    ord = ord.divexact(&q);
                }
            }
            lcm = lcm.lcm(&ord);
            let first = lo.cdiv_q(&lcm).unwrap();
            let first = &first * &lcm;
            if &first + &lcm > hi {
                return first;
            }
        }
        // Fall back on counting (small p only reach here).
        let mut n = p + 1;
        let mut x = Integer::zero();
        while x < *p {
            n = &n + &Integer::from_i64(self.rhs(&x).kronecker(p) as i64);
            x = &x + 1;
        }
        n
    }
}

/// The curve ECM uses modulo the prime p for sigma: Suyama's Montgomery
/// curve b y^2 = x^3 + A x^2 + x through (x0, 1), in the form
/// y^2 = x^3 + bA x^2 + b^2 x.
fn ecm_curve_mod(p: &Integer, sigma: &Integer) -> RResult<Curve> {
    let singular = || RuntimeError::runtime("Curve is singular").in_context("EllipticCurve");
    let (num, den, xn, xd) = suyama(sigma);
    let inv = modp(&den, p).invmod(p).ok_or_else(singular)?;
    let a = modp(&(&(&(&num * &inv) * &int(4)) - &int(2)), p);
    let x0 = modp(&(&xn * &modp(&xd, p).invmod(p).ok_or_else(singular)?), p);
    let b = modp(&(&(&(&(&x0 * &x0) * &x0) + &(&(&a * &x0) * &x0)) + &x0), p);
    let disc = modp(&(&(&b * &b) * &(&(&a * &a) - &int(4))), p);
    if disc.is_zero() {
        return Err(singular());
    }
    Ok(Curve { p: p.clone(), a2: modp(&(&b * &a), p), a4: modp(&(&b * &b), p) })
}

fn ecm_order_of(it: &mut Interp, a: &CallArgs) -> RResult<Integer> {
    let (p, s) = (a.int(0)?.clone(), a.int(1)?.clone());
    if p.sign() <= 0 || !p.is_prime() {
        return Err(super::bare(RuntimeError::runtime("First argument must be a positive prime")));
    }
    let c = ecm_curve_mod(&p, &s)?;
    Ok(c.order(&mut it.rng))
}

fn ecm_order(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    intv(ecm_order_of(it, a)?)
}

fn ecm_factored_order(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    one(fact_value(&factor(&ecm_order_of(it, a)?)))
}

// ----- coprime bases and partial factorizations ------------------------------------------------------

/// The natural coprime base of the integers (ignoring signs, 0 and 1),
/// with the exponent of each base element in their product.
pub fn coprime_basis(s: &[Integer]) -> Fact {
    let mut base: Vec<Integer> = s.iter().map(|x| x.abs()).filter(|x| !x.is_zero() && !x.is_one()).collect();
    base.sort();
    base.dedup();
    'outer: loop {
        for i in 0..base.len() {
            for j in i + 1..base.len() {
                let g = base[i].gcd(&base[j]);
                if !g.is_one() {
                    let (a, b) = (base[i].divexact(&g), base[j].divexact(&g));
                    base.remove(j);
                    base.remove(i);
                    base.extend([g, a, b].into_iter().filter(|x| !x.is_one()));
                    base.sort();
                    base.dedup();
                    continue 'outer;
                }
            }
        }
        break;
    }
    base.into_iter()
        .map(|b| {
            let e = s.iter().filter(|x| !x.is_zero()).map(|x| x.remove(&b).0).sum();
            (b, e)
        })
        .collect()
}

fn coprime_basis_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    one(fact_value(&coprime_basis(&super::ints::ints_of(&a.args[0])?)))
}

/// Primary bucket counts of Magma's hash tables for sets, beyond the
/// initial 11.
const SET_TABLE_SIZES: [u64; 69] = [
    17, 19, 29, 37, 43, 53, 67, 89, 127, 157, 211, 277, 373, 491, 653, 877, 1153, 1543, 2039, 2711, 3607, 4793, 6379, 8501, 11279, 15013, 19949, 26539, 35291,
    46933, 62417, 83009, 110419, 146833, 195311, 259733, 345451, 459443, 611057, 812699, 1080899, 1437577, 1911977, 2542919, 3382103, 4498177, 5982577,
    7956821, 10582571, 14074807, 18719483, 24896917, 33112897, 44040163, 58573399, 77902631, 103610489, 137801941, 183276589, 243757873, 324197953, 431183287,
    574911079, 766548109, 1022064149, 1362752201, 1817002973, 2422670633, 3230227519,
];

fn set_table_size(required: u64) -> u64 {
    if required < 12 { 11 } else { SET_TABLE_SIZES.iter().copied().find(|&b| b >= required).unwrap_or(required) }
}

/// The order in which Magma iterates `Subsets({1..n}, 1)`, as 0-based
/// positions.
///
/// The singletons sit in a chained hash table with `set_table_size(n)`
/// primary buckets B and max(floor(6B/5), B + 1) - B collision nodes; {i}
/// hashes to 1 xor (27 i (i + 11) + 7) mod 2^32. When a collision finds no
/// free node, the table grows to `set_table_size(floor(3B/2))` buckets and
/// takes the old elements in their iteration order before retrying.
/// Iteration visits the buckets in turn, each followed by its chain.
fn singleton_order(n: usize) -> Vec<usize> {
    fn insert(buckets: &mut Vec<Vec<usize>>, collisions: &mut usize, i: usize) {
        let x = i as u32;
        let hash = 1 ^ 27u32.wrapping_mul(x).wrapping_mul(x.wrapping_add(11)).wrapping_add(7);
        loop {
            let b = buckets.len();
            let chain = &mut buckets[hash as usize % b];
            if chain.is_empty() {
                chain.push(i);
                return;
            }
            if *collisions < (b * 6 / 5).max(b + 1) - b {
                chain.push(i);
                *collisions += 1;
                return;
            }
            let old = buckets.concat();
            *buckets = vec![Vec::new(); set_table_size((b + b / 2) as u64) as usize];
            *collisions = 0;
            for y in old {
                insert(buckets, collisions, y);
            }
        }
    }
    let mut buckets = vec![Vec::new(); set_table_size(n as u64) as usize];
    let mut collisions = 0;
    for i in 1..=n {
        insert(&mut buckets, &mut collisions, i);
    }
    buckets.concat().into_iter().map(|i| i - 1).collect()
}

/// Square factors and pairwise coprime cofactors of each integer, using
/// only gcds and exact divisions: Lemma 2.5 of Cremona and Rusin,
/// "Efficient solution of rational conics", Math. Comp. 72 (2003).
///
/// Each subset I of the positions carries a value c_I, starting from
/// c_{i} = |a_i| with the singletons in `singleton_order`. Each sweep visits
/// the pairs I, J of subsets known when it starts; if d = gcd(c_I, c_J) > 1,
/// c_I and c_J are divided by d, c of the symmetric difference (added at the
/// end if new) is multiplied by d, and <d, 2> joins the square part of each
/// position in both I and J. Sweeps repeat until nothing changes. The
/// cofactors of position i are the values c_I > 1 with i in I, in subset
/// order.
fn partial_factorization(s: &[Integer]) -> Vec<(Fact, Fact)> {
    let n = s.len();
    let words = n.div_ceil(64);
    let has = |w: &[u64], k: usize| w[k / 64] >> (k % 64) & 1 == 1;
    let mut supports: Vec<Vec<u64>> = Vec::new();
    let mut values: Vec<Integer> = Vec::new();
    for i in singleton_order(n) {
        let mut w = vec![0u64; words];
        w[i / 64] |= 1 << (i % 64);
        supports.push(w);
        values.push(s[i].abs());
    }
    let mut index: HashMap<Vec<u64>, usize> = supports.iter().cloned().zip(0..).collect();
    let mut f: Vec<Fact> = vec![Fact::new(); n];
    loop {
        let mut changed = false;
        let m = supports.len();
        for i in 0..m {
            for j in i + 1..m {
                if values[i].is_one() {
                    break;
                }
                let d = values[i].gcd(&values[j]);
                if d.is_one() {
                    continue;
                }
                values[i] = values[i].divexact(&d);
                values[j] = values[j].divexact(&d);
                let x: Vec<u64> = supports[i].iter().zip(&supports[j]).map(|(a, b)| a ^ b).collect();
                match index.get(&x) {
                    Some(&k) => values[k] = &values[k] * &d,
                    None => {
                        index.insert(x.clone(), supports.len());
                        supports.push(x);
                        values.push(d.clone());
                    }
                }
                for k in (0..n).filter(|&k| has(&supports[i], k) && has(&supports[j], k)) {
                    match f[k].iter_mut().find(|(y, _)| *y == d) {
                        Some((_, e)) => *e += 2,
                        None => f[k].push((d.clone(), 2)),
                    }
                }
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    f.into_iter()
        .enumerate()
        .map(|(k, fk)| {
            let g = supports.iter().zip(&values).filter(|(w, c)| has(w, k) && !c.is_one()).map(|(_, c)| (c.clone(), 1)).collect();
            (fk, g)
        })
        .collect()
}

fn partial_factorization_fn(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let s = super::ints::ints_of(&a.args[0])?;
    if s.iter().any(|x| x.is_zero()) {
        return Err(RuntimeError::runtime("The integers must be non-zero"));
    }
    let out: Vec<Value> = partial_factorization(&s)
        .into_iter()
        .map(|(f, g)| Value::seq(None, vec![fact_value(&f), fact_value(&g)]))
        .collect();
    one(Value::seq(None, out))
}

// ----- Cunningham numbers ---------------------------------------------------------------------------------

/// Phi_d(b), the d-th cyclotomic polynomial at b.
fn cyclotomic_value(d: u64, b: &Integer) -> Integer {
    let mut num = Integer::one();
    let mut den = Integer::one();
    for e in super::factseq::divisors_of(&factor(&Integer::from_u64(d))) {
        let e = e.to_u64().unwrap();
        let t = &b.pow(e) - &Integer::one();
        match moebius(d / e) {
            1 => num = &num * &t,
            -1 => den = &den * &t,
            _ => {}
        }
    }
    num.divexact(&den)
}

fn moebius(n: u64) -> i32 {
    let f = factor(&Integer::from_u64(n));
    if f.iter().any(|(_, e)| *e > 1) {
        0
    } else if f.len() % 2 == 0 {
        1
    } else {
        -1
    }
}

fn cunningham(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (b, k, c) = (a.int(0)?.clone(), a.int(1)?.clone(), a.int(2)?.clone());
    if b < int(2) || b > int(1073741823) {
        return Err(arg_range(1, &b, 2, 1073741823));
    }
    if k < int(1) || k > int(10000) {
        return Err(arg_range(2, &k, 1, 10000));
    }
    if c != int(1) && c != int(-1) {
        return Err(RuntimeError::runtime("Argument 3 should be -1 or +1"));
    }
    let k = k.to_u64().unwrap();
    // b^k - 1 is the product of Phi_d(b) over d | k, and b^k + 1 that over
    // the d dividing 2k but not k.
    let ds: Vec<u64> = if c.sign() < 0 {
        super::factseq::divisors_of(&factor(&Integer::from_u64(k))).into_iter().map(|d| d.to_u64().unwrap()).collect()
    } else {
        super::factseq::divisors_of(&factor(&Integer::from_u64(2 * k))).into_iter().map(|d| d.to_u64().unwrap()).filter(|d| k % d != 0).collect()
    };
    let mut f = Fact::new();
    for d in ds {
        let v = cyclotomic_value(d, &b);
        if !v.is_one() {
            f = fact_mul(&f, &factor(&v));
        }
    }
    one(fact_value(&sorted_fact(f)))
}

pub fn register(it: &mut Interp) {
    let params = [
        ("Proof", Value::Bool(true)),
        ("Bases", Value::int(20)),
        ("TrialDivisionLimit", Value::int(10000)),
        ("SQUFOFLimit", Value::int(24)),
        ("PollardRhoLimit", Value::int(8191)),
        ("ECMLimit", Value::Undef),
        ("MPQSLimit", Value::Undef),
    ];
    for name in ["Factorization", "Factorisation"] {
        it.def_params(
            name,
            "n::RngIntElt -> RngIntEltFact, RngIntElt, SeqEnum",
            &params,
            "The prime factorization of |n|, the sign of n, and any composites left unfactored.",
            factorization,
        );
    }
    it.def("StoreFactor", "n::RngIntElt", "Store the prime n for Factorization to try first.", store_factor);
    it.def("StoreFactor", "S::[RngIntElt]", "Store the primes in S for Factorization to try first.", store_factor);
    it.def("StoreFactor", "S::{RngIntElt}", "Store the primes in S for Factorization to try first.", store_factor);
    it.def("GetStoredFactors", "-> [RngIntElt]", "The stored factors.", get_stored_factors);
    it.def("ClearStoredFactors", "", "Clear the stored factors.", clear_stored_factors);
    let pb = [("Proof", Value::Bool(true)), ("Bases", Value::int(20))];
    it.def_params(
        "TrialDivision",
        "n::RngIntElt -> RngIntEltFact, RngIntElt",
        &pb,
        "The factorization of the part of |n| made of primes up to 10000, and the rest of |n|.",
        trial_division_fn,
    );
    it.def_params(
        "TrialDivision",
        "n::RngIntElt, B::RngIntElt -> RngIntEltFact, RngIntElt",
        &pb,
        "The factorization of the part of |n| made of primes up to B, and the rest of |n|.",
        trial_division_fn,
    );
    it.def_params(
        "PollardRho",
        "n::RngIntElt -> RngIntEltFact, [RngIntElt]",
        &pb,
        "Factor n by Pollard's rho method: the factorization found and the composites left.",
        pollard_rho_fn,
    );
    it.def_params(
        "PollardRho",
        "n::RngIntElt, c::RngIntElt, s::RngIntElt, k::RngIntElt -> RngIntEltFact, [RngIntElt]",
        &pb,
        "Factor n by Pollard's rho method iterating x^2 + c k times from s.",
        pollard_rho_fn,
    );
    it.def_params("SQUFOF", "n::RngIntElt -> RngIntEltFact, [RngIntElt]", &pb, "Factor n by Shanks's square form factorization.", squfof_fn);
    it.def_params(
        "SQUFOF",
        "n::RngIntElt, k::RngIntElt -> RngIntEltFact, [RngIntElt]",
        &pb,
        "Factor n by Shanks's square form factorization with at most k iterations.",
        squfof_fn,
    );
    let pm = [("x0", Value::Undef), ("B2", Value::Undef), ("k", Value::Undef)];
    it.def_params("pMinus1", "n::RngIntElt, B1::RngIntElt -> RngIntElt", &pm, "A factor of n found by Pollard's p - 1 method, or 0.", p_minus_1_fn);
    it.def_params("pPlus1", "n::RngIntElt, B1::RngIntElt -> RngIntElt", &pm, "A factor of n found by Williams's p + 1 method, or 0.", p_plus_1_fn);
    it.def_params(
        "ECM",
        "n::RngIntElt, B1::RngIntElt -> RngIntElt, RngIntElt",
        &[("Sigma", Value::Undef), ("x0", Value::Undef), ("B2", Value::Undef), ("k", Value::int(2))],
        "A factor of n found by one elliptic curve (Suyama's parametrization), and its sigma; or 0.",
        ecm_fn,
    );
    it.def(
        "ECMSteps",
        "n::RngIntElt, L::RngIntElt, U::RngIntElt -> RngIntElt, RngIntElt",
        "A factor of n found by ECM with B1 growing from L to U, and its sigma; or 0.",
        ecm_steps,
    );
    it.def_params("MPQS", "n::RngIntElt -> RngIntEltFact, [RngIntElt]", &pb, "Factor n by the quadratic sieve.", mpqs);
    it.def("ECMOrder", "p::RngIntElt, s::RngIntElt -> RngIntElt", "The order of the ECM curve for sigma = s modulo the prime p.", ecm_order);
    it.def(
        "ECMFactoredOrder",
        "p::RngIntElt, s::RngIntElt -> RngIntEltFact",
        "The factored order of the ECM curve for sigma = s modulo the prime p.",
        ecm_factored_order,
    );
    it.def("CoprimeBasis", "S::[RngIntElt] -> RngIntEltFact", "A factorization sequence of pairwise coprime bases for the product of S.", coprime_basis_fn);
    it.def("CoprimeBasis", "S::{RngIntElt} -> RngIntEltFact", "A factorization sequence of pairwise coprime bases for the product of S.", coprime_basis_fn);
    it.def(
        "PartialFactorization",
        "S::[RngIntElt] -> [RngIntEltFact]",
        "Square factors and coprime cofactors of the integers in S, found with gcds only.",
        partial_factorization_fn,
    );
    it.def("Cunningham", "b::RngIntElt, k::RngIntElt, c::RngIntElt -> RngIntEltFact", "The factorization of b^k + c for c = 1 or -1.", cunningham);
}
