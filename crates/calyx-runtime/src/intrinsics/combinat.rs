//! Combinatorial functions of the integers.

use calyx_flint::Integer;

use super::{arg_not, intv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

fn binomial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (n, k) = (a.int(0)?.clone(), a.int(1)?.clone());
    if k.sign() < 0 {
        return intv(Integer::zero());
    }
    // As Magma does: C(n, k) = (-1)^k C(k - n - 1, k) for n < 0, and
    // C(m, k) = C(m, m - k). Results of more than 2^32 bits are refused.
    let m = if n.sign() < 0 { &(&k - &n) - 1 } else { n.clone() };
    if k > m {
        return intv(Integer::zero());
    }
    let j = std::cmp::min(k.clone(), &m - &k);
    let big = || RuntimeError::runtime("Binomial computation is too big");
    let j = j.to_u64().filter(|&j| j < 1 << 32 && j * m.bits() <= 1 << 32).ok_or_else(big)?;
    let c = (&(&m - &Integer::from_u64(j)) + 1).rising_factorial(j).divexact(&Integer::factorial(j));
    intv(if n.sign() < 0 && k.is_odd() { -c } else { c })
}

fn multinomial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int_ge(0, 0)?;
    let parts = super::ints::ints_of(&a.args[1])?;
    if parts.is_empty() {
        return Err(RuntimeError::runtime("Argument 2 has length 0: should be >= 2"));
    }
    if let Some(r) = parts.iter().find(|r| r.sign() < 0 || **r > n) {
        return Err(RuntimeError::runtime(format!("Bad multinomial argument {r}")));
    }
    if parts.iter().fold(Integer::zero(), |s, r| &s + r) != n {
        return Err(RuntimeError::runtime("Sum of elements of argument 2 does not equal argument 1"));
    }
    let small = |x: &Integer| x.to_u64().filter(|&v| v < 100_000_000).ok_or_else(|| RuntimeError::runtime("Argument is too large"));
    let mut r = Integer::factorial(small(&n)?);
    for p in &parts {
        r = r.divexact(&Integer::factorial(small(p)?));
    }
    intv(r)
}

fn factorial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.small_ge(0, 0)?;
    if n >= 100_000_000 {
        return Err(RuntimeError::runtime("Argument 1 is too large"));
    }
    intv(Integer::factorial(n))
}

fn is_factorial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?.clone();
    let no = Ok(vals![Value::Bool(false), Value::Undef]);
    if n.sign() <= 0 {
        return no;
    }
    let mut m = n;
    let mut k = 1u64;
    // Divide by 2, 3, ... while the quotient stays whole.
    loop {
        if m.is_one() {
            return Ok(vals![Value::Bool(true), Value::Int(Integer::from_u64(k.max(1)))]);
        }
        let d = Integer::from_u64(k + 1);
        if !m.is_divisible_by(&d) {
            return no;
        }
        m = m.divexact(&d);
        k += 1;
    }
}

/// The partitions of `n` into parts from `parts` (decreasing), each with
/// its parts in decreasing order, in reverse lexicographic order. `k`
/// restricts the number of parts.
fn partitions_of(n: u64, parts: &[u64], k: Option<u64>) -> Vec<Vec<u64>> {
    fn go(n: u64, parts: &[u64], k: Option<u64>, cur: &mut Vec<u64>, out: &mut Vec<Vec<u64>>) {
        if n == 0 {
            if k.is_none_or(|k| cur.len() as u64 == k) {
                out.push(cur.clone());
            }
            return;
        }
        if k.is_some_and(|k| cur.len() as u64 >= k) {
            return;
        }
        for (i, &p) in parts.iter().enumerate() {
            if p <= n {
                cur.push(p);
                go(n - p, &parts[i..], k, cur, out);
                cur.pop();
            }
        }
    }
    let mut out = Vec::new();
    go(n, parts, k, &mut Vec::new(), &mut out);
    out
}

fn partitions_value(ps: Vec<Vec<u64>>) -> Value {
    let inner = Value::structure(StructKind::PowerSeq(Some(Value::integers())));
    let elems = ps.into_iter().map(|p| Value::int_seq(p.into_iter().map(Integer::from_u64))).collect();
    Value::seq(Some(inner), elems)
}

fn partitions(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?;
    if n.sign() < 0 {
        return Err(arg_not(1, "non-negative"));
    }
    let n = n.to_u64().filter(|&n| n <= 1000).ok_or_else(|| RuntimeError::runtime("Argument 1 is too large"))?;
    let parts: Vec<u64> = (1..=n).rev().collect();
    one(partitions_value(partitions_of(n, &parts, None)))
}

fn number_of_partitions(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.small_ge(0, 0)?;
    intv(Integer::partitions(n))
}

fn restricted_partitions(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?;
    if n.sign() < 0 {
        return Err(arg_not(1, "positive"));
    }
    let n = n.to_u64().ok_or_else(|| RuntimeError::runtime("Argument 1 is too large"))?;
    let (k, set) = if a.args.len() == 3 { (Some(a.small_ge(1, 0)?), &a.args[2]) } else { (None, &a.args[1]) };
    let bad = || RuntimeError::runtime("Set elements must be positive single integers");
    let mut parts = Vec::new();
    for m in super::ints::ints_of(set)? {
        parts.push(m.to_u64().filter(|&m| m > 0 && m < 1 << 30).ok_or_else(bad)?);
    }
    parts.sort_by(|a, b| b.cmp(a));
    one(partitions_value(partitions_of(n, &parts, k)))
}

fn stirling_first(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (n, k) = (a.small_ge(0, 0)?, a.small_ge(1, 0)?);
    intv(Integer::stirling1(n, k))
}

fn stirling_second(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (n, k) = (a.small_ge(0, 0)?, a.small_ge(1, 0)?);
    intv(Integer::stirling2(n, k))
}

fn bell(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.small_ge(0, 0).map_err(super::bare)?;
    intv(Integer::bell(n))
}

/// F_n for any integer n (F_(-n) = (-1)^(n+1) F_n).
fn fibonacci_any(n: i64) -> Integer {
    let f = Integer::fibonacci(n.unsigned_abs());
    if n < 0 && n % 2 == 0 { -f } else { f }
}

/// The n-th term of the sequence with G_0 = g0, G_1 = g1 and
/// G_n = G_(n-1) + G_(n-2), for any integer n: g0 F_(n-1) + g1 F_n.
fn generalized_fibonacci(g0: &Integer, g1: &Integer, n: i64) -> Integer {
    &(g0 * &fibonacci_any(n - 1)) + &(g1 * &fibonacci_any(n))
}

fn fibonacci(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(fibonacci_any(a.small(0)?))
}

fn lucas(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.small(0)?;
    let m = n.unsigned_abs();
    let l = if m == 0 { Integer::from_i64(2) } else { &Integer::fibonacci(m - 1) + &Integer::fibonacci(m + 1) };
    intv(if n < 0 && m % 2 == 1 { -l } else { l })
}

fn generalized_fibonacci_number(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.small(2)?;
    intv(generalized_fibonacci(a.int(0)?, a.int(1)?, n))
}

pub fn register(it: &mut Interp) {
    it.def("Binomial", "n::RngIntElt, r::RngIntElt -> RngIntElt", "The binomial coefficient n choose r.", binomial);
    it.def("Multinomial", "n::RngIntElt, Q::[RngIntElt] -> RngIntElt", "The multinomial coefficient n choose Q[1], ..., Q[k].", multinomial);
    it.def("Factorial", "n::RngIntElt -> RngIntElt", "n factorial.", factorial);
    it.def("IsFactorial", "n::RngIntElt -> BoolElt, RngIntElt", "Whether n = k! for some k, and k.", is_factorial);
    it.def("Partitions", "n::RngIntElt -> [[RngIntElt]]", "The partitions of n, each in decreasing order.", partitions);
    it.def("NumberOfPartitions", "n::RngIntElt -> RngIntElt", "The number of partitions of n.", number_of_partitions);
    it.def("RestrictedPartitions", "n::RngIntElt, M::{RngIntElt} -> [[RngIntElt]]", "The partitions of n into parts from M.", restricted_partitions);
    it.def(
        "RestrictedPartitions",
        "n::RngIntElt, k::RngIntElt, M::{RngIntElt} -> [[RngIntElt]]",
        "The partitions of n into k parts from M.",
        restricted_partitions,
    );
    it.def("StirlingFirst", "n::RngIntElt, k::RngIntElt -> RngIntElt", "The (signed) Stirling number of the first kind s(n, k).", stirling_first);
    it.def("StirlingSecond", "n::RngIntElt, k::RngIntElt -> RngIntElt", "The Stirling number of the second kind S(n, k).", stirling_second);
    it.def("Bell", "n::RngIntElt -> RngIntElt", "The n-th Bell number.", bell);
    it.def("Fibonacci", "n::RngIntElt -> RngIntElt", "The n-th Fibonacci number.", fibonacci);
    it.def("Lucas", "n::RngIntElt -> RngIntElt", "The n-th Lucas number.", lucas);
    it.def(
        "GeneralizedFibonacciNumber",
        "g0::RngIntElt, g1::RngIntElt, n::RngIntElt -> RngIntElt",
        "The n-th term of the Fibonacci recursion started at g0, g1.",
        generalized_fibonacci_number,
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn partitions_are_complete_and_ordered() {
        for n in 0..=25u64 {
            let parts: Vec<u64> = (1..=n).rev().collect();
            let ps = partitions_of(n, &parts, None);
            assert_eq!(Integer::from_u64(ps.len() as u64), Integer::partitions(n), "#Partitions({n})");
            assert!(ps.iter().all(|p| p.iter().sum::<u64>() == n && p.windows(2).all(|w| w[0] >= w[1])), "Partitions({n})");
            assert!(ps.windows(2).all(|w| w[0] > w[1]), "Partitions({n}) in reverse lexicographic order");
            for k in 0..=n {
                assert_eq!(partitions_of(n, &parts, Some(k)).len(), ps.iter().filter(|p| p.len() as u64 == k).count(), "Partitions({n}, {k})");
            }
        }
        // Parts from a set: the coefficients of 1/((1 - x^7)(1 - x^5)(1 - x^3)).
        let parts = [7u64, 5, 3];
        let mut ways = [0usize; 61];
        ways[0] = 1;
        for p in parts {
            for i in p as usize..=60 {
                ways[i] += ways[i - p as usize];
            }
        }
        for n in 0..=60 {
            assert_eq!(partitions_of(n, &parts, None).len(), ways[n as usize], "RestrictedPartitions({n}, {{3, 5, 7}})");
        }
    }

    #[test]
    fn fibonacci_numbers_follow_the_recurrence_both_ways() {
        let int = Integer::from_i64;
        assert_eq!([-2, -1, 0, 1, 2].map(fibonacci_any), [-1, 1, 0, 1, 1].map(int));
        let (g0, g1) = (int(3), int(-7));
        assert_eq!((generalized_fibonacci(&g0, &g1, 0), generalized_fibonacci(&g0, &g1, 1)), (g0.clone(), g1.clone()));
        for n in -80..=80 {
            assert_eq!(fibonacci_any(n + 2), &fibonacci_any(n + 1) + &fibonacci_any(n), "Fibonacci({n})");
            assert_eq!(generalized_fibonacci(&g0, &g1, n + 2), &generalized_fibonacci(&g0, &g1, n + 1) + &generalized_fibonacci(&g0, &g1, n), "G({n})");
        }
    }
}
