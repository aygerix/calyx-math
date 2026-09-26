//! Nearfields (#43): the regular nearfields of Dickson.
//!
//! A nearfield has the elements and the addition of a finite field K; only
//! the multiplication differs, and it is right distributive. In the
//! Dickson nearfield of the pair (q, v), with z a primitive element of
//! K = GF(q^v), w * u = w^(q^i) u for u in the coset z^((q^i - 1)/(q - 1))
//! <z^v> of the v-th powers, as the handbook describes. With Zech
//! logarithms that is arithmetic on the logarithms.

use std::rc::Rc;

use calyx_flint::gr::{Elem, Truth};
use calyx_flint::{Integer, Nmod};
use calyx_syntax::ast::BinOp;

use super::{boolv, intv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::rings::finite::{self, field_of};
use crate::rings::make_elt;
use crate::sym::Sym;
use crate::types::{TypeId, t};
use crate::value::*;

// ----- nearfields and their elements ---------------------------------------------------------

pub struct Nearfield {
    pub kind: NfdKind,
    /// The finite field of the elements.
    pub gf: Rc<Struct>,
    twist: Twist,
}

pub enum NfdKind {
    /// The pair (q, v) with q = p^h, the variant s modulo v (0 when v = 1),
    /// and the exponent e of the primitive element z = z0^e (z0 that of K,
    /// and e = s modulo v).
    Dickson { p: Integer, h: u64, q: Integer, v: u64, s: u64, e: Integer },
}

/// How multiplication differs from that of the field.
enum Twist {
    /// Not at all (v = 1).
    Field,
    /// w * u = w^(q^i) u with i = frob[k], for k the residue of log_z(u)
    /// modulo v.
    Frobenius { h: u64, frob: Vec<u64>, residue: Residue },
}

/// The residue of log_z(u) modulo v.
enum Residue {
    /// With Zech logarithms L to the base z0: L einv modulo v. Also q^i
    /// modulo q^v - 1 for each i, to apply the Frobenius to logarithms.
    Zech { v: u64, einv: u64, qm1: u64, qpow: Vec<u64> },
    /// Otherwise u^m is omega^k, for m = (q^v - 1)/v and omega = z^m.
    Power { m: Integer, omegas: Vec<Elem> },
}

/// An element of a nearfield: an element of its field.
pub struct NfdElt {
    pub parent: Rc<Struct>,
    pub x: Elem,
}

impl Nearfield {
    pub fn order(&self) -> Integer {
        field_of(&self.gf).expect("a finite field").1.order()
    }

    pub fn type_id(&self) -> TypeId {
        match self.kind {
            NfdKind::Dickson { .. } => t::NFD_DCK,
        }
    }

    /// Whether `self` and `other` are equal, as Magma's `eq` has it: the same
    /// Dickson pair and the same variant modulo v. (Variants of one class
    /// give isomorphic nearfields, but not equal ones.)
    pub fn same_as(&self, other: &Nearfield) -> bool {
        match (&self.kind, &other.kind) {
            (NfdKind::Dickson { q, v, s, .. }, NfdKind::Dickson { q: q2, v: v2, s: s2, .. }) => q == q2 && v == v2 && s == s2,
        }
    }

    pub fn hash_key(&self) -> (u64, Integer, u64) {
        match &self.kind {
            NfdKind::Dickson { q, v, s, .. } => (*v, q.clone(), *s),
        }
    }

    /// The index i of the Frobenius x -> x^(q^i) by which u twists.
    fn frob_index(&self, u: &Elem) -> RResult<u64> {
        let Twist::Frobenius { frob, residue, .. } = &self.twist else { return Ok(0) };
        let k = match residue {
            Residue::Zech { v, einv, .. } => (u.zech_log().expect("a unit") % v) * einv % v,
            Residue::Power { m, omegas } => {
                let c = u.pow(m)?;
                omegas.iter().position(|w| w.equal(&c) == Truth::True).expect("a v-th root of unity") as u64
            }
        };
        Ok(frob[k as usize])
    }

    /// w^(q^i).
    fn frobenius(&self, w: &Elem, i: u64) -> RResult<Elem> {
        let Twist::Frobenius { h, residue, .. } = &self.twist else { return Ok(w.clone()) };
        if i == 0 || is_zero(w) {
            return Ok(w.clone());
        }
        Ok(match residue {
            Residue::Zech { qm1, qpow, .. } => {
                let l = w.zech_log().expect("a unit") * qpow[i as usize] % qm1;
                Elem::fq_from_zech_log(w.ctx(), l).expect("a logarithm")
            }
            Residue::Power { .. } => w.fq_frobenius((h * i) as i64)?,
        })
    }

    /// w * u.
    pub fn mul(&self, w: &Elem, u: &Elem) -> RResult<Elem> {
        if is_zero(w) || is_zero(u) {
            return Ok(Elem::zero(w.ctx()));
        }
        if let (Twist::Frobenius { residue: Residue::Zech { qm1, qpow, .. }, .. }, Some(lw), Some(lu)) = (&self.twist, w.zech_log(), u.zech_log()) {
            let i = self.frob_index(u)?;
            return Ok(Elem::fq_from_zech_log(w.ctx(), (lw * qpow[i as usize] + lu) % qm1).expect("a logarithm"));
        }
        let i = self.frob_index(u)?;
        Ok(self.frobenius(w, i)?.mul(u)?)
    }

    /// The inverse of a unit u: w with w * u = 1, so w^(q^i) = 1/u.
    pub fn inverse(&self, u: &Elem) -> RResult<Elem> {
        let i = self.frob_index(u)?;
        let w = u.inv()?;
        match &self.twist {
            Twist::Frobenius { frob, .. } => {
                let v = frob.len() as u64;
                self.frobenius(&w, (v - i) % v)
            }
            Twist::Field => Ok(w),
        }
    }

    /// x^n, for n of any sign (x a unit if n < 0).
    pub fn pow(&self, x: &Elem, n: &Integer) -> RResult<Elem> {
        let ctx = x.ctx();
        if n.is_zero() {
            return Ok(Elem::one(ctx)?);
        }
        if is_zero(x) {
            if n.sign() < 0 {
                return Err(no_inverse());
            }
            return Ok(x.clone());
        }
        let (base, n) = if n.sign() < 0 { (self.inverse(x)?, -n) } else { (x.clone(), n.clone()) };
        // The units form a group of order q^v - 1.
        let n = n.div_rem_euclid(&(&self.order() - &Integer::one())).map(|(_, r)| r).unwrap_or(n);
        let mut r = Elem::one(ctx)?;
        for i in (0..n.bits()).rev() {
            r = self.mul(&r, &r)?;
            if n.fdiv_2exp(i).is_odd() {
                r = self.mul(&r, &base)?;
            }
        }
        Ok(r)
    }

    /// The order of the unit x in the group of units.
    pub fn unit_order(&self, x: &Elem) -> RResult<Integer> {
        let mut n = &self.order() - &Integer::one();
        for (l, e) in finite::qm1_factors(&self.gf) {
            for _ in 0..*e {
                let m = n.divexact(l);
                if self.pow(x, &m)?.is_one() != Truth::True {
                    break;
                }
                n = m;
            }
        }
        Ok(n)
    }
}

fn is_zero(x: &Elem) -> bool {
    x.is_zero() == Truth::True
}

/// Magma's error for the inverse of zero, from the `Inverse` that division
/// and powers call.
fn no_inverse() -> RuntimeError {
    RuntimeError::runtime("Cannot invert the zero element").in_context("Inverse")
}

/// Whether x and y lie in the same nearfield: equal nearfields count as one.
fn same_parent(x: &NfdElt, y: &NfdElt) -> bool {
    Rc::ptr_eq(&x.parent, &y.parent) || nfd(&x.parent).same_as(nfd(&y.parent))
}

fn not_same() -> RuntimeError {
    super::bare(RuntimeError::runtime("Elements must belong to the same nearfield"))
}

/// `x eq y` for elements of nearfields.
pub fn nfd_equal(x: &NfdElt, y: &NfdElt) -> RResult<bool> {
    if !same_parent(x, y) {
        return Err(not_same());
    }
    Ok(x.x.equal(&y.x) == Truth::True)
}

const CARRIER: &str = "Finite field element is not in the carrier set of the nearfield";

/// The nearfield of a nearfield structure.
pub fn nearfield_of(st: &Struct) -> Option<&Rc<Nearfield>> {
    match &st.kind {
        StructKind::Nearfield(n) => Some(n),
        _ => None,
    }
}

fn nfd(st: &Struct) -> &Rc<Nearfield> {
    nearfield_of(st).expect("a nearfield")
}

fn elt(st: &Rc<Struct>, x: Elem) -> Value {
    Value::Nfd(Rc::new(NfdElt { parent: st.clone(), x }))
}

/// The element of the field that a nearfield element is.
pub fn as_field_value(x: &NfdElt) -> Value {
    make_elt(&nfd(&x.parent).gf, x.x.clone())
}

pub fn negate(x: &NfdElt) -> RResult<Value> {
    Ok(elt(&x.parent, x.x.neg()?))
}

/// How a nearfield prints: its kind, name (`$` if it has none) and order.
pub fn describe(s: &Struct) -> [String; 2] {
    let n = nfd(s);
    let name = s.name.borrow().map(|n| n.to_string()).unwrap_or_else(|| "$".to_string());
    match &n.kind {
        NfdKind::Dickson { q, v, .. } => [format!("Nearfield {name} of Dickson type defined by the pair ({q}, {v})"), format!("Order = {}", n.order())],
    }
}

impl Interp {
    /// Operators with an element of a nearfield among the operands. Elements
    /// meet only elements of the same nearfield, and integers only as
    /// exponents and (lying in the kernel) as scalars.
    pub fn nfd_binop(&mut self, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
        use BinOp::*;
        let arith = matches!(op, Add | Sub | Mul | Div | Pow | Eq | Ne | Lt | Le | Gt | Ge);
        match (a, b) {
            (Value::Nfd(x), Value::Nfd(y)) if arith => {
                if !same_parent(x, y) {
                    return Err(not_same());
                }
                let n = nfd(&x.parent).clone();
                let r = match op {
                    Add => x.x.add(&y.x)?,
                    Sub => x.x.sub(&y.x)?,
                    Mul => n.mul(&x.x, &y.x)?,
                    Div | Pow if is_zero(&y.x) => return Err(no_inverse()),
                    Div => n.mul(&x.x, &n.inverse(&y.x)?)?,
                    // x^y = y^-1 x y.
                    Pow => n.mul(&n.mul(&n.inverse(&y.x)?, &x.x)?, &y.x)?,
                    Eq => return Ok(Some(Value::Bool(nfd_equal(x, y)?))),
                    Ne => return Ok(Some(Value::Bool(!nfd_equal(x, y)?))),
                    _ => return Err(RuntimeError::runtime("No comparison algorithm exists for given objects").in_context(op.intrinsic_name())),
                };
                Ok(Some(elt(&x.parent, r)))
            }
            (Value::Nfd(x), Value::Int(n)) if op == Pow => Ok(Some(elt(&x.parent, nfd(&x.parent).pow(&x.x, n)?))),
            (Value::Nfd(x), Value::Int(_)) | (Value::Int(_), Value::Nfd(x)) if op == Mul => {
                let c = if let Value::Int(_) = a { a } else { b };
                let Ok(Value::Nfd(c)) = self.coerce_into_nearfield(&x.parent, c, false)? else { return Ok(None) };
                Ok(Some(elt(&x.parent, x.x.mul(&c.x)?)))
            }
            _ if arith => Err(self.bad_types(op, a, b)),
            _ => Ok(None),
        }
    }

    /// `N ! x`: an element of N (or of a nearfield equal to N), or of its
    /// field, or something that coerces into the field (as `Element(N, x)`
    /// does for field elements). Only `!` (`strict`) reports field elements
    /// outside the carrier; coercions into universes just fail.
    pub fn coerce_into_nearfield(&mut self, st: &Rc<Struct>, x: &Value, strict: bool) -> RResult<Result<Value, Option<String>>> {
        match x {
            Value::Nfd(e) if Rc::ptr_eq(&e.parent, st) || nfd(&e.parent).same_as(nfd(st)) => Ok(Ok(elt(st, e.x.clone()))),
            Value::Nfd(_) => Ok(Err(None)),
            _ => {
                let gf = Value::Struct(nfd(st).gf.clone());
                let is_ff = matches!(crate::rings::small::elt_of(x), Some(e) if field_of(&e.parent).is_some());
                // (Rationals such as 1/p fail with an error of their own.)
                let into_gf = match self.try_coerce(&gf, x) {
                    Err(e) if e.kind == crate::error::ErrKind::Interrupt => return Err(e),
                    Err(_) => Err(None),
                    Ok(r) => r,
                };
                match into_gf {
                    Ok(v) => match crate::rings::small::elt_of(&v) {
                        Some(e) => Ok(Ok(elt(st, e.x.clone()))),
                        None => Ok(Err(None)),
                    },
                    Err(_) if is_ff && strict => Err(RuntimeError::runtime(CARRIER).in_context("Element")),
                    Err(_) => Ok(Err(None)),
                }
            }
        }
    }

    /// `x in N` for a nearfield N: whether x is an element of N (or of a
    /// nearfield equal to N).
    pub fn nfd_contains(&mut self, st: &Rc<Struct>, x: &Value) -> RResult<bool> {
        Ok(matches!(x, Value::Nfd(e) if Rc::ptr_eq(&e.parent, st) || nfd(&e.parent).same_as(nfd(st))))
    }

    /// Magma does not iterate over nearfields.
    pub fn enumerate_nearfield(&mut self, _st: &Rc<Struct>) -> RResult<Vec<Value>> {
        Err(RuntimeError::runtime(crate::error::NOT_ITERABLE))
    }
}

/// Whether a and b are different nearfield objects: Magma's aggregates find
/// no common universe for them, even when they are equal.
pub fn distinct_nearfields(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Struct(x), Value::Struct(y)) => {
            matches!((&x.kind, &y.kind), (StructKind::Nearfield(_), StructKind::Nearfield(_))) && !Rc::ptr_eq(x, y)
        }
        _ => false,
    }
}

// ----- Dickson pairs ----------------------------------------------------------------------------

/// The prime factors of n.
fn prime_factors(mut n: u64) -> Vec<u64> {
    let mut out = Vec::new();
    let mut d = 2;
    while d * d <= n {
        if n % d == 0 {
            out.push(d);
            while n % d == 0 {
                n /= d;
            }
        }
        d += 1;
    }
    if n > 1 {
        out.push(n);
    }
    out
}

/// Whether (q, v) is a Dickson pair, with the errors of the Magma functions
/// that decide it (`IsPrimePower` for q < 2, `PrimeBasis` for v = 0): q is
/// a prime power, every prime factor of v divides q - 1, and 4 divides
/// q - 1 if it divides v. (Magma lets v be negative.)
fn dickson_pair(q: &Integer, v: i64) -> RResult<bool> {
    if q < &Integer::from_u64(2) {
        return Err(RuntimeError::runtime(format!("Argument 1 ({q}) should be >= 2")).in_context("IsPrimePower"));
    }
    if v == 0 {
        return Err(RuntimeError::runtime("Argument 1 is not non-zero").in_context("PrimeBasis"));
    }
    if prime_power(q).is_none() {
        return Ok(false);
    }
    let q1 = q - &Integer::one();
    let w = v.unsigned_abs();
    Ok(prime_factors(w).iter().all(|&r| q1.mod_u64(r) == 0) && (w % 4 != 0 || q1.mod_u64(4) == 0))
}

/// q = p^h with p prime and h >= 1, or `None`.
fn prime_power(q: &Integer) -> Option<(Integer, u64)> {
    if q <= &Integer::one() {
        return None;
    }
    let fac = q.factor()?.factors;
    match &fac[..] {
        [(p, h)] => Some((p.clone(), *h)),
        _ => None,
    }
}

/// x^k modulo m.
fn pow_mod(x: u64, mut k: u64, m: u64) -> u64 {
    let (mut r, mut b) = (1 % m, x % m);
    while k > 0 {
        if k & 1 == 1 {
            r = (r as u128 * b as u128 % m as u128) as u64;
        }
        b = (b as u128 * b as u128 % m as u128) as u64;
        k >>= 1;
    }
    r
}

/// Generators of the units modulo v with their orders, as Magma's unit
/// group has them: for each prime power l^k of v in turn, the least
/// primitive root (-1 and then 5 for 2^k, k >= 3), lifted to 1 modulo the
/// rest of v.
fn unit_generators(v: u64) -> Vec<(u64, u64)> {
    let mut gens = Vec::new();
    for l in prime_factors(v) {
        let mut lk = 1;
        while v % (lk * l) == 0 {
            lk *= l;
        }
        let rest = v / lk;
        // g modulo l^k and 1 modulo the rest.
        let lift = |g: u64| {
            let t = (g + lk - 1) % lk * Nmod::new(lk).inv(rest % lk).expect("coprime") % lk;
            1 + rest * t
        };
        if l == 2 {
            if lk == 4 {
                gens.push((lift(3), 2));
            } else if lk >= 8 {
                gens.push((lift(lk - 1), 2));
                gens.push((lift(5), lk / 4));
            }
            continue;
        }
        let phi = lk / l * (l - 1);
        let primes = prime_factors(phi);
        let g = (2..lk).find(|&g| g % l != 0 && primes.iter().all(|&r| pow_mod(g, phi / r, lk) != 1)).expect("a primitive root");
        gens.push((lift(g), phi));
    }
    gens
}

/// Representatives of the variants of the Dickson triple (p, h, v): the
/// units modulo v up to multiplication by powers of p, each by the first
/// member met when the units run through the products of powers of
/// `unit_generators`, the power of the first generator the fastest.
fn variant_reps(p: &Integer, v: u64) -> Vec<u64> {
    if v == 1 {
        return vec![1];
    }
    let gens = unit_generators(v);
    let pm = p.mod_u64(v);
    let mut seen = vec![false; v as usize];
    let mut reps = Vec::new();
    let mut exps = vec![0; gens.len()];
    loop {
        let x = gens.iter().zip(&exps).fold(1, |x, (&(g, _), &e)| (x as u128 * pow_mod(g, e, v) as u128 % v as u128) as u64);
        if !seen[x as usize] {
            reps.push(x);
            let mut y = x;
            while !seen[y as usize] {
                seen[y as usize] = true;
                y = (y as u128 * pm as u128 % v as u128) as u64;
            }
        }
        let Some(i) = (0..gens.len()).find(|&i| exps[i] + 1 < gens[i].1) else { return reps };
        exps[i] += 1;
        exps[..i].iter_mut().for_each(|e| *e = 0);
    }
}

/// A bound of the ranges that the pair functions run through.
fn bound_arg(a: &CallArgs, i: usize) -> RResult<i64> {
    let n = a.int(i)?;
    n.to_i64().filter(|n| n.unsigned_abs() < 1 << 30).ok_or_else(|| RuntimeError::runtime(format!("Argument {} ({n}) is not small", i + 1)))
}

/// Argument 1, a prime (up to sign, as Magma's `IsPrime` has it).
fn prime_arg(a: &CallArgs) -> RResult<Integer> {
    let p = a.int(0)?.clone();
    if !p.abs().is_prime() {
        return Err(RuntimeError::runtime("p must be prime"));
    }
    Ok(p)
}

/// The Dickson pairs (p^h, v), with h and v running through their ranges.
fn dickson_pairs_in(p: &Integer, hs: std::ops::RangeInclusive<i64>, vs: std::ops::RangeInclusive<i64>) -> RResult<Value> {
    let mut out = Vec::new();
    for h in hs {
        if h < 0 {
            return Err(RuntimeError::runtime("Bad argument types\nArgument types given: FldRatElt").in_context("IsPrimePower"));
        }
        let q = p.pow(h as u64);
        for v in vs.clone() {
            if dickson_pair(&q, v)? {
                out.push(Value::seq(None, vec![Value::Int(q.clone()), Value::Int(Integer::from_i64(v))]));
            }
        }
    }
    Ok(Value::seq(None, out))
}

fn dickson_pairs(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = prime_arg(a).map_err(super::bare)?;
    let (hlo, hhi, vlo, vhi) = (bound_arg(a, 1)?, bound_arg(a, 2)?, bound_arg(a, 3)?, bound_arg(a, 4)?);
    one(dickson_pairs_in(&p, hlo..=hhi, vlo..=vhi)?)
}

fn dickson_pairs_bounded(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = prime_arg(a)?;
    one(dickson_pairs_in(&p, 1..=bound_arg(a, 1)?, 1..=bound_arg(a, 2)?)?)
}

fn dickson_triples(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = prime_arg(a).map_err(super::bare)?;
    let (hb, vb) = (bound_arg(a, 1)?, bound_arg(a, 2)?);
    let mut out = Vec::new();
    for h in 1..=hb {
        let q = p.pow(h as u64);
        for v in 1..=vb {
            if dickson_pair(&q, v)? {
                let t = [p.clone(), Integer::from_i64(h), Integer::from_i64(v)];
                out.push(Value::seq(None, t.into_iter().map(Value::Int).collect()));
            }
        }
    }
    one(Value::seq(None, out))
}

/// The Dickson pair (q, v) of arguments 1 and 2, with the prime and the
/// exponent of q; v may be negative.
fn pair_args(a: &CallArgs) -> RResult<(Integer, u64, Integer, i64)> {
    let q = a.int(0)?.clone();
    let v = a.int(1)?.to_i64().filter(|v| v.unsigned_abs() < 1 << 30).ok_or_else(|| RuntimeError::runtime("Argument 2 is not small"))?;
    if !dickson_pair(&q, v)? {
        return Err(super::bare(RuntimeError::runtime(format!("({q}, {v}) is not a Dickson pair"))));
    }
    let (p, h) = prime_power(&q).expect("a prime power");
    Ok((p, h, q, v))
}

fn number_of_variants(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (p, _, _, v) = pair_args(a)?;
    if v < 0 {
        return Err(RuntimeError::runtime("Argument 1 is not positive").in_context("EulerPhi"));
    }
    intv(Integer::from_u64(variant_reps(&p, v as u64).len() as u64))
}

fn number_of_variants_n(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = nfd_arg(a, 0)?;
    let NfdKind::Dickson { p, v, .. } = &nfd(&st).kind;
    intv(Integer::from_u64(variant_reps(p, *v).len() as u64))
}

fn variant_representatives(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (p, _, _, v) = pair_args(a)?;
    if v < 0 {
        return Err(RuntimeError::runtime(format!("Argument 1 ({v}) should be >= 2")).in_context("ResidueClassRing"));
    }
    one(Value::seq(None, variant_reps(&p, v as u64).into_iter().map(|s| Value::Int(Integer::from_u64(s))).collect()))
}

// ----- construction ----------------------------------------------------------------------------

/// The exponent e of the primitive element z0^e for the variant s (reduced
/// modulo v), as Magma picks it: 1 for s = 1, else s + N/m for N = q^v - 1
/// and m the product over the prime powers l^a of N of l^a if l divides s,
/// else of l^(a - 1 - b) for l^b the power of l in v. That is prime to N
/// and s modulo v.
fn variant_exponent(s: u64, v: u64, n: &Integer, factors: &[(Integer, u64)]) -> Integer {
    if s <= 1 {
        return Integer::one();
    }
    let mut m = Integer::one();
    for (l, a) in factors {
        let small = l.to_u64();
        let k = if small.is_some_and(|l| s % l == 0) {
            *a
        } else {
            let mut b = 0;
            if let Some(l) = small {
                let mut w = v;
                while w % l == 0 {
                    w /= l;
                    b += 1;
                }
            }
            a.saturating_sub(1 + b)
        };
        m = &m * &l.pow(k);
    }
    let e = &Integer::from_u64(s) + &n.divexact(&m);
    e.div_rem_euclid(n).map(|(_, r)| r).unwrap_or(e)
}

fn dickson_nearfield(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (p, h, q, v) = pair_args(a)?;
    if v < 0 {
        return Err(super::bare(RuntimeError::runtime("Bad argument types\nArgument types given: FldRatElt, FldRatElt")));
    }
    let v = v as u64;
    let s = match a.param("Variant").cloned() {
        Some(x) => match it.coerce(&Value::integers(), &x).map_err(|e| e.in_context("!"))? {
            Value::Int(s) => s,
            _ => return Err(RuntimeError::runtime("Bad argument types")),
        },
        None => Integer::one(),
    };
    if !s.gcd(&Integer::from_u64(v)).is_one() {
        return Err(super::bare(RuntimeError::runtime("Variant must be coprime to v")));
    }
    if a.param("LargeMatrices").is_some_and(|x| !matches!(x, Value::Bool(_))) {
        return Err(super::bare(RuntimeError::runtime("Expected a logical for the 'select' operator")));
    }
    let s = s.mod_u64(v);
    let gf = it.default_field(&p, h * v)?;
    let qm1 = &field_of(&gf).expect("a finite field").1.order() - &Integer::one();
    let e = if s <= 1 { Integer::one() } else { variant_exponent(s, v, &qm1, finite::qm1_factors(&gf)) };
    let ctx = field_of(&gf).expect("a finite field").0.ctx.clone();
    let z0 = it.ff_primitive(&gf)?;
    let z = z0.pow(&e)?;
    // frob[(q^i - 1)/(q - 1) mod v] = i mod v, for 1 <= i <= v.
    let qv_mod = q.mod_u64(v);
    let mut frob = vec![u64::MAX; v as usize];
    let mut c = 1 % v;
    for i in 1..=v {
        frob[c as usize] = i % v;
        c = (c * qv_mod + 1) % v;
    }
    let twist = if v == 1 {
        Twist::Field
    } else {
        let residue = match (Elem::zech_order(&ctx), z0.zech_log()) {
            (Some(qm1), Some(1)) => {
                let einv = Nmod::new(v).inv(e.mod_u64(v)).expect("a unit modulo v");
                let qq = q.mod_u64(qm1);
                let mut qpow = Vec::with_capacity(v as usize);
                let mut x = 1 % qm1;
                for _ in 0..v {
                    qpow.push(x);
                    x = x * qq % qm1;
                }
                Residue::Zech { v, einv, qm1, qpow }
            }
            _ => {
                let m = qm1.divexact(&Integer::from_u64(v));
                let omega = z.pow(&m)?;
                let mut omegas = vec![Elem::one(&ctx)?];
                for _ in 1..v {
                    let w = omegas.last().unwrap().mul(&omega)?;
                    omegas.push(w);
                }
                Residue::Power { m, omegas }
            }
        };
        Twist::Frobenius { h, frob: frob.clone(), residue }
    };
    // Magma's attributes: the Frobenius index for each residue of the
    // logarithm (v for 0) and the power of q it raises to.
    let twists: Vec<u64> = frob.iter().map(|&i| if i == 0 { v } else { i }).collect();
    let int = |n: u64| Value::Int(Integer::from_u64(n));
    let rho = Value::seq(None, twists.iter().map(|&i| Value::Int(q.pow(i))).collect());
    let twist_seq = Value::seq(None, twists.iter().map(|&i| int(i)).collect());
    let attrs = [
        ("gf", Value::Struct(gf.clone())),
        ("h", int(h)),
        ("p", Value::Int(p.clone())),
        ("q", Value::Int(q.clone())),
        ("v", int(v)),
        ("sz", Value::Int(q.clone())),
        ("rho", rho),
        ("twist", twist_seq),
        ("prim", make_elt(&gf, z)),
    ];
    let kind = NfdKind::Dickson { p, h, q, v, s, e };
    let n = Nearfield { kind, gf: gf.clone(), twist };
    let st = Struct::new(StructKind::Nearfield(Rc::new(n)));
    st.attrs.borrow_mut().extend(attrs.into_iter().map(|(k, x)| (Sym::new(k), x)));
    one(Value::Struct(st))
}

// ----- elements --------------------------------------------------------------------------------

fn nfd_arg(a: &CallArgs, i: usize) -> RResult<Rc<Struct>> {
    match &a.args[i] {
        Value::Struct(st) if nearfield_of(st).is_some() => Ok(st.clone()),
        _ => Err(RuntimeError::runtime("Bad argument types")),
    }
}

fn nfd_elt_arg(a: &CallArgs, i: usize) -> RResult<Rc<NfdElt>> {
    match &a.args[i] {
        Value::Nfd(x) => Ok(x.clone()),
        _ => Err(RuntimeError::runtime("Bad argument types")),
    }
}

fn element(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = nfd_arg(a, 0)?;
    let x = a.args[1].clone();
    match it.coerce_into_nearfield(&st, &x, true) {
        Ok(Ok(v)) => one(v),
        Ok(Err(e)) => Err(RuntimeError::runtime(e.unwrap_or_else(|| "Illegal coercion".to_string()))),
        // Called directly, Magma's `Element` does not name itself.
        Err(e) if e.message == CARRIER => Err(super::bare(RuntimeError::runtime(CARRIER))),
        Err(e) => Err(e),
    }
}

/// `IsCoercible(N, x)`, which gives Magma's reason when x does not coerce.
fn is_coercible(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (n, x) = (a.args[0].clone(), a.args[1].clone());
    match it.try_coerce(&n, &x)? {
        Ok(v) => Ok(vals![Value::Bool(true), v]),
        Err(_) => Ok(vals![Value::Bool(false), Value::str("Illegal coercion")]),
    }
}

fn eltseq(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = nfd_elt_arg(a, 0)?;
    one(it.call_intrinsic_named(Sym::new("Eltseq"), vec![as_field_value(&x)])?)
}

fn inverse(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = nfd_elt_arg(a, 0)?;
    if is_zero(&x.x) {
        return Err(super::bare(RuntimeError::runtime("Cannot invert the zero element")));
    }
    one(elt(&x.parent, nfd(&x.parent).inverse(&x.x)?))
}

fn order(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = nfd_elt_arg(a, 0)?;
    if is_zero(&x.x) {
        return Err(super::bare(RuntimeError::runtime("Attempting to find the order of a non-unit")));
    }
    intv(nfd(&x.parent).unit_order(&x.x)?)
}

fn is_zero_n(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(is_zero(&nfd_elt_arg(a, 0)?.x))
}

fn is_unit(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(!is_zero(&nfd_elt_arg(a, 0)?.x))
}

fn is_identity(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(nfd_elt_arg(a, 0)?.x.is_one() == Truth::True)
}

// ----- nearfields ------------------------------------------------------------------------------

fn cardinality(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = nfd_arg(a, 0)?;
    intv(nfd(&st).order())
}

fn identity(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = nfd_arg(a, 0)?;
    let ctx = field_of(&nfd(&st).gf).expect("a finite field").0.ctx.clone();
    one(elt(&st, Elem::one(&ctx)?))
}

fn zero(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = nfd_arg(a, 0)?;
    let ctx = field_of(&nfd(&st).gf).expect("a finite field").0.ctx.clone();
    one(elt(&st, Elem::zero(&ctx)))
}

fn random(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = nfd_arg(a, 0)?;
    let x = it.call_intrinsic_named(Sym::new("Random"), vec![Value::Struct(nfd(&st).gf.clone())])?;
    let e = crate::rings::small::elt_of(&x).expect("a field element");
    one(elt(&st, e.x.clone()))
}

fn prime_field(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = nfd_arg(a, 0)?;
    let NfdKind::Dickson { p, .. } = &nfd(&st).kind;
    let p = p.clone();
    one(Value::Struct(it.default_field(&p, 1)?))
}

/// The kernel of a Dickson nearfield is its centre, GF(q).
fn kernel(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = nfd_arg(a, 0)?;
    let NfdKind::Dickson { p, h, .. } = &nfd(&st).kind;
    let (p, h) = (p.clone(), *h);
    one(Value::Struct(it.default_field(&p, h)?))
}

pub fn register(it: &mut Interp) {
    // Magma's attributes of nearfields and their elements.
    let dickson = ["gf", "h", "matgrp", "p", "phi", "prim", "psi", "q", "rho", "sz", "twist", "v"];
    let zassenhaus = ["gf", "matgrp", "mu", "ndx", "p", "phi", "prim", "psi", "q", "sz"];
    let attrs: [(_, &[&str]); 4] = [(t::NFD, &dickson[..]), (t::NFD_DCK, &dickson), (t::NFD_ZSS, &zassenhaus), (t::NFD_ELT, &["elt", "log", "parent"])];
    for (ty, names) in attrs {
        for name in names {
            if ty != t::NFD || !["h", "rho", "twist", "v"].contains(name) {
                it.types.add_attribute(ty, Sym::new(name));
            }
        }
    }
    let pairs = "The Dickson pairs (p^h, v) for hlo <= h <= hhi and vlo <= v <= vhi.";
    it.def("DicksonPairs", "p::RngIntElt, hlo::RngIntElt, hhi::RngIntElt, vlo::RngIntElt, vhi::RngIntElt -> SeqEnum", pairs, dickson_pairs);
    it.def("DicksonPairs", "p::RngIntElt, h1::RngIntElt, v1::RngIntElt -> SeqEnum", "The Dickson pairs (p^h, v) for h <= h1 and v <= v1.", dickson_pairs_bounded);
    it.def("DicksonTriples", "p::RngIntElt, hb::RngIntElt, vb::RngIntElt -> SeqEnum", "The Dickson triples (p, h, v) for h <= hb and v <= vb.", dickson_triples);
    it.def("NumberOfVariants", "q::RngIntElt, v::RngIntElt -> RngIntElt", "The number of Dickson nearfields with the pair (q, v).", number_of_variants);
    it.def("NumberOfVariants", "N::NfdDck -> RngIntElt", "The number of variants of the Dickson nearfield N.", number_of_variants_n);
    it.def("VariantRepresentatives", "q::RngIntElt, v::RngIntElt -> SeqEnum", "Representatives of the variants of the pair (q, v).", variant_representatives);
    it.def_params(
        "DicksonNearfield",
        "q::RngIntElt, v::RngIntElt -> NfdDck",
        &[("Variant", Value::int(1)), ("LargeMatrices", Value::Bool(false))],
        "The Dickson nearfield of the pair (q, v).",
        dickson_nearfield,
    );

    it.def("Element", "N::Nfd, x::FldFinElt -> NfdElt", "The element x of the field of N as an element of N.", element);
    it.def("IsCoercible", "N::Nfd, x::. -> BoolElt, .", "Whether x can be coerced into N, and the result or the reason it cannot.", is_coercible);
    for name in ["ElementToSequence", "Eltseq"] {
        it.def(name, "x::NfdElt -> SeqEnum", "The coefficients of x as an element of its field.", eltseq);
    }
    it.def("Inverse", "a::NfdElt -> NfdElt", "The inverse of a.", inverse);
    it.def("Order", "x::NfdElt -> RngIntElt", "The order of the unit x.", order);
    it.def("IsZero", "a::NfdElt -> BoolElt", "Whether a is zero.", is_zero_n);
    it.def("IsUnit", "a::NfdElt -> BoolElt", "Whether a is a unit.", is_unit);
    it.def("IsIdentity", "a::NfdElt -> BoolElt", "Whether a is the identity.", is_identity);

    it.def("Cardinality", "N::Nfd -> RngIntElt", "The number of elements of N.", cardinality);
    it.def("Identity", "N::Nfd -> NfdElt", "The identity of N.", identity);
    it.def("Zero", "N::Nfd -> NfdElt", "The zero of N.", zero);
    it.def("Random", "N::Nfd -> NfdElt", "A random element of N.", random);
    it.def("PrimeField", "N::Nfd -> FldFin", "The prime field of N.", prime_field);
    it.def("Kernel", "N::Nfd -> FldFin", "The kernel of N, as a finite field.", kernel);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(n: u64) -> Integer {
        Integer::from_u64(n)
    }

    #[test]
    fn dickson_pairs_follow_the_condition() {
        let pair = |q: u64, v: i64| dickson_pair(&int(q), v).unwrap();
        assert!(pair(5, 4) && pair(25, 3) && pair(9, 4) && pair(7, 2) && pair(49, 4) && pair(5, -2));
        // Not (5, 3), (125, 3) or (7, 4) (7 = 3 mod 4), and 6 is no prime power.
        assert!(!pair(5, 3) && !pair(125, 3) && !pair(7, 4) && !pair(3, 4) && !pair(6, 2));
        assert!(dickson_pair(&int(1), 2).is_err() && dickson_pair(&int(3), 0).is_err());
    }

    #[test]
    fn variants_in_magmas_order() {
        // H23E2: two variants of (625, 4), with representatives 1 and 3.
        assert_eq!(variant_reps(&int(5), 4), vec![1, 3]);
        // The units modulo 13 are the powers of 2; modulo 60 the products of
        // powers of 31, 41 and 37; modulo 16 of -1 and 5.
        assert_eq!(variant_reps(&int(3), 13), vec![1, 2, 4, 8]);
        assert_eq!(variant_reps(&int(61), 60), vec![1, 31, 41, 11, 37, 7, 17, 47, 49, 19, 29, 59, 13, 43, 53, 23]);
        assert_eq!(variant_reps(&int(7), 16), vec![1, 15, 5, 11]);
    }

    #[test]
    fn variant_exponents_as_magma_picks_them() {
        let e = |q: u64, v: u64, s: u64| {
            let n = &int(q).pow(v) - &Integer::one();
            variant_exponent(s, v, &n, &n.factor().unwrap().factors)
        };
        assert_eq!((e(5, 4, 3), e(49, 4, 3), e(7, 9, 2), e(7, 9, 5)), (int(107), int(48043), int(20176805), int(5)));
    }
}
