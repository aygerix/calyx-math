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
    /// The pair (q, v) with q = p^h; the variant s, the least member of its
    /// class, and the exponent e of the primitive element z = z0^e (z0 that
    /// of K, and s = e modulo v).
    Dickson { p: Integer, h: u64, q: Integer, v: u64, variant: Integer, class: u64, e: Integer },
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

    /// Whether `self` and `other` are the same nearfield up to isomorphism:
    /// the same Dickson pair and the same class of variants.
    pub fn same_as(&self, other: &Nearfield) -> bool {
        match (&self.kind, &other.kind) {
            (NfdKind::Dickson { q, v, class, .. }, NfdKind::Dickson { q: q2, v: v2, class: c2, .. }) => q == q2 && v == v2 && class == c2,
        }
    }

    pub fn hash_key(&self) -> (u64, Integer, u64) {
        match &self.kind {
            NfdKind::Dickson { q, v, class, .. } => (*v, q.clone(), *class),
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
                return Err(RuntimeError::runtime("Illegal negative power of zero element"));
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

/// How a nearfield prints: its kind, name and order.
pub fn describe(s: &Struct) -> [String; 2] {
    let n = nfd(s);
    match &n.kind {
        NfdKind::Dickson { q, v, .. } => {
            let name = s.name.borrow().map(|n| n.to_string()).unwrap_or_else(|| "D".to_string());
            [format!("Nearfield {name} of Dickson type defined by the pair ({q}, {v})"), format!("Order = {}", n.order())]
        }
    }
}

const INCOMPATIBLE: &str = "Arguments are not compatible\nArgument types given: NfdElt, NfdElt";

impl Interp {
    /// Operators with an element of a nearfield among the operands; `None`
    /// leaves the rest to the generic rules.
    pub fn nfd_binop(&mut self, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
        use BinOp::*;
        let name = op.intrinsic_name();
        if op == Pow {
            return match (a, b) {
                (Value::Nfd(x), Value::Int(n)) => {
                    let y = nfd(&x.parent).pow(&x.x, n).map_err(|e| e.in_context(name))?;
                    Ok(Some(elt(&x.parent, y)))
                }
                // x^y = y^-1 x y.
                (Value::Nfd(x), Value::Nfd(y)) if Rc::ptr_eq(&x.parent, &y.parent) => {
                    if is_zero(&y.x) {
                        return Err(RuntimeError::runtime("Division by zero").in_context(name));
                    }
                    let n = nfd(&x.parent);
                    let r = n.mul(&n.mul(&n.inverse(&y.x)?, &x.x)?, &y.x)?;
                    Ok(Some(elt(&x.parent, r)))
                }
                (Value::Nfd(_), Value::Nfd(_)) => Err(RuntimeError::runtime(INCOMPATIBLE).in_context(name)),
                _ => Ok(None),
            };
        }
        if !matches!(op, Add | Sub | Mul | Div | Eq | Ne | Cmpeq | Cmpne) {
            return Ok(None);
        }
        // Integers come into the nearfield of the other operand.
        let st = match (a, b) {
            (Value::Nfd(x), Value::Nfd(y)) if !Rc::ptr_eq(&x.parent, &y.parent) => {
                return Err(RuntimeError::runtime(INCOMPATIBLE).in_context(name));
            }
            (Value::Nfd(x), _) | (_, Value::Nfd(x)) => x.parent.clone(),
            _ => return Ok(None),
        };
        let operand = |me: &mut Interp, v: &Value| -> RResult<Option<Elem>> {
            match v {
                Value::Nfd(x) => Ok(Some(x.x.clone())),
                Value::Int(_) => match me.coerce_into_nearfield(&st, v, false)? {
                    Ok(Value::Nfd(x)) => Ok(Some(x.x.clone())),
                    _ => Ok(None),
                },
                _ => Ok(None),
            }
        };
        let (Some(x), Some(y)) = (operand(self, a)?, operand(self, b)?) else { return Ok(None) };
        let n = nfd(&st).clone();
        let r = match op {
            Add => x.add(&y)?,
            Sub => x.sub(&y)?,
            Mul => n.mul(&x, &y)?,
            Div => {
                if is_zero(&y) {
                    return Err(RuntimeError::runtime("Division by zero").in_context(name));
                }
                n.mul(&x, &n.inverse(&y)?)?
            }
            Eq | Cmpeq => return Ok(Some(Value::Bool(x.equal(&y) == Truth::True))),
            _ => return Ok(Some(Value::Bool(x.equal(&y) != Truth::True))),
        };
        Ok(Some(elt(&st, r)))
    }

    /// `N ! x`: an element of N, or of its field (or something that
    /// coerces into the field, such as an integer).
    pub fn coerce_into_nearfield(&mut self, st: &Rc<Struct>, x: &Value, strict: bool) -> RResult<Result<Value, Option<String>>> {
        let _ = strict;
        match x {
            Value::Nfd(e) if Rc::ptr_eq(&e.parent, st) => Ok(Ok(x.clone())),
            Value::Nfd(_) => Ok(Err(None)),
            _ => {
                let gf = Value::Struct(nfd(st).gf.clone());
                match self.try_coerce(&gf, x)? {
                    Ok(v) => match crate::rings::small::elt_of(&v) {
                        Some(e) => Ok(Ok(elt(st, e.x.clone()))),
                        None => Ok(Err(None)),
                    },
                    Err(e) => Ok(Err(e)),
                }
            }
        }
    }

    /// `x in N` for a nearfield N.
    pub fn nfd_contains(&mut self, st: &Rc<Struct>, x: &Value) -> RResult<bool> {
        match x {
            Value::Nfd(e) => Ok(Rc::ptr_eq(&e.parent, st)),
            _ => Err(RuntimeError::runtime("Bad argument types").in_context("in")),
        }
    }

    /// The elements of a nearfield, in the order of its field.
    pub fn enumerate_nearfield(&mut self, st: &Rc<Struct>) -> RResult<Vec<Value>> {
        let gf = nfd(st).gf.clone();
        let xs = self.enumerate_ring(&gf)?;
        Ok(xs.iter().filter_map(crate::rings::small::elt_of).map(|e| elt(st, e.x.clone())).collect())
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

/// Whether (q, v) is a Dickson pair: every prime factor of v divides
/// q - 1, and 4 divides q - 1 if it divides v.
fn is_dickson_pair(q: &Integer, v: u64) -> bool {
    let q1 = q - &Integer::one();
    prime_factors(v).iter().all(|&r| q1.mod_u64(r) == 0) && (v % 4 != 0 || q1.mod_u64(4) == 0)
}

/// The classes of variants: the units modulo v up to multiplication by
/// powers of p, each by its least member.
fn variant_classes(p: &Integer, v: u64) -> Vec<u64> {
    if v == 1 {
        return vec![1];
    }
    let pm = p.mod_u64(v);
    let mut seen = vec![false; v as usize];
    let mut reps = Vec::new();
    for s in 1..v {
        if seen[s as usize] || calyx_flint::gcd_u64(s, v) != 1 {
            continue;
        }
        reps.push(s);
        let mut x = s;
        while !seen[x as usize] {
            seen[x as usize] = true;
            x = (x as u128 * pm as u128 % v as u128) as u64;
        }
    }
    reps
}

/// The least member of the class of the variant s modulo v.
fn class_of(p: &Integer, v: u64, s: &Integer) -> u64 {
    if v == 1 {
        return 1;
    }
    let (pm, s) = (p.mod_u64(v), s.mod_u64(v));
    let (mut x, mut least) = (s, s);
    loop {
        x = (x as u128 * pm as u128 % v as u128) as u64;
        if x == s {
            return least;
        }
        least = least.min(x);
    }
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

/// A small non-negative integer argument.
fn small_arg(a: &CallArgs, i: usize) -> RResult<u64> {
    let n = a.int(i)?;
    n.to_u64().filter(|&n| n < 1 << 30).ok_or_else(|| RuntimeError::runtime(format!("Argument {} ({n}) is not small and non-negative", i + 1)))
}

fn prime_arg(a: &CallArgs) -> RResult<Integer> {
    let p = a.int(0)?.clone();
    if !p.is_prime() {
        return Err(RuntimeError::runtime("Argument 1 is not prime"));
    }
    Ok(p)
}

fn dickson_pairs_in(p: &Integer, hs: std::ops::RangeInclusive<u64>, vs: std::ops::RangeInclusive<u64>) -> Value {
    let mut out = Vec::new();
    for h in hs {
        let q = p.pow(h);
        for v in vs.clone() {
            if v >= 1 && is_dickson_pair(&q, v) {
                out.push(Value::seq(None, vec![Value::Int(q.clone()), Value::Int(Integer::from_u64(v))]));
            }
        }
    }
    Value::seq(None, out)
}

fn dickson_pairs(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = prime_arg(a)?;
    let (hlo, hhi, vlo, vhi) = (small_arg(a, 1)?.max(1), small_arg(a, 2)?, small_arg(a, 3)?.max(1), small_arg(a, 4)?);
    one(dickson_pairs_in(&p, hlo..=hhi, vlo..=vhi))
}

fn dickson_pairs_bounded(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = prime_arg(a)?;
    one(dickson_pairs_in(&p, 1..=small_arg(a, 1)?, 1..=small_arg(a, 2)?))
}

fn dickson_triples(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = prime_arg(a)?;
    let (hb, vb) = (small_arg(a, 1)?, small_arg(a, 2)?);
    let mut out = Vec::new();
    for h in 1..=hb {
        let q = p.pow(h);
        for v in 1..=vb {
            if is_dickson_pair(&q, v) {
                let t = [p.clone(), Integer::from_u64(h), Integer::from_u64(v)];
                out.push(Value::seq(None, t.into_iter().map(Value::Int).collect()));
            }
        }
    }
    one(Value::seq(None, out))
}

/// The Dickson pair (q, v) of arguments 1 and 2, with the prime and the
/// exponent of q.
fn pair_args(a: &CallArgs) -> RResult<(Integer, u64, Integer, u64)> {
    let q = a.int(0)?.clone();
    let (p, h) = prime_power(&q).ok_or_else(|| RuntimeError::runtime("Argument 1 is not a prime power"))?;
    let v = small_arg(a, 1)?;
    if v == 0 || !is_dickson_pair(&q, v) {
        return Err(RuntimeError::runtime(format!("({q}, {v}) is not a Dickson pair")));
    }
    Ok((p, h, q, v))
}

fn number_of_variants(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (p, _, _, v) = pair_args(a)?;
    intv(Integer::from_u64(variant_classes(&p, v).len() as u64))
}

fn number_of_variants_n(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let st = nfd_arg(a, 0)?;
    let NfdKind::Dickson { p, v, .. } = &nfd(&st).kind;
    intv(Integer::from_u64(variant_classes(p, *v).len() as u64))
}

fn variant_representatives(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (p, _, _, v) = pair_args(a)?;
    one(Value::seq(None, variant_classes(&p, v).into_iter().map(|s| Value::Int(Integer::from_u64(s))).collect()))
}

// ----- construction ----------------------------------------------------------------------------

/// The exponent e of the primitive element z0^e for the variant s: the
/// least e >= s (or >= 1) with e = s modulo v and e prime to q^v - 1.
fn variant_exponent(s: &Integer, v: u64, qm1: &Integer) -> Integer {
    let vv = Integer::from_u64(v);
    let mut e = if s.sign() > 0 { s.clone() } else { Integer::from_u64(s.mod_u64(v)) };
    if e.is_zero() {
        e = vv.clone();
    }
    while !e.gcd(qm1).is_one() {
        e = &e + &vv;
    }
    e
}

fn dickson_nearfield(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (p, h, q, v) = pair_args(a)?;
    let s = match a.param("Variant") {
        Some(Value::Int(s)) => s.clone(),
        _ => Integer::one(),
    };
    if !s.gcd(&Integer::from_u64(v)).is_one() {
        return Err(RuntimeError::runtime(format!("The variant ({s}) must be prime to {v}")));
    }
    let qv = q.pow(v);
    let qm1 = &qv - &Integer::one();
    let e = variant_exponent(&s, v, &qm1);
    let gf = it.default_field(&p, h * v)?;
    let ctx = field_of(&gf).expect("a finite field").0.ctx.clone();
    let z0 = it.ff_primitive(&gf)?;
    let z = z0.pow(&e)?;
    let twist = if v == 1 {
        Twist::Field
    } else {
        // frob[(q^i - 1)/(q - 1) mod v] = i mod v, for 1 <= i <= v.
        let qv_mod = q.mod_u64(v);
        let mut frob = vec![u64::MAX; v as usize];
        let mut c = 1 % v;
        for i in 1..=v {
            frob[c as usize] = i % v;
            c = (c * qv_mod + 1) % v;
        }
        if frob.contains(&u64::MAX) {
            return Err(RuntimeError::runtime(format!("({q}, {v}) is not a Dickson pair")));
        }
        let residue = match (Elem::zech_order(&ctx), z0.zech_log()) {
            (Some(qm1), Some(1)) => {
                let einv = if v == 1 { 0 } else { Nmod::new(v).inv(e.mod_u64(v)).expect("a unit modulo v") };
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
        Twist::Frobenius { h, frob, residue }
    };
    let class = class_of(&p, v, &s);
    let kind = NfdKind::Dickson { p, h, q, v, variant: s, class, e };
    let n = Nearfield { kind, gf: gf.clone(), twist };
    let st = Struct::new(StructKind::Nearfield(Rc::new(n)));
    {
        let mut attrs = st.attrs.borrow_mut();
        attrs.insert(Sym::new("gf"), Value::Struct(gf.clone()));
        attrs.insert(Sym::new("prim"), make_elt(&gf, z));
    }
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
    match it.coerce_into_nearfield(&st, &x, true)? {
        Ok(v) => one(v),
        Err(e) => Err(RuntimeError::runtime(e.unwrap_or_else(|| "Illegal coercion".to_string()))),
    }
}

fn eltseq(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = nfd_elt_arg(a, 0)?;
    one(it.call_intrinsic_named(Sym::new("Eltseq"), vec![as_field_value(&x)])?)
}

fn inverse(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = nfd_elt_arg(a, 0)?;
    if is_zero(&x.x) {
        return Err(RuntimeError::runtime("Element is not invertible"));
    }
    one(elt(&x.parent, nfd(&x.parent).inverse(&x.x)?))
}

fn order(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = nfd_elt_arg(a, 0)?;
    if is_zero(&x.x) {
        return Err(RuntimeError::runtime("Element is not a unit"));
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
        // (5, 4), (25, 3); not (5, 3), (125, 3) or (7, 4) (7 = 3 mod 4).
        assert!(is_dickson_pair(&int(5), 4) && is_dickson_pair(&int(25), 3) && is_dickson_pair(&int(9), 4));
        assert!(!is_dickson_pair(&int(5), 3) && !is_dickson_pair(&int(125), 3) && !is_dickson_pair(&int(7), 4));
        assert!(is_dickson_pair(&int(7), 2) && !is_dickson_pair(&int(3), 4) && is_dickson_pair(&int(49), 4));
    }

    #[test]
    fn variants() {
        // H23E2: two variants of (625, 4), with representatives 1 and 3.
        assert_eq!(variant_classes(&int(5), 4), vec![1, 3]);
        assert_eq!(class_of(&int(5), 4, &int(5)), 1);
        // Modulo 13 the powers of 3 are {1, 3, 9}: four classes.
        assert_eq!(variant_classes(&int(3), 13), vec![1, 2, 4, 7]);
        assert_eq!(class_of(&int(3), 13, &int(12)), 4);
    }
}
