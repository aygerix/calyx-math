//! Roots of univariate polynomials, with Magma's choice of roots over finite
//! fields.

use std::cmp::Ordering;
use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{Elem, GrError, GrResult, Truth};
use calyx_flint::mpoly as fm;
use calyx_flint::upoly as fu;

use super::tower::{Tower, poly_divides};
use super::{base_of, bctx, len, nonzero, pol, sort_by_ring_order};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::one;
use crate::rings::{Elt, RingKind, ring_of};
use crate::value::*;

/// The roots of `f` over a polynomial ring R (see `tower`): -b/a for its
/// linear factors a x + b with a dividing b in R.
fn tower_roots(f: &Elt, t: &Tower) -> RResult<Vec<(Elem, u64)>> {
    let (_, fs) = fm::factor(&t.flatten(&f.x)?, false)?;
    let mut out = Vec::new();
    for (q, e) in fs {
        let q = t.unflatten(&q)?;
        if q.poly_len() == 2 {
            if let Some(r) = poly_divides(&q.poly_coeff(0).neg()?, &q.poly_coeff(1))? {
                out.push((r, e));
            }
        }
    }
    Ok(out)
}

/// The roots of `f` in its coefficient ring with multiplicities, in the
/// ring's order.
fn root_values(it: &mut Interp, f: &Elt) -> RResult<Vec<(Value, u64)>> {
    nonzero(f)?;
    let rs = match Tower::of(f.x.ctx()) {
        Some(t) => tower_roots(f, &t)?,
        None => fu::roots(&f.x).map_err(|e| match e {
            GrError::Unable => RuntimeError::runtime("Coefficient ring must be a real or complex field or a field with factorization"),
            e => e.into(),
        })?,
    };
    let base = base_of(f);
    let mut out: Vec<(Value, u64)> = rs.into_iter().map(|(r, m)| (it.elem_to_value(&base, r), m)).collect();
    sort_by_ring_order(it, &mut out);
    Ok(out)
}

/// `f` over the ring `s` (argument 2 of `Roots(f, S)` and friends), as `!`
/// coerces it; `verb` words the error (Roots says "coerced", HasRoot
/// "changed").
fn over(it: &mut Interp, f: &Rc<Elt>, s: &Value, verb: &str) -> RResult<Rc<Elt>> {
    let q = it.poly_ring(s, true)?;
    let Value::Struct(st) = &q else { unreachable!() };
    match it.to_ring_elem(st, &Value::Elt(f.clone()), true).ok().flatten() {
        Some(x) => Ok(Rc::new(Elt { parent: st.clone(), x })),
        None => Err(RuntimeError::runtime(format!("Argument 1 cannot be {verb} to be over argument 2"))),
    }
}

/// The coefficient ring of `f` if it is a finite field.
fn coefficient_field(f: &Elt) -> Option<&crate::rings::FiniteField> {
    match &f.ring().base()?.as_struct()? {
        StructKind::Ring(r) => r.finite_field(),
        _ => None,
    }
}

/// The order and the characteristic of the coefficient ring of `f` if it
/// is a finite field or the integers modulo a prime.
fn finite_field_order(f: &Elt) -> Option<(Integer, Integer)> {
    if let Some(fld) = coefficient_field(f) {
        return Some((fld.order(), fld.p.clone()));
    }
    match ring_of(&base_of(f)).map(|(_, r)| &r.kind) {
        Some(RingKind::Residue(m)) if m.is_prime() => Some((m.clone(), m.clone())),
        _ => None,
    }
}

/// Magma's square root of a non-zero square `d` of the prime field of odd
/// order `p`: Tonelli and Shanks's algorithm with the least non-residue
/// (so d^((p+1)/4) for p = 3 mod 4). This is Magma's choice for p = 3
/// mod 4 and p = 5 mod 8; for p = 1 mod 8 Magma draws the non-residue at
/// random, so its roots differ from these at times.
fn ff_sqrt(d: &Elem, p: &Integer) -> GrResult<Elem> {
    let ctx = d.ctx();
    let q1 = p - 1;
    let mut s = 0u64;
    let mut odd = q1.clone();
    while odd.is_even() {
        odd = odd.fdiv_2exp(1);
        s += 1;
    }
    let half = q1.fdiv_2exp(1);
    let mut z = Elem::from_i64(ctx, 2)?;
    while z.pow(&half)?.is_neg_one() != Truth::True {
        z = z.add(&Elem::one(ctx)?)?;
    }
    let (mut m, mut c, mut t, mut r) = (s, z.pow(&odd)?, d.pow(&odd)?, d.pow(&(&odd + 1).fdiv_2exp(1))?);
    while t.is_one() != Truth::True {
        let (mut i, mut tt) = (0u64, t.clone());
        while tt.is_one() != Truth::True {
            tt = tt.mul(&tt)?;
            i += 1;
        }
        let b = c.pow(&Integer::one().mul_2exp(m - i - 1))?;
        m = i;
        c = b.mul(&b)?;
        t = t.mul(&c)?;
        r = r.mul(&b)?;
    }
    Ok(r)
}

/// The squarefree parts of `f` over a finite field in the ring's order,
/// each with its multiplicity and its roots in the order of the field:
/// Magma looks for roots part by part in this order.
fn ff_root_parts(it: &mut Interp, f: &Elt) -> RResult<Vec<(u64, Vec<Elem>)>> {
    let mut parts: Vec<(u64, Elem, Vec<Elem>)> = Vec::new();
    for (g, e) in fu::factor(&f.x)?.factors {
        let i = match parts.iter().position(|p| p.0 == e) {
            Some(i) => i,
            None => {
                parts.push((e, Elem::one(f.x.ctx())?, Vec::new()));
                parts.len() - 1
            }
        };
        if g.poly_len() == 2 {
            parts[i].2.push(g.poly_coeff(0).neg()?.div(&g.poly_coeff(1))?);
        }
        parts[i].1 = parts[i].1.mul(&g)?;
    }
    let (pring, base) = (f.ring_rc(), base_of(f));
    let Some((_, bring)) = ring_of(&base) else { unreachable!("a finite field") };
    parts.sort_by(|a, b| it.ring_elt_cmp(&pring, &a.1, &b.1).ok().flatten().unwrap_or(Ordering::Equal));
    for p in parts.iter_mut() {
        p.2.sort_by(|a, b| it.ring_elt_cmp(bring, a, b).ok().flatten().unwrap_or(Ordering::Equal));
    }
    Ok(parts.into_iter().map(|(e, _, rs)| (e, rs)).collect())
}

/// The root of `f` over a finite field (of characteristic `p`) that
/// HasRoot returns, and with `zero_first` unset that of Roots(f : Max :=
/// 1): 0 if it is a root (HasRoot only); otherwise one of the first
/// squarefree part with roots: its only root, (s + Sqrt(D))/2 for two
/// roots in the prime field of odd order with sum s and discriminant D,
/// and otherwise the least root. (This is Magma's choice in GF(q) for
/// q < 25; for three or more roots in larger fields, and two outside the
/// prime field, Magma's choice depends on its random state.)
fn ff_root(it: &mut Interp, f: &Elt, p: &Integer, zero_first: bool) -> RResult<Option<Elem>> {
    nonzero(f)?;
    if zero_first && f.x.poly_coeff(0).is_zero() == Truth::True {
        return Ok(Some(Elem::zero(&bctx(f))));
    }
    for (_, rs) in ff_root_parts(it, f)? {
        match rs.len() {
            0 => continue,
            2 if !p.is_even() && rs.iter().all(|r| r.pow(p).is_ok_and(|x| x.equal(r) == Truth::True)) => {
                let s = rs[0].add(&rs[1])?;
                let d = rs[0].sub(&rs[1])?;
                let r = s.add(&ff_sqrt(&d.mul(&d)?, p)?)?;
                return Ok(Some(r.div(&Elem::from_i64(&bctx(f), 2)?)?));
            }
            _ => return Ok(Some(rs[0].clone())),
        }
    }
    Ok(None)
}

/// The roots Roots gives with Max := m. Over a finite field (or modulo a
/// prime) of order q: the least m if deg f <= 2 or deg f >= q; otherwise
/// for m = 1 the root `ff_root` picks, with multiplicity 1, and for more
/// the roots of the squarefree parts in turn (in the ring's order) until
/// there are m, then the least m of those. Over other rings the largest m.
fn roots_max(it: &mut Interp, f: &Elt, m: usize) -> RResult<Vec<(Value, u64)>> {
    nonzero(f)?;
    let Some((q, p)) = finite_field_order(f) else {
        let mut rs = root_values(it, f)?;
        return Ok(rs.split_off(rs.len().saturating_sub(m)));
    };
    let deg = len(f) as u64 - 1;
    if deg <= 2 || Integer::from_u64(deg) >= q {
        let mut rs = root_values(it, f)?;
        rs.truncate(m);
        return Ok(rs);
    }
    let base = base_of(f);
    if m == 1 {
        return Ok(ff_root(it, f, &p, false)?.map(|r| (it.elem_to_value(&base, r), 1)).into_iter().collect());
    }
    let mut out: Vec<(Value, u64)> = Vec::new();
    for (e, rs) in ff_root_parts(it, f)? {
        if out.len() >= m {
            break;
        }
        out.extend(rs.into_iter().map(|r| (it.elem_to_value(&base, r), e)));
    }
    sort_by_ring_order(it, &mut out);
    out.truncate(m);
    Ok(out)
}

/// The parameter Max of Roots: a small non-negative integer, if given.
fn max_param(it: &mut Interp, a: &CallArgs) -> RResult<Option<usize>> {
    match a.param("Max") {
        None | Some(Value::Undef) => Ok(None),
        Some(Value::Int(m)) => match m.to_i64() {
            Some(v) if (0..1 << 30).contains(&v) => Ok(Some(v as usize)),
            _ => Err(RuntimeError::runtime("Bad value for parameter 'Max': value not small non-negative")),
        },
        Some(_) => {
            let types: Vec<String> = a.args.iter().map(|v| it.type_name_ext(v)).collect();
            Err(RuntimeError::runtime(format!("Bad type for parameter 'Max'\nArgument types given: {}", types.join(", "))))
        }
    }
}

fn roots_seq(it: &mut Interp, f: &Rc<Elt>, a: &CallArgs) -> RResult<Vals> {
    let rs = match max_param(it, a)? {
        Some(m) => roots_max(it, f, m)?,
        None => root_values(it, f)?,
    };
    let elems = rs.into_iter().map(|(r, m)| Value::tuple(vec![r, Value::int(m as i64)])).collect();
    one(Value::seq(None, elems))
}

pub(super) fn roots(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    roots_seq(it, &f, a)
}

pub(super) fn roots_in(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = over(it, &pol(a, 0), &a.args[1].clone(), "coerced")?;
    roots_seq(it, &f, a)
}

/// A root, if there is one: that of the first linear factor in Magma's
/// order (the largest over the integers and rationals; 0, else the
/// largest, modulo a prime); over finite fields see `ff_root`.
fn has_root_of(it: &mut Interp, f: &Rc<Elt>) -> RResult<Vals> {
    let pick = if let Some(fld) = coefficient_field(f) {
        ff_root(it, f, &fld.p, true)?.map(|r| it.elem_to_value(&base_of(f), r))
    } else {
        let rs = root_values(it, f).map_err(|e| match e.message.starts_with("Coefficient ring must be") {
            true => RuntimeError::runtime("Roots not computable over given coefficient ring"),
            false => e,
        })?;
        let zero_first = matches!(ring_of(&base_of(f)).map(|(_, r)| &r.kind), Some(RingKind::Residue(_))) && f.x.poly_coeff(0).is_zero() == Truth::True;
        if zero_first { rs.into_iter().next() } else { rs.into_iter().last() }.map(|(r, _)| r)
    };
    match pick {
        Some(r) => Ok(vals![Value::Bool(true), r]),
        None => Ok(vals![Value::Bool(false), Value::Undef]),
    }
}

pub(super) fn has_root(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    has_root_of(it, &pol(a, 0))
}

pub(super) fn has_root_in(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = over(it, &pol(a, 0), &a.args[1].clone(), "changed")?;
    has_root_of(it, &f)
}
