//! Univariate polynomial rings (the handbook chapter of that name):
//! creating polynomials, changing coefficient rings, the functions of
//! polynomials, greatest common divisors and content, the functions for
//! integer polynomials, factorization, resultants and Hensel lifting.
//!
//! Polynomials are `gr_poly`s. The algorithms beyond generic arithmetic run
//! on FLINT's specialised types through `calyx_flint::upoly`, over the
//! integers, the rationals, prime residue rings and finite fields.

use std::cmp::Ordering;
use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{Ctx, CtxKind, Elem, GrError, GrResult, Truth};
use calyx_flint::upoly as fu;
use calyx_syntax::ast::BinOp;

use super::{arg_ge, arg_not, bare, boolv, intv, none, one};
use crate::error::{ErrStyle, ErrorInfo, RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::ops::div_by_zero;
use crate::rings::props::ring_props;
use crate::rings::{Elt, Ring, RingKind, make_elt, ring_of};
use crate::value::*;

// ----- helpers ---------------------------------------------------------------

/// Argument `i`, which the signature makes a polynomial.
fn pol(a: &CallArgs, i: usize) -> Rc<Elt> {
    match &a.args[i] {
        Value::Elt(e) => e.clone(),
        _ => unreachable!("a polynomial argument"),
    }
}

/// Argument `i`, a univariate polynomial ring (the ring of an ideal of
/// one), or a quotient of one.
fn ring_arg(a: &CallArgs, i: usize) -> (Rc<Struct>, Rc<Ring>) {
    match &a.args[i] {
        Value::Struct(s) => match &s.kind {
            StructKind::Ring(r) => (s.clone(), r.clone()),
            StructKind::UPolIdeal(g) => (g.parent.clone(), g.ring_rc()),
            _ => unreachable!("a polynomial ring argument"),
        },
        _ => unreachable!("a polynomial ring argument"),
    }
}

/// The coefficient ring of the ring of `f`.
fn base_of(f: &Elt) -> Value {
    f.ring().base().expect("a polynomial").clone()
}

/// The FLINT context of the coefficients of `f`.
fn bctx(f: &Elt) -> Rc<Ctx> {
    f.x.ctx().base().expect("a polynomial").clone()
}

fn len(f: &Elt) -> usize {
    f.x.poly_len()
}

/// A polynomial in the ring of `f`.
fn like(f: &Elt, x: Elem) -> Value {
    make_elt(&f.parent, x)
}

/// A coefficient of `f` as a value of the coefficient ring.
fn cval(it: &Interp, f: &Elt, c: Elem) -> Value {
    it.elem_to_value(&base_of(f), c)
}

fn poly_seq(f: &Elt, xs: Vec<Elem>) -> Value {
    Value::seq(Some(f.parent_value()), xs.into_iter().map(|x| like(f, x)).collect())
}

fn coeff_seq(it: &Interp, f: &Elt, cs: Vec<Elem>) -> Value {
    let b = base_of(f);
    Value::seq(Some(b.clone()), cs.into_iter().map(|c| it.elem_to_value(&b, c)).collect())
}

fn nonzero(f: &Elt) -> RResult<()> {
    if len(f) == 0 { Err(arg_not(1, "non-zero")) } else { Ok(()) }
}

fn is_field(v: &Value) -> bool {
    ring_props(v).is_some_and(|p| p.field)
}

fn is_integers(f: &Elt) -> bool {
    matches!(bctx(f).kind(), CtxKind::Integers)
}

/// Two polynomials in one ring (the ring of the first if the second
/// coerces into it).
fn pair_of(it: &mut Interp, u: &Value, v: &Value) -> RResult<(Rc<Elt>, Elem)> {
    if let (Value::Elt(f), Value::Elt(g)) = (u, v) {
        if f.ring().id == g.ring().id {
            return Ok((f.clone(), g.x.clone()));
        }
    }
    let (pu, pv) = (it.parent_of(u)?, it.parent_of(v)?);
    if let Some(Value::Struct(st)) = it.common_ring(&pu, &pv)? {
        let x = it.to_ring_elem(&st, u, false)?;
        let y = it.to_ring_elem(&st, v, false)?;
        if let (Some(x), Some(y)) = (x, y) {
            return Ok((Rc::new(Elt { parent: st, x }), y));
        }
    }
    Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}, {}", it.type_name_ext(u), it.type_name_ext(v))))
}

/// The two polynomial arguments in one ring.
fn pair(it: &mut Interp, a: &CallArgs) -> RResult<(Rc<Elt>, Elem)> {
    pair_of(it, &a.args[0], &a.args[1])
}

/// A unit (constant) polynomial?
fn is_unit_poly(f: &Elem) -> bool {
    f.poly_len() == 1 && f.poly_coeff(0).is_invertible() == Truth::True
}

/// Sort values of one ring in its order.
fn sort_by_ring_order<T>(it: &mut Interp, v: &mut [(Value, T)]) {
    v.sort_by(|a, b| it.compare_ord(&a.0, &b.0).ok().flatten().unwrap_or(Ordering::Equal));
}

/// Errors of Magma's package intrinsics, reported without a position.
fn package_error(msg: &str) -> RuntimeError {
    ErrorInfo { style: ErrStyle::Bare, ..ErrorInfo::runtime(msg) }.into()
}

// ----- division ----------------------------------------------------------------

/// Quotient and remainder of `f` by `g` in `ring`, as Magma divides: over
/// the integers and fields see `calyx_flint::upoly::divrem`; over other
/// coefficient rings each coefficient of the quotient, from the top, is the
/// coefficient ring's `div` of the current coefficient by the leading
/// coefficient of `g` (exact division when that is a unit).
pub fn quotrem(it: &mut Interp, ring: &Ring, f: &Elem, g: &Elem) -> RResult<(Elem, Elem)> {
    if g.poly_len() == 0 {
        return Err(div_by_zero());
    }
    let b = f.ctx().base().expect("a polynomial").clone();
    let lc = fu::lead(g);
    if matches!(b.kind(), CtxKind::Integers) || fu::over_field(f.ctx()) || lc.is_invertible() == Truth::True {
        return Ok(fu::divrem(f, g)?);
    }
    let base = ring.base().expect("a polynomial ring").clone();
    let lcv = it.elem_to_value(&base, lc);
    let (lf, lg) = (f.poly_len(), g.poly_len());
    let mut r = f.clone();
    let mut q = vec![Elem::zero(&b); lf.saturating_sub(lg - 1)];
    for i in (lg - 1..lf).rev() {
        let c = r.poly_coeff(i);
        if c.is_zero() == Truth::True {
            continue;
        }
        let cv = it.elem_to_value(&base, c);
        let d = it.binop(BinOp::IntDiv, cv, lcv.clone())?;
        let Some(d) = it.to_structure_elem(&base, &d, false)? else { continue };
        if d.is_zero() == Truth::True {
            continue;
        }
        r = r.sub(&fu::shift_left(&g.poly_mul_scalar(&d)?, i + 1 - lg)?)?;
        q[i + 1 - lg] = d;
    }
    Ok((Elem::poly_from_coeffs(f.ctx(), &q)?, r))
}

/// The exact quotient `f / g`, if there is one (`g` non-zero).
fn exact_div(it: &mut Interp, ring: &Ring, f: &Elem, g: &Elem) -> RResult<Option<Elem>> {
    if matches!(g.ctx().base().map(|b| b.kind()), Some(CtxKind::Integers)) {
        return Ok(fu::divides(f, g)?);
    }
    let (q, r) = quotrem(it, ring, f, g)?;
    Ok((r.is_zero() == Truth::True).then_some(q))
}

// ----- creation ------------------------------------------------------------------

fn polynomial_seq(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Some(u) = a.seq(0)?.universe.clone() else {
        return Err(bare(RuntimeError::runtime("Argument 1 must be non-null")));
    };
    let p = it.poly_ring(&u, true)?;
    one(it.coerce(&p, &a.args[0])?)
}

fn polynomial_over(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = it.poly_ring(&a.args[0], true)?;
    match it.try_coerce(&p, &a.args[1])? {
        Ok(v) => one(v),
        Err(_) => Err(bare(RuntimeError::runtime("Argument 2 is not coercible over argument 1"))),
    }
}

fn identity(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, r) = ring_arg(a, 0);
    one(make_elt(&st, Elem::one(&r.ctx)?))
}

/// `P.i` and `Name(P, i)`: the indeterminate (of a quotient ring, its
/// image; of an ideal, its generator).
fn indeterminate(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, r) = ring_arg(a, 0);
    let i = a.int(1)?;
    if !i.is_one() {
        return Err(RuntimeError::runtime(format!("Value for name index ({i}) should be in the range [1..1]")));
    }
    if let Some(StructKind::UPolIdeal(g)) = a.args[0].as_struct() {
        return one(Value::Elt(g.clone()));
    }
    let x = r.ctx.generator()?;
    let x = if let RingKind::UPolyRes { modulus, .. } = &r.kind { res_reduce(modulus, x)? } else { x };
    one(make_elt(&st, x))
}

fn assign_names(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, r) = ring_arg(a, 0);
    let names = a.seq(1)?;
    if names.elems.len() != 1 {
        return Err(RuntimeError::runtime("Argument 2 must have length 1"));
    }
    let Value::Str(s) = &names.elems[0] else { return Err(RuntimeError::runtime("Names must be strings")) };
    *r.names.borrow_mut() = vec![Rc::from(s.as_str())];
    none()
}

// ----- changing rings ---------------------------------------------------------------

/// The map of `ChangeRing` between polynomial rings: coercion of the
/// coefficients, or a map applied to them.
struct CoefficientMap(Option<Rc<MapObj>>);

impl NativeMap for CoefficientMap {
    fn apply(&self, it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        let x = it.coerce(&m.domain, x).map_err(|_| RuntimeError::runtime("Element is not in the domain of the map").in_context("map application"))?;
        let Value::Elt(f) = &x else { unreachable!("a polynomial") };
        let Some((cst, cod)) = ring_of(&m.codomain) else { unreachable!("a polynomial ring") };
        let (cst, target, ctx) = (cst.clone(), cod.base().expect("a polynomial ring").clone(), cod.ctx.clone());
        let mut cs = Vec::with_capacity(len(f));
        for i in 0..len(f) {
            let mut c = cval(it, f, f.x.poly_coeff(i));
            if let Some(g) = &self.0 {
                c = it.apply_map(g, &c)?;
            }
            match it.to_structure_elem(&target, &c, true)? {
                Some(e) => cs.push(e),
                None => {
                    let msg = "Cannot coerce element from source coefficent ring into the destination coefficient ring";
                    return Err(RuntimeError::runtime(msg).in_context("map application"));
                }
            }
        }
        Ok(make_elt(&cst, Elem::poly_from_coeffs(&ctx, &cs)?))
    }

    fn preimage(&self, _it: &mut Interp, _m: &MapObj, _y: &Value) -> RResult<Value> {
        Err(RuntimeError::runtime("No inverse is known for the map").in_context("@@"))
    }
}

fn change_ring(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let q = it.poly_ring(&a.args[1], true)?;
    let f = match a.args.get(2) {
        Some(Value::Map(m)) => Some(m.clone()),
        _ => None,
    };
    let h = MapObj { kind: MapKind::Map, domain: a.args[0].clone(), codomain: q.clone(), imp: MapImpl::Native(Rc::new(CoefficientMap(f))) };
    Ok(vals![q, Value::Map(Rc::new(h))])
}

// ----- predicates -----------------------------------------------------------------

fn is_monic(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    boolv(len(&f) > 0 && fu::lead(&f.x).is_one() == Truth::True)
}

/// Whether `f` is not a zero divisor: Magma answers only over domains.
fn is_regular(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let domain = ring_props(&base_of(&f)).is_some_and(|p| p.domain);
    boolv(domain && len(&f) > 0)
}

// ----- coefficients and terms ---------------------------------------------------------

fn coefficients(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let cs = (0..len(&f)).map(|i| f.x.poly_coeff(i)).collect();
    one(coeff_seq(it, &f, cs))
}

/// Argument `i` as a non-negative machine integer.
fn index_arg(a: &CallArgs, i: usize) -> RResult<usize> {
    let n = a.int(i)?;
    if n.sign() < 0 {
        return Err(arg_ge(i + 1, n, 0));
    }
    n.to_u64().filter(|&k| k < 1 << 62).map(|k| k as usize).ok_or_else(|| RuntimeError::runtime(format!("Argument {} ({n}) is too large", i + 1)))
}

fn coefficient(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let i = index_arg(a, 1)?;
    let c = if i < len(&f) { f.x.poly_coeff(i) } else { Elem::zero(&bctx(&f)) };
    one(cval(it, &f, c))
}

fn monomial_coefficient(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, m) = pair(it, a)?;
    let n = m.poly_len();
    let monomial = n > 0 && m.poly_coeff(n - 1).is_one() == Truth::True && (0..n - 1).all(|i| m.poly_coeff(i).is_zero() == Truth::True);
    if !monomial {
        return Err(RuntimeError::runtime("Argument 2 must be a monomial"));
    }
    let c = if n - 1 < len(&f) { f.x.poly_coeff(n - 1) } else { Elem::zero(&bctx(&f)) };
    one(cval(it, &f, c))
}

/// The index of the lowest non-zero coefficient of a non-zero polynomial.
fn low(f: &Elem) -> usize {
    (0..f.poly_len()).find(|&i| f.poly_coeff(i).is_zero() != Truth::True).unwrap_or(0)
}

fn leading_coefficient(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    nonzero(&f)?;
    one(cval(it, &f, fu::lead(&f.x)))
}

fn trailing_coefficient(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    nonzero(&f)?;
    one(cval(it, &f, f.x.poly_coeff(low(&f.x))))
}

fn constant_coefficient(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let c = if len(&f) > 0 { f.x.poly_coeff(0) } else { Elem::zero(&bctx(&f)) };
    one(cval(it, &f, c))
}

fn terms(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let mut out = Vec::new();
    for i in 0..len(&f) {
        let c = f.x.poly_coeff(i);
        if c.is_zero() != Truth::True {
            out.push(fu::monomial(f.x.ctx(), &c, i)?);
        }
    }
    one(poly_seq(&f, out))
}

fn leading_term(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    nonzero(&f)?;
    let n = len(&f) - 1;
    one(like(&f, fu::monomial(f.x.ctx(), &f.x.poly_coeff(n), n)?))
}

fn trailing_term(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    nonzero(&f)?;
    let k = low(&f.x);
    one(like(&f, fu::monomial(f.x.ctx(), &f.x.poly_coeff(k), k)?))
}

fn monomials(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let one_c = Elem::one(&bctx(&f))?;
    let out = (0..len(&f)).map(|i| fu::monomial(f.x.ctx(), &one_c, i)).collect::<Result<Vec<_>, _>>()?;
    one(poly_seq(&f, out))
}

fn support(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let (mut idx, mut cs) = (Vec::new(), Vec::new());
    for i in 0..len(&f) {
        let c = f.x.poly_coeff(i);
        if c.is_zero() != Truth::True {
            idx.push(Integer::from_u64(i as u64));
            cs.push(c);
        }
    }
    // The coefficients are returned only when asked for.
    if a.nresults < 2 {
        return one(Value::int_seq(idx));
    }
    Ok(vals![Value::int_seq(idx), coeff_seq(it, &f, cs)])
}

fn reductum(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    nonzero(&f)?;
    one(like(&f, fu::truncate(&f.x, len(&f) - 1)?))
}

/// The polynomial over the integers with the coefficients rounded.
fn round(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let mut cs = Vec::with_capacity(len(&f));
    for i in 0..len(&f) {
        cs.push(match cval(it, &f, f.x.poly_coeff(i)) {
            Value::Int(n) => n,
            Value::Rat(q) => q.round(),
            Value::Real(r) => r.x.round(),
            _ => return Err(RuntimeError::runtime("Coefficient ring is not a real subring")),
        });
    }
    let zx = it.poly_ring(&Value::integers(), true)?;
    let Some((st, r)) = ring_of(&zx) else { unreachable!() };
    let zz = Ctx::integers();
    let cs: Vec<Elem> = cs.iter().map(|c| Elem::from_integer(&zz, c)).collect::<Result<_, _>>()?;
    one(make_elt(st, Elem::poly_from_coeffs(&r.ctx, &cs)?))
}

fn valuation(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    if len(&f) == 0 {
        return one(Value::Infinity(true));
    }
    intv(Integer::from_u64(low(&f.x) as u64))
}

fn degree(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_i64(len(&pol(a, 0)) as i64 - 1))
}

// ----- roots -------------------------------------------------------------------------

/// The roots of `f` in its coefficient ring with multiplicities, in the
/// ring's order.
fn root_values(it: &mut Interp, f: &Elt) -> RResult<Vec<(Value, u64)>> {
    nonzero(f)?;
    let rs = fu::roots(&f.x).map_err(|e| match e {
        GrError::Unable => RuntimeError::runtime("Coefficient ring must be a real or complex field or a field with factorization"),
        e => e.into(),
    })?;
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

fn roots(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    roots_seq(it, &f, a)
}

fn roots_in(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
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
        None => boolv(false),
    }
}

fn has_root(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    has_root_of(it, &pol(a, 0))
}

fn has_root_in(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = over(it, &pol(a, 0), &a.args[1].clone(), "changed")?;
    has_root_of(it, &f)
}

// ----- derivatives, evaluation, interpolation -------------------------------------------

fn derivative(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let n = if a.args.len() > 1 { index_arg(a, 1)? } else { 1 };
    one(like(&f, fu::nth_derivative(&f.x, n as u64)?))
}

fn integral(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let p = ring_props(&base_of(&f));
    if !p.as_ref().is_some_and(|p| p.field) {
        return Err(RuntimeError::runtime("Coefficient ring of argument 1 is not a field"));
    }
    if !p.is_some_and(|p| p.characteristic.is_zero()) {
        return Err(RuntimeError::runtime("Coefficient ring must have characteristic 0"));
    }
    one(like(&f, fu::integral(&f.x)?))
}

/// `Evaluate(f, r)`: in the coefficient ring when `r` coerces into it,
/// else by Horner's rule in the structure of `r`.
fn evaluate(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let r = a.args[1].clone();
    let base = base_of(&f);
    let pr = it.parent_of(&r)?;
    if it.auto_coerces(&pr, &base) {
        if let Some(x) = it.to_structure_elem(&base, &r, false)? {
            let v = if len(&f) == 0 { Elem::zero(&bctx(&f)) } else { f.x.poly_evaluate(&x)? };
            return one(it.elem_to_value(&base, v));
        }
    }
    let n = len(&f);
    if n == 0 {
        return one(it.binop(BinOp::Mul, r, Value::int(0))?);
    }
    let mut acc = cval(it, &f, f.x.poly_coeff(n - 1));
    for i in (0..n - 1).rev() {
        acc = it.binop(BinOp::Mul, acc, r.clone())?;
        let c = cval(it, &f, f.x.poly_coeff(i));
        acc = it.binop(BinOp::Add, acc, c)?;
    }
    one(acc)
}

fn interpolation(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (xs, ys) = (a.seq(0)?.clone(), a.seq(1)?.clone());
    let (Some(u), Some(v)) = (xs.universe.clone(), ys.universe.clone()) else {
        return Err(RuntimeError::runtime("Must have a ring universe"));
    };
    if u != v {
        return Err(RuntimeError::runtime("Arguments have different rings"));
    }
    let n = xs.elems.len();
    if ys.elems.len() != n {
        return Err(RuntimeError::runtime("Arguments have different lengths"));
    }
    for i in 0..n {
        for j in 0..i {
            if it.values_equal(&xs.elems[i], &xs.elems[j])? {
                return Err(RuntimeError::runtime("Elements of argument 1 are not distinct"));
            }
        }
    }
    if !is_field(&u) {
        return Err(RuntimeError::runtime("Ring is not a field"));
    }
    let p = it.poly_ring(&u, true)?;
    let Some((st, r)) = ring_of(&p) else { unreachable!() };
    let (st, ctx) = (st.clone(), r.ctx.clone());
    let mut conv = |vs: &[Value]| -> RResult<Vec<Elem>> {
        vs.iter().map(|v| it.to_structure_elem(&u, v, false)?.ok_or_else(|| RuntimeError::runtime("Arguments have different rings"))).collect()
    };
    let (px, py) = (conv(&xs.elems)?, conv(&ys.elems)?);
    one(make_elt(&st, fu::interpolate(&ctx, &px, &py)?))
}

// ----- quotient and remainder ---------------------------------------------------------

fn quotrem_fn(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = pair(it, a)?;
    let ring = f.ring_rc();
    let (q, r) = quotrem(it, &ring, &f.x, &g)?;
    Ok(vals![like(&f, q), like(&f, r)])
}

fn is_divisible_by(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = pair(it, a)?;
    if g.poly_len() == 0 {
        return Err(div_by_zero());
    }
    match exact_div(it, &f.ring_rc(), &f.x, &g)? {
        Some(q) => Ok(vals![Value::Bool(true), like(&f, q)]),
        None => boolv(false),
    }
}

fn exact_quotient(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = pair(it, a)?;
    if g.poly_len() == 0 {
        return Err(div_by_zero());
    }
    match exact_div(it, &f.ring_rc(), &f.x, &g)? {
        Some(q) => one(like(&f, q)),
        None => Err(RuntimeError::runtime("Argument 1 is not exactly divisible by argument 2")),
    }
}

/// The largest k with `g^k` dividing `f`.
fn valuation_by(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = pair(it, a)?;
    if g.poly_len() == 0 {
        return Err(div_by_zero());
    }
    if len(&f) == 0 {
        return one(Value::Infinity(true));
    }
    if is_unit_poly(&g) {
        return Err(RuntimeError::runtime("Argument 2 must not be a unit"));
    }
    let ring = f.ring_rc();
    let (mut h, mut k) = (f.x.clone(), 0u64);
    while let Some(q) = exact_div(it, &ring, &h, &g)? {
        h = q;
        k += 1;
    }
    intv(Integer::from_u64(k))
}

fn pseudo_remainder(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = pair(it, a)?;
    if g.poly_len() == 0 {
        return Err(div_by_zero());
    }
    one(like(&f, fu::pseudo_rem(&f.x, &g)?))
}

fn euclidean_norm(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(len(&pol(a, 0)) as u64))
}

// ----- modular arithmetic ---------------------------------------------------------------

fn modexp(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(1)?.clone();
    let (f, g) = pair_of(it, &a.args[0], &a.args[2])?;
    if n.sign() < 0 {
        return Err(arg_ge(2, &n, 0));
    }
    if !fu::over_field(f.x.ctx()) {
        return Err(RuntimeError::runtime("Algorithm is not available for this kind of coefficient ring"));
    }
    if g.poly_len() == 0 {
        return Err(div_by_zero());
    }
    one(like(&f, fu::powmod(&f.x, &n, &g)?))
}

fn crt(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (xs, ms) = (a.seq(0)?.clone(), a.seq(1)?.clone());
    let elt = |v: &Value| match v {
        Value::Elt(e) if matches!(e.ring().kind, RingKind::UPoly { .. }) => Ok(e.clone()),
        _ => Err(RuntimeError::runtime("Bad argument types")),
    };
    let Some(m0) = ms.elems.first() else { return Err(RuntimeError::runtime("Argument 2 must be non-empty")) };
    let m0 = elt(m0)?;
    if !fu::over_field(m0.x.ctx()) {
        return Err(RuntimeError::runtime("Coefficient ring of argument 1 is not a field"));
    }
    let ring = m0.ring_rc();
    let st = m0.parent.clone();
    let get = |it: &mut Interp, v: &Value| -> RResult<Elem> { it.to_ring_elem(&st, v, false)?.ok_or_else(|| RuntimeError::runtime("Arguments are not compatible")) };
    let mods: Vec<Elem> = ms.elems.iter().map(|v| get(it, v)).collect::<RResult<_>>()?;
    for i in 0..mods.len() {
        for j in 0..i {
            if fu::gcd(&mods[i], &mods[j])?.poly_len() != 1 {
                return Err(package_error("Error, ChineseRemainderTheorem: modules must be coprime."));
            }
        }
    }
    if xs.elems.len() < mods.len() {
        return Err(RuntimeError::runtime("Arguments have different lengths"));
    }
    let mut m = mods[0].clone();
    let x0 = get(it, &xs.elems[0])?;
    let mut t = quotrem(it, &ring, &x0, &m)?.1;
    for (xi, mi) in xs.elems.iter().zip(&mods).skip(1) {
        let x = get(it, xi)?;
        let (_, s, _) = fu::xgcd(&m, mi)?;
        let c = quotrem(it, &ring, &x.sub(&t)?.mul(&s)?, mi)?.1;
        t = t.add(&m.mul(&c)?)?;
        m = m.mul(mi)?;
    }
    one(make_elt(&st, t))
}

// ----- other operations ---------------------------------------------------------------

fn reciprocal_polynomial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    one(like(&f, fu::reverse(&f.x, len(&f))?))
}

/// The polynomial whose roots are the n-th powers of those of `f`:
/// `(-1)^((n-1) d) Res_x(f(x), y - x^n)` for `f` of degree `d`, which is
/// `prod_k f(z^k x)` for the n-th roots of unity `z^k` as a polynomial in
/// `x^n`.
fn power_polynomial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let n = a.int(1)?;
    if n.sign() <= 0 {
        return Err(arg_ge(2, n, 1));
    }
    let n = n.to_u64().filter(|&k| k < 1 << 20).ok_or_else(|| RuntimeError::runtime("Argument 2 is too large"))? as usize;
    if n == 1 || len(&f) == 0 {
        return one(like(&f, f.x.clone()));
    }
    // Over R[y]: F(x) with constant coefficients, and G(x) = y - x^n.
    let ry = f.x.ctx().clone();
    let outer = Ctx::poly(&ry);
    let cs: Vec<Elem> = (0..len(&f)).map(|i| Elem::poly_from_coeffs(&ry, &[f.x.poly_coeff(i)])).collect::<Result<_, _>>()?;
    let big_f = Elem::poly_from_coeffs(&outer, &cs)?;
    let mut gs = vec![Elem::zero(&ry); n + 1];
    gs[0] = ry.generator()?;
    gs[n] = Elem::from_i64(&ry, -1)?;
    let big_g = Elem::poly_from_coeffs(&outer, &gs)?;
    let mut r = big_f.poly_resultant(&big_g)?;
    if (n - 1) * (len(&f) - 1) % 2 == 1 {
        r = r.neg()?;
    }
    one(like(&f, r))
}

// ----- greatest common divisors -------------------------------------------------------

/// Over which coefficient rings gcds are computed.
fn gcd_ring(f: &Elt) -> RResult<()> {
    let b = bctx(f);
    if matches!(b.kind(), CtxKind::Integers) || fu::over_field(f.x.ctx()) {
        return Ok(());
    }
    Err(RuntimeError::runtime("Algorithm is not available for this kind of coefficient ring"))
}

fn gcd(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = pair(it, a)?;
    gcd_ring(&f)?;
    one(like(&f, fu::gcd(&f.x, &g)?))
}

fn xgcd(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = pair(it, a)?;
    match fu::xgcd(&f.x, &g) {
        Ok((d, s, t)) => Ok(vals![like(&f, d), like(&f, s), like(&f, t)]),
        Err(GrError::Domain) => Err(RuntimeError::runtime("Coefficient ring of argument 1 is not a field")),
        Err(e) => Err(e.into()),
    }
}

fn lcm(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = pair(it, a)?;
    gcd_ring(&f)?;
    if len(&f) == 0 || g.poly_len() == 0 {
        return one(like(&f, Elem::zero(f.x.ctx())));
    }
    let d = fu::gcd(&f.x, &g)?;
    let l = Elt { parent: f.parent.clone(), x: fu::divides(&f.x, &d)?.expect("the gcd divides").mul(&g)? };
    one(like(&f, normalized(it, &l)?))
}

/// The unit `u` of the coefficient ring `base` making `u c` normalized: the
/// sign over the integers, the inverse over a field, the unit of
/// `Normalize` over a residue class ring, and recursively that of the
/// leading coefficient over a polynomial ring.
pub(crate) fn norm_unit(it: &mut Interp, base: &Value, c: &Elem) -> RResult<Elem> {
    let ctx = c.ctx().clone();
    if c.is_zero() == Truth::True {
        return Ok(Elem::one(&ctx)?);
    }
    if let Some((_, r)) = ring_of(base) {
        match &r.kind {
            RingKind::UPoly { base: b2, .. } => {
                let b2 = b2.clone();
                let u = norm_unit(it, &b2, &fu::lead(c))?;
                return Ok(Elem::poly_from_coeffs(&ctx, &[u])?);
            }
            RingKind::MPoly { base: b2, .. } => {
                let b2 = b2.clone();
                let u = norm_unit(it, &b2, &c.mpoly_term(0).0)?;
                let mut e = Elem::zero(&ctx);
                e.mpoly_set_scalar(&u)?;
                return Ok(e);
            }
            RingKind::Residue(_) => {
                let v = it.elem_to_value(base, c.clone());
                let mut args = vec![v];
                let out = it.call_intrinsic(crate::sym::Sym::new("Normalize"), &mut args, &[false], Vec::new(), 2, false, Default::default(), None)?;
                let u = out.and_then(|vs| vs.into_iter().nth(1)).unwrap_or(Value::int(1));
                return Ok(it.to_structure_elem(base, &u, false)?.unwrap_or(Elem::one(&ctx)?));
            }
            _ => {}
        }
    }
    if matches!(ctx.kind(), CtxKind::Integers) {
        return Ok(Elem::from_i64(&ctx, if c.to_integer()?.sign() < 0 { -1 } else { 1 })?);
    }
    if is_field(base) {
        return Ok(c.inv()?);
    }
    Ok(Elem::one(&ctx)?)
}

/// The normalized associate: positive leading coefficient over the
/// integers, monic over a field, and so on (see `norm_unit`).
fn normalized(it: &mut Interp, f: &Elt) -> RResult<Elem> {
    if len(f) == 0 {
        return Ok(f.x.clone());
    }
    let u = norm_unit(it, &base_of(f), &fu::lead(&f.x))?;
    Ok(f.x.poly_mul_scalar(&u)?)
}

fn normalize(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    one(like(&f, normalized(it, &f)?))
}

/// The content and the primitive part: over the integers the gcd of the
/// coefficients (the primitive part keeps the sign), over a field 1, over
/// `Z/nZ` the gcd of the coefficients and n, and over a polynomial ring
/// the gcd of the coefficients there.
fn contpp(it: &Interp, f: &Elt) -> RResult<(Value, Value)> {
    let b = bctx(f);
    if is_integers(f) {
        let c = fu::content_z(&f.x);
        let pp = if c.is_zero() { f.x.clone() } else { fu::divexact_z(&f.x, &c) };
        return Ok((Value::Int(c), like(f, pp)));
    }
    if fu::over_field(f.x.ctx()) {
        let one_c = if len(f) == 0 { Elem::zero(&b) } else { Elem::one(&b)? };
        return Ok((cval(it, f, one_c), like(f, f.x.clone())));
    }
    if let Some((_, r)) = ring_of(&base_of(f)) {
        match &r.kind {
            RingKind::Residue(m) => {
                let cs: Vec<Integer> = (0..len(f)).map(|i| Ok(f.x.poly_coeff(i).to_integer()?)).collect::<RResult<_>>()?;
                let c = cs.iter().fold(m.clone(), |g, x| g.gcd(x));
                let pp: Vec<Elem> = cs.iter().map(|x| Elem::from_integer(&b, &x.divexact(&c))).collect::<Result<_, _>>()?;
                return Ok((cval(it, f, Elem::from_integer(&b, &c)?), like(f, Elem::poly_from_coeffs(f.x.ctx(), &pp)?)));
            }
            RingKind::UPoly { .. } if len(f) > 0 && (matches!(b.base().map(|c| c.kind()), Some(CtxKind::Integers)) || fu::over_field(&b)) => {
                let mut c = Elem::zero(&b);
                for i in 0..len(f) {
                    c = fu::gcd(&c, &f.x.poly_coeff(i))?;
                }
                let pp: Vec<Elem> = (0..len(f)).map(|i| Ok(fu::divides(&f.x.poly_coeff(i), &c)?.expect("the content divides"))).collect::<RResult<_>>()?;
                return Ok((cval(it, f, c), like(f, Elem::poly_from_coeffs(f.x.ctx(), &pp)?)));
            }
            _ => {}
        }
    }
    Err(RuntimeError::runtime("Algorithm is not available for this kind of coefficient ring"))
}

fn content(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(contpp(it, &pol(a, 0))?.0)
}

fn primitive_part(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(contpp(it, &pol(a, 0))?.1)
}

fn content_and_primitive_part(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (c, p) = contpp(it, &pol(a, 0))?;
    Ok(vals![c, p])
}

// ----- polynomials over the integers --------------------------------------------------

/// The coefficients of an integer polynomial.
fn int_coeffs(f: &Elt) -> RResult<Vec<Integer>> {
    if !is_integers(f) {
        return Err(RuntimeError::runtime("Coefficient ring of argument must be Z"));
    }
    (0..len(f)).map(|i| Ok(f.x.poly_coeff(i).to_integer()?)).collect()
}

fn sign(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let cs = int_coeffs(&pol(a, 0))?;
    intv(Integer::from_i64(cs.last().map_or(0, |c| c.sign() as i64)))
}

fn abs(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let cs = int_coeffs(&f)?;
    one(like(&f, if cs.last().is_some_and(|c| c.sign() < 0) { f.x.neg()? } else { f.x.clone() }))
}

fn max_norm(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let cs = int_coeffs(&pol(a, 0))?;
    intv(cs.iter().map(|c| c.abs()).max().unwrap_or_default())
}

fn sum_norm(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let cs = int_coeffs(&pol(a, 0))?;
    intv(cs.iter().fold(Integer::zero(), |s, c| &s + &c.abs()))
}

/// Dedekind's criterion: with `f = prod g_i^e_i` mod p, `g = prod g_i`
/// and `h = f / g` mod p (lifted), and `F = (g h - f) / p`, the equation
/// order of `f` is maximal at p iff `gcd(F, g, h) = 1` mod p.
fn dedekind_test(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let p = a.int(1)?.clone();
    if !is_integers(&f) {
        return Err(RuntimeError::runtime("argument 1 not a polynomial over Z"));
    }
    if fu::lead(&f.x).is_one() != Truth::True {
        return Err(RuntimeError::runtime("Argument 1 is not monic"));
    }
    if !p.is_prime() {
        return Err(super::arg_prime(2, &p));
    }
    let fp = it.finite_field(&p, 1)?;
    let px = it.poly_ring(&fp, true)?;
    let Some((_, pr)) = ring_of(&px) else { unreachable!() };
    let pctx = pr.ctx.clone();
    let zx = f.x.ctx().clone();
    let fbar = fu::convert(&pctx, &f.x)?;
    let fac = fu::factor(&fbar)?;
    let mut g = Elem::one(&pctx)?;
    for (q, _) in &fac.factors {
        g = g.mul(q)?;
    }
    let h = fu::divrem(&fbar, &g)?.0;
    let lift = |e: &Elem| -> RResult<Elem> {
        let cs: Vec<Elem> = (0..e.poly_len()).map(|i| Elem::from_integer(&Ctx::integers(), &e.poly_coeff(i).to_integer()?)).collect::<Result<_, _>>()?;
        Ok(Elem::poly_from_coeffs(&zx, &cs)?)
    };
    let big = lift(&g)?.mul(&lift(&h)?)?.sub(&f.x)?;
    let cs: Vec<Elem> = (0..big.poly_len()).map(|i| Ok::<_, RuntimeError>(Elem::from_integer(&Ctx::integers(), &big.poly_coeff(i).to_integer()?.divexact(&p))?)).collect::<Result<_, _>>()?;
    let fq = fu::convert(&pctx, &Elem::poly_from_coeffs(&zx, &cs)?)?;
    let d = fu::gcd(&fu::gcd(&fq, &g)?, &h)?;
    boolv(d.poly_len() == 1)
}

// ----- polynomials over finite fields ----------------------------------------------------

/// The coefficient field of a polynomial ring over a finite field (not a
/// residue class ring), with its characteristic and degree.
fn finite_base(r: &Ring) -> RResult<(Value, Integer, u64)> {
    let base = r.base().expect("a polynomial ring").clone();
    if let Some((_, k)) = ring_of(&base) {
        if let RingKind::Finite(f) = &k.kind {
            let (p, e) = (f.p.clone(), f.degree);
            return Ok((base, p, e));
        }
    }
    Err(RuntimeError::runtime("Polynomial ring must be defined over a finite field"))
}

/// The number of monic irreducible polynomials of degree `d` over the field
/// of `q` elements, `(1/d) sum_{k | d} mu(k) q^(d/k)`.
fn prime_poly_count(q: &Integer, d: u64) -> Integer {
    let mut s = Integer::zero();
    for k in (1..=d).filter(|k| d % k == 0) {
        match Integer::from_u64(k).moebius_mu() {
            1 => s = &s + &q.pow(d / k),
            -1 => s = &s - &q.pow(d / k),
            _ => {}
        }
    }
    s.divexact(&Integer::from_u64(d))
}

fn degree_arg(a: &CallArgs, i: usize) -> RResult<u64> {
    let d = a.int(i)?;
    if d.sign() <= 0 {
        return Err(arg_ge(i + 1, d, 1));
    }
    d.to_u64().filter(|&d| d < 1 << 30).ok_or_else(|| RuntimeError::runtime(format!("Argument {} ({d}) is too large", i + 1)))
}

fn number_of_prime_polynomials(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let q = match &a.args[0] {
        Value::Int(q) => {
            let pp = q > &Integer::one() && q.perfect_power().map_or(q.clone(), |(b, _)| b).is_prime();
            if !pp {
                return Err(RuntimeError::runtime(format!("Argument 1 ({q}) is not a prime power")));
            }
            q.clone()
        }
        Value::Struct(s) => match &s.kind {
            StructKind::Ring(r) => match (&r.kind, r.finite_field()) {
                (RingKind::UPoly { .. }, _) => {
                    let (_, p, e) = finite_base(r)?;
                    p.pow(e)
                }
                (_, Some(f)) => f.order(),
                _ => unreachable!("a finite field or polynomial ring"),
            },
            _ => unreachable!("a finite field or polynomial ring"),
        },
        _ => unreachable!("a finite field or polynomial ring"),
    };
    let d = degree_arg(a, 1)?;
    intv(prime_poly_count(&q, d))
}

/// The monic irreducible polynomials of degree `d` over `K = GF(q)` in
/// Magma's order, at most `max` of them: `x` and then `x - a^k` for
/// `k = 1, ..., q - 1` in degree 1, and otherwise the minimal polynomials of
/// `a^k` for the least elements `k` of the classes `{k q^i mod (q^d - 1)}`
/// of size `d`, by increasing `k`, where `a` is the primitive element of
/// `GF(q^d)` (a root of its Conway polynomial).
fn prime_polys_of_degree(it: &mut Interp, px: &Rc<Struct>, d: u64, max: usize) -> RResult<Vec<Elem>> {
    let StructKind::Ring(pr) = &px.kind else { unreachable!() };
    let (k, p, e) = finite_base(pr)?;
    let kctx = ring_of(&k).expect("a finite field").1.ctx.clone();
    let q = p.pow(e);
    let mut out = Vec::new();
    if max == 0 {
        return Ok(out);
    }
    let mono = |c: Elem| Elem::poly_from_coeffs(&pr.ctx, &[c.neg()?, Elem::one(&kctx)?]);
    let prim = |it: &mut Interp, f: &Value| -> RResult<Elem> {
        let a = it.call_intrinsic_named(crate::sym::Sym::new("PrimitiveElement"), vec![f.clone()])?;
        Ok(it.to_structure_elem(f, &a, false)?.expect("an element of the field"))
    };
    if d == 1 {
        out.push(fu::monomial(&pr.ctx, &Elem::one(&kctx)?, 1)?);
        let a = prim(it, &k)?;
        let mut c = a.clone();
        while out.len() < max && c.is_one() != Truth::True {
            out.push(mono(c.clone())?);
            c = c.mul(&a)?;
        }
        if out.len() < max {
            out.push(mono(c)?);
        }
        return Ok(out);
    }
    // GF(q^d) with q = p^e, and the embedding of K in it.
    let lv = it.finite_field(&p, e * d)?;
    let Some((_, lr)) = ring_of(&lv) else { unreachable!() };
    let lctx = lr.ctx.clone();
    let conway = |r: &Ring| r.finite_field().is_some_and(|f| f.conway || f.degree == 1);
    let kr = ring_of(&k).expect("a finite field").1;
    if e > 1 && !(conway(kr) && conway(lr) && kr.finite_field().is_some_and(|f| f.default)) {
        return Err(not_available());
    }
    let a = prim(it, &lv)?;
    let n = &q.pow(d) - &Integer::one();
    // The subfield GF(q) is generated by b = a^((q^d - 1)/(q - 1)), the
    // image of the generator of K; coefficients map back by logarithms.
    let r = n.divexact(&(&q - &Integer::one()));
    let mut logs: std::collections::HashMap<Vec<Integer>, u64> = Default::default();
    if e > 1 {
        let qm1 = (&q - &Integer::one()).to_u64().filter(|&m| m <= 1 << 20).ok_or_else(not_available)?;
        let b = a.pow(&r)?;
        let mut c = Elem::one(&lctx)?;
        for j in 0..qm1 {
            logs.insert(c.fq_coords(), j);
            c = c.mul(&b)?;
        }
    }
    let w = if e > 1 { Some(kctx.generator()?) } else { None };
    let to_k = |c: &Elem| -> RResult<Elem> {
        if c.is_zero() == Truth::True {
            return Ok(Elem::zero(&kctx));
        }
        match &w {
            None => Ok(Elem::from_integer(&kctx, &c.fq_prime_value().expect("a coefficient in the prime field"))?),
            Some(w) => Ok(w.pow_i64(*logs.get(&c.fq_coords()).expect("a coefficient in the subfield") as i64)?),
        }
    };
    let qi = q.to_u64();
    let mut kk = Integer::one();
    while out.len() < max && kk < n {
        // Is kk the least element of its class, of size d?
        let mut m = kk.clone();
        let mut leader = true;
        for _ in 1..d {
            m = (&m * &q).div_rem_euclid(&n).expect("a non-zero modulus").1;
            if m <= kk {
                leader = false;
                break;
            }
        }
        if leader {
            // The product of x - g over the conjugates g of a^kk.
            let mut g = a.pow(&kk)?;
            let mut cs = vec![Elem::one(&lctx)?];
            for _ in 0..d {
                let mut next = vec![Elem::zero(&lctx); cs.len() + 1];
                for (j, c) in cs.iter().enumerate() {
                    next[j + 1] = next[j + 1].add(c)?;
                    next[j] = next[j].sub(&g.mul(c)?)?;
                }
                cs = next;
                g = match qi {
                    Some(_) => g.fq_frobenius(e as i64)?,
                    None => g.pow(&q)?,
                };
            }
            let kcs: Vec<Elem> = cs.iter().map(&to_k).collect::<RResult<_>>()?;
            out.push(Elem::poly_from_coeffs(&pr.ctx, &kcs)?);
        }
        kk = &kk + &Integer::one();
    }
    Ok(out)
}

/// The polynomials of degree `d` (or the first `n`, continuing into higher
/// degrees if needed).
fn prime_polynomials(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (px, pr) = ring_arg(a, 0);
    let (_, p, e) = finite_base(&pr)?;
    let d = degree_arg(a, 1)?;
    let n = if a.args.len() > 2 {
        let n = a.int(2)?;
        if n.sign() < 0 {
            return Err(arg_ge(3, n, 0));
        }
        n.to_u64().unwrap_or(u64::MAX)
    } else {
        prime_poly_count(&p.pow(e), d).to_u64().unwrap_or(u64::MAX)
    };
    if n > 1 << 24 {
        return Err(RuntimeError::runtime("Too many polynomials requested"));
    }
    let mut out = Vec::new();
    let mut deg = d;
    while (out.len() as u64) < n {
        let more = prime_polys_of_degree(it, &px, deg, (n - out.len() as u64) as usize)?;
        out.extend(more);
        deg += 1;
    }
    let vals = out.into_iter().map(|x| make_elt(&px, x)).collect();
    one(Value::seq(Some(Value::Struct(px)), vals))
}

/// A random monic irreducible polynomial of degree `d`.
fn random_prime_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (px, pr) = ring_arg(a, 0);
    let (k, p, e) = finite_base(&pr)?;
    let d = degree_arg(a, 1)?;
    let kctx = ring_of(&k).expect("a finite field").1.ctx.clone();
    for _ in 0..1_000_000 {
        let mut cs = Vec::with_capacity(d as usize + 1);
        for _ in 0..d {
            let coords: Vec<Integer> = (0..e).map(|_| it.rng.below(&p)).collect();
            cs.push(if e == 1 { Elem::from_integer(&kctx, &coords[0])? } else { Elem::fq_from_coords(&kctx, &coords)? });
        }
        cs.push(Elem::one(&kctx)?);
        let f = Elem::poly_from_coeffs(&pr.ctx, &cs)?;
        if fu::is_irreducible(&f)? {
            return one(make_elt(&px, f));
        }
    }
    Err(RuntimeError::runtime("No irreducible polynomial found"))
}

/// The Jacobi symbol `(a/b)` over `GF(q)`, q odd: multiplicative in `b`,
/// and for irreducible `b` whether `a` is a square modulo `b` (0 if `b`
/// divides `a`). Computed by the Euclidean algorithm with the reciprocity
/// law `(a/b) = (-1)^((q-1)/2 deg a deg b) (b/a)` for monic coprime `a`,
/// `b`, and `(c/b) = chi(c)^deg b` for constants `c`.
fn jacobi_symbol(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (fa, fb) = (pol(a, 0), pol(a, 1));
    if fa.ring().id != fb.ring().id {
        return Err(bare(RuntimeError::runtime(format!("Arguments are not compatible\nArgument types given: {}, {}", it.type_name_ext(&fa.parent_value()), it.type_name_ext(&fb.parent_value())))));
    }
    let q = match finite_base(fa.ring()) {
        Ok((_, p, e)) if p != Integer::from_i64(2) => p.pow(e),
        _ => return Err(bare(RuntimeError::runtime("Only polynomials over finite fields of odd characteristic are supported"))),
    };
    if len(&fb) < 2 {
        return Err(bare(RuntimeError::runtime("The second polynomial must have degree at least 1")));
    }
    let half = (&q - &Integer::one()).divexact(&Integer::from_i64(2));
    let half_odd = !half.is_even();
    let mut b = fu::make_monic(&fb.x)?;
    let mut x = fu::divrem(&fa.x, &b)?.1;
    let mut sign = 1;
    loop {
        let db = b.poly_len() - 1;
        if db == 0 {
            return intv(Integer::from_i64(sign));
        }
        if x.poly_len() == 0 {
            return intv(Integer::zero());
        }
        let c = fu::lead(&x);
        if c.pow(&half)?.is_one() != Truth::True && db % 2 == 1 {
            sign = -sign;
        }
        let x1 = fu::make_monic(&x)?;
        if half_odd && (x1.poly_len() - 1) % 2 == 1 && db % 2 == 1 {
            sign = -sign;
        }
        let r = fu::divrem(&b, &x1)?.1;
        b = x1;
        x = r;
    }
}

// ----- factorization -------------------------------------------------------------------

fn not_available() -> RuntimeError {
    RuntimeError::runtime("Algorithm is not available for this kind of coefficient ring")
}

fn can_factor(f: &Elt) -> RResult<()> {
    if fu::can_factor(f.x.ctx()) { Ok(()) } else { Err(not_available()) }
}

/// Whether polynomials over the ring `r` factor: over the integers, the
/// rationals, finite fields, prime residue rings, and (as Magma has it)
/// polynomial rings over these.
fn has_factorization(r: &Value) -> bool {
    let Value::Struct(s) = r else { return false };
    match &s.kind {
        StructKind::Integers | StructKind::Rationals => true,
        StructKind::Ring(ring) => match &ring.kind {
            RingKind::Finite(_) => true,
            RingKind::Residue(m) => m.is_prime(),
            RingKind::UPoly { base, .. } | RingKind::MPoly { base, .. } => has_factorization(base),
            RingKind::Complex(_) | RingKind::UPolyRes { .. } => false,
        },
        _ => false,
    }
}

/// Constant polynomials `<p, e>` for the prime powers of an integer.
fn prime_factors(f: &Elt, c: &Integer) -> RResult<Vec<(Elem, u64)>> {
    let zz = bctx(f);
    let Some(fz) = c.abs().factor() else { return Ok(Vec::new()) };
    fz.factors.iter().map(|(p, e)| Ok((Elem::poly_from_coeffs(f.x.ctx(), &[Elem::from_integer(&zz, p)?])?, *e))).collect()
}

/// A factorization sequence `[<q, k>, ...]` of polynomials in the ring of
/// `f`, in Magma's order: by multiplicity first if `by_mult`, then by
/// degree and coefficients from the top.
fn factorization_seq(it: &mut Interp, f: &Elt, mut v: Vec<(Elem, u64)>, by_mult: bool) -> Value {
    let ring = f.ring_rc();
    v.sort_by(|a, b| {
        let m = if by_mult { a.1.cmp(&b.1) } else { Ordering::Equal };
        m.then_with(|| it.ring_elt_cmp(&ring, &a.0, &b.0).ok().flatten().unwrap_or(Ordering::Equal))
    });
    Value::seq(None, v.into_iter().map(|(q, k)| Value::tuple(vec![like(f, q), Value::int(k as i64)])).collect())
}

/// The factorization into irreducibles, normalized as `Normalize` does,
/// and the unit: over the integers the prime factors of the content come
/// first as constant factors and the unit is the sign.
fn factorization(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    nonzero(&f)?;
    can_factor(&f)?;
    let fac = fu::factor(&f.x)?;
    let mut v = fac.factors;
    let unit = if is_integers(&f) {
        let c = fac.unit.to_integer()?;
        v.extend(prime_factors(&f, &c)?);
        Value::int(if c.sign() < 0 { -1 } else { 1 })
    } else {
        cval(it, &f, fac.unit)
    };
    let seq = factorization_seq(it, &f, v, false);
    if a.nresults >= 2 { Ok(vals![seq, unit]) } else { one(seq) }
}

fn is_irreducible(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    nonzero(&f)?;
    can_factor(&f)?;
    boolv(fu::is_irreducible(&f.x)?)
}

/// The squarefree factorization, by increasing multiplicity; over the
/// integers the content contributes its prime powers `<p, e>`.
fn squarefree_factorization(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    nonzero(&f)?;
    can_factor(&f)?;
    let fac = fu::factor_squarefree(&f.x)?;
    let mut v = fac.factors;
    if is_integers(&f) {
        v.extend(prime_factors(&f, &fac.unit.to_integer()?)?);
    }
    one(factorization_seq(it, &f, v, true))
}

/// Whether `f` (of positive degree, over a field) has no repeated factor.
fn squarefree(f: &Elem) -> RResult<bool> {
    Ok(fu::gcd(f, &f.poly_derivative()?)?.poly_len() == 1)
}

/// The products of the irreducible factors of each degree: all of them in
/// Magma's order of the products, or those up to degree `Degree` by
/// increasing degree.
fn distinct_degree_factorization(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let limit = match a.param("Degree") {
        Some(Value::Int(n)) => n.clone(),
        _ => Integer::zero(),
    };
    if limit.sign() < 0 {
        return Err(RuntimeError::runtime("Degree should be greater than or equal to 0"));
    }
    if !fu::over_finite_field(f.x.ctx()) {
        return Err(RuntimeError::runtime("Coefficient ring of argument 1 is not a finite field"));
    }
    nonzero(&f)?;
    if len(&f) > 1 && !squarefree(&f.x)? {
        return Err(RuntimeError::runtime("Argument 1 is not squarefree"));
    }
    let mut v = fu::distinct_degree(&f.x)?;
    if limit.is_zero() {
        let ring = f.ring_rc();
        v.sort_by(|a, b| it.ring_elt_cmp(&ring, &a.1, &b.1).ok().flatten().unwrap_or(Ordering::Equal));
    } else {
        v.retain(|(d, _)| Integer::from_i64(*d as i64) <= limit);
    }
    one(Value::seq(None, v.into_iter().map(|(d, g)| Value::tuple(vec![Value::int(d as i64), like(&f, g)])).collect()))
}

/// The irreducible factors of `f`, which should be a product of distinct
/// irreducibles of degree `d` (with `g = x^q mod f`); the factors are found
/// by factoring `f`, so other input gives its irreducible factors.
fn equal_degree_factorization(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    if !fu::over_finite_field(f.x.ctx()) {
        return Err(RuntimeError::runtime("Coefficient ring of argument 1 is not a finite field"));
    }
    nonzero(&f)?;
    let ring = f.ring_rc();
    let mut v: Vec<Elem> = fu::factor(&f.x)?.factors.into_iter().map(|(q, _)| q).collect();
    v.sort_by(|a, b| it.ring_elt_cmp(&ring, a, b).ok().flatten().unwrap_or(Ordering::Equal));
    one(poly_seq(&f, v))
}

fn is_separable(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    if !fu::can_factor(f.x.ctx()) || !fu::over_field(f.x.ctx()) {
        return Err(RuntimeError::runtime("Coefficient ring of argument 1 must be a field with factorization"));
    }
    if len(&f) < 2 {
        return Err(RuntimeError::runtime("Degree must be >= 1"));
    }
    boolv(squarefree(&f.x)?)
}

fn has_polynomial_factorization(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(has_factorization(&a.args[0]))
}

/// The product of a factorization sequence of polynomials.
fn facpol(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let q = a.seq(0)?.clone();
    let bad = || bare(RuntimeError::runtime("Not the factorisation sequence of a polynomial"));
    let mut prod: Option<Value> = None;
    for t in &q.elems {
        let Value::Tuple(t) = t else { return Err(bad()) };
        let [g @ Value::Elt(e), k @ Value::Int(_)] = &t.elems[..] else { return Err(bad()) };
        if !matches!(e.ring().kind, RingKind::UPoly { .. } | RingKind::MPoly { .. }) {
            return Err(bad());
        }
        let p = it.binop(BinOp::Pow, g.clone(), k.clone())?;
        prod = Some(match prod {
            Some(x) => it.binop(BinOp::Mul, x, p)?,
            None => p,
        });
    }
    match prod {
        Some(p) => one(p),
        None => Err(bare(RuntimeError::runtime("Illegal null sequence"))),
    }
}

// ----- resultants and discriminants --------------------------------------------------------

fn resultant(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = pair(it, a)?;
    one(cval(it, &f, fu::resultant(&f.x, &g)?))
}

fn discriminant(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    if len(&f) < 2 {
        return Err(RuntimeError::runtime("Degree of argument is less than 1"));
    }
    one(cval(it, &f, fu::discriminant(&f.x)?))
}

// ----- Hensel lifting ------------------------------------------------------------------

/// Lift the factorization of the integer polynomial `f` modulo a prime `p`
/// (monic squarefree factors `s`, whose product is `f / lc(f)`) to monic
/// factors modulo the modulus `p^k` of the coefficient ring of `P`.
fn hensel_lift(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    if !is_integers(&f) {
        return Err(RuntimeError::runtime("Argument 1 not a polynomial over Z"));
    }
    let s = a.seq(1)?.clone();
    let (pst, pr) = ring_arg(a, 2);
    let modulus = match pr.base().and_then(ring_of) {
        Some((_, r)) => match &r.kind {
            RingKind::Residue(m) => m.clone(),
            _ => return Err(RuntimeError::runtime("Argument 3 not a polynomial algebra over Zm")),
        },
        None => return Err(RuntimeError::runtime("Argument 3 not a polynomial algebra over Zm")),
    };
    let not_seq = || RuntimeError::runtime("Given sequence is not a factorization sequence");
    let Some(first) = s.elems.first() else { return Err(RuntimeError::runtime("Sequence argument 2 must be non-empty")) };
    let Value::Elt(s1) = first else { return Err(not_seq()) };
    let p = ring_props(&base_of(s1)).map(|pp| pp.characteristic).unwrap_or_default();
    // The modulus must be a power p^k of the characteristic of the factors.
    let (k, m) = if p > Integer::one() { modulus.remove(&p) } else { (0, modulus.clone()) };
    if k == 0 || !m.is_one() {
        return Err(RuntimeError::runtime("Invalid modulus of coefficient ring of argument 3"));
    }
    let pctx = s1.x.ctx().clone();
    let mut factors = Vec::with_capacity(s.elems.len());
    for (i, v) in s.elems.iter().enumerate() {
        let Value::Elt(e) = v else { return Err(not_seq()) };
        if len(e) == 0 || fu::lead(&e.x).is_one() != Truth::True {
            return Err(RuntimeError::runtime(format!("element {} of argument 2 is not monic", i + 1)));
        }
        factors.push(if e.ring().id == s1.ring().id { e.x.clone() } else { fu::convert(&pctx, &e.x).map_err(|_| not_seq())? });
    }
    // f made monic modulo p^k, with its coefficients in [0, p^k).
    let pk = pst.clone();
    let fk = fu::convert(&pr.ctx, &f.x)?;
    let fk = fk.poly_mul_scalar(&fu::lead(&fk).inv().map_err(|_| not_seq())?)?;
    let zx = f.x.ctx().clone();
    let zz = Ctx::integers();
    let lift = |e: &Elem| -> RResult<Elem> {
        let cs: Vec<Elem> = (0..e.poly_len()).map(|i| Elem::from_integer(&zz, &e.poly_coeff(i).to_integer()?)).collect::<Result<_, _>>()?;
        Ok(Elem::poly_from_coeffs(&zx, &cs)?)
    };
    let fz = lift(&fk)?;
    // The factors must multiply to f modulo p and be coprime.
    let mut prod = Elem::one(&pctx)?;
    for g in &factors {
        prod = prod.mul(g)?;
    }
    let fp = fu::convert(&pctx, &fz)?;
    if prod.equal(&fp) != Truth::True || !squarefree(&fp)? {
        return Err(not_seq());
    }
    let lifted = if k == 1 { factors.clone() } else { fu::hensel_lift(&fz, &factors, k).map_err(|_| not_seq())? };
    let out: Vec<Value> = lifted.iter().map(|g| Ok(make_elt(&pk, fu::convert(&pr.ctx, g)?))).collect::<RResult<_>>()?;
    one(Value::seq(Some(Value::Struct(pst)), out))
}

// ----- special families ------------------------------------------------------------------

/// Argument 1 of the families: one of Magma's small non-negative integers.
fn family_index(a: &CallArgs) -> RResult<u64> {
    let n = a.int(0)?;
    match n.to_u64() {
        Some(k) if k < 1 << 30 => Ok(k),
        _ => Err(RuntimeError::runtime(format!("Argument 1 ({n}) is not small and non-negative"))),
    }
}

/// A polynomial of a family computed by FLINT, in the global polynomial
/// ring over `base` (the integers or the rationals).
fn family_poly(it: &mut Interp, base: Value, fam: fu::Family, n: Option<u64>) -> RResult<Vals> {
    let px = it.poly_ring(&base, true)?;
    let Some((st, r)) = ring_of(&px) else { unreachable!() };
    let f = match n {
        Some(n) => fu::family(&r.ctx, fam, n),
        None => Elem::zero(&r.ctx),
    };
    one(make_elt(st, f))
}

fn chebyshev_t(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = family_index(a)?;
    family_poly(it, Value::integers(), fu::Family::ChebyshevT, Some(n))
}

/// Magma's `ChebyshevU(n)` is `U_(n-1)`, of degree `n - 1` (0 for n = 0).
fn chebyshev_u(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = family_index(a)?;
    family_poly(it, Value::integers(), fu::Family::ChebyshevU, n.checked_sub(1))
}

fn legendre_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = family_index(a)?;
    family_poly(it, Value::rationals(), fu::Family::Legendre, Some(n))
}

fn hermite_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = family_index(a)?;
    family_poly(it, Value::integers(), fu::Family::Hermite, Some(n))
}

fn bernoulli_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?;
    if n.sign() < 0 {
        return Err(RuntimeError::runtime(format!("Argument 1 ({n}) should be non-negative")));
    }
    let n = n.to_u64().filter(|&k| k < 1 << 30).ok_or_else(|| RuntimeError::runtime(format!("Argument 1 ({n}) is too large")))?;
    family_poly(it, Value::rationals(), fu::Family::Bernoulli, Some(n))
}

/// The polynomials of a family with parameter `m` are computed over the
/// parent of `m` (its field of fractions if `field`): the global polynomial
/// ring there, its context, and `m` as a coefficient.
fn param_ring(it: &mut Interp, m: &Value, field: bool) -> RResult<(Rc<Struct>, Rc<Ctx>, Elem)> {
    let mut k = it.parent_of(m)?;
    if field && !is_field(&k) {
        if !matches!(k.as_struct(), Some(StructKind::Integers)) {
            return Err(RuntimeError::runtime("Ring does not have a determinable field of fractions"));
        }
        k = Value::rationals();
    }
    let px = it.poly_ring(&k, true)?;
    let Some((st, r)) = ring_of(&px) else { unreachable!() };
    let (st, pctx) = (st.clone(), r.ctx.clone());
    let me = it.to_structure_elem(&k, m, false)?.ok_or_else(|| RuntimeError::runtime("Bad argument types"))?;
    Ok((st, pctx, me))
}

/// The three-term recurrence `f_n = (s_n x + t_n) f_(n-1) + u_n f_(n-2)`
/// in `pctx` from `f_0` and `f_1`, where `coeffs(n)` gives `(s_n, t_n, u_n)`.
fn recurrence(pctx: &Rc<Ctx>, n: u64, f0: Elem, f1: Elem, mut coeffs: impl FnMut(u64) -> GrResult<(Elem, Elem, Elem)>) -> GrResult<Elem> {
    if n == 0 {
        return Ok(f0);
    }
    let (mut a, mut b) = (f0, f1);
    for k in 2..=n {
        let (s, t, u) = coeffs(k)?;
        let lin = Elem::poly_from_coeffs(pctx, &[t, s])?;
        let c = lin.mul(&b)?.add(&a.poly_mul_scalar(&u)?)?;
        a = std::mem::replace(&mut b, c);
    }
    Ok(b)
}

/// `1/n` in the coefficient field (0 where n is not invertible there, which
/// is what Magma's recurrences give).
fn inv_or_zero(k: &Rc<Ctx>, n: u64) -> GrResult<Elem> {
    Ok(Elem::from_i64(k, n as i64)?.inv().unwrap_or_else(|_| Elem::zero(k)))
}

/// The generalized Laguerre polynomial `L_n^(m)`: `L_0 = 1`,
/// `L_1 = 1 + m - x`, `n L_n = (2n + m - 1 - x) L_(n-1) - (n - 1 + m) L_(n-2)`.
fn laguerre_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = family_index(a)?;
    if a.args.len() == 1 {
        return family_poly(it, Value::rationals(), fu::Family::Laguerre, Some(n));
    }
    let (st, pctx, m) = param_ring(it, &a.args[1].clone(), true)?;
    let k = pctx.base().expect("a polynomial ring").clone();
    let int = |v: i64| Elem::from_i64(&k, v);
    let f0 = Elem::one(&pctx)?;
    let f1 = Elem::poly_from_coeffs(&pctx, &[int(1)?.add(&m)?, int(-1)?])?;
    let f = recurrence(&pctx, n, f0, f1, |j| {
        let inv = inv_or_zero(&k, j)?;
        let t = int(2 * j as i64 - 1)?.add(&m)?.mul(&inv)?;
        let u = int(j as i64 - 1)?.add(&m)?.neg()?.mul(&inv)?;
        Ok((inv.neg()?, t, u))
    })?;
    one(make_elt(&st, f))
}

/// The Gegenbauer polynomial `C_n^(m)`: `C_0 = 1`, `C_1 = 2 m x`,
/// `n C_n = 2 (n - 1 + m) x C_(n-1) - (n + 2m - 2) C_(n-2)`.
fn gegenbauer_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = family_index(a)?;
    let (st, pctx, m) = param_ring(it, &a.args[1].clone(), true)?;
    let k = pctx.base().expect("a polynomial ring").clone();
    let int = |v: i64| Elem::from_i64(&k, v);
    let f0 = Elem::one(&pctx)?;
    let f1 = Elem::poly_from_coeffs(&pctx, &[Elem::zero(&k), m.add(&m)?])?;
    let f = recurrence(&pctx, n, f0, f1, |j| {
        let inv = inv_or_zero(&k, j)?;
        let s = int(j as i64 - 1)?.add(&m)?.mul(&int(2)?)?.mul(&inv)?;
        let u = int(j as i64 - 2)?.add(&m)?.add(&m)?.neg()?.mul(&inv)?;
        Ok((s, Elem::zero(&k), u))
    })?;
    one(make_elt(&st, f))
}

/// The Dickson polynomials `D_n(x, a)` (first kind, `D_0 = 2`) and
/// `E_n(x, a)` (second kind, `E_0 = 1`), with `f_1 = x` and
/// `f_n = x f_(n-1) - a f_(n-2)`, over the parent of `a`.
fn dickson(it: &mut Interp, a: &mut CallArgs, first: bool) -> RResult<Vals> {
    let n = family_index(a)?;
    let (st, pctx, c) = param_ring(it, &a.args[1].clone(), false)?;
    let k = pctx.base().expect("a polynomial ring").clone();
    let f0 = Elem::poly_from_coeffs(&pctx, &[Elem::from_i64(&k, if first { 2 } else { 1 })?])?;
    let f1 = fu::monomial(&pctx, &Elem::one(&k)?, 1)?;
    let nc = c.neg()?;
    let f = recurrence(&pctx, n, f0, f1, |_| Ok((Elem::one(&k)?, Elem::zero(&k), nc.clone())))?;
    one(make_elt(&st, f))
}

fn dickson_first(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    dickson(it, a, true)
}

fn dickson_second(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    dickson(it, a, false)
}

/// The n-th Swinnerton-Dyer polynomial, over the integers.
fn swinnerton_dyer_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?;
    if n.sign() <= 0 {
        return Err(bare(arg_ge(1, n, 1)));
    }
    let n = n.to_u64().filter(|&n| n <= 20).ok_or_else(|| RuntimeError::runtime(format!("Argument 1 ({n}) is too large")))?;
    let zx = it.poly_ring(&Value::integers(), true)?;
    let Some((st, r)) = ring_of(&zx) else { unreachable!() };
    one(make_elt(st, fu::swinnerton_dyer(&r.ctx, n)))
}

// ----- ideals and quotient rings ------------------------------------------------------------
//
// An ideal of a univariate polynomial ring P over a field is a structure of
// type RngUPol with its monic (or zero) generator (`StructKind::UPolIdeal`);
// the ideal generated by a unit is P itself. The quotient P/(f) is a ring
// of type RngUPolRes (`RingKind::UPolyRes`) whose elements are remainders
// modulo f in the context of P, reduced here rather than by FLINT.

/// The modulus of a quotient ring.
pub fn res_modulus(r: &Ring) -> &Elem {
    match &r.kind {
        RingKind::UPolyRes { modulus, .. } => modulus,
        _ => unreachable!("a polynomial quotient ring"),
    }
}

/// `x` reduced modulo the modulus `f` (monic, or over a field).
pub fn res_reduce(f: &Elem, x: Elem) -> GrResult<Elem> {
    if x.poly_len() < f.poly_len() {
        return Ok(x);
    }
    Ok(fu::divrem(&x, f)?.1)
}

/// The inverse of `x` modulo `f`: `None` if `x` is not a unit, an error
/// where Magma cannot decide (coefficient rings that are not fields).
pub fn res_inverse(f: &Elem, x: &Elem) -> RResult<Option<Elem>> {
    if !fu::over_field(f.ctx()) {
        if x.poly_len() == 1 && x.poly_coeff(0).is_invertible() == Truth::True {
            return Ok(Some(Elem::poly_from_coeffs(f.ctx(), &[x.poly_coeff(0).inv()?])?));
        }
        return Err(RuntimeError::runtime("Inverse/unit testing not available"));
    }
    if f.poly_len() == 1 {
        return Ok(Some(Elem::zero(f.ctx())));
    }
    let (d, s, _) = fu::xgcd(x, f)?;
    if d.poly_len() != 1 {
        return Ok(None);
    }
    Ok(Some(res_reduce(f, s)?))
}

/// `x^k` in a quotient ring (`k < 0` for units).
pub fn res_pow(f: &Elem, x: &Elem, k: &Integer) -> RResult<Elem> {
    let (x, k) = if k.sign() < 0 {
        match res_inverse(f, x).map_err(|e| e.in_context("^"))? {
            Some(y) => (y, -k),
            None => return Err(RuntimeError::runtime("Argument is not invertible").in_context("^")),
        }
    } else {
        (x.clone(), k.clone())
    };
    Ok(fu::powmod(&x, &k, f)?)
}

/// `x / y` in a quotient ring.
pub fn res_div(f: &Elem, x: &Elem, y: &Elem) -> RResult<Elem> {
    match res_inverse(f, y).map_err(|e| e.in_context("/"))? {
        Some(z) => Ok(res_reduce(f, x.mul(&z)?)?),
        None => Err(RuntimeError::runtime("Argument is not invertible").in_context("/")),
    }
}

/// The elements of a finite quotient ring, counting through the vectors of
/// coefficients (constant term fastest) with each coefficient running
/// through the coefficient ring in its order.
pub fn enumerate_res(it: &mut Interp, st: &Rc<Struct>, r: &Ring) -> RResult<Vec<Value>> {
    let RingKind::UPolyRes { base, modulus, .. } = &r.kind else { unreachable!() };
    let (base, d) = (base.clone(), modulus.poly_len() - 1);
    let q = ring_props(&base).and_then(|p| p.cardinality).ok_or_else(|| RuntimeError::runtime(crate::error::NOT_ITERABLE))?;
    let n = q.pow(d as u64).to_u64().filter(|&n| n <= 1 << 26).ok_or_else(|| RuntimeError::runtime("The ring is too large to enumerate"))?;
    let digits: Vec<Elem> = match &base {
        Value::Struct(bs) => it.enumerate_ring(bs)?.iter().map(|v| Ok(it.to_structure_elem(&base, v, false)?.expect("an element of the coefficient ring"))).collect::<RResult<_>>()?,
        _ => unreachable!("a finite coefficient ring"),
    };
    let mut idx = vec![0usize; d];
    let mut out = Vec::with_capacity(n as usize);
    for _ in 0..n {
        let cs: Vec<Elem> = idx.iter().map(|&i| digits[i].clone()).collect();
        out.push(make_elt(st, Elem::poly_from_coeffs(&r.ctx, &cs)?));
        for i in idx.iter_mut() {
            *i += 1;
            if *i < digits.len() {
                break;
            }
            *i = 0;
        }
    }
    Ok(out)
}

/// Whether the quotient by `f` is a domain (and so a field over a field):
/// `f` irreducible, where that can be decided.
pub fn res_is_domain(f: &Elem) -> bool {
    fu::can_factor(f.ctx()) && fu::is_irreducible(f).unwrap_or(false)
}

/// The generators of `ideal<P | ...>` or `quo<P | ...>` as polynomials:
/// elements coercing into P, sequences of them, and ideals of P.
fn poly_generators(it: &mut Interp, pst: &Rc<Struct>, right: &[Value], ctx: &str) -> RResult<Vec<Elem>> {
    let invalid = |i: usize| RuntimeError::runtime(format!("Rhs argument {} is invalid for this constructor", i + 1)).in_context(ctx);
    let mut out = Vec::new();
    for (i, v) in right.iter().enumerate() {
        if let Some(StructKind::UPolIdeal(g)) = v.as_struct() {
            if Rc::ptr_eq(&g.parent, pst) {
                out.push(g.x.clone());
                continue;
            }
            return Err(invalid(i));
        }
        let items: Vec<Value> = match v {
            Value::Seq(s) => s.elems.clone(),
            _ => vec![v.clone()],
        };
        for x in items {
            out.push(it.to_ring_elem(pst, &x, false)?.ok_or_else(|| invalid(i))?);
        }
    }
    Ok(out)
}

/// The monic gcd of polynomials over a field (0 for none).
fn gcd_all(ctx: &Rc<Ctx>, gs: &[Elem]) -> GrResult<Elem> {
    let mut g = Elem::zero(ctx);
    for x in gs {
        g = fu::gcd(&g, x)?;
    }
    if g.poly_len() > 0 { fu::make_monic(&g) } else { Ok(g) }
}

/// The ideal of the ring `pst` generated by `g` (monic or zero): the ring
/// itself for a unit.
fn poly_ideal(pst: &Rc<Struct>, g: Elem) -> Value {
    if g.poly_len() == 1 {
        return Value::Struct(pst.clone());
    }
    Value::structure(StructKind::UPolIdeal(Rc::new(Elt { parent: pst.clone(), x: g })))
}

/// A univariate polynomial ring, or an ideal of one: the ring and the
/// generator of the ideal (1 for the ring).
pub fn poly_ideal_parts(v: &Value) -> Option<(Rc<Struct>, Elem)> {
    match v.as_struct()? {
        StructKind::UPolIdeal(g) => Some((g.parent.clone(), g.x.clone())),
        StructKind::Ring(r) if matches!(r.kind, RingKind::UPoly { .. }) => {
            let Value::Struct(st) = v else { unreachable!() };
            Some((st.clone(), Elem::one(&r.ctx).ok()?))
        }
        _ => None,
    }
}

fn coercion_map(domain: Value, codomain: Value) -> Value {
    Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain, codomain, imp: MapImpl::Coercion }))
}

/// `ideal<P | ...>` for a univariate polynomial ring P over a field.
pub fn ideal_constructor(it: &mut Interp, base: &Value, right: &[Value]) -> RResult<Option<Vec<Value>>> {
    let Some((pst, pr)) = ring_of(base).filter(|(_, r)| matches!(r.kind, RingKind::UPoly { .. })) else { return Ok(None) };
    let (pst, pctx) = (pst.clone(), pr.ctx.clone());
    if !fu::over_field(&pctx) {
        return Err(RuntimeError::runtime("Coefficient ring of LHS must be a field").in_context("ideal< ... >"));
    }
    let gs = poly_generators(it, &pst, right, "ideal< ... >")?;
    Ok(Some(vec![poly_ideal(&pst, gcd_all(&pctx, &gs)?)]))
}

/// `quo<P | ...>` for a univariate polynomial ring P: the quotient by the
/// ideal generated (P itself for the zero ideal) and the quotient map. Over
/// coefficient rings that are not fields there must be one monic generator.
pub fn quo_constructor(it: &mut Interp, base: &Value, right: &[Value]) -> RResult<Option<Vec<Value>>> {
    let Some((pst, pr)) = ring_of(base).filter(|(_, r)| matches!(r.kind, RingKind::UPoly { .. })) else { return Ok(None) };
    let (pst, pctx) = (pst.clone(), pr.ctx.clone());
    let gs = poly_generators(it, &pst, right, "quo< ... >")?;
    let g = if fu::over_field(&pctx) {
        gcd_all(&pctx, &gs)?
    } else {
        if gs.len() != 1 {
            return Err(RuntimeError::runtime("Arity must be 1 if coefficient ring is not a field").in_context("quo< ... >"));
        }
        if gs[0].poly_len() == 0 || fu::lead(&gs[0]).is_one() != Truth::True {
            return Err(RuntimeError::runtime("Polynomial must be monic").in_context("quo< ... >"));
        }
        gs[0].clone()
    };
    if g.poly_len() == 0 {
        return Ok(Some(vec![base.clone(), coercion_map(base.clone(), base.clone())]));
    }
    let q = it.upoly_res(&pst, g);
    Ok(Some(vec![q.clone(), coercion_map(base.clone(), q)]))
}

/// Operators on ideals of univariate polynomial rings (with at least one
/// proper ideal among the operands).
pub fn ideal_binop(it: &mut Interp, op: BinOp, a: &Value, b: &Value) -> RResult<Option<Value>> {
    let is_ideal = |v: &Value| matches!(v.as_struct(), Some(StructKind::UPolIdeal(_)));
    if !is_ideal(a) && !is_ideal(b) {
        return Ok(None);
    }
    let (Some((r, f)), Some((s, g))) = (poly_ideal_parts(a), poly_ideal_parts(b)) else { return Ok(None) };
    if !Rc::ptr_eq(&r, &s) {
        if matches!(op, BinOp::Eq | BinOp::Ne) {
            return Ok(Some(Value::Bool(op == BinOp::Ne)));
        }
        return Err(RuntimeError::runtime(format!("Arguments are not compatible\nArgument types given: {}, {}", it.type_name_ext(a), it.type_name_ext(b))).in_context(op.intrinsic_name()));
    }
    // I is contained in J when the generator of J divides that of I.
    let contained = |f: &Elem, g: &Elem| -> GrResult<bool> { Ok(if g.poly_len() == 0 { f.poly_len() == 0 } else { fu::divrem(f, g)?.1.poly_len() == 0 }) };
    let ctx = f.ctx().clone();
    Ok(Some(match op {
        BinOp::Add => poly_ideal(&r, gcd_all(&ctx, &[f, g])?),
        BinOp::Mul => poly_ideal(&r, f.mul(&g)?),
        BinOp::Meet => {
            let l = if f.poly_len() == 0 || g.poly_len() == 0 { Elem::zero(&ctx) } else { fu::divrem(&f.mul(&g)?, &fu::gcd(&f, &g)?)?.0 };
            poly_ideal(&r, if l.poly_len() > 0 { fu::make_monic(&l)? } else { l })
        }
        BinOp::Eq | BinOp::Ne => Value::Bool((f.equal(&g) == Truth::True) == (op == BinOp::Eq)),
        BinOp::Subset => Value::Bool(contained(&f, &g)?),
        BinOp::Notsubset => Value::Bool(!contained(&f, &g)?),
        _ => return Ok(None),
    }))
}

/// Whether `x` lies in the ideal generated by `g` of the ring `pst`: the
/// element of P if it does (`None` if x is not in P).
pub fn ideal_member(it: &mut Interp, pst: &Rc<Struct>, g: &Elem, x: &Value) -> RResult<Option<(Value, bool)>> {
    let Some(y) = it.to_ring_elem(pst, x, false)? else { return Ok(None) };
    let inside = if g.poly_len() == 0 { y.poly_len() == 0 } else { fu::divrem(&y, g)?.1.poly_len() == 0 };
    Ok(Some((make_elt(pst, y), inside)))
}

/// The text of an ideal: `Ideal of P generated by g`, or at the Magma
/// level `ideal<P | g>` (with the generator in the variable x, as Magma
/// prints it).
pub fn format_ideal(it: &mut Interp, g: &Elt, level: crate::print::Level) -> RResult<String> {
    use crate::print::Level;
    if level == Level::Magma {
        let p = it.format_flat(&g.parent_value(), Level::Magma)?;
        let gs = crate::rings::upoly_text(it, &base_of(g), &g.x, "x", Level::Default)?;
        return Ok(format!("ideal<{p} | {gs}>"));
    }
    let p = it.format_flat(&g.parent_value(), Level::Default)?;
    let gs = it.format_flat(&Value::Elt(Rc::new(Elt { parent: g.parent.clone(), x: g.x.clone() })), level)?;
    Ok(format!("Ideal of {p} generated by {gs}"))
}

fn ideal_generators(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Some((pst, g)) = poly_ideal_parts(&a.args[0]) else { return Err(RuntimeError::runtime("Bad argument types")) };
    one(Value::Set(Rc::new(SetEnum::new(Some(Value::Struct(pst.clone())), [make_elt(&pst, g)].into_iter().collect()))))
}

fn ideal_is_prime(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Some((_, g)) = poly_ideal_parts(&a.args[0]) else { return Err(RuntimeError::runtime("Bad argument types")) };
    boolv(g.poly_len() == 0 || (g.poly_len() > 1 && res_is_domain(&g)))
}

fn ideal_is_maximal(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Some((_, g)) = poly_ideal_parts(&a.args[0]) else { return Err(RuntimeError::runtime("Bad argument types")) };
    boolv(g.poly_len() > 1 && res_is_domain(&g))
}

fn ideal_is_principal(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(poly_ideal_parts(&a.args[0]).is_some())
}

fn modulus(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, r) = ring_arg(a, 0);
    let RingKind::UPolyRes { preimage, modulus, .. } = &r.kind else { unreachable!() };
    one(make_elt(preimage, modulus.clone()))
}

fn preimage_ring(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, r) = ring_arg(a, 0);
    let RingKind::UPolyRes { preimage, .. } = &r.kind else { unreachable!() };
    one(Value::Struct(preimage.clone()))
}

fn res_is_unit(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    boolv(res_inverse(res_modulus(f.ring()), &f.x)?.is_some())
}

/// The coefficient ring of a polynomial ring, ideal or quotient (or of the
/// parent of an element).
fn coefficient_ring(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let r = match &a.args[0] {
        Value::Elt(e) => e.ring_rc(),
        _ => ring_arg(a, 0).1,
    };
    one(r.base().expect("a polynomial ring").clone())
}

fn res_is_zero(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(pol(a, 0).x.poly_len() == 0)
}

fn res_is_one(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(pol(a, 0).x.is_one() == Truth::True)
}

fn res_is_minus_one(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(pol(a, 0).x.is_neg_one() == Truth::True)
}

// ----- registration ----------------------------------------------------------------------

pub fn register(it: &mut Interp) {
    // Creation.
    it.def("Polynomial", "Q::[RngElt] -> RngUPolElt", "The polynomial over the universe of Q with coefficients Q (constant term first).", polynomial_seq);
    it.def("Polynomial", "R::Rng, Q::[RngElt] -> RngUPolElt", "The polynomial over R with coefficients Q coerced into R.", polynomial_over);
    it.def("Polynomial", "R::Rng, f::RngUPolElt -> RngUPolElt", "The polynomial f with its coefficients coerced into R.", polynomial_over);
    it.def("Identity", "P::RngUPol -> RngUPolElt", "The identity of P.", identity);
    it.def(".", "P::RngUPol, i::RngIntElt -> RngUPolElt", "The indeterminate of P (i = 1).", indeterminate);
    it.def("Name", "P::RngUPol, i::RngIntElt -> RngUPolElt", "The indeterminate of P (i = 1).", indeterminate);
    it.def("AssignNames", "~P::RngUPol, S::[MonStgElt]", "Name the indeterminate of P (for printing).", assign_names);
    it.def(".", "Q::RngUPolRes, i::RngIntElt -> RngUPolResElt", "The image of the indeterminate in Q (i = 1).", indeterminate);
    it.def("Name", "Q::RngUPolRes, i::RngIntElt -> RngUPolResElt", "The image of the indeterminate in Q (i = 1).", indeterminate);
    it.def("AssignNames", "~Q::RngUPolRes, S::[MonStgElt]", "Name the indeterminate of Q (for printing).", assign_names);
    it.def("ChangeRing", "P::RngUPol, S::Rng -> RngUPol, Map", "The polynomial ring over S, with the map from P coercing coefficients.", change_ring);
    it.def("ChangeRing", "P::RngUPol, S::Rng, f::Map -> RngUPol, Map", "The polynomial ring over S, with the map from P applying f to the coefficients.", change_ring);

    // Predicates.
    it.def("IsMonic", "f::RngUPolElt -> BoolElt", "Whether the leading coefficient of f is 1.", is_monic);
    it.def("IsRegular", "f::RngUPolElt -> BoolElt", "Whether f is not a zero divisor.", is_regular);

    // Coefficients and terms.
    for name in ["Coefficients", "ElementToSequence", "Eltseq"] {
        it.def(name, "f::RngUPolElt -> [RngElt]", "The coefficients of f, constant term first.", coefficients);
    }
    it.def("Coefficient", "f::RngUPolElt, i::RngIntElt -> RngElt", "The coefficient of x^i in f.", coefficient);
    it.def("MonomialCoefficient", "f::RngUPolElt, m::RngUPolElt -> RngElt", "The coefficient of the monomial m in f.", monomial_coefficient);
    it.def("LeadingCoefficient", "f::RngUPolElt -> RngElt", "The coefficient of the highest power of x in f.", leading_coefficient);
    it.def("TrailingCoefficient", "f::RngUPolElt -> RngElt", "The coefficient of the lowest power of x in f.", trailing_coefficient);
    it.def("ConstantCoefficient", "f::RngUPolElt -> RngElt", "The constant term of f.", constant_coefficient);
    it.def("Terms", "f::RngUPolElt -> [RngUPolElt]", "The non-zero terms of f in ascending order.", terms);
    it.def("LeadingTerm", "f::RngUPolElt -> RngUPolElt", "The term of f of highest degree.", leading_term);
    it.def("TrailingTerm", "f::RngUPolElt -> RngUPolElt", "The term of f of lowest degree.", trailing_term);
    it.def("Monomials", "f::RngUPolElt -> [RngUPolElt]", "The powers of x up to the degree of f.", monomials);
    it.def("Support", "f::RngUPolElt -> [RngIntElt], [RngElt]", "The exponents of the non-zero terms of f, and their coefficients.", support);
    it.def("Reductum", "f::RngUPolElt -> RngUPolElt", "f without its leading term.", reductum);
    it.def("Round", "f::RngUPolElt -> RngUPolElt", "The integer polynomial with the coefficients of f rounded.", round);
    it.def("Valuation", "f::RngUPolElt -> RngIntElt", "The exponent of the largest power of x dividing f.", valuation);
    it.def("Degree", "f::RngUPolElt -> RngIntElt", "The degree of f (-1 for zero).", degree);

    // Roots.
    it.def_params("Roots", "f::RngUPolElt -> [Tup]", &[("Max", Value::Undef)], "The roots of f in its coefficient ring with their multiplicities.", roots);
    it.def_params("Roots", "f::RngUPolElt, S::Rng -> [Tup]", &[("Max", Value::Undef)], "The roots of f in S with their multiplicities.", roots_in);
    it.def("HasRoot", "f::RngUPolElt -> BoolElt, RngElt", "Whether f has a root in its coefficient ring, and a root.", has_root);
    it.def("HasRoot", "f::RngUPolElt, S::Rng -> BoolElt, RngElt", "Whether f has a root in S, and a root.", has_root_in);

    // Derivatives, evaluation and interpolation.
    it.def("Derivative", "f::RngUPolElt -> RngUPolElt", "The derivative of f.", derivative);
    it.def("Derivative", "f::RngUPolElt, n::RngIntElt -> RngUPolElt", "The n-th derivative of f.", derivative);
    it.def("Integral", "f::RngUPolElt -> RngUPolElt", "The integral of f with constant term 0.", integral);
    it.def("Evaluate", "f::RngUPolElt, r::RngElt -> RngElt", "The value of f at r.", evaluate);
    it.def("Interpolation", "I::[RngElt], V::[RngElt] -> RngUPolElt", "The polynomial of least degree taking the values V at the points I.", interpolation);

    // Quotient and remainder.
    it.def("Quotrem", "f::RngUPolElt, g::RngUPolElt -> RngUPolElt, RngUPolElt", "The quotient and remainder of f by g.", quotrem_fn);
    it.def("IsDivisibleBy", "f::RngUPolElt, g::RngUPolElt -> BoolElt, RngUPolElt", "Whether g divides f, and the quotient.", is_divisible_by);
    it.def("ExactQuotient", "f::RngUPolElt, g::RngUPolElt -> RngUPolElt", "f / g for g dividing f.", exact_quotient);
    it.def("Valuation", "f::RngUPolElt, g::RngUPolElt -> RngIntElt", "The exponent of the largest power of g dividing f.", valuation_by);
    it.def("PseudoRemainder", "f::RngUPolElt, g::RngUPolElt -> RngUPolElt", "The pseudo-remainder of f by g.", pseudo_remainder);
    it.def("EuclideanNorm", "f::RngUPolElt -> RngIntElt", "The degree of f plus one (0 for zero).", euclidean_norm);

    // Modular arithmetic.
    it.def("Modexp", "f::RngUPolElt, n::RngIntElt, g::RngUPolElt -> RngUPolElt", "f^n mod g.", modexp);
    for name in ["ChineseRemainderTheorem", "CRT"] {
        it.def(name, "X::[RngUPolElt], M::[RngUPolElt] -> RngUPolElt", "The polynomial congruent to X[i] modulo M[i] for each i.", crt);
    }

    // Other operations.
    it.def("ReciprocalPolynomial", "f::RngUPolElt -> RngUPolElt", "The coefficients of f reversed.", reciprocal_polynomial);
    it.def("PowerPolynomial", "f::RngUPolElt, n::RngIntElt -> RngUPolElt", "The polynomial whose roots are the n-th powers of those of f.", power_polynomial);

    // Greatest common divisors and content.
    for name in ["GreatestCommonDivisor", "Gcd", "GCD"] {
        it.def(name, "f::RngUPolElt, g::RngUPolElt -> RngUPolElt", "The normalized greatest common divisor of f and g.", gcd);
    }
    for name in ["ExtendedGreatestCommonDivisor", "Xgcd", "XGCD"] {
        it.def(name, "f::RngUPolElt, g::RngUPolElt -> RngUPolElt, RngUPolElt, RngUPolElt", "The monic gcd d of f and g over a field, with a and b such that d = a f + b g.", xgcd);
    }
    for name in ["LeastCommonMultiple", "Lcm", "LCM"] {
        it.def(name, "f::RngUPolElt, g::RngUPolElt -> RngUPolElt", "The normalized least common multiple of f and g.", lcm);
    }
    for name in ["Normalize", "Normalise"] {
        it.def(name, "f::RngUPolElt -> RngUPolElt", "The normalized associate of f.", normalize);
    }
    it.def("Content", "f::RngUPolElt -> RngElt", "The gcd of the coefficients of f.", content);
    it.def("PrimitivePart", "f::RngUPolElt -> RngUPolElt", "f divided by its content.", primitive_part);
    for name in ["ContentAndPrimitivePart", "Contpp"] {
        it.def(name, "f::RngUPolElt -> RngElt, RngUPolElt", "The content and the primitive part of f.", content_and_primitive_part);
    }

    // Polynomials over the integers.
    it.def("Sign", "f::RngUPolElt -> RngIntElt", "The sign of the leading coefficient of f.", sign);
    for name in ["AbsoluteValue", "Abs"] {
        it.def(name, "f::RngUPolElt -> RngUPolElt", "f or -f, whichever has a non-negative leading coefficient.", abs);
    }
    it.def("MaxNorm", "f::RngUPolElt -> RngIntElt", "The largest absolute value of a coefficient of f.", max_norm);
    it.def("SumNorm", "f::RngUPolElt -> RngIntElt", "The sum of the absolute values of the coefficients of f.", sum_norm);
    it.def("DedekindTest", "f::RngUPolElt, p::RngIntElt -> BoolElt", "Whether the equation order of the monic f is maximal at the prime p.", dedekind_test);

    // Polynomials over finite fields.
    it.def("PrimePolynomials", "R::RngUPol, d::RngIntElt -> [RngUPolElt]", "The monic irreducible polynomials of degree d over the finite field of R.", prime_polynomials);
    it.def("PrimePolynomials", "R::RngUPol, d::RngIntElt, n::RngIntElt -> [RngUPolElt]", "The first n monic irreducible polynomials of degree d (and more) over the finite field of R.", prime_polynomials);
    it.def("RandomPrimePolynomial", "R::RngUPol, d::RngIntElt -> RngUPolElt", "A random monic irreducible polynomial of degree d over the finite field of R.", random_prime_polynomial);
    for t in ["RngIntElt", "FldFin", "RngUPol"] {
        it.def("NumberOfPrimePolynomials", &format!("q::{t}, d::RngIntElt -> RngIntElt"), "The number of monic irreducible polynomials of degree d over the finite field of size q.", number_of_prime_polynomials);
    }
    it.def("JacobiSymbol", "a::RngUPolElt, b::RngUPolElt -> RngIntElt", "The Jacobi symbol (a/b) of polynomials over a finite field of odd characteristic.", jacobi_symbol);

    // Factorization.
    for name in ["Factorization", "Factorisation"] {
        let al = [("Al", Value::str("Default"))];
        it.def_params(name, "f::RngUPolElt -> [Tup], RngElt", &al, "The factorization of f into normalized irreducibles, and the unit.", factorization);
    }
    it.def("IsIrreducible", "f::RngUPolElt -> BoolElt", "Whether f is irreducible.", is_irreducible);
    it.def("IsPrime", "f::RngUPolElt -> BoolElt", "Whether f is irreducible (prime).", is_irreducible);
    it.def("SquarefreeFactorization", "f::RngUPolElt -> [Tup]", "The squarefree factorization of f.", squarefree_factorization);
    let deg = [("Degree", Value::int(0))];
    it.def_params("DistinctDegreeFactorization", "f::RngUPolElt -> [Tup]", &deg, "The products of the irreducible factors of each degree of the squarefree f.", distinct_degree_factorization);
    it.def("EqualDegreeFactorization", "f::RngUPolElt, d::RngIntElt, g::RngUPolElt -> [RngUPolElt]", "The irreducible factors of f, a product of irreducibles of degree d (g = x^q mod f).", equal_degree_factorization);
    it.def("IsSeparable", "f::RngUPolElt -> BoolElt", "Whether f has no repeated roots.", is_separable);
    it.def("HasPolynomialFactorization", "R::Rng -> BoolElt", "Whether polynomials over R can be factored.", has_polynomial_factorization);
    for name in ["FactorisationToPolynomial", "Facpol"] {
        it.def(name, "Q::[Tup] -> RngElt", "The product of the factorization sequence Q of a polynomial.", facpol);
    }

    // Special families.
    for name in ["ChebyshevFirst", "ChebyshevT"] {
        it.def(name, "n::RngIntElt -> RngUPolElt", "The Chebyshev polynomial of the first kind T_n.", chebyshev_t);
    }
    for name in ["ChebyshevSecond", "ChebyshevU"] {
        it.def(name, "n::RngIntElt -> RngUPolElt", "The Chebyshev polynomial of the second kind of degree n - 1.", chebyshev_u);
    }
    it.def("LegendrePolynomial", "n::RngIntElt -> RngUPolElt", "The Legendre polynomial P_n.", legendre_polynomial);
    it.def("LaguerrePolynomial", "n::RngIntElt -> RngUPolElt", "The Laguerre polynomial L_n.", laguerre_polynomial);
    it.def("LaguerrePolynomial", "n::RngIntElt, m::RngElt -> RngUPolElt", "The generalized Laguerre polynomial L_n^m.", laguerre_polynomial);
    it.def("HermitePolynomial", "n::RngIntElt -> RngUPolElt", "The Hermite polynomial H_n.", hermite_polynomial);
    it.def("GegenbauerPolynomial", "n::RngIntElt, m::RngElt -> RngUPolElt", "The Gegenbauer polynomial C_n^m.", gegenbauer_polynomial);
    it.def("DicksonFirst", "n::RngIntElt, a::RngElt -> RngUPolElt", "The Dickson polynomial of the first kind D_n(x, a).", dickson_first);
    it.def("DicksonSecond", "n::RngIntElt, a::RngElt -> RngUPolElt", "The Dickson polynomial of the second kind E_n(x, a).", dickson_second);
    it.def("BernoulliPolynomial", "n::RngIntElt -> RngUPolElt", "The n-th Bernoulli polynomial.", bernoulli_polynomial);
    it.def("SwinnertonDyerPolynomial", "n::RngIntElt -> RngUPolElt", "The minimal polynomial of the sum of the square roots of the first n primes.", swinnerton_dyer_polynomial);

    // Ideals and quotient rings.
    it.def("Modulus", "Q::RngUPolRes -> RngUPolElt", "The polynomial f of the quotient Q = P/(f).", modulus);
    it.def("PreimageRing", "Q::RngUPolRes -> RngUPol", "The polynomial ring P of the quotient Q = P/(f).", preimage_ring);
    it.def("IsUnit", "x::RngUPolResElt -> BoolElt", "Whether x is a unit.", res_is_unit);
    it.def("IsZero", "x::RngUPolResElt -> BoolElt", "Whether x is zero.", res_is_zero);
    it.def("IsOne", "x::RngUPolResElt -> BoolElt", "Whether x is one.", res_is_one);
    it.def("IsMinusOne", "x::RngUPolResElt -> BoolElt", "Whether x is minus one.", res_is_minus_one);
    for name in ["BaseRing", "CoefficientRing"] {
        for t in ["I::RngUPol", "Q::RngUPolRes", "f::RngUPolResElt"] {
            it.def(name, &format!("{t} -> Rng"), "The coefficient ring.", coefficient_ring);
        }
    }
    it.def("Generators", "I::RngUPol -> SetEnum", "The generator of the ideal I, as a set.", ideal_generators);
    it.def("IsPrime", "I::RngUPol -> BoolElt", "Whether the ideal I is prime.", ideal_is_prime);
    it.def("IsMaximal", "I::RngUPol -> BoolElt", "Whether the ideal I is maximal.", ideal_is_maximal);
    it.def("IsPrincipal", "I::RngUPol -> BoolElt", "Whether the ideal I is principal (always).", ideal_is_principal);
    for name in ["Coefficients", "ElementToSequence", "Eltseq"] {
        it.def(name, "f::RngUPolResElt -> [RngElt]", "The coefficients of the reduced representative of f, constant term first.", coefficients);
    }
    it.def("Coefficient", "f::RngUPolResElt, i::RngIntElt -> RngElt", "The coefficient of x^i in the reduced representative of f.", coefficient);
    it.def("LeadingCoefficient", "f::RngUPolResElt -> RngElt", "The leading coefficient of the reduced representative of f.", leading_coefficient);
    it.def("TrailingCoefficient", "f::RngUPolResElt -> RngElt", "The trailing coefficient of the reduced representative of f.", trailing_coefficient);
    it.def("ConstantCoefficient", "f::RngUPolResElt -> RngElt", "The constant term of the reduced representative of f.", constant_coefficient);
    it.def("Terms", "f::RngUPolResElt -> [RngUPolResElt]", "The non-zero terms of the reduced representative of f.", terms);
    it.def("LeadingTerm", "f::RngUPolResElt -> RngUPolResElt", "The leading term of the reduced representative of f.", leading_term);
    it.def("TrailingTerm", "f::RngUPolResElt -> RngUPolResElt", "The trailing term of the reduced representative of f.", trailing_term);
    it.def("Degree", "f::RngUPolResElt -> RngIntElt", "The degree of the reduced representative of f.", degree);

    // Resultants, discriminants and Hensel lifting.
    it.def("Resultant", "f::RngUPolElt, g::RngUPolElt -> RngElt", "The resultant of f and g.", resultant);
    it.def("Discriminant", "f::RngUPolElt -> RngElt", "The discriminant of f.", discriminant);
    it.def("HenselLift", "f::RngUPolElt, s::[RngUPolElt], P::RngUPol -> [RngUPolElt]", "Lift the factors s of f modulo p to factors modulo p^k in P over Z/p^kZ.", hensel_lift);
}
