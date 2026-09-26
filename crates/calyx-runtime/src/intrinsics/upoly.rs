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
use calyx_flint::gr::{Ctx, CtxKind, Elem, GrError, Truth};
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

/// Argument `i`, a univariate polynomial ring.
fn ring_arg(a: &CallArgs, i: usize) -> (Rc<Struct>, Rc<Ring>) {
    match &a.args[i] {
        Value::Struct(s) => match &s.kind {
            StructKind::Ring(r) => (s.clone(), r.clone()),
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

/// `P.i` and `Name(P, i)`: the indeterminate.
fn indeterminate(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, r) = ring_arg(a, 0);
    let i = a.int(1)?;
    if !i.is_one() {
        return Err(RuntimeError::runtime(format!("Value for name index ({i}) should be in the range [1..1]")));
    }
    one(make_elt(&st, r.ctx.generator()?))
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
        GrError::Unable => RuntimeError::runtime("Roots are not available over this coefficient ring"),
        e => e.into(),
    })?;
    let base = base_of(f);
    let mut out: Vec<(Value, u64)> = rs.into_iter().map(|(r, m)| (it.elem_to_value(&base, r), m)).collect();
    sort_by_ring_order(it, &mut out);
    Ok(out)
}

/// `f` over the ring `s` (argument 2 of `Roots(f, S)` and friends).
fn over(it: &mut Interp, f: &Rc<Elt>, s: &Value) -> RResult<Rc<Elt>> {
    let q = it.poly_ring(s, true)?;
    let Value::Struct(st) = &q else { unreachable!() };
    match it.to_ring_elem(st, &Value::Elt(f.clone()), false)? {
        Some(x) => Ok(Rc::new(Elt { parent: st.clone(), x })),
        None => Err(RuntimeError::runtime("Argument 1 cannot be coerced to be over argument 2")),
    }
}

fn roots_seq(it: &mut Interp, f: &Rc<Elt>, a: &CallArgs) -> RResult<Vals> {
    let mut rs = root_values(it, f)?;
    if let Some(Value::Int(m)) = a.param("Max") {
        if m.sign() >= 0 {
            rs.truncate(m.to_u64().unwrap_or(u64::MAX) as usize);
        }
    }
    let elems = rs.into_iter().map(|(r, m)| Value::tuple(vec![r, Value::int(m as i64)])).collect();
    one(Value::seq(None, elems))
}

fn roots(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    roots_seq(it, &f, a)
}

fn roots_in(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = over(it, &pol(a, 0), &a.args[1].clone())?;
    roots_seq(it, &f, a)
}

/// A root, if there is one: over the integers and rationals the largest
/// (the root of the first linear factor in Magma's order), elsewhere the
/// least.
fn has_root_of(it: &mut Interp, f: &Rc<Elt>) -> RResult<Vals> {
    let rs = root_values(it, f)?;
    let pick = if matches!(bctx(f).kind(), CtxKind::Integers | CtxKind::Rationals) { rs.last() } else { rs.first() };
    match pick {
        Some((r, _)) => Ok(vals![Value::Bool(true), r.clone()]),
        None => boolv(false),
    }
}

fn has_root(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    has_root_of(it, &pol(a, 0))
}

fn has_root_in(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = over(it, &pol(a, 0), &a.args[1].clone())?;
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
    for i in 1..mods.len() {
        let x = get(it, &xs.elems[i])?;
        let (_, s, _) = fu::xgcd(&m, &mods[i])?;
        let c = quotrem(it, &ring, &x.sub(&t)?.mul(&s)?, &mods[i])?.1;
        t = t.add(&m.mul(&c)?)?;
        m = m.mul(&mods[i])?;
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
fn norm_unit(it: &mut Interp, base: &Value, c: &Elem) -> RResult<Elem> {
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
            RingKind::Complex(_) => false,
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

/// The n-th Swinnerton-Dyer polynomial, over the integers.
fn swinnerton_dyer_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?;
    if n.sign() <= 0 {
        return Err(bare(arg_ge(1, n, 1)));
    }
    let n = n.to_u64().filter(|&n| n <= 20).ok_or_else(|| RuntimeError::runtime(format!("Argument 1 ({n}) is too large")))?;
    let zx = it.poly_ring(&Value::integers(), true)?;
    let Some((st, r)) = ring_of(&zx) else { unreachable!() };
    one(make_elt(&st, fu::swinnerton_dyer(&r.ctx, n)))
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
    it.def("SwinnertonDyerPolynomial", "n::RngIntElt -> RngUPolElt", "The minimal polynomial of the sum of the square roots of the first n primes.", swinnerton_dyer_polynomial);

    // Resultants, discriminants and Hensel lifting.
    it.def("Resultant", "f::RngUPolElt, g::RngUPolElt -> RngElt", "The resultant of f and g.", resultant);
    it.def("Discriminant", "f::RngUPolElt -> RngElt", "The discriminant of f.", discriminant);
    it.def("HenselLift", "f::RngUPolElt, s::[RngUPolElt], P::RngUPol -> [RngUPolElt]", "Lift the factors s of f modulo p to factors modulo p^k in P over Z/p^kZ.", hensel_lift);
}
