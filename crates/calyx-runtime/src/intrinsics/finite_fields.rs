//! Finite fields: creation, subfields and embeddings, the functions of the
//! fields and of their elements, polynomials over finite fields, discrete
//! logarithms and permutation polynomials. The lattice of fields and the
//! maps between them are in `rings::finite`.
//!
//! Coordinates of an element over a subfield E of F are taken in the power
//! basis of `Generator(F, E)` (`F.1` when it generates F over E), as in
//! Magma; over the ground field this is the basis of `F.1` in which
//! elements print.

use std::rc::Rc;

use calyx_flint::gr::{Ctx, CtxKind, Elem, Truth};
use calyx_flint::{Integer, Nmod};

use super::{boolv, intv, none, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::rings::finite::{self, field_of};
use crate::rings::fp::{Coords, LinMap};
use crate::rings::{FiniteField, Ring, make_elt};
use crate::sym::Sym;
use crate::value::*;

fn bad() -> RuntimeError {
    RuntimeError::runtime("Bad argument types")
}

fn ff(st: &Struct) -> (&Ring, &FiniteField) {
    field_of(st).expect("a finite field")
}

fn id(st: &Struct) -> u64 {
    ff(st).0.id
}

fn degree(st: &Struct) -> u64 {
    ff(st).1.degree
}

fn is_zero(x: &Elem) -> bool {
    x.is_zero() == Truth::True
}

fn is_zech(ctx: &Ctx) -> bool {
    matches!(ctx.kind(), CtxKind::FqZech { .. })
}

fn field_arg(a: &CallArgs, i: usize) -> RResult<Rc<Struct>> {
    finite::field_struct(&a.args[i]).cloned().ok_or_else(bad)
}

/// A finite field element argument: its field and its FLINT element.
fn felt_arg(a: &CallArgs, i: usize) -> RResult<(Rc<Struct>, Elem)> {
    let e = crate::rings::small::elt_of(&a.args[i]).ok_or_else(bad)?;
    if field_of(&e.parent).is_none() {
        return Err(bad());
    }
    Ok((e.parent.clone(), e.x.clone()))
}

fn prime_of(it: &mut Interp, st: &Struct) -> RResult<Rc<Struct>> {
    let p = ff(st).1.p.clone();
    it.default_field(&p, 1)
}

/// The ground field: the field `st` was built over, else the prime field.
fn ground_of(it: &mut Interp, st: &Struct) -> RResult<Rc<Struct>> {
    match &ff(st).1.ground {
        Some(g) => Ok(g.field.clone()),
        None => prime_of(it, st),
    }
}

/// The polynomial with coefficients `cs` (in the context of `base`,
/// constant term first) in the global polynomial ring over `base`.
fn poly_value(it: &mut Interp, base: &Rc<Struct>, cs: &[Elem]) -> RResult<Value> {
    let px = it.poly_ring(&Value::Struct(base.clone()), true)?;
    let Value::Struct(ps) = &px else { unreachable!() };
    let StructKind::Ring(pr) = &ps.kind else { unreachable!() };
    Ok(make_elt(ps, Elem::poly_from_coeffs(&pr.ctx, cs)?))
}

/// The polynomial with integer coefficients over GF(p).
fn int_poly_value(it: &mut Interp, p: &Integer, cs: &[Integer]) -> RResult<Value> {
    let fp = it.default_field(p, 1)?;
    let ctx = ff(&fp).0.ctx.clone();
    poly_value(it, &fp, &finite::int_poly_in(cs, &ctx))
}

const NOT_SUB: &str = "Argument 2 is not a subfield of the parent of argument 1";
const NOT_SUB_OF: &str = "Argument 2 is not a subfield of argument 1";

/// The image in `f` of the generator of the context of its known subfield
/// `e`, else the error `msg`.
fn sub_image(e: &Rc<Struct>, f: &Rc<Struct>, msg: &str) -> RResult<Elem> {
    finite::find_emb(e, f).ok_or_else(|| RuntimeError::runtime(msg))
}

/// `y`, an element of `f` lying in its known subfield `e`, in `e`.
fn down(y: &Elem, f: &Rc<Struct>, e: &Rc<Struct>) -> Elem {
    finite::restrict(y, f, e).flatten().expect("an element of the subfield")
}

/// Magma's order on the elements of a field: prime fields by residue,
/// others as `rings::finite::elt_order`.
fn elem_cmp(a: &Elem, b: &Elem) -> std::cmp::Ordering {
    match a.ctx().kind() {
        CtxKind::Nmod(_) | CtxKind::FmpzMod(_) => a.to_integer().unwrap_or_default().cmp(&b.to_integer().unwrap_or_default()),
        _ => finite::elt_order(a, b),
    }
}

fn sort_elems(v: &mut [Elem]) {
    v.sort_by(elem_cmp);
}

/// A random element of the field.
/// `Random(F)`: by index as for other finite structures when F is small
/// enough to list, else by coordinates.
fn random(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    if ff(&f).1.order().to_u64().is_some_and(|q| q <= 1 << 30) {
        let (_, x) = it.random_element_indexed(&a.args[0])?;
        return one(x);
    }
    one(make_elt(&f, random_elem(it, &f)))
}

fn random_elem(it: &mut Interp, st: &Struct) -> Elem {
    let (r, f) = ff(st);
    let cs: Vec<Integer> = (0..f.degree).map(|_| it.rng.below(&f.p)).collect();
    Coords::B(cs).to_elem(&r.ctx)
}

// ----- creation ----------------------------------------------------------------

fn finite_field_q(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let q = a.int_ge(0, 2)?;
    let err = || RuntimeError::runtime(format!("Argument 1 ({q}) is not a prime power"));
    let f = q.factor().ok_or_else(err)?;
    if f.factors.len() != 1 {
        return Err(err());
    }
    let (p, n) = f.factors[0].clone();
    one(it.finite_field(&p, n)?)
}

fn finite_field_pn(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = a.int(0)?.clone();
    let check = a.param_bool("Check")?;
    if p.sign() <= 0 || (check && !p.is_probable_prime()) {
        return Err(super::arg_prime(1, &p));
    }
    let n = a.int_ge(1, 1)?;
    let n = n.to_u64().ok_or_else(|| RuntimeError::runtime("Degree is too large"))?;
    one(it.finite_field(&p, n)?)
}

/// A random monic irreducible polynomial of degree n over `k` (n >= 1).
fn random_irreducible(it: &mut Interp, k: &Rc<Struct>, n: u64) -> RResult<Vec<Elem>> {
    let ctx = ff(k).0.ctx.clone();
    let px = Ctx::poly(&ctx);
    for _ in 0..100_000 {
        let mut cs: Vec<Elem> = (0..n).map(|_| random_elem(it, k)).collect();
        cs.push(Elem::one(&ctx)?);
        if Elem::poly_from_coeffs(&px, &cs)?.poly_is_irreducible()? || n == 1 {
            return Ok(cs);
        }
    }
    Err(RuntimeError::runtime("No irreducible polynomial found"))
}

/// `ext<K | P>` for a monic irreducible P over K (K itself if P is linear).
fn ext_by(it: &mut Interp, k: &Rc<Struct>, poly: Vec<Elem>) -> RResult<Rc<Struct>> {
    if poly.len() <= 2 {
        return Ok(k.clone());
    }
    if degree(k) == 1 {
        let p = ff(k).1.p.clone();
        return it.ff_from_poly(&p, poly.iter().map(|c| c.to_integer().unwrap_or_default()).collect());
    }
    it.ff_relative(k, poly)
}

fn random_extension(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = field_arg(a, 0)?;
    let n = a.small_ge(1, 1).map_err(super::bare)?;
    let poly = random_irreducible(it, &k, n)?;
    one(Value::Struct(ext_by(it, &k, poly)?))
}

/// The polynomial argument over a finite field: its coefficient field and
/// the FLINT polynomial.
fn ff_poly_arg(v: &Value) -> RResult<(Rc<Struct>, Elem)> {
    let e = crate::rings::small::elt_of(v).ok_or_else(bad)?;
    let base = e.ring().base().and_then(finite::field_struct).cloned().ok_or_else(bad)?;
    Ok((base, e.x.clone()))
}

/// The least common multiple of the degrees of the irreducible factors.
fn splitting_degree(f: &Elem) -> RResult<u64> {
    if f.poly_len() < 2 {
        return Ok(1);
    }
    let (_, fs) = f.poly_factor()?;
    Ok(fs.iter().fold(1u64, |l, (g, _)| {
        let d = g.poly_len() as u64 - 1;
        l / calyx_flint::gcd_u64(l, d) * d
    }))
}

fn splitting_field(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (k, f) = ff_poly_arg(&a.args[0])?;
    if f.poly_len() == 0 {
        return Err(super::arg_not(1, "non-zero"));
    }
    let l = splitting_degree(&f)?;
    one(Value::Struct(it.ff_ext_degree(&k, l)?))
}

fn splitting_field_set(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Set(s) = &a.args[0] else { return Err(bad()) };
    let elems: Vec<Value> = s.iter().collect();
    let mut field: Option<Rc<Struct>> = None;
    let mut l = 1u64;
    for v in &elems {
        let (k, f) = ff_poly_arg(v)?;
        if field.as_ref().is_some_and(|x| id(x) != id(&k)) {
            return Err(RuntimeError::runtime("Polynomials must have the same coefficient field"));
        }
        field = Some(k);
        let d = splitting_degree(&f)?;
        l = l / calyx_flint::gcd_u64(l, d) * d;
    }
    let k = field.ok_or_else(|| RuntimeError::runtime("Argument 1 must be non-empty"))?;
    one(Value::Struct(it.ff_ext_degree(&k, l)?))
}

/// The roots of a non-constant polynomial in its coefficient field with
/// their multiplicities, in Magma's order.
fn poly_roots(f: &Elem) -> RResult<Vec<(Elem, u64)>> {
    let mut roots = match f.poly_roots() {
        Ok(rs) => rs,
        Err(_) => f.poly_factor()?.1.into_iter().filter(|(h, _)| h.poly_len() == 2).map(|(h, m)| (h.poly_coeff(0).neg().unwrap(), m)).collect(),
    };
    roots.sort_by(|x, y| elem_cmp(&x.0, &y.0));
    Ok(roots)
}

/// `RootsInSplittingField` and `FactorizationOverSplittingField`: the
/// roots in order, or the linear factors ordered by their constant terms.
fn over_splitting_field(it: &mut Interp, a: &mut CallArgs, factors: bool) -> RResult<Vals> {
    let (k, f) = ff_poly_arg(&a.args[0])?;
    if f.poly_len() == 0 {
        return Err(super::arg_not(1, "non-zero"));
    }
    let l = splitting_degree(&f)?;
    let s = it.ff_ext_degree(&k, l)?;
    let img = sub_image(&k, &s, "No embedding")?;
    let sctx = ff(&s).0.ctx.clone();
    let cs: Vec<Elem> = (0..f.poly_len()).map(|i| finite::embed_with(&f.poly_coeff(i), degree(&k), &img)).collect();
    let g = Elem::poly_from_coeffs(&Ctx::poly(&sctx), &cs)?;
    let mut roots = if g.poly_len() >= 2 { poly_roots(&g)? } else { Vec::new() };
    if factors {
        roots.iter_mut().for_each(|(r, _)| *r = r.neg().unwrap());
        roots.sort_by(|x, y| elem_cmp(&x.0, &y.0));
    }
    let mut out = Vec::with_capacity(roots.len());
    for (r, m) in roots {
        let x = if factors { poly_value(it, &s, &[r, Elem::one(&sctx)?])? } else { make_elt(&s, r) };
        out.push(Value::tuple(vec![x, Value::int(m as i64)]));
    }
    Ok(vals![Value::seq(None, out), Value::Struct(s)])
}

fn roots_in_splitting_field(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    over_splitting_field(it, a, false)
}

fn factorization_over_splitting_field(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    over_splitting_field(it, a, true)
}

fn ground_field(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    one(Value::Struct(ground_of(it, &f)?))
}

fn meet(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = (field_arg(a, 0)?, field_arg(a, 1)?);
    let none_err = || RuntimeError::runtime("Arguments have no covering field");
    if ff(&f).1.p != ff(&g).1.p || it.ff_cover(&f, &g)?.is_none() {
        return Err(none_err());
    }
    if finite::is_subfield(&f, &g) {
        return one(Value::Struct(f));
    }
    if finite::is_subfield(&g, &f) {
        return one(Value::Struct(g));
    }
    let d = calyx_flint::gcd_u64(degree(&f), degree(&g));
    let p = ff(&f).1.p.clone();
    let e = if d == 1 || ff(&f).1.default || ff(&g).1.default { it.default_field(&p, d)? } else { it.ff_sub_degree(&f, d)? };
    one(Value::Struct(e))
}

fn common_overfield(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = (field_arg(a, 0)?, field_arg(a, 1)?);
    match it.ff_cover(&f, &g)? {
        Some(c) => one(Value::Struct(c)),
        None => Err(super::bare(RuntimeError::runtime("No covering field exists"))),
    }
}

fn embed(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (e, f) = (field_arg(a, 0)?, field_arg(a, 1)?);
    it.ff_embed_fields(&e, &f, a.args.get(2))?;
    none()
}

/// An isomorphism between fields of the same size, given by the image of
/// the generator of the context of its domain.
struct FieldIso {
    image: Elem,
    from: Rc<Struct>,
    to: Rc<Struct>,
}

impl NativeMap for FieldIso {
    fn apply(&self, it: &mut Interp, _m: &MapObj, x: &Value) -> RResult<Value> {
        let failed = || RuntimeError::runtime("Application of map failed").in_context("map application");
        let x = it.to_structure_elem(&Value::Struct(self.from.clone()), x, false)?.ok_or_else(failed)?;
        Ok(make_elt(&self.to, finite::embed_with(&x, degree(&self.from), &self.image)))
    }

    fn preimage(&self, it: &mut Interp, _m: &MapObj, y: &Value) -> RResult<Value> {
        let failed = || RuntimeError::runtime("Application of map failed").in_context("@@");
        let y = it.to_structure_elem(&Value::Struct(self.to.clone()), y, false)?.ok_or_else(failed)?;
        let x = finite::restrict_by(&y, &self.from, &self.image, &self.to).ok_or_else(failed)?;
        Ok(make_elt(&self.from, x))
    }
}

fn is_isomorphic(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (e, f) = (field_arg(a, 0)?, field_arg(a, 1)?);
    if ff(&e).1.p != ff(&f).1.p || degree(&e) != degree(&f) {
        return Ok(vals![Value::Bool(false), Value::Undef]);
    }
    let image = finite::iso_image(&e, &f).ok_or_else(|| RuntimeError::runtime("No isomorphism found"))?;
    let imp = FieldIso { image, from: e.clone(), to: f.clone() };
    let map = Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain: Value::Struct(e), codomain: Value::Struct(f), imp: MapImpl::Native(Rc::new(imp)) }));
    Ok(vals![Value::Bool(true), map])
}

// ----- structure -----------------------------------------------------------------

fn degree_ff(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    intv(Integer::from_u64(degree(&f)))
}

fn degree_over(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, e) = (field_arg(a, 0)?, field_arg(a, 1)?);
    sub_image(&e, &f, NOT_SUB_OF)?;
    intv(Integer::from_u64(degree(&f) / degree(&e)))
}

fn is_conway(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    boolv(ff(&f).1.conway)
}

fn is_default(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    boolv(ff(&f).1.default)
}

fn defining_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    let fd = ff(&f).1;
    if let Some(g) = &fd.ground {
        let (k, poly) = (g.field.clone(), g.poly.clone());
        return one(poly_value(it, &k, &poly)?);
    }
    let p = fd.p.clone();
    // A prime field is generated by 1.
    let modulus = if fd.degree == 1 { vec![&p - &Integer::one(), Integer::one()] } else { fd.modulus.clone() };
    one(int_poly_value(it, &p, &modulus)?)
}

fn defining_polynomial_over(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, e) = (field_arg(a, 0)?, field_arg(a, 1)?);
    sub_image(&e, &f, NOT_SUB_OF)?;
    let g = gen_over(it, &f, &e)?;
    let mp = finite::min_poly(&g, &f, &e).ok_or_else(bad)?;
    one(poly_value(it, &e, &mp)?)
}

/// The map from an abelian group onto the additive or multiplicative group
/// of a field: `A.i` to the (i-1)-th power of `Generator(F, GF(p))`, or
/// `M.1` to the primitive element.
struct GroupMap {
    field: Rc<Struct>,
    base: Elem,
    additive: bool,
}

fn group_coords(m: &MapObj, x: &Value) -> RResult<Box<[Integer]>> {
    match (x, &m.domain) {
        (Value::AbElt(e), Value::Struct(st)) if Rc::ptr_eq(&e.group, st) => Ok(e.coords.clone()),
        _ => Err(RuntimeError::runtime("Application of map failed").in_context("map application")),
    }
}

impl NativeMap for GroupMap {
    fn apply(&self, _it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        let c = group_coords(m, x)?;
        let ctx = ff(&self.field).0.ctx.clone();
        let y = if self.additive {
            let mut acc = Elem::zero(&ctx);
            for ci in c.iter().rev() {
                acc = acc.mul(&self.base)?.add(&Elem::from_integer(&ctx, ci)?)?;
            }
            acc
        } else {
            self.base.pow(&c[0])?
        };
        Ok(make_elt(&self.field, y))
    }

    fn preimage(&self, it: &mut Interp, m: &MapObj, y: &Value) -> RResult<Value> {
        let fail = || RuntimeError::runtime("Application of map failed").in_context("@@");
        let y = it.to_structure_elem(&Value::Struct(self.field.clone()), y, false)?.ok_or_else(fail)?;
        let Value::Struct(g) = &m.domain else { unreachable!() };
        let coords = if self.additive {
            let fp = prime_of(it, &self.field)?;
            let one_ = Elem::one(&ff(&fp).0.ctx)?;
            coords_over(&self.field, &y, &fp, &one_, &self.base).iter().map(|c| c.to_integer().unwrap_or_default()).collect()
        } else {
            if is_zero(&y) {
                return Err(fail());
            }
            vec![log_base(it, &self.field, &self.base, &y)?.ok_or_else(fail)?]
        };
        Ok(crate::abgroups::elt(g, coords))
    }
}

/// A group with its map; a statement printing the call shows the group.
fn with_map(a: &CallArgs, group: Rc<Struct>, map: Value) -> RResult<Vals> {
    if a.nresults < 2 { one(Value::Struct(group)) } else { Ok(vals![Value::Struct(group), map]) }
}

fn group_map(group: &Rc<Struct>, f: &Rc<Struct>, imp: GroupMap) -> Value {
    let (domain, codomain) = (Value::Struct(group.clone()), Value::Struct(f.clone()));
    Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain, codomain, imp: MapImpl::Native(Rc::new(imp)) }))
}

fn additive_group(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    let (p, n) = (ff(&f).1.p.clone(), degree(&f));
    let group = crate::abgroups::new_group(vec![p; n as usize]);
    let fp = prime_of(it, &f)?;
    let base = gen_over(it, &f, &fp)?;
    let map = group_map(&group, &f, GroupMap { field: f.clone(), base, additive: true });
    with_map(a, group, map)
}

fn multiplicative_group(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    let q1 = &ff(&f).1.order() - &Integer::one();
    let group = crate::abgroups::new_group(vec![q1]);
    let base = it.ff_primitive(&f)?;
    let map = group_map(&group, &f, GroupMap { field: f.clone(), base, additive: false });
    with_map(a, group, map)
}

fn root_of_unity(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?.clone();
    let k = field_arg(a, 1)?;
    if n.sign() <= 0 {
        return Err(super::arg_ge(1, &n, 1));
    }
    if n.to_u64().is_none_or(|n| n >= 1 << 30) {
        return Err(RuntimeError::runtime(format!("Argument 1 ({n}) is too large")));
    }
    let q = ff(&k).1.order();
    if !n.gcd(&q).is_one() {
        return Err(RuntimeError::runtime(format!("Argument 1 ({n}) is not coprime to the size of argument 2")));
    }
    let m = crate::intrinsics::ints::modorder(&q.div_rem_euclid(&n).unwrap().1, &n).to_u64().filter(|&m| m < 1 << 20);
    let m = m.ok_or_else(|| RuntimeError::runtime("Extension degree is too large"))?;
    let m = m.max(1);
    let l = it.ff_ext_degree(&k, m)?;
    let pe = it.ff_primitive(&l)?;
    let e = (&ff(&l).1.order() - &Integer::one()).divexact(&n);
    one(make_elt(&l, pe.pow(&e)?))
}

// ----- printing options ----------------------------------------------------------

/// Turn power printing on or off, with Magma's errors.
fn power_printing(f: &Struct, on: bool) -> RResult<()> {
    let (r, fd) = ff(f);
    if fd.degree == 1 {
        return Err(RuntimeError::runtime("Changing of printing style illegal for this kind of field"));
    }
    if on && !is_zech(&r.ctx) {
        return Err(RuntimeError::runtime("Power printing is not available for this kind of field"));
    }
    if on && !finite::is_primitive(f, &finite::gen1(r, fd)) {
        return Err(RuntimeError::runtime("Power printing not available (generator not primitive)"));
    }
    fd.power_printing.set(on);
    Ok(())
}

fn set_power_printing(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    power_printing(&f, a.bool(1)?)?;
    none()
}

fn assert_attribute(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    let name = a.str(1)?.to_string();
    if name == "PowerPrinting" {
        let Value::Bool(on) = a.args[2] else {
            return Err(RuntimeError::runtime("Bad rhs type for attribute \"PowerPrinting\""));
        };
        power_printing(&f, on)?;
        return none();
    }
    f.attrs.borrow_mut().insert(Sym::new(&name), a.args[2].clone());
    none()
}

fn has_attribute(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    let name = Sym::new(a.str(1)?);
    if &*name.as_rc() == "PowerPrinting" {
        let (r, fd) = ff(&f);
        if !is_zech(&r.ctx) {
            return Ok(vals![Value::Bool(false), Value::Undef]);
        }
        return Ok(vals![Value::Bool(true), Value::Bool(fd.power_printing.get())]);
    }
    let v = a.args[0].clone();
    match it.attr_assigned(&v, name) {
        Ok(true) => Ok(vals![Value::Bool(true), it.get_attr(&v, name)?]),
        _ => Ok(vals![Value::Bool(false), Value::Undef]),
    }
}

// ----- special elements ------------------------------------------------------------

/// `Generator(F, E)`: `F.1` if it generates F over E, else the primitive
/// element.
fn gen_over(it: &mut Interp, f: &Rc<Struct>, e: &Rc<Struct>) -> RResult<Elem> {
    let (r, fd) = ff(f);
    let g = finite::gen1(r, fd);
    let m = fd.degree / degree(e);
    if finite::conjugates(&g, degree(e), m).len() as u64 == m {
        return Ok(g);
    }
    it.ff_primitive(f)
}

fn generator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    let (r, fd) = ff(&f);
    one(make_elt(&f, finite::gen1(r, fd)))
}

fn generator_over(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, e) = (field_arg(a, 0)?, field_arg(a, 1)?);
    sub_image(&e, &f, NOT_SUB_OF)?;
    one(make_elt(&f, gen_over(it, &f, &e)?))
}

fn primitive_element(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    one(make_elt(&f, it.ff_primitive(&f)?))
}

fn set_primitive_element(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, (g, x)) = (field_arg(a, 0)?, felt_arg(a, 1)?);
    if id(&g) != id(&f) {
        return Err(RuntimeError::runtime("Argument 2 is not in argument 1"));
    }
    let (r, fd) = ff(&f);
    // Fields with Zech logarithms have theirs from the start; others once
    // it is set or had to be found.
    if is_zech(&r.ctx) || fd.cache.primitive_fixed.get() {
        if it.ff_primitive(&f)?.equal(&x) != Truth::True {
            return Err(RuntimeError::runtime("Primitive element already set to different value"));
        }
        return none();
    }
    if !finite::is_primitive(&f, &x) {
        return Err(RuntimeError::runtime("Argument 2 is not primitive"));
    }
    *fd.cache.primitive.borrow_mut() = Some(x);
    fd.cache.primitive_fixed.set(true);
    none()
}

/// Whether x, x^q, ..., x^(q^(m-1)) is a basis of f over its subfield e
/// (with q = #e).
fn is_normal_over(f: &Rc<Struct>, x: &Elem, e: &Rc<Struct>, ei: &Elem) -> bool {
    let fd = ff(f).1;
    if is_zero(x) {
        return false;
    }
    let (n, d) = (fd.degree, degree(e));
    if n == d {
        return true;
    }
    let mut cols = Vec::with_capacity(n as usize);
    let mut c = x.clone();
    for _ in 0..n / d {
        let mut t = c.clone();
        for _ in 0..d {
            cols.push(Coords::of(&t));
            t = t.mul(ei).unwrap();
        }
        c = c.fq_frobenius(d as i64).unwrap();
    }
    LinMap::from_columns(&fd.p, &cols, n as usize).inverse().is_some()
}

/// The first power of the generator of the context of `f` that is normal
/// over `e` (so the first normal element in Magma's order when there are
/// logarithms; Magma itself picks one at random).
fn normal_element_over(f: &Rc<Struct>, e: &Rc<Struct>) -> RResult<Vals> {
    let ei = sub_image(e, f, NOT_SUB_OF)?;
    let ctx = ff(f).0.ctx.clone();
    let g = if degree(f) == 1 { Elem::one(&ctx)? } else { ctx.generator()? };
    let mut x = Elem::one(&ctx)?;
    for _ in 0..1 << 20 {
        if is_normal_over(f, &x, e, &ei) {
            return one(make_elt(f, x));
        }
        x = x.mul(&g)?;
    }
    Err(RuntimeError::runtime("No normal element found"))
}

fn normal_element(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    let g = ground_of(it, &f)?;
    normal_element_over(&f, &g)
}

fn normal_element_e(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, e) = (field_arg(a, 0)?, field_arg(a, 1)?);
    normal_element_over(&f, &e)
}

// ----- sequences ---------------------------------------------------------------------

/// The coordinates of `x` over the subfield `e` of `f` in the power basis of
/// `g` (which generates f over e), in the context of `e`; `ei` is the image
/// of the generator of the context of `e`.
fn coords_over(f: &Rc<Struct>, x: &Elem, e: &Rc<Struct>, ei: &Elem, g: &Elem) -> Vec<Elem> {
    let ((fr, fd), (er, ed)) = (ff(f), ff(e));
    if fd.degree == 1 {
        return vec![x.clone()];
    }
    let (d, m) = (ed.degree as usize, (fd.degree / ed.degree) as usize);
    let mut cols = Vec::with_capacity(fd.degree as usize);
    let mut gi = Elem::one(&fr.ctx).unwrap();
    for _ in 0..m {
        let mut t = gi.clone();
        for _ in 0..d {
            cols.push(Coords::of(&t));
            t = t.mul(ei).unwrap();
        }
        gi = gi.mul(g).unwrap();
    }
    let inv = LinMap::from_columns(&fd.p, &cols, fd.degree as usize).inverse().expect("a basis");
    let v = inv.apply(&Coords::of(x));
    (0..m).map(|i| v.chunk(i, d).to_elem(&er.ctx)).collect()
}

/// The coordinates of `x` over the subfield `e` (see `coords_over`).
fn eltseq_over(it: &mut Interp, f: &Rc<Struct>, x: &Elem, e: &Rc<Struct>) -> RResult<Vec<Elem>> {
    let ei = sub_image(e, f, NOT_SUB)?;
    if id(e) == id(f) {
        return Ok(vec![x.clone()]);
    }
    let k = ground_of(it, f)?;
    if id(&k) == id(e) {
        return Ok(finite::ground_elems(f, x, &ff(e).0.ctx));
    }
    let g = gen_over(it, f, e)?;
    Ok(coords_over(f, x, e, &ei, &g))
}

fn elt_seq(e: &Rc<Struct>, cs: Vec<Elem>) -> Value {
    Value::seq(Some(Value::Struct(e.clone())), cs.into_iter().map(|c| make_elt(e, c)).collect())
}

fn eltseq(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    let g = ground_of(it, &f)?;
    let cs = eltseq_over(it, &f, &x, &g)?;
    one(elt_seq(&g, cs))
}

fn eltseq_e(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    let e = field_arg(a, 1)?;
    let cs = eltseq_over(it, &f, &x, &e)?;
    one(elt_seq(&e, cs))
}

fn seqelt(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = a.seq(0)?.clone();
    let f = field_arg(a, 1)?;
    let e = match &s.universe {
        Some(u) => finite::field_struct(u).cloned().ok_or_else(bad)?,
        None => ground_of(it, &f)?,
    };
    let ei = sub_image(&e, &f, NOT_SUB)?;
    let m = degree(&f) / degree(&e);
    if s.elems.len() as u64 != m {
        return Err(RuntimeError::runtime(format!("Argument 1 must have length {m}")));
    }
    let g = gen_over(it, &f, &e)?;
    let ctx = ff(&f).0.ctx.clone();
    let mut acc = Elem::zero(&ctx);
    for v in s.elems.iter().rev() {
        let c = crate::rings::small::elt_of(v).ok_or_else(bad)?;
        acc = acc.mul(&g)?.add(&finite::embed_with(&c.x, degree(&e), &ei))?;
    }
    one(make_elt(&f, acc))
}

// ----- element functions -----------------------------------------------------------

fn is_primitive_elt(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    boolv(finite::is_primitive(&f, &x))
}

fn is_normal(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    let e = if a.args.len() > 1 { field_arg(a, 1)? } else { ground_of(it, &f)? };
    let ei = sub_image(&e, &f, NOT_SUB)?;
    boolv(is_normal_over(&f, &x, &e, &ei))
}

/// The field element argument and the subfield argument `i` (default the
/// ground field), checked to be a known subfield.
fn elt_and_sub(it: &mut Interp, a: &CallArgs, i: usize) -> RResult<(Rc<Struct>, Elem, Rc<Struct>)> {
    let (f, x) = felt_arg(a, 0)?;
    let e = if a.args.len() > i { field_arg(a, i)? } else { ground_of(it, &f)? };
    sub_image(&e, &f, NOT_SUB)?;
    Ok((f, x, e))
}

fn minimal_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x, e) = elt_and_sub(it, a, 1)?;
    let mp = finite::min_poly(&x, &f, &e).ok_or_else(bad)?;
    one(poly_value(it, &e, &mp)?)
}

fn characteristic_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x, e) = elt_and_sub(it, a, 1)?;
    let (d, m) = (degree(&e), degree(&f) / degree(&e));
    let cs = finite::conjugates(&x, d, m);
    let all: Vec<Elem> = cs.iter().cycle().take(m as usize).cloned().collect();
    let cp = finite::poly_from_roots(&all, &ff(&f).0.ctx);
    let cp: Vec<Elem> = cp.iter().map(|c| down(c, &f, &e)).collect();
    one(poly_value(it, &e, &cp)?)
}

/// The norm of `x` from `f` to its subfield `e`, in `e`.
fn norm_to(f: &Rc<Struct>, x: &Elem, e: &Rc<Struct>) -> RResult<Elem> {
    let (q, n) = (ff(e).1.order(), degree(f) / degree(e));
    let one_ = Integer::one();
    let y = x.pow(&(&q.pow(n) - &one_).divexact(&(&q - &one_)))?;
    Ok(down(&y, f, e))
}

/// The trace of `x` from `f` to its subfield `e`, in `e`.
fn trace_to(f: &Rc<Struct>, x: &Elem, e: &Rc<Struct>) -> RResult<Elem> {
    let (d, n) = (degree(e), degree(f) / degree(e));
    let mut acc = x.clone();
    let mut c = x.clone();
    for _ in 1..n {
        c = c.fq_frobenius(d as i64)?;
        acc = acc.add(&c)?;
    }
    Ok(down(&acc, f, e))
}

fn norm(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x, e) = elt_and_sub(it, a, 1)?;
    one(make_elt(&e, norm_to(&f, &x, &e)?))
}

fn trace(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x, e) = elt_and_sub(it, a, 1)?;
    one(make_elt(&e, trace_to(&f, &x, &e)?))
}

fn absolute_norm(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    let e = prime_of(it, &f)?;
    one(make_elt(&e, norm_to(&f, &x, &e)?))
}

fn absolute_trace(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    let e = prime_of(it, &f)?;
    one(make_elt(&e, trace_to(&f, &x, &e)?))
}

/// `x^(#E^r)` for the subfield of degree `d`.
fn frobenius_by(f: &Struct, x: &Elem, d: u64, r: &Integer) -> RResult<Elem> {
    let n = degree(f);
    if n == 1 {
        return Ok(x.clone());
    }
    let r = r.div_rem_euclid(&Integer::from_u64(n)).unwrap().1.to_u64().unwrap();
    let k = (d as u128 * r as u128 % n as u128) as i64;
    Ok(if k == 0 { x.clone() } else { x.fq_frobenius(k)? })
}

fn frobenius(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    let (e, r) = match a.args.len() {
        1 => (ground_of(it, &f)?, Integer::one()),
        2 if matches!(a.args[1], Value::Int(_)) => (ground_of(it, &f)?, a.int(1)?.clone()),
        2 => (field_arg(a, 1)?, Integer::one()),
        _ => (field_arg(a, 1)?, a.int(2)?.clone()),
    };
    sub_image(&e, &f, NOT_SUB)?;
    one(make_elt(&f, frobenius_by(&f, &x, degree(&e), &r)?))
}

fn norm_equation(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = field_arg(a, 0)?;
    let (s, y) = felt_arg(a, 1)?;
    sub_image(&s, &k, "The parent of argument 2 is not a subfield of argument 1")?;
    if is_zero(&y) {
        return Ok(vals![Value::Bool(true), make_elt(&k, Elem::zero(&ff(&k).0.ctx))]);
    }
    // The norm of the primitive element generates the units of S.
    let pe = it.ff_primitive(&k)?;
    let g = norm_to(&k, &pe, &s)?;
    let j = log_base(it, &s, &g, &y)?.ok_or_else(|| RuntimeError::runtime("Discrete logarithm is too hard"))?;
    Ok(vals![Value::Bool(true), make_elt(&k, pe.pow(&j)?)])
}

/// For `Hilbert90(a, q)` and `AdditiveHilbert90(a, q)`: the field L of
/// least degree containing the field of a and GF(q), a in L, q and its
/// degree e.
fn hilbert_field(it: &mut Interp, a: &CallArgs) -> RResult<(Rc<Struct>, Elem, Integer, u64)> {
    let (k, x) = felt_arg(a, 0)?;
    let q = a.int(1)?.clone();
    if q <= Integer::one() {
        return Err(RuntimeError::runtime("Argument 2 must be larger than 1"));
    }
    let (p, n) = (ff(&k).1.p.clone(), degree(&k));
    let mut e = 0u64;
    let mut r = q.clone();
    while r.is_divisible_by(&p) && e < n {
        r = r.divexact(&p);
        e += 1;
    }
    if !r.is_one() {
        return Err(RuntimeError::runtime("Argument 2 must divide the size of the parent of argument 1"));
    }
    let l = n / calyx_flint::gcd_u64(n, e) * e;
    let f = it.ff_ext_degree(&k, l / n)?;
    let y = finite::embed(&x, &k, &f).ok_or_else(bad)?;
    Ok((f, y, q, e))
}

/// `L` itself, or its extension of degree m (of bounded size).
fn hilbert_ext(it: &mut Interp, f: &Rc<Struct>, y: Elem, m: &Integer) -> RResult<(Rc<Struct>, Elem)> {
    if m.is_one() {
        return Ok((f.clone(), y));
    }
    let m = m.to_u64().filter(|&m| m.saturating_mul(degree(f)) <= 1 << 16).ok_or_else(|| RuntimeError::runtime("Extension degree is too large"))?;
    let l = it.ff_ext_degree(f, m)?;
    let z = finite::embed(&y, f, &l).ok_or_else(bad)?;
    Ok((l, z))
}

/// A solution of x^(q-1) = a: the least (q-1)-th root of a in the extension
/// of the field L of a and GF(q) whose degree over L is the order of the
/// norm of a to GF(q).
fn hilbert90(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, y, q, _) = hilbert_field(it, a)?;
    if is_zero(&y) {
        return one(make_elt(&f, y));
    }
    let q1 = &q - &Integer::one();
    let nm = y.pow(&(&ff(&f).1.order() - &Integer::one()).divexact(&q1))?;
    let m = finite::mult_order(&f, &nm);
    let (l, z) = hilbert_ext(it, &f, y, &m)?;
    let x = nth_roots(it, &l, &z, &q1, false)?.into_iter().next().ok_or_else(bad)?;
    one(make_elt(&l, x))
}

/// A solution of x^q - x = a: in the field L of a and GF(q) when the trace
/// of a to GF(q) is zero, else in the extension of degree p of L; the one
/// with zero coordinates at the free variables of the linear system (as
/// in Magma, where it answers).
fn additive_hilbert90(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, y, _, e) = hilbert_field(it, a)?;
    let (p, n) = (ff(&f).1.p.clone(), degree(&f));
    let mut t = y.clone();
    let mut c = y.clone();
    for _ in 1..n / e {
        c = c.fq_frobenius(e as i64)?;
        t = t.add(&c)?;
    }
    let m = if is_zero(&t) { Integer::one() } else { p.clone() };
    let (l, z) = hilbert_ext(it, &f, y, &m)?;
    // Solve over GF(p) in the basis of the context of l.
    let (lr, lf) = ff(&l);
    let ctx = lr.ctx.clone();
    let dl = lf.degree as usize;
    let frob = |x: &Elem| -> RResult<Elem> { Ok(if dl == 1 { x.clone() } else { x.fq_frobenius((e % dl as u64) as i64)? }) };
    let g = if dl == 1 { Elem::one(&ctx)? } else { ctx.generator()? };
    let mut cols = Vec::with_capacity(dl);
    let mut b = Elem::one(&ctx)?;
    for _ in 0..dl {
        cols.push(Coords::of(&frob(&b)?.sub(&b)?));
        b = b.mul(&g)?;
    }
    let sol = LinMap::from_columns(&p, &cols, dl).solve(&Coords::of(&z)).ok_or_else(bad)?;
    one(make_elt(&l, sol.to_elem(&ctx)))
}

fn factored_order(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    if is_zero(&x) {
        return Err(RuntimeError::runtime("Can not take order of zero element"));
    }
    let q1 = &ff(&f).1.order() - &Integer::one();
    let fac = q1.factor().map(|x| x.factors).unwrap_or_default();
    let mut out = Vec::new();
    let mut n = q1.clone();
    for (r, e) in &fac {
        // Remove the factors of r that x^(n/r) = 1 allows.
        let mut k = *e;
        while k > 0 {
            let m = n.divexact(r);
            if x.pow(&m)?.is_one() != Truth::True {
                break;
            }
            n = m;
            k -= 1;
        }
        if k > 0 {
            out.push((r.clone(), k));
        }
    }
    one(crate::intrinsics::factseq::fact_value(&out))
}

// ----- roots ---------------------------------------------------------------------------

/// The n-th roots of `x` in `f`, least first (all of them, or the one Magma
/// returns first).
fn nth_roots(it: &mut Interp, f: &Rc<Struct>, x: &Elem, n: &Integer, all: bool) -> RResult<Vec<Elem>> {
    let (r, fd) = ff(f);
    let ctx = r.ctx.clone();
    if is_zero(x) {
        return Ok(vec![x.clone()]);
    }
    let q1 = &fd.order() - &Integer::one();
    let g = n.gcd(&q1);
    if x.pow(&q1.divexact(&g))?.is_one() != Truth::True {
        return Ok(Vec::new());
    }
    if let (Some(k), Some(m)) = (x.zech_log(), Elem::zech_order(&ctx)) {
        // With logarithms: j n = k modulo q - 1, least j first.
        let g = g.to_u64().unwrap();
        let (m1, k1, n1) = (m / g, k / g, n.divexact(&Integer::from_u64(g)).mod_u64(m / g));
        let j0 = if m1 == 1 { 0 } else { Nmod::new(m1).mul(k1 % m1, Nmod::new(m1).inv(n1).unwrap()) };
        let count = if all { g } else { 1 };
        return Ok((0..count).map(|t| Elem::fq_from_zech_log(&ctx, j0 + t * m1).unwrap()).collect());
    }
    let x0 = one_root(it, f, x, n, &g)?;
    if !all {
        return Ok(vec![x0]);
    }
    // All roots: x0 times the g-th roots of unity.
    let pe = it.ff_primitive(f)?;
    let w = pe.pow(&q1.divexact(&g))?;
    let gg = g.to_u64().filter(|&g| g <= 1 << 24).ok_or_else(|| RuntimeError::runtime("Too many roots"))?;
    let mut out = Vec::with_capacity(gg as usize);
    let mut y = x0;
    for _ in 0..gg {
        out.push(y.clone());
        y = y.mul(&w)?;
    }
    sort_elems(&mut out);
    Ok(out)
}

/// One n-th root of `x` (known to exist; g = gcd(n, q - 1)) in a field
/// without logarithm tables: Tonelli–Shanks with the least non-residue for
/// square roots, the unique root when g = 1, else a root through a g-th
/// root.
fn one_root(it: &mut Interp, f: &Rc<Struct>, x: &Elem, n: &Integer, g: &Integer) -> RResult<Elem> {
    let q1 = &ff(f).1.order() - &Integer::one();
    // x^n = a: take a g-th root y, then x = y^w with w n/g = 1 mod (q-1)/g.
    let m = q1.divexact(g);
    let w = if m.is_one() { Integer::zero() } else { n.divexact(g).invmod(&m).unwrap_or_default() };
    let y = if g.is_one() {
        x.clone()
    } else if *g == Integer::from_u64(2) {
        sqrt_ts(it, f, x)?
    } else {
        root_by_factors(it, f, x, g)?
    };
    if m.is_one() {
        return Ok(y);
    }
    Ok(y.pow(&w)?)
}

/// The least element of the field (in counting order) that is not a
/// square.
fn least_non_square(f: &Rc<Struct>) -> Elem {
    let (r, fd) = ff(f);
    let q1 = &fd.order() - &Integer::one();
    let h = q1.fdiv_2exp(1);
    for i in 2..1u64 << 20 {
        let z = counted_elem(&r.ctx, fd, i);
        if z.pow(&h).map(|y| y.is_neg_one() == Truth::True).unwrap_or(false) {
            return z;
        }
    }
    unreachable!("a non-square exists")
}

/// The i-th element of the field counting coordinates in base p (so i
/// itself for a prime field).
fn counted_elem(ctx: &Rc<Ctx>, fd: &FiniteField, i: u64) -> Elem {
    let mut c = Integer::from_u64(i);
    let mut cs = Vec::with_capacity(fd.degree as usize);
    for _ in 0..fd.degree {
        let (qq, rr) = c.div_rem_euclid(&fd.p).unwrap();
        cs.push(rr);
        c = qq;
    }
    Coords::B(cs).to_elem(ctx)
}

/// Tonelli–Shanks.
fn sqrt_ts(_it: &mut Interp, f: &Rc<Struct>, a: &Elem) -> RResult<Elem> {
    let q1 = &ff(f).1.order() - &Integer::one();
    let (mut q, mut s) = (q1.clone(), 0u64);
    while q.is_even() {
        q = q.fdiv_2exp(1);
        s += 1;
    }
    if s == 0 {
        // Characteristic 2: the square root is a^(q/2), q = #F.
        return Ok(a.pow(&(&q1 + &Integer::one()).fdiv_2exp(1))?);
    }
    let z = least_non_square(f);
    let mut m = s;
    let mut c = z.pow(&q)?;
    let mut t = a.pow(&q)?;
    let mut r = a.pow(&(&q + &Integer::one()).fdiv_2exp(1))?;
    while t.is_one() != Truth::True {
        let (mut i, mut tt) = (0u64, t.clone());
        while tt.is_one() != Truth::True && i < m {
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

/// A g-th root (g dividing q - 1) of a g-th power, one prime at a time by
/// Adleman–Manders–Miller.
fn root_by_factors(it: &mut Interp, f: &Rc<Struct>, a: &Elem, g: &Integer) -> RResult<Elem> {
    let fac = g.factor().map(|x| x.factors).unwrap_or_default();
    let mut y = a.clone();
    for (r, e) in fac {
        for _ in 0..e {
            y = if r == Integer::from_u64(2) { sqrt_ts(it, f, &y)? } else { amm_root(f, &y, &r)? };
        }
    }
    Ok(y)
}

/// An r-th root (r prime dividing q - 1) of an r-th power.
fn amm_root(f: &Rc<Struct>, a: &Elem, r: &Integer) -> RResult<Elem> {
    let (rr, fd) = ff(f);
    let q1 = &fd.order() - &Integer::one();
    // q - 1 = r^s t with t prime to r.
    let (mut t, mut s) = (q1.clone(), 0u64);
    while t.is_divisible_by(r) {
        t = t.divexact(r);
        s += 1;
    }
    // alpha with r alpha = 1 mod t.
    let alpha = if t.is_one() { Integer::zero() } else { r.invmod(&t).unwrap() };
    if s == 1 {
        return Ok(a.pow(&alpha)?);
    }
    // A non-r-th power rho.
    let h = q1.divexact(r);
    let mut rho = None;
    for i in 2..1u64 << 20 {
        let z = counted_elem(&rr.ctx, fd, i);
        if z.pow(&h)?.is_one() != Truth::True {
            rho = Some(z);
            break;
        }
    }
    let rho = rho.ok_or_else(|| RuntimeError::runtime("No non-residue found"))?;
    // Work in the subgroup of order r^s: a^alpha is a root up to an element
    // of it, found digit by digit.
    let x = a.pow(&alpha)?;
    let err = x.pow(r)?.div(a)?;
    let gam = rho.pow(&t)?;
    let zeta = gam.pow(&r.pow(s - 1))?;
    let mut e = err;
    let mut corr = Elem::one(&rr.ctx)?;
    for i in 1..s {
        let d = e.pow(&r.pow(s - 1 - i))?;
        let mut j = 0u64;
        let mut zj = Elem::one(&rr.ctx)?;
        let rmax = r.to_u64().unwrap_or(u64::MAX);
        while zj.equal(&d) != Truth::True && j < rmax {
            zj = zj.mul(&zeta)?;
            j += 1;
        }
        // Remove gam^(j r^(i-1))... from the error.
        let c = gam.pow(&(&r.pow(i - 1) * &Integer::from_u64(j)))?;
        corr = corr.mul(&c)?;
        e = e.div(&c.pow(r)?)?;
    }
    Ok(x.div(&corr)?)
}

fn is_square(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    match nth_roots(it, &f, &x, &Integer::from_u64(2), false)?.into_iter().next() {
        Some(y) => Ok(vals![Value::Bool(true), make_elt(&f, y)]),
        None => Ok(vals![Value::Bool(false), Value::Undef]),
    }
}

fn sqrt(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    match nth_roots(it, &f, &x, &Integer::from_u64(2), false)?.into_iter().next() {
        Some(y) => one(make_elt(&f, y)),
        None => Err(RuntimeError::runtime("Argument has no square root")),
    }
}

fn root(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    let n = a.int(1)?.clone();
    if n.sign() <= 0 {
        // (sic: Magma numbers the argument 85)
        return Err(RuntimeError::runtime("Argument 85 is not positive"));
    }
    match nth_roots(it, &f, &x, &n, false)?.into_iter().next() {
        Some(y) => one(make_elt(&f, y)),
        None => Err(RuntimeError::runtime("No solution exists")),
    }
}

fn is_power(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    let n = a.int(1)?.clone();
    if n.sign() <= 0 {
        return Err(super::arg_not(2, "positive"));
    }
    match nth_roots(it, &f, &x, &n, false)?.into_iter().next() {
        Some(y) => Ok(vals![Value::Bool(true), make_elt(&f, y)]),
        None => Ok(vals![Value::Bool(false), Value::Undef]),
    }
}

fn all_roots(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    let n = a.int_ge(1, 1)?.clone();
    let rs = nth_roots(it, &f, &x, &n, true)?;
    one(elt_seq(&f, rs))
}

// ----- logarithms ----------------------------------------------------------------------

/// The least k >= 0 with b^k = y (both non-zero), or `None` when y is not a
/// power of b.
fn log_base(it: &mut Interp, f: &Rc<Struct>, b: &Elem, y: &Elem) -> RResult<Option<Integer>> {
    let (r, fd) = ff(f);
    let q1 = &fd.order() - &Integer::one();
    // Logarithms to the base of the context generator, or of the primitive
    // element.
    let (lb, ly) = match (b.zech_log(), y.zech_log()) {
        (Some(lb), Some(ly)) => (Integer::from_u64(lb), Integer::from_u64(ly)),
        _ => {
            let pe = if fd.degree == 1 { it.ff_primitive(f)? } else { it.ff_primitive(f)? };
            let fac = q1.factor().map(|x| x.factors).unwrap_or_default();
            let hard = || RuntimeError::runtime("Discrete logarithm is too hard");
            let lg = |x: &Elem| -> Option<Integer> {
                match r.ctx.kind() {
                    CtxKind::Nmod(_) | CtxKind::FmpzMod(_) => {
                        super::dlog::log_mod_prime(&x.to_integer().ok()?, &pe.to_integer().ok()?, &fd.p, &fac)
                    }
                    _ => super::dlog::log_in_field(x, &pe, &q1, &fac),
                }
            };
            (lg(b).ok_or_else(hard)?, lg(y).ok_or_else(hard)?)
        }
    };
    // lb k = ly modulo q - 1.
    let g = lb.gcd(&q1);
    if !ly.is_divisible_by(&g) {
        return Ok(None);
    }
    let m = q1.divexact(&g);
    if m.is_one() {
        return Ok(Some(Integer::zero()));
    }
    let k = (&ly.divexact(&g) * &lb.divexact(&g).invmod(&m).unwrap()).div_rem_euclid(&m).unwrap().1;
    Ok(Some(k))
}

fn log(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    if is_zero(&x) {
        return Err(RuntimeError::runtime("Can not take log of zero element"));
    }
    let pe = it.ff_primitive(&f)?;
    intv(log_base(it, &f, &pe, &x)?.unwrap_or_default())
}

fn log_b(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, b) = felt_arg(a, 0)?;
    let (g, x) = felt_arg(a, 1)?;
    let (f, b, x) = if id(&f) == id(&g) {
        (f, b, x)
    } else {
        let c = it.ff_cover(&f, &g)?.ok_or_else(|| RuntimeError::runtime("Arguments are not compatible"))?;
        let b = it.ff_convert(&b, &f, &c)?.ok_or_else(bad)?;
        let x = it.ff_convert(&x, &g, &c)?.ok_or_else(bad)?;
        (c, b, x)
    };
    if is_zero(&b) || is_zero(&x) {
        return Err(RuntimeError::runtime("Can not take log of zero element"));
    }
    match log_base(it, &f, &b, &x)? {
        Some(k) => intv(k),
        None => intv(Integer::from_i64(-1)),
    }
}

fn zech_log(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    let n = a.int(1)?.clone();
    let pe = it.ff_primitive(&f)?;
    let q1 = &ff(&f).1.order() - &Integer::one();
    let y = pe.pow(&n.div_rem_euclid(&q1).unwrap().1)?.add(&Elem::one(&ff(&f).0.ctx)?)?;
    if is_zero(&y) {
        return intv(Integer::from_i64(-1));
    }
    intv(log_base(it, &f, &pe, &y)?.unwrap_or_default())
}

fn sieve(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    field_arg(a, 0)?;
    none()
}

// ----- polynomials -------------------------------------------------------------------

fn conway_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = a.int(0)?.clone();
    let n = a.int(1)?.clone();
    if !p.is_prime() {
        return Err(super::arg_prime(1, &p));
    }
    if n.sign() <= 0 {
        return Err(super::arg_ge(2, &n, 1));
    }
    let c = p.to_u64().zip(n.to_u64()).and_then(|(p, n)| calyx_flint::gr::conway_polynomial(p, n));
    let Some(c) = c else {
        return Err(RuntimeError::runtime("Conway polynomial not known for these parameters"));
    };
    one(int_poly_value(it, &p, &c)?)
}

fn exists_conway_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = a.int(0)?.clone();
    let n = a.int(1)?.clone();
    if !p.is_prime() {
        return Err(super::arg_prime(1, &p));
    }
    if n.sign() <= 0 {
        return Err(super::arg_ge(2, &n, 1));
    }
    match p.to_u64().zip(n.to_u64()).and_then(|(p, n)| calyx_flint::gr::conway_polynomial(p, n)) {
        Some(c) => Ok(vals![Value::Bool(true), int_poly_value(it, &p, &c)?]),
        None => Ok(vals![Value::Bool(false), Value::Undef]),
    }
}

/// An irreducible polynomial of degree n over `k`: the Conway polynomial or
/// the defining polynomial of the default field over a prime field, else
/// the first sparse one.
fn irreducible_over(it: &mut Interp, k: &Rc<Struct>, n: u64) -> RResult<Vec<Elem>> {
    let ctx = ff(k).0.ctx.clone();
    if n == 1 {
        return Ok(vec![Elem::zero(&ctx), Elem::one(&ctx)?]);
    }
    if degree(k) == 1 {
        let p = ff(k).1.p.clone();
        let d = it.default_field(&p, n)?;
        return Ok(finite::int_poly_in(&ff(&d).1.modulus.clone(), &ctx));
    }
    it.ff_irreducible(k, n)
}

fn irreducible_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = field_arg(a, 0)?;
    let n = a.small_ge(1, 1)?;
    let cs = irreducible_over(it, &k, n)?;
    one(poly_value(it, &k, &cs)?)
}

fn random_irreducible_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = field_arg(a, 0)?;
    let n = a.small_ge(1, 1).map_err(super::bare)?;
    let cs = random_irreducible(it, &k, n)?;
    one(poly_value(it, &k, &cs)?)
}

/// Whether x generates the multiplicative group of k[x]/(f) for an
/// irreducible f of degree n over k.
fn poly_is_primitive(k: &Rc<Struct>, f: &Elem) -> RResult<bool> {
    let n = f.poly_len() as u64 - 1;
    if n == 0 || !f.poly_is_irreducible()? {
        return Ok(false);
    }
    let q1 = &ff(k).1.order().pow(n) - &Integer::one();
    let primes: Vec<Integer> = q1.factor().map(|x| x.factors.into_iter().map(|(p, _)| p).collect()).unwrap_or_default();
    let ctx = f.ctx().clone();
    let base = ctx.base().unwrap().clone();
    let x = Elem::poly_from_coeffs(&ctx, &[Elem::zero(&base), Elem::one(&base)?])?;
    let one_ = Elem::poly_from_coeffs(&ctx, &[Elem::one(&base)?])?;
    // x^(q1/r) mod f for each prime r.
    for r in &primes {
        let e = q1.divexact(r);
        if poly_powmod(&x, &e, f)?.equal(&one_) == Truth::True {
            return Ok(false);
        }
    }
    // x must also be a unit: f(0) != 0 (true for irreducible f of degree > 1).
    Ok(n > 1 || poly_powmod(&x, &q1, f)?.equal(&one_) == Truth::True && !is_zero(&f.poly_coeff(0)))
}

/// `b^e mod f` for polynomials.
fn poly_powmod(b: &Elem, e: &Integer, f: &Elem) -> RResult<Elem> {
    let ctx = b.ctx().clone();
    let base = ctx.base().unwrap().clone();
    let mut acc = Elem::poly_from_coeffs(&ctx, &[Elem::one(&base)?])?;
    let b = b.poly_divrem(f)?.1;
    for i in (0..e.bits()).rev() {
        acc = acc.mul(&acc)?.poly_divrem(f)?.1;
        if !e.fdiv_2exp(i).is_even() {
            acc = acc.mul(&b)?.poly_divrem(f)?.1;
        }
    }
    Ok(acc)
}

fn is_primitive_poly(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (k, f) = ff_poly_arg(&a.args[0])?;
    if f.poly_len() < 2 {
        return Err(RuntimeError::runtime("Argument 1 must have positive degree"));
    }
    boolv(poly_is_primitive(&k, &f)?)
}

fn primitive_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = field_arg(a, 0)?;
    let m = a.small_ge(1, 2)?;
    let ctx = ff(&k).0.ctx.clone();
    let px = Ctx::poly(&ctx);
    // The defining polynomial of the default field when it is primitive.
    if degree(&k) == 1 {
        let cs = irreducible_over(it, &k, m)?;
        if poly_is_primitive(&k, &Elem::poly_from_coeffs(&px, &cs)?)? {
            return one(poly_value(it, &k, &cs)?);
        }
    }
    for _ in 0..100_000 {
        let cs = random_irreducible(it, &k, m)?;
        if poly_is_primitive(&k, &Elem::poly_from_coeffs(&px, &cs)?)? {
            return one(poly_value(it, &k, &cs)?);
        }
    }
    Err(RuntimeError::runtime("No primitive polynomial found"))
}

fn all_irreducible_polynomials(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = field_arg(a, 0)?;
    let m = a.small_ge(1, 1)?;
    let (r, kf) = ff(&k);
    let ctx = r.ctx.clone();
    let q = kf.order().to_u64().ok_or_else(|| RuntimeError::runtime("Too many polynomials"))?;
    let total = (q as u128).checked_pow(m as u32).filter(|&t| t <= 1 << 24).ok_or_else(|| RuntimeError::runtime("Too many polynomials"))? as u64;
    let elems: Vec<Elem> = (0..q).map(|i| finite::nth_elem(&ctx, kf, i)).collect();
    let px = Ctx::poly(&ctx);
    let pv = it.poly_ring(&Value::Struct(k.clone()), true)?;
    let Value::Struct(ps) = &pv else { unreachable!() };
    let mut out = Vec::new();
    for i in 0..total {
        let mut cs = Vec::with_capacity(m as usize + 1);
        let mut c = i;
        for _ in 0..m {
            cs.push(elems[(c % q) as usize].clone());
            c /= q;
        }
        cs.push(Elem::one(&ctx)?);
        let f = Elem::poly_from_coeffs(&px, &cs)?;
        if f.poly_is_irreducible()? {
            out.push(make_elt(ps, f));
        }
    }
    let set: VSet = out.into_iter().collect();
    one(Value::Set(Rc::new(SetEnum::new(Some(pv.clone()), set))))
}

/// A polynomial over GF(2) with the given exponents.
fn gf2_poly(it: &mut Interp, exps: &[u64]) -> RResult<Value> {
    let n = *exps.iter().max().unwrap_or(&0) as usize;
    let mut cs = vec![Integer::zero(); n + 1];
    for &e in exps {
        cs[e as usize] = Integer::one();
    }
    int_poly_value(it, &Integer::from_u64(2), &cs)
}

/// Polynomials over GF(2) as bits (bit i is the coefficient of x^i), for
/// the searches for sparse irreducible polynomials of large degree.
mod gf2 {
    fn deg(a: u64) -> u32 {
        63 - a.leading_zeros()
    }

    /// The product of polynomials of degree below 32.
    fn clmul(a: u64, b: u64) -> u64 {
        (0..32).filter(|i| b >> i & 1 == 1).fold(0, |r, i| r ^ a << i)
    }

    fn rem(mut a: u64, h: u64) -> u64 {
        let dh = deg(h);
        while a != 0 && deg(a) >= dh {
            a ^= h << (deg(a) - dh);
        }
        a
    }

    /// x^e mod h for h of degree below 32.
    fn xpow_mod(e: u64, h: u64) -> u64 {
        let mut r = 1;
        for i in (0..64 - e.leading_zeros()).rev() {
            r = rem(clmul(r, r), h);
            if e >> i & 1 == 1 {
                r = rem(r << 1, h);
            }
        }
        r
    }

    /// Trial division of x^n + g by the irreducible polynomials of degree at
    /// most 12, for n above 12.
    pub struct Sieve {
        hs: Vec<(u64, u64)>,
    }

    impl Sieve {
        pub fn new(n: u64) -> Sieve {
            let mut irr: Vec<u64> = Vec::new();
            for h in 2u64..1 << 13 {
                if irr.iter().take_while(|&&g| 2 * deg(g) <= deg(h)).all(|&g| rem(h, g) != 0) {
                    irr.push(h);
                }
            }
            Sieve { hs: irr.into_iter().map(|h| (h, xpow_mod(n, h))).collect() }
        }

        /// Whether x^n + g (the sum of x^e over `low`) has a small factor.
        pub fn divides(&self, low: &[u64]) -> bool {
            self.hs.iter().any(|&(h, r)| low.iter().fold(0, |a, &e| a ^ if e < 64 { rem(1 << e, h) } else { xpow_mod(e, h) }) == r)
        }
    }

    /// Swan's theorem: x^n + x^k + 1 (0 < k < n) has an even number of
    /// irreducible factors, so is reducible.
    pub fn swan_reducible(n: u64, k: u64) -> bool {
        let k = if n % 2 == 1 && k % 2 == 1 { n - k } else { k };
        match (n % 2, k % 2) {
            (0, 0) => true,
            (0, _) => n != 2 * k && (n * k / 2) % 4 <= 1,
            _ if (2 * n) % k != 0 => matches!(n % 8, 3 | 5),
            _ => matches!(n % 8, 1 | 7),
        }
    }

    fn degree(a: &[u64]) -> Option<usize> {
        a.iter().rposition(|&w| w != 0).map(|i| i * 64 + deg(a[i]) as usize)
    }

    /// dst ^= src * x^s, within the words of dst.
    fn xor_shifted(dst: &mut [u64], src: &[u64], s: usize) {
        let (ws, bs) = (s / 64, s % 64);
        for (i, &w) in src.iter().enumerate().filter(|(_, w)| **w != 0) {
            if let Some(d) = dst.get_mut(i + ws) {
                *d ^= w << bs;
            }
            if bs > 0 {
                if let Some(d) = dst.get_mut(i + ws + 1) {
                    *d ^= w >> (64 - bs);
                }
            }
        }
    }

    /// The bits of `a` from `n` up.
    fn high(a: &[u64], n: usize) -> Vec<u64> {
        let (ws, bs) = (n / 64, n % 64);
        (ws..a.len()).map(|i| if bs == 0 { a[i] } else { a[i] >> bs | a.get(i + 1).map_or(0, |w| w << (64 - bs)) }).collect()
    }

    /// Clear the bits of `a` from `n` up.
    fn truncate(a: &mut [u64], n: usize) {
        let (ws, bs) = (n / 64, n % 64);
        for (i, w) in a.iter_mut().enumerate().skip(ws) {
            *w &= if i == ws && bs > 0 { (1 << bs) - 1 } else { 0 };
        }
    }

    /// Interleave the bits of a 32-bit word with zeros.
    fn spread(x: u64) -> u64 {
        let x = (x | x << 16) & 0x0000_ffff_0000_ffff;
        let x = (x | x << 8) & 0x00ff_00ff_00ff_00ff;
        let x = (x | x << 4) & 0x0f0f_0f0f_0f0f_0f0f;
        let x = (x | x << 2) & 0x3333_3333_3333_3333;
        (x | x << 1) & 0x5555_5555_5555_5555
    }

    /// t^2 modulo x^n + (the sum of x^e over `low`, all below n).
    fn sqr_mod(t: &[u64], n: usize, low: &[u64]) -> Vec<u64> {
        let mut a: Vec<u64> = t.iter().flat_map(|&w| [spread(w & 0xffff_ffff), spread(w >> 32)]).collect();
        loop {
            let h = high(&a, n);
            if h.iter().all(|&w| w == 0) {
                break;
            }
            truncate(&mut a, n);
            for &e in low {
                xor_shifted(&mut a, &h, e as usize);
            }
        }
        a.truncate(t.len());
        a
    }

    fn gcd_is_one(mut a: Vec<u64>, mut b: Vec<u64>) -> bool {
        loop {
            let Some(db) = degree(&b) else { return degree(&a) == Some(0) };
            while let Some(da) = degree(&a).filter(|&da| da >= db) {
                let b2 = b.clone();
                xor_shifted(&mut a, &b2, da - db);
            }
            std::mem::swap(&mut a, &mut b);
        }
    }

    /// Rabin's test: whether x^n + (the sum of x^e over `low`, all below n)
    /// is irreducible.
    pub fn is_irreducible(n: u64, low: &[u64]) -> bool {
        let n = n as usize;
        if n < 2 {
            return n == 1;
        }
        let mut f = vec![0u64; (n + 1).div_ceil(64)];
        f[n / 64] |= 1 << (n % 64);
        for &e in low {
            f[e as usize / 64] ^= 1 << (e % 64);
        }
        let mut x = vec![0u64; n.div_ceil(64)];
        x[0] = 2;
        let qs: Vec<usize> = (2..=n).filter(|&q| n % q == 0 && (2..q).take_while(|r| r * r <= q).all(|r| q % r != 0)).collect();
        let mut t = x.clone();
        for i in 1..=n {
            t = sqr_mod(&t, n, low);
            if qs.iter().any(|&q| i == n / q) {
                let mut u = t.clone();
                u[0] ^= 2;
                if !gcd_is_one(f.clone(), u) {
                    return false;
                }
            }
        }
        t == x
    }
}

/// `IrreducibleLowTermGF2Polynomial` and `IrreducibleSparseGF2Polynomial`
/// look their degree up in tables in Magma.
fn gf2_degree(a: &CallArgs, range: std::ops::RangeInclusive<u64>) -> RResult<u64> {
    let n = a.int(0)?;
    if n.sign() <= 0 {
        // (sic: Magma numbers the argument 2)
        return Err(super::arg_ge(2, n, 1));
    }
    n.to_u64().filter(|n| range.contains(n)).ok_or_else(|| RuntimeError::runtime("No polynomial known for this degree"))
}

fn irreducible_low_term_gf2(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = gf2_degree(a, 1..=100_000)?;
    let sieve = (n > 12).then(|| gf2::Sieve::new(n));
    // x^n + g with deg g minimal, then g least with its top coefficients
    // compared first.
    for d in 0..n.min(64) {
        for bits in (1..1u64 << d).step_by(2).chain((d == 0).then_some(0)) {
            let low: Vec<u64> = std::iter::once(d).chain((0..d).filter(|i| bits >> i & 1 == 1)).collect();
            if sieve.as_ref().is_none_or(|s| !s.divides(&low)) && gf2::is_irreducible(n, &low) {
                return one(gf2_poly(it, &[&[n][..], &low].concat())?);
            }
        }
    }
    Err(RuntimeError::runtime("No polynomial known for this degree"))
}

fn irreducible_sparse_gf2(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = gf2_degree(a, 4..=12_800)?;
    let sieve = (n > 12).then(|| gf2::Sieve::new(n));
    let found = |low: &[u64]| sieve.as_ref().is_none_or(|s| !s.divides(low)) && gf2::is_irreducible(n, low);
    for k in (1..n).filter(|&k| !gf2::swan_reducible(n, k)) {
        if found(&[k, 0]) {
            return one(gf2_poly(it, &[n, k, 0])?);
        }
    }
    for k3 in 3..n {
        for k2 in 2..k3 {
            for k1 in 1..k2 {
                if found(&[k3, k2, k1, 0]) {
                    return one(gf2_poly(it, &[n, k3, k2, k1, 0])?);
                }
            }
        }
    }
    Err(RuntimeError::runtime("No polynomial known for this degree"))
}

// ----- permutation polynomials -------------------------------------------------------

// (DicksonFirst and DicksonSecond are in `upoly.rs`.)

fn is_probably_permutation_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (k, f) = ff_poly_arg(&a.args[0])?;
    let (r, kf) = ff(&k);
    let ctx = r.ctx.clone();
    if f.poly_len() < 2 {
        return boolv(kf.order().is_one());
    }
    // Small fields: all values are distinct.
    if let Some(q) = kf.order().to_u64().filter(|&q| q <= 1 << 16) {
        let mut seen: Vec<Vec<u64>> = Vec::with_capacity(q as usize);
        for i in 0..q {
            seen.push(f.poly_evaluate(&finite::nth_elem(&ctx, kf, i))?.fq_coords_u64());
        }
        seen.sort();
        seen.dedup();
        return boolv(seen.len() as u64 == q);
    }
    // Otherwise f(x) - f(x0) has the single root x0 for random x0.
    let attempts = match a.param("NumAttempts") {
        Some(Value::Int(n)) => n.to_u64().unwrap_or(100),
        _ => 100,
    };
    let q = kf.order();
    let px = f.ctx().clone();
    let x = Elem::poly_from_coeffs(&px, &[Elem::zero(&ctx), Elem::one(&ctx)?])?;
    let xq = poly_powmod(&x, &q, &f)?;
    let _ = xq;
    for _ in 0..attempts.min(1000) {
        let x0 = random_elem(it, &k);
        let y = f.poly_evaluate(&x0)?;
        let g = f.sub(&Elem::poly_from_coeffs(&px, &[y])?)?;
        let h = poly_powmod(&x, &q, &g)?.sub(&x)?;
        if h.poly_gcd(&g)?.poly_len() != 2 {
            return boolv(false);
        }
    }
    boolv(true)
}

// ----- registration --------------------------------------------------------------------

pub fn register(it: &mut Interp) {
    for name in ["FiniteField", "GaloisField", "GF"] {
        it.def_params(
            name,
            "q::RngIntElt -> FldFin",
            &[("Optimize", Value::Bool(true)), ("Sparse", Value::Bool(false))],
            "The finite field with q elements.",
            finite_field_q,
        );
        it.def_params(
            name,
            "p::RngIntElt, n::RngIntElt -> FldFin",
            &[("Check", Value::Bool(true)), ("Optimize", Value::Bool(true)), ("Sparse", Value::Bool(false))],
            "The finite field with p^n elements.",
            finite_field_pn,
        );
    }
    it.def("RandomExtension", "F::FldFin, n::RngIntElt -> FldFin", "The extension of F by a random irreducible polynomial of degree n.", random_extension);
    it.def("SplittingField", "P::RngUPolElt[FldFin] -> FldFin", "The splitting field of P over its coefficient field.", splitting_field);
    it.def("SplittingField", "S::{RngUPolElt} -> FldFin", "The splitting field of the polynomials in S.", splitting_field_set);
    it.def("RootsInSplittingField", "f::RngUPolElt[FldFin] -> [Tup], FldFin", "The roots of f in its splitting field S, and S.", roots_in_splitting_field);
    for name in ["FactorizationOverSplittingField", "FactorisationOverSplittingField"] {
        it.def(
            name,
            "f::RngUPolElt[FldFin] -> [Tup], FldFin",
            "The factorization of f into linear factors over its splitting field S, and S.",
            factorization_over_splitting_field,
        );
    }
    for name in ["GroundField", "BaseField"] {
        it.def(name, "F::FldFin -> FldFin", "The field F was constructed over (the prime field if none).", ground_field);
    }
    it.def("meet", "F::FldFin, G::FldFin -> FldFin", "The intersection of F and G.", meet);
    it.def("CommonOverfield", "K::FldFin, L::FldFin -> FldFin", "The smallest field containing K and L.", common_overfield);
    it.def("Embed", "E::FldFin, F::FldFin", "Embed E in F.", embed);
    it.def("Embed", "E::FldFin, F::FldFin, x::FldFinElt", "Embed E in F, mapping the generator of E to x.", embed);
    it.def("IsIsomorphic", "E::FldFin, F::FldFin -> BoolElt, Map", "Whether E and F are isomorphic, and an isomorphism.", is_isomorphic);

    it.def("FieldOfFractions", "F::FldFin -> FldFin", "The field F itself.", |_, a| one(a.args[0].clone()));
    it.def("Degree", "F::FldFin -> RngIntElt", "The degree of F over its prime field.", degree_ff);
    it.def("Degree", "F::FldFin, E::FldFin -> RngIntElt", "The degree of F over its subfield E.", degree_over);
    it.def("IsConway", "F::FldFin -> BoolElt", "Whether F is defined by a Conway polynomial.", is_conway);
    it.def("IsDefault", "F::FldFin -> BoolElt", "Whether F is a default field.", is_default);
    it.def("DefiningPolynomial", "F::FldFin -> RngUPolElt", "The polynomial defining F over its ground field.", defining_polynomial);
    it.def("DefiningPolynomial", "F::FldFin, E::FldFin -> RngUPolElt", "The minimal polynomial of Generator(F, E) over E.", defining_polynomial_over);
    it.def("AdditiveGroup", "F::FldFin -> GrpAb, Map", "The additive group of F, and its map to F.", additive_group);
    for name in ["MultiplicativeGroup", "UnitGroup"] {
        it.def(name, "F::FldFin -> GrpAb, Map", "The multiplicative group of F, and its map to F.", multiplicative_group);
    }
    it.def(
        "RootOfUnity",
        "n::RngIntElt, K::FldFin -> FldFinElt",
        "A primitive n-th root of unity in the smallest extension of K containing one.",
        root_of_unity,
    );

    it.def("SetPowerPrinting", "F::FldFin, l::BoolElt", "Print the elements of F as powers of the primitive element (or not).", set_power_printing);
    it.def("AssertAttribute", "F::FldFin, A::MonStgElt, l::.", "Set attribute A of F (PowerPrinting: the printing of elements).", assert_attribute);
    it.def("HasAttribute", "F::FldFin, A::MonStgElt -> BoolElt, .", "Whether attribute A of F is set, and its value.", has_attribute);

    it.def("Generator", "F::FldFin -> FldFinElt", "The generator F.1 of F over its ground field.", generator);
    it.def("Generator", "F::FldFin, E::FldFin -> FldFinElt", "An element generating F over its subfield E (F.1 if it does).", generator_over);
    it.def("PrimitiveElement", "F::FldFin -> FldFinElt", "The primitive element of F (the base of Log).", primitive_element);
    it.def("SetPrimitiveElement", "F::FldFin, x::FldFinElt", "Set the primitive element of F to x.", set_primitive_element);
    it.def("Identity", "F::FldFin -> FldFinElt", "The identity 1 of F.", |_, a| {
        let f = field_arg(a, 0)?;
        one(make_elt(&f, Elem::one(&ff(&f).0.ctx)?))
    });
    it.def("Random", "F::FldFin -> FldFinElt", "A random element of F.", random);
    it.def("NormalElement", "F::FldFin -> FldFinElt", "A normal element of F over its ground field.", normal_element);
    it.def("NormalElement", "F::FldFin, E::FldFin -> FldFinElt", "A normal element of F over its subfield E.", normal_element_e);
    for name in ["SequenceToElement", "Seqelt"] {
        it.def(name, "s::[FldFinElt], F::FldFin -> FldFinElt", "The element of F with coordinates s over the field of s.", seqelt);
    }
    for name in ["ElementToSequence", "Eltseq"] {
        it.def(name, "a::FldFinElt -> [FldFinElt]", "The coordinates of a over the ground field.", eltseq);
        it.def(name, "a::FldFinElt, E::FldFin -> [FldFinElt]", "The coordinates of a over the subfield E.", eltseq_e);
    }

    it.def("IsPrimitive", "a::FldFinElt -> BoolElt", "Whether a generates the multiplicative group.", is_primitive_elt);
    it.def("IsPrimitive", "f::RngUPolElt[FldFin] -> BoolElt", "Whether x is primitive in the extension defined by f.", is_primitive_poly);
    it.def("IsRegular", "a::FldFinElt -> BoolElt", "Whether a is not a zero divisor (is non-zero).", |_, a| {
        let (_, x) = felt_arg(a, 0)?;
        boolv(!is_zero(&x))
    });
    it.def("IsNormal", "a::FldFinElt -> BoolElt", "Whether a generates a normal basis over the ground field.", is_normal);
    it.def("IsNormal", "a::FldFinElt, E::FldFin -> BoolElt", "Whether a generates a normal basis over E.", is_normal);
    it.def("IsSquare", "a::FldFinElt -> BoolElt, FldFinElt", "Whether a is a square, and a square root.", is_square);
    for name in ["SquareRoot", "Sqrt"] {
        it.def(name, "a::FldFinElt -> FldFinElt", "A square root of a.", sqrt);
    }
    it.def("Root", "a::FldFinElt, n::RngIntElt -> FldFinElt", "An n-th root of a.", root);
    it.def("IsPower", "a::FldFinElt, n::RngIntElt -> BoolElt, FldFinElt", "Whether a is an n-th power, and an n-th root.", is_power);
    it.def("AllRoots", "a::FldFinElt, n::RngIntElt -> [FldFinElt]", "All n-th roots of a in its field.", all_roots);
    it.def("MinimalPolynomial", "a::FldFinElt -> RngUPolElt", "The minimal polynomial of a over the ground field.", minimal_polynomial);
    it.def("MinimalPolynomial", "a::FldFinElt, E::FldFin -> RngUPolElt", "The minimal polynomial of a over E.", minimal_polynomial);
    it.def("CharacteristicPolynomial", "a::FldFinElt -> RngUPolElt", "The characteristic polynomial of a over the ground field.", characteristic_polynomial);
    it.def("CharacteristicPolynomial", "a::FldFinElt, E::FldFin -> RngUPolElt", "The characteristic polynomial of a over E.", characteristic_polynomial);
    it.def("Norm", "a::FldFinElt -> FldFinElt", "The norm of a to the ground field.", norm);
    it.def("Norm", "a::FldFinElt, E::FldFin -> FldFinElt", "The norm of a to E.", norm);
    it.def("Trace", "a::FldFinElt -> FldFinElt", "The trace of a to the ground field.", trace);
    it.def("Trace", "a::FldFinElt, E::FldFin -> FldFinElt", "The trace of a to E.", trace);
    for name in ["AbsoluteNorm", "NormAbs"] {
        it.def(name, "a::FldFinElt -> FldFinElt", "The norm of a to the prime field.", absolute_norm);
    }
    for name in ["AbsoluteTrace", "TraceAbs"] {
        it.def(name, "a::FldFinElt -> FldFinElt", "The trace of a to the prime field.", absolute_trace);
    }
    it.def("Frobenius", "a::FldFinElt -> FldFinElt", "a^q for q the size of the ground field.", frobenius);
    it.def("Frobenius", "a::FldFinElt, r::RngIntElt -> FldFinElt", "a^(q^r) for q the size of the ground field.", frobenius);
    it.def("Frobenius", "a::FldFinElt, E::FldFin -> FldFinElt", "a^#E.", frobenius);
    it.def("Frobenius", "a::FldFinElt, E::FldFin, r::RngIntElt -> FldFinElt", "a^((#E)^r).", frobenius);
    it.def(
        "NormEquation",
        "K::FldFin, y::FldFinElt -> BoolElt, FldFinElt",
        "Whether y is a norm from K to the field of y, and an element of K of norm y.",
        norm_equation,
    );
    it.def("Hilbert90", "a::FldFinElt, q::RngIntElt -> FldFinElt", "A solution of x^(q-1) = a, in an extension if needed.", hilbert90);
    it.def("AdditiveHilbert90", "a::FldFinElt, q::RngIntElt -> FldFinElt", "A solution of x^q - x = a, in an extension if needed.", additive_hilbert90);
    it.def("FactoredOrder", "a::FldFinElt -> RngIntEltFact", "The factored multiplicative order of a.", factored_order);

    it.def("Log", "x::FldFinElt -> RngIntElt", "The logarithm of x to the base of the primitive element.", log);
    it.def("Log", "b::FldFinElt, x::FldFinElt -> RngIntElt", "The logarithm of x to the base b (-1 if there is none).", log_b);
    it.def("ZechLog", "K::FldFin, n::RngIntElt -> RngIntElt", "The Zech logarithm of n: the logarithm of w^n + 1 for the primitive element w.", zech_log);
    it.def_params("Sieve", "K::FldFin", &[("Lanczos", Value::Bool(false))], "Prepare the logarithms of K (nothing to do here).", sieve);
    it.verbose.insert(Rc::from("FFLog"), (0, 2));

    it.def("ConwayPolynomial", "p::RngIntElt, n::RngIntElt -> RngUPolElt", "The Conway polynomial of degree n over GF(p).", conway_polynomial);
    it.def(
        "ExistsConwayPolynomial",
        "p::RngIntElt, n::RngIntElt -> BoolElt, RngUPolElt",
        "Whether the Conway polynomial of degree n over GF(p) is known, and the polynomial.",
        exists_conway_polynomial,
    );
    it.def("IrreduciblePolynomial", "F::FldFin, n::RngIntElt -> RngUPolElt", "An irreducible polynomial of degree n over F.", irreducible_polynomial);
    it.def(
        "RandomIrreduciblePolynomial",
        "F::FldFin, n::RngIntElt -> RngUPolElt",
        "A random irreducible polynomial of degree n over F.",
        random_irreducible_polynomial,
    );
    it.def("PrimitivePolynomial", "F::FldFin, m::RngIntElt -> RngUPolElt", "A primitive polynomial of degree m over F.", primitive_polynomial);
    it.def(
        "AllIrreduciblePolynomials",
        "F::FldFin, m::RngIntElt -> SetEnum",
        "The monic irreducible polynomials of degree m over F.",
        all_irreducible_polynomials,
    );
    it.def(
        "IrreducibleLowTermGF2Polynomial",
        "n::RngIntElt -> RngUPolElt",
        "The irreducible x^n + g over GF(2) with g of least degree, first in lexicographic order.",
        irreducible_low_term_gf2,
    );
    it.def(
        "IrreducibleSparseGF2Polynomial",
        "n::RngIntElt -> RngUPolElt",
        "The first irreducible trinomial x^n + x^k + 1 over GF(2), else pentanomial.",
        irreducible_sparse_gf2,
    );

    it.def_params(
        "IsProbablyPermutationPolynomial",
        "p::RngUPolElt[FldFin] -> BoolElt",
        &[("NumAttempts", Value::int(100))],
        "Whether p probably permutes its coefficient field.",
        is_probably_permutation_polynomial,
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    /// FLINT's test of x^n + (the sum of x^e over `low`) over GF(2).
    fn flint_irreducible(n: u64, low: &[u64]) -> bool {
        let fp = Ctx::residue_ring(&Integer::from_u64(2));
        let mut cs = vec![Elem::zero(&fp); n as usize + 1];
        for &e in low.iter().chain([n].iter()) {
            cs[e as usize] = cs[e as usize].add(&Elem::one(&fp).unwrap()).unwrap();
        }
        Elem::poly_from_coeffs(&Ctx::poly(&fp), &cs).unwrap().poly_is_irreducible().unwrap()
    }

    #[test]
    fn gf2_irreducibility_agrees_with_flint() {
        for n in 1..=11u64 {
            for bits in 0..1u64 << n {
                let low: Vec<u64> = (0..n).filter(|i| bits >> i & 1 == 1).collect();
                assert_eq!(gf2::is_irreducible(n, &low), flint_irreducible(n, &low), "{n} {bits:b}");
            }
        }
        let mut seed = 12345u64;
        for _ in 0..300 {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let n = 13 + seed % 300;
            let low: Vec<u64> = std::iter::once(0).chain((1..n).filter(|i| (seed >> (i % 61)) & 7 == 0 && i % 3 == 1)).collect();
            let sieve = gf2::Sieve::new(n);
            let fast = !sieve.divides(&low) && gf2::is_irreducible(n, &low);
            assert_eq!(fast, flint_irreducible(n, &low), "{n} {low:?}");
        }
    }

    #[test]
    fn swan_reducible_trinomials_are_reducible() {
        for n in 2..=64u64 {
            for k in 1..n {
                if gf2::swan_reducible(n, k) {
                    assert!(!flint_irreducible(n, &[k, 0]), "{n} {k}");
                }
            }
        }
    }
}
