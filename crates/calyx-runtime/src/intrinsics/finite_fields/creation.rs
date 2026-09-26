//! Creation functions: the fields (`GF`, `ext< >`, splitting fields,
//! `meet`) and their special options (power printing).

use super::*;

pub(super) fn finite_field_q(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let q = a.int_ge(0, 2)?;
    let err = || RuntimeError::runtime(format!("Argument 1 ({q}) is not a prime power"));
    let f = it.factor_int(&q);
    let [(p, n)] = &f[..] else { return Err(err()) };
    one(it.finite_field(p, *n)?)
}

pub(super) fn finite_field_pn(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
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
pub(super) fn random_irreducible(it: &mut Interp, k: &Rc<Struct>, n: u64) -> RResult<Vec<Elem>> {
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

pub(super) fn random_extension(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = field_arg(a, 0)?;
    let n = a.small_ge(1, 1).map_err(super::bare)?;
    let poly = random_irreducible(it, &k, n)?;
    one(Value::Struct(ext_by(it, &k, poly)?))
}

/// The polynomial argument over a finite field: its coefficient field and
/// the FLINT polynomial.
pub(super) fn ff_poly_arg(v: &Value) -> RResult<(Rc<Struct>, Elem)> {
    let e = crate::rings::small::elt_of(v).ok_or_else(bad)?;
    let base = e.ring().base().and_then(finite::field_struct).cloned().ok_or_else(bad)?;
    Ok((base, e.x.clone()))
}

/// The least common multiple of the degrees of the irreducible factors.
pub(super) fn splitting_degree(f: &Elem) -> RResult<u64> {
    if f.poly_len() < 2 {
        return Ok(1);
    }
    let (_, fs) = f.poly_factor()?;
    Ok(fs.iter().fold(1u64, |l, (g, _)| {
        let d = g.poly_len() as u64 - 1;
        l / calyx_flint::gcd_u64(l, d) * d
    }))
}

pub(super) fn splitting_field(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (k, f) = ff_poly_arg(&a.args[0])?;
    if f.poly_len() == 0 {
        return Err(super::arg_not(1, "non-zero"));
    }
    let l = splitting_degree(&f)?;
    one(Value::Struct(it.ff_ext_degree(&k, l)?))
}

pub(super) fn splitting_field_set(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
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

pub(super) fn ground_field(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    one(Value::Struct(ground_of(it, &f)?))
}

pub(super) fn meet(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
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

pub(super) fn common_overfield(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = (field_arg(a, 0)?, field_arg(a, 1)?);
    match it.ff_cover(&f, &g)? {
        Some(c) => one(Value::Struct(c)),
        None => Err(super::bare(RuntimeError::runtime("No covering field exists"))),
    }
}

// ----- special options -----------------------------------------------------------

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

pub(super) fn set_power_printing(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    power_printing(&f, a.bool(1)?)?;
    none()
}

pub(super) fn assert_attribute(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
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

pub(super) fn has_attribute(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
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
