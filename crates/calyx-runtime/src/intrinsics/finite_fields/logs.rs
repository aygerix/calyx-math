//! Discrete logarithms.

use super::*;

/// The least k >= 0 with b^k = y (both non-zero), or `None` when y is not a
/// power of b.
pub(super) fn log_base(it: &mut Interp, f: &Rc<Struct>, b: &Elem, y: &Elem) -> RResult<Option<Integer>> {
    let (r, fd) = ff(f);
    let q1 = &fd.order() - &Integer::one();
    // Logarithms to the base of the context generator, or of the primitive
    // element.
    let (lb, ly) = match (b.zech_log(), y.zech_log()) {
        (Some(lb), Some(ly)) => (Integer::from_u64(lb), Integer::from_u64(ly)),
        _ => {
            // (Remembered, as Magma remembers them.)
            let pe = it.ff_primitive(f)?;
            let fac = finite::qm1_factors(f);
            let prime = matches!(r.ctx.kind(), CtxKind::Nmod(_) | CtxKind::FmpzMod(_));
            let lg = |x: &Elem| -> RResult<Integer> {
                if x.equal(&pe) == Truth::True {
                    return Ok(Integer::one());
                }
                let key = if prime { vec![x.to_integer().unwrap_or_default()] } else { x.fq_coords() };
                if let Some(k) = fd.cache.logs.borrow().get(&key) {
                    return Ok(k.clone());
                }
                let k = if prime {
                    let (x, g) = (x.to_integer().unwrap_or_default(), pe.to_integer().unwrap_or_default());
                    super::dlog::log_mod_prime(&x, &g, &fd.p, fac)
                } else {
                    super::dlog::log_in_field(x, &pe, &q1, fac)
                };
                let k = k.ok_or_else(|| RuntimeError::runtime("Discrete logarithm is too hard"))?;
                let mut logs = fd.cache.logs.borrow_mut();
                if logs.len() >= 1 << 12 {
                    logs.clear();
                }
                logs.insert(key, k.clone());
                Ok(k)
            };
            (lg(b)?, lg(y)?)
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

pub(super) fn log(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    if is_zero(&x) {
        return Err(RuntimeError::runtime("Can not take log of zero element"));
    }
    let pe = it.ff_primitive(&f)?;
    intv(log_base(it, &f, &pe, &x)?.unwrap_or_default())
}

pub(super) fn log_b(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, b) = felt_arg(a, 0)?;
    let (g, x) = felt_arg(a, 1)?;
    if id(&f) != id(&g) {
        return Err(RuntimeError::runtime("Arguments are not compatible\nArgument types given: FldFinElt, FldFinElt"));
    }
    if is_zero(&b) {
        return Err(RuntimeError::runtime("Base argument 1 must be non-zero"));
    }
    if is_zero(&x) {
        return Err(RuntimeError::runtime("Can not take log of zero element"));
    }
    match log_base(it, &f, &b, &x)? {
        Some(k) => intv(k),
        None => intv(Integer::from_i64(-1)),
    }
}

pub(super) fn zech_log(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
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

pub(super) fn sieve(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    field_arg(a, 0)?;
    none()
}
