//! Element operations: predicates, minimal polynomials, norms, traces
//! and the Frobenius, orders and roots.

use super::*;

pub(super) fn is_primitive_elt(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    boolv(finite::is_primitive(&f, &x))
}

pub(super) fn is_normal(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
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

pub(super) fn minimal_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x, e) = elt_and_sub(it, a, 1)?;
    let mp = finite::min_poly(&x, &f, &e).ok_or_else(bad)?;
    one(poly_value(it, &e, &mp)?)
}

pub(super) fn characteristic_polynomial(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x, e) = elt_and_sub(it, a, 1)?;
    let (d, m) = (degree(&e), degree(&f) / degree(&e));
    let cs = finite::conjugates(&x, d, m);
    let all: Vec<Elem> = cs.iter().cycle().take(m as usize).cloned().collect();
    let cp = finite::poly_from_roots(&all, &ff(&f).0.ctx);
    let cp: Vec<Elem> = cp.iter().map(|c| down(c, &f, &e)).collect();
    one(poly_value(it, &e, &cp)?)
}

/// The norm of `x` from `f` to its subfield `e`, in `e`. To the prime field
/// FLINT's norm (a resultant) is much faster than the power.
fn norm_to(f: &Rc<Struct>, x: &Elem, e: &Rc<Struct>) -> RResult<Elem> {
    if degree(e) == 1 && degree(f) > 1 {
        return Ok(Elem::from_integer(&ff(e).0.ctx, &x.fq_norm()?)?);
    }
    let (q, n) = (ff(e).1.order(), degree(f) / degree(e));
    let one_ = Integer::one();
    let y = x.pow(&(&q.pow(n) - &one_).divexact(&(&q - &one_)))?;
    Ok(down(&y, f, e))
}

/// The trace of `x` from `f` to its subfield `e`, in `e`: to the prime
/// field FLINT's, otherwise the sum of the conjugates.
fn trace_to(f: &Rc<Struct>, x: &Elem, e: &Rc<Struct>) -> RResult<Elem> {
    if degree(e) == 1 && degree(f) > 1 {
        return Ok(Elem::from_integer(&ff(e).0.ctx, &x.fq_trace()?)?);
    }
    let (d, n) = (degree(e), degree(f) / degree(e));
    let mut acc = x.clone();
    let mut c = x.clone();
    for _ in 1..n {
        c = c.fq_frobenius(d as i64)?;
        acc = acc.add(&c)?;
    }
    Ok(down(&acc, f, e))
}

pub(super) fn norm(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x, e) = elt_and_sub(it, a, 1)?;
    one(make_elt(&e, norm_to(&f, &x, &e)?))
}

pub(super) fn trace(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x, e) = elt_and_sub(it, a, 1)?;
    one(make_elt(&e, trace_to(&f, &x, &e)?))
}

pub(super) fn absolute_norm(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    let e = prime_of(it, &f)?;
    one(make_elt(&e, norm_to(&f, &x, &e)?))
}

pub(super) fn absolute_trace(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
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

pub(super) fn frobenius(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
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

pub(super) fn norm_equation(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
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
pub(super) fn hilbert90(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
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
pub(super) fn additive_hilbert90(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
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

pub(super) fn factored_order(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
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
    let is_power = match g.to_u64() {
        Some(1) => true,
        Some(2) => is_square_elem(f, x)?,
        _ => x.pow(&q1.divexact(&g))?.is_one() == Truth::True,
    };
    if !is_power {
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
    let mut c = match ff(f).1.cache.non_square.get() {
        Some(c) => c.clone(),
        None => {
            let c = least_non_square(f).pow(&q)?;
            ff(f).1.cache.non_square.get_or_init(|| c).clone()
        }
    };
    let mut m = s;
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

/// Whether x is a square: always in characteristic 2, and otherwise when its
/// norm to the prime field is one (the norm maps the squares onto the
/// squares), which is much faster than a power.
fn is_square_elem(f: &Rc<Struct>, x: &Elem) -> RResult<bool> {
    let p = &ff(f).1.p;
    if is_zero(x) || *p == Integer::from_u64(2) {
        return Ok(true);
    }
    if let (Some(k), Some(_)) = (x.zech_log(), Elem::zech_order(x.ctx())) {
        return Ok(k % 2 == 0);
    }
    let n = if degree(f) == 1 { x.to_integer()? } else { x.fq_norm()? };
    Ok(n.kronecker(p) == 1)
}

pub(super) fn is_square(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    if !is_square_elem(&f, &x)? {
        return Ok(vals![Value::Bool(false), Value::Undef]);
    }
    // The root only when it is asked for (0 asks for every result).
    if a.nresults == 1 {
        return boolv(true);
    }
    match nth_roots(it, &f, &x, &Integer::from_u64(2), false)?.into_iter().next() {
        Some(y) => Ok(vals![Value::Bool(true), make_elt(&f, y)]),
        None => Ok(vals![Value::Bool(false), Value::Undef]),
    }
}

pub(super) fn sqrt(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    match nth_roots(it, &f, &x, &Integer::from_u64(2), false)?.into_iter().next() {
        Some(y) => one(make_elt(&f, y)),
        None => Err(RuntimeError::runtime("Argument has no square root")),
    }
}

pub(super) fn root(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
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

pub(super) fn is_power(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
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

pub(super) fn all_roots(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    let n = a.int_ge(1, 1)?.clone();
    let rs = nth_roots(it, &f, &x, &n, true)?;
    one(elt_seq(&f, rs))
}
