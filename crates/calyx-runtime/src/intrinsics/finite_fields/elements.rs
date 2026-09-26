//! The creation of elements, special elements and sequence conversions.

use super::*;

/// A random element of the field.
/// `Random(F)`: by coordinates, without listing F.
pub(super) fn random(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    one(make_elt(&f, random_elem(it, &f)))
}

pub(super) fn random_elem(it: &mut Interp, st: &Struct) -> Elem {
    let (r, f) = ff(st);
    let cs: Vec<Integer> = (0..f.degree).map(|_| it.rng.below(&f.p)).collect();
    Coords::B(cs).to_elem(&r.ctx)
}

// ----- special elements ------------------------------------------------------------

/// `Generator(F, E)`: `F.1` if it generates F over E, else the primitive
/// element.
pub(super) fn gen_over(it: &mut Interp, f: &Rc<Struct>, e: &Rc<Struct>) -> RResult<Elem> {
    let (r, fd) = ff(f);
    let g = finite::gen1(r, fd);
    let m = fd.degree / degree(e);
    if finite::conjugates(&g, degree(e), m).len() as u64 == m {
        return Ok(g);
    }
    it.ff_primitive(f)
}

pub(super) fn generator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    let (r, fd) = ff(&f);
    one(make_elt(&f, finite::gen1(r, fd)))
}

pub(super) fn generator_over(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, e) = (field_arg(a, 0)?, field_arg(a, 1)?);
    sub_image(&e, &f, NOT_SUB_OF)?;
    one(make_elt(&f, gen_over(it, &f, &e)?))
}

pub(super) fn primitive_element(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    one(make_elt(&f, it.ff_primitive(&f)?))
}

pub(super) fn set_primitive_element(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
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
    fd.cache.logs.borrow_mut().clear();
    none()
}

/// Whether x, x^q, ..., x^(q^(m-1)) is a basis of f over its subfield e
/// (with q = #e).
pub(super) fn is_normal_over(f: &Rc<Struct>, x: &Elem, e: &Rc<Struct>, ei: &Elem) -> bool {
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

pub(super) fn normal_element(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = field_arg(a, 0)?;
    let g = ground_of(it, &f)?;
    normal_element_over(&f, &g)
}

pub(super) fn normal_element_e(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, e) = (field_arg(a, 0)?, field_arg(a, 1)?);
    normal_element_over(&f, &e)
}

// ----- sequences ---------------------------------------------------------------------

/// The coordinates of `x` over the subfield `e` of `f` in the power basis of
/// `g` (which generates f over e), in the context of `e`; `ei` is the image
/// of the generator of the context of `e`.
pub(super) fn coords_over(f: &Rc<Struct>, x: &Elem, e: &Rc<Struct>, ei: &Elem, g: &Elem) -> Vec<Elem> {
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

pub(super) fn elt_seq(e: &Rc<Struct>, cs: Vec<Elem>) -> Value {
    Value::seq(Some(Value::Struct(e.clone())), cs.into_iter().map(|c| make_elt(e, c)).collect())
}

pub(super) fn eltseq(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    let g = ground_of(it, &f)?;
    let cs = eltseq_over(it, &f, &x, &g)?;
    one(elt_seq(&g, cs))
}

pub(super) fn eltseq_e(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, x) = felt_arg(a, 0)?;
    let e = field_arg(a, 1)?;
    let cs = eltseq_over(it, &f, &x, &e)?;
    one(elt_seq(&e, cs))
}

pub(super) fn seqelt(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
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
