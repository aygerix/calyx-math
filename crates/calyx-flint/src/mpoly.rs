//! Multivariate polynomial algorithms on FLINT's specialised types.
//!
//! calyx keeps multivariate polynomials as generic `gr_mpoly`s, whose
//! arithmetic is fast, but gr_mpoly has no exact division, gcd,
//! factorization or resultants. For those, polynomials over the integers,
//! the rationals, prime residue rings and finite fields of word-sized
//! characteristic are converted to fmpz_mpoly, fmpq_mpoly, nmod_mpoly,
//! fmpz_mod_mpoly or fq_nmod_mpoly (fields with Zech logarithms or packed
//! elements go through fq_nmod). These pack exponents as gr_mpoly does for
//! the same number of variables and order, so only the coefficients need
//! converting. Other coefficient rings report `Unable`.
//!
//! FLINT's algorithms over Z/nZ assume a prime modulus (and abort on
//! non-invertible elements), so composite moduli are refused.

use std::rc::Rc;

use flint3_sys as sys;

use crate::Integer;
use crate::gr::{Ctx, CtxKind, Elem, GrError, GrResult, MonomialOrder};

/// A context of the specialised type for the polynomials of a gr_mpoly
/// context.
enum SCtx {
    Z(Box<sys::fmpz_mpoly_ctx_struct>),
    Q(Box<sys::fmpq_mpoly_ctx_struct>),
    Nmod(Box<sys::nmod_mpoly_ctx_struct>),
    FmpzMod(Box<sys::fmpz_mod_mpoly_ctx_struct>),
    /// A finite field, with the way to its elements.
    Fq(Box<sys::fq_nmod_mpoly_ctx_struct>, FqElts),
}

/// How the elements of a gr finite field become fq_nmod ones.
#[derive(Clone, Copy)]
enum FqElts {
    Nmod,
    /// Through the field's Zech logarithm context.
    Zech(*const sys::fq_zech_ctx_struct),
    /// From words (see `packed`), with the field's gr context.
    Packed(*mut sys::gr_ctx_struct),
}

struct Spec {
    ctx: Rc<Ctx>,
    c: SCtx,
}

impl Drop for Spec {
    fn drop(&mut self) {
        unsafe {
            match &mut self.c {
                SCtx::Z(c) => sys::fmpz_mpoly_ctx_clear(&mut **c),
                SCtx::Q(c) => sys::fmpq_mpoly_ctx_clear(&mut **c),
                SCtx::Nmod(c) => sys::nmod_mpoly_ctx_clear(&mut **c),
                SCtx::FmpzMod(c) => sys::fmpz_mod_mpoly_ctx_clear(&mut **c),
                SCtx::Fq(c, _) => sys::fq_nmod_mpoly_ctx_clear(&mut **c),
            }
        }
    }
}

/// A polynomial of the specialised type.
enum Raw {
    Z(sys::fmpz_mpoly_struct),
    Q(sys::fmpq_mpoly_struct),
    Nmod(sys::nmod_mpoly_struct),
    FmpzMod(sys::fmpz_mod_mpoly_struct),
    Fq(sys::fq_nmod_mpoly_struct),
}

struct Poly<'a> {
    s: &'a Spec,
    raw: Raw,
}

impl Drop for Poly<'_> {
    fn drop(&mut self) {
        unsafe {
            match (&mut self.raw, &self.s.c) {
                (Raw::Z(p), SCtx::Z(c)) => sys::fmpz_mpoly_clear(p, &**c),
                (Raw::Q(p), SCtx::Q(c)) => sys::fmpq_mpoly_clear(p, &**c),
                (Raw::Nmod(p), SCtx::Nmod(c)) => sys::nmod_mpoly_clear(p, &**c),
                (Raw::FmpzMod(p), SCtx::FmpzMod(c)) => sys::fmpz_mod_mpoly_clear(p, &**c),
                (Raw::Fq(p), SCtx::Fq(c, _)) => sys::fq_nmod_mpoly_clear(p, &**c),
                _ => unreachable!("a polynomial of another context"),
            }
        }
    }
}

fn gm(e: &Elem) -> &sys::gr_mpoly_struct {
    unsafe { &*(e.as_ptr() as *const sys::gr_mpoly_struct) }
}

/// The number of words of a packed exponent vector.
fn words(bits: sys::flint_bitcnt_t, m: &sys::mpoly_ctx_struct) -> usize {
    (if bits <= 64 { m.lut_words_per_exp[bits as usize - 1] } else { (bits / 64) as sys::slong * m.nfields }) as usize
}

impl Spec {
    fn new(ctx: &Rc<Ctx>) -> GrResult<Spec> {
        let CtxKind::MPoly { nvars, order } = *ctx.kind() else { return Err(GrError::Unable) };
        let base = ctx.base().expect("a polynomial ring");
        let ord = match order {
            MonomialOrder::Lex => sys::ordering_t_ORD_LEX,
            MonomialOrder::DegLex => sys::ordering_t_ORD_DEGLEX,
            MonomialOrder::DegRevLex => sys::ordering_t_ORD_DEGREVLEX,
        };
        let n = nvars as sys::slong;
        // A gr context starts with its data: the nmod_t, or a pointer to the
        // finite field context.
        let data = base.ptr() as *const u8;
        let c = unsafe {
            match base.kind() {
                CtxKind::Integers => {
                    let mut c = Box::new(sys::fmpz_mpoly_ctx_struct::default());
                    sys::fmpz_mpoly_ctx_init(&mut *c, n, ord);
                    SCtx::Z(c)
                }
                CtxKind::Rationals => {
                    let mut c = Box::new(sys::fmpq_mpoly_ctx_struct::default());
                    sys::fmpq_mpoly_ctx_init(&mut *c, n, ord);
                    SCtx::Q(c)
                }
                CtxKind::Nmod(m) if sys::n_is_prime(*m as sys::ulong) != 0 => {
                    let mut c = Box::new(sys::nmod_mpoly_ctx_struct::default());
                    sys::nmod_mpoly_ctx_init(&mut *c, n, ord, *m as sys::ulong);
                    SCtx::Nmod(c)
                }
                CtxKind::FmpzMod(m) if crate::upoly::fmpz_mod_is_field(base) => {
                    let mut c = Box::new(sys::fmpz_mod_mpoly_ctx_struct::default());
                    sys::fmpz_mod_mpoly_ctx_init(&mut *c, n, ord, m.raw_ptr());
                    SCtx::FmpzMod(c)
                }
                CtxKind::FqNmod { .. } => {
                    let mut c = Box::new(sys::fq_nmod_mpoly_ctx_struct::default());
                    sys::fq_nmod_mpoly_ctx_init(&mut *c, n, ord, *(data as *const *const sys::fq_nmod_ctx_struct));
                    SCtx::Fq(c, FqElts::Nmod)
                }
                CtxKind::FqZech { .. } => {
                    let z = *(data as *const *const sys::fq_zech_ctx_struct);
                    let mut c = Box::new(sys::fq_nmod_mpoly_ctx_struct::default());
                    sys::fq_nmod_mpoly_ctx_init(&mut *c, n, ord, (*z).fq_nmod_ctx);
                    SCtx::Fq(c, FqElts::Zech(z))
                }
                CtxKind::FqPacked { .. } => {
                    let mut c = Box::new(sys::fq_nmod_mpoly_ctx_struct::default());
                    sys::fq_nmod_mpoly_ctx_init(&mut *c, n, ord, crate::packed::fq_nmod_ctx(base));
                    SCtx::Fq(c, FqElts::Packed(base.ptr()))
                }
                _ => return Err(GrError::Unable),
            }
        };
        Ok(Spec { ctx: ctx.clone(), c })
    }

    fn minfo(&self) -> &sys::mpoly_ctx_struct {
        match &self.c {
            SCtx::Z(c) => &c.minfo[0],
            SCtx::Q(c) => &c.zctx[0].minfo[0],
            SCtx::Nmod(c) => &c.minfo[0],
            SCtx::FmpzMod(c) => &c.minfo[0],
            SCtx::Fq(c, _) => &c.minfo[0],
        }
    }

    fn zero(&self) -> Poly<'_> {
        let raw = unsafe {
            match &self.c {
                SCtx::Z(c) => {
                    let mut p = sys::fmpz_mpoly_struct::default();
                    sys::fmpz_mpoly_init(&mut p, &**c);
                    Raw::Z(p)
                }
                SCtx::Q(c) => {
                    let mut p = sys::fmpq_mpoly_struct::default();
                    sys::fmpq_mpoly_init(&mut p, &**c);
                    Raw::Q(p)
                }
                SCtx::Nmod(c) => {
                    let mut p = sys::nmod_mpoly_struct::default();
                    sys::nmod_mpoly_init(&mut p, &**c);
                    Raw::Nmod(p)
                }
                SCtx::FmpzMod(c) => {
                    let mut p = sys::fmpz_mod_mpoly_struct::default();
                    sys::fmpz_mod_mpoly_init(&mut p, &**c);
                    Raw::FmpzMod(p)
                }
                SCtx::Fq(c, _) => {
                    let mut p = sys::fq_nmod_mpoly_struct::default();
                    sys::fq_nmod_mpoly_init(&mut p, &**c);
                    Raw::Fq(p)
                }
            }
        };
        Poly { s: self, raw }
    }

    /// The polynomial `e` (of the gr context) in the specialised type.
    fn convert(&self, e: &Elem) -> Poly<'_> {
        let g = gm(e);
        let (n, bits) = (g.length, g.bits);
        let len = n as usize;
        let w = words(bits, self.minfo()) * len;
        let mut p = self.zero();
        unsafe {
            match (&mut p.raw, &self.c) {
                (Raw::Z(p), SCtx::Z(c)) => {
                    sys::fmpz_mpoly_fit_length_reset_bits(p, n, bits, &**c);
                    std::ptr::copy_nonoverlapping(g.exps, p.exps, w);
                    let cs = g.coeffs as *const sys::fmpz;
                    for i in 0..len {
                        sys::fmpz_set(p.coeffs.add(i), cs.add(i));
                    }
                    p.length = n;
                }
                (Raw::Q(p), SCtx::Q(c)) => {
                    // The integer polynomial times 1/L, for the least common
                    // multiple L of the denominators, made canonical.
                    let cs = g.coeffs as *const sys::fmpq;
                    let mut l = Integer::one();
                    let lp = l.raw_mut_ptr();
                    for i in 0..len {
                        sys::fmpz_lcm(lp, lp, &(*cs.add(i)).den);
                    }
                    let z = p.zpoly.as_mut_ptr();
                    sys::fmpz_mpoly_fit_length_reset_bits(z, n, bits, c.zctx.as_ptr());
                    std::ptr::copy_nonoverlapping(g.exps, (*z).exps, w);
                    let mut t = Integer::zero();
                    for i in 0..len {
                        sys::fmpz_divexact(t.raw_mut_ptr(), l.raw_ptr(), &(*cs.add(i)).den);
                        sys::fmpz_mul((*z).coeffs.add(i), &(*cs.add(i)).num, t.raw_ptr());
                    }
                    (*z).length = n;
                    sys::fmpq_set_fmpz_frac(p.content.as_mut_ptr(), Integer::one().raw_ptr(), l.raw_ptr());
                    sys::fmpq_mpoly_reduce(p, &**c);
                }
                (Raw::Nmod(p), SCtx::Nmod(c)) => {
                    sys::nmod_mpoly_fit_length_reset_bits(p, n, bits, &**c);
                    std::ptr::copy_nonoverlapping(g.exps, p.exps, w);
                    std::ptr::copy_nonoverlapping(g.coeffs as *const sys::ulong, p.coeffs, len);
                    p.length = n;
                }
                (Raw::FmpzMod(p), SCtx::FmpzMod(c)) => {
                    sys::fmpz_mod_mpoly_fit_length_reset_bits(p, n, bits, &**c);
                    std::ptr::copy_nonoverlapping(g.exps, p.exps, w);
                    let cs = g.coeffs as *const sys::fmpz;
                    for i in 0..len {
                        sys::fmpz_set(p.coeffs.add(i), cs.add(i));
                    }
                    p.length = n;
                }
                (Raw::Fq(p), SCtx::Fq(c, elts)) => {
                    let fq = c.fqctx.as_ptr();
                    let d = sys::fq_nmod_ctx_degree(fq) as usize;
                    sys::fq_nmod_mpoly_fit_length_reset_bits(p, n, bits, &**c);
                    std::ptr::copy_nonoverlapping(g.exps, p.exps, w);
                    match elts {
                        FqElts::Nmod => {
                            let cs = g.coeffs as *const sys::nmod_poly_struct;
                            for i in 0..len {
                                sys::n_fq_set_fq_nmod(p.coeffs.add(d * i), cs.add(i), fq);
                            }
                        }
                        FqElts::Zech(z) => {
                            let cs = g.coeffs as *const sys::fq_zech_struct;
                            let mut t = sys::nmod_poly_struct::default();
                            sys::fq_nmod_init(&mut t, fq);
                            for i in 0..len {
                                sys::fq_zech_get_fq_nmod(&mut t, cs.add(i), *z);
                                sys::n_fq_set_fq_nmod(p.coeffs.add(d * i), &t, fq);
                            }
                            sys::fq_nmod_clear(&mut t, fq);
                        }
                        FqElts::Packed(k) => {
                            let size = (**k).sizeof_elem as usize;
                            for i in 0..len {
                                crate::packed::get_n_fq(p.coeffs.add(d * i), g.coeffs.cast::<u8>().add(i * size).cast(), *k);
                            }
                        }
                    }
                    p.length = n;
                }
                _ => unreachable!("a polynomial of another context"),
            }
        }
        p
    }

    /// The polynomial `p` as an element of the gr context.
    fn to_gr(&self, p: &Poly) -> Elem {
        let mut e = Elem::new(&self.ctx);
        let g = e.as_mut_ptr() as *mut sys::gr_mpoly_struct;
        let ctx = self.ctx.ptr();
        let m = self.minfo();
        unsafe {
            // Room for n terms with the exponents of `exps`.
            let fill = |exps: *const sys::ulong, n: sys::slong, bits: sys::flint_bitcnt_t| {
                sys::gr_mpoly_fit_length_reset_bits(g, n, bits, ctx);
                std::ptr::copy_nonoverlapping(exps, (*g).exps, words(bits, m) * n as usize);
                n as usize
            };
            let n = match (&p.raw, &self.c) {
                (Raw::Z(p), _) => {
                    let n = fill(p.exps, p.length, p.bits);
                    let cs = (*g).coeffs as *mut sys::fmpz;
                    for i in 0..n {
                        sys::fmpz_set(cs.add(i), p.coeffs.add(i));
                    }
                    n
                }
                (Raw::Q(p), _) => {
                    let z = &p.zpoly[0];
                    let n = fill(z.exps, z.length, z.bits);
                    let cs = (*g).coeffs as *mut sys::fmpq;
                    for i in 0..n {
                        sys::fmpq_mul_fmpz(cs.add(i), p.content.as_ptr(), z.coeffs.add(i));
                    }
                    n
                }
                (Raw::Nmod(p), _) => {
                    let n = fill(p.exps, p.length, p.bits);
                    std::ptr::copy_nonoverlapping(p.coeffs, (*g).coeffs as *mut sys::ulong, n);
                    n
                }
                (Raw::FmpzMod(p), _) => {
                    let n = fill(p.exps, p.length, p.bits);
                    let cs = (*g).coeffs as *mut sys::fmpz;
                    for i in 0..n {
                        sys::fmpz_set(cs.add(i), p.coeffs.add(i));
                    }
                    n
                }
                (Raw::Fq(p), SCtx::Fq(c, elts)) => {
                    let fq = c.fqctx.as_ptr();
                    let d = sys::fq_nmod_ctx_degree(fq) as usize;
                    let n = fill(p.exps, p.length, p.bits);
                    match elts {
                        FqElts::Nmod => {
                            let cs = (*g).coeffs as *mut sys::nmod_poly_struct;
                            for i in 0..n {
                                sys::n_fq_get_fq_nmod(cs.add(i), p.coeffs.add(d * i), fq);
                            }
                        }
                        FqElts::Zech(z) => {
                            let cs = (*g).coeffs as *mut sys::fq_zech_struct;
                            let mut t = sys::nmod_poly_struct::default();
                            sys::fq_nmod_init(&mut t, fq);
                            for i in 0..n {
                                sys::n_fq_get_fq_nmod(&mut t, p.coeffs.add(d * i), fq);
                                sys::fq_zech_set_fq_nmod(cs.add(i), &t, *z);
                            }
                            sys::fq_nmod_clear(&mut t, fq);
                        }
                        FqElts::Packed(k) => {
                            let size = (**k).sizeof_elem as usize;
                            for i in 0..n {
                                crate::packed::set_n_fq((*g).coeffs.cast::<u8>().add(i * size).cast(), p.coeffs.add(d * i), *k);
                            }
                        }
                    }
                    n
                }
                _ => unreachable!("a polynomial of another context"),
            };
            sys::_gr_mpoly_set_length(g, n as sys::slong, ctx);
        }
        e
    }

    /// A constant of the specialised type (from a factorization) as an
    /// element of the coefficient ring.
    fn constant(&self, c: *const std::ffi::c_void) -> Elem {
        let base = self.ctx.base().expect("a polynomial ring");
        let mut e = Elem::new(base);
        unsafe {
            match &self.c {
                SCtx::Z(_) | SCtx::FmpzMod(_) => sys::fmpz_set(e.as_mut_ptr().cast(), c.cast()),
                SCtx::Q(_) => sys::fmpq_set(e.as_mut_ptr().cast(), c.cast()),
                SCtx::Nmod(_) => *(e.as_mut_ptr() as *mut sys::ulong) = *(c as *const sys::ulong),
                SCtx::Fq(q, FqElts::Nmod) => sys::fq_nmod_set(e.as_mut_ptr().cast(), c.cast(), q.fqctx.as_ptr()),
                SCtx::Fq(_, FqElts::Zech(z)) => sys::fq_zech_set_fq_nmod(e.as_mut_ptr().cast(), c.cast(), *z),
                SCtx::Fq(_, FqElts::Packed(k)) => crate::packed::set_fq_nmod(e.as_mut_ptr(), c, *k),
            }
        }
        e
    }
}

/// `a / b` if b divides a exactly (over the integers: with an integral
/// quotient), `None` otherwise. `b` must be non-zero.
pub fn divides(a: &Elem, b: &Elem) -> GrResult<Option<Elem>> {
    let s = Spec::new(a.ctx())?;
    let (x, y, mut q) = (s.convert(a), s.convert(b), s.zero());
    let ok = unsafe {
        match (&mut q.raw, &x.raw, &y.raw, &s.c) {
            (Raw::Z(q), Raw::Z(a), Raw::Z(b), SCtx::Z(c)) => sys::fmpz_mpoly_divides(q, a, b, &**c),
            (Raw::Q(q), Raw::Q(a), Raw::Q(b), SCtx::Q(c)) => sys::fmpq_mpoly_divides(q, a, b, &**c),
            (Raw::Nmod(q), Raw::Nmod(a), Raw::Nmod(b), SCtx::Nmod(c)) => sys::nmod_mpoly_divides(q, a, b, &**c),
            (Raw::FmpzMod(q), Raw::FmpzMod(a), Raw::FmpzMod(b), SCtx::FmpzMod(c)) => sys::fmpz_mod_mpoly_divides(q, a, b, &**c),
            (Raw::Fq(q), Raw::Fq(a), Raw::Fq(b), SCtx::Fq(c, _)) => sys::fq_nmod_mpoly_divides(q, a, b, &**c),
            _ => unreachable!("polynomials of another context"),
        }
    };
    Ok((ok != 0).then(|| s.to_gr(&q)))
}

/// The greatest common divisor of `a` and `b`: with positive leading
/// coefficient over the integers, monic over fields (0 if both are 0).
pub fn gcd(a: &Elem, b: &Elem) -> GrResult<Elem> {
    let s = Spec::new(a.ctx())?;
    let (x, y, mut g) = (s.convert(a), s.convert(b), s.zero());
    let ok = unsafe {
        match (&mut g.raw, &x.raw, &y.raw, &s.c) {
            (Raw::Z(g), Raw::Z(a), Raw::Z(b), SCtx::Z(c)) => sys::fmpz_mpoly_gcd(g, a, b, &**c),
            (Raw::Q(g), Raw::Q(a), Raw::Q(b), SCtx::Q(c)) => sys::fmpq_mpoly_gcd(g, a, b, &**c),
            (Raw::Nmod(g), Raw::Nmod(a), Raw::Nmod(b), SCtx::Nmod(c)) => sys::nmod_mpoly_gcd(g, a, b, &**c),
            (Raw::FmpzMod(g), Raw::FmpzMod(a), Raw::FmpzMod(b), SCtx::FmpzMod(c)) => sys::fmpz_mod_mpoly_gcd(g, a, b, &**c),
            (Raw::Fq(g), Raw::Fq(a), Raw::Fq(b), SCtx::Fq(c, _)) => sys::fq_nmod_mpoly_gcd(g, a, b, &**c),
            _ => unreachable!("polynomials of another context"),
        }
    };
    if ok == 0 {
        return Err(GrError::Unable);
    }
    Ok(s.to_gr(&g))
}

/// The resultant of `a` and `b` with respect to variable `var` (from 0).
pub fn resultant(a: &Elem, b: &Elem, var: usize) -> GrResult<Elem> {
    let s = Spec::new(a.ctx())?;
    let (x, y, mut r) = (s.convert(a), s.convert(b), s.zero());
    let v = var as sys::slong;
    let ok = unsafe {
        match (&mut r.raw, &x.raw, &y.raw, &s.c) {
            (Raw::Z(r), Raw::Z(a), Raw::Z(b), SCtx::Z(c)) => sys::fmpz_mpoly_resultant(r, a, b, v, &**c),
            (Raw::Q(r), Raw::Q(a), Raw::Q(b), SCtx::Q(c)) => sys::fmpq_mpoly_resultant(r, a, b, v, &**c),
            (Raw::Nmod(r), Raw::Nmod(a), Raw::Nmod(b), SCtx::Nmod(c)) => sys::nmod_mpoly_resultant(r, a, b, v, &**c),
            (Raw::FmpzMod(r), Raw::FmpzMod(a), Raw::FmpzMod(b), SCtx::FmpzMod(c)) => sys::fmpz_mod_mpoly_resultant(r, a, b, v, &**c),
            (Raw::Fq(r), Raw::Fq(a), Raw::Fq(b), SCtx::Fq(c, _)) => sys::fq_nmod_mpoly_resultant(r, a, b, v, &**c),
            _ => unreachable!("polynomials of another context"),
        }
    };
    if ok == 0 {
        return Err(GrError::Unable);
    }
    Ok(s.to_gr(&r))
}

/// The discriminant of `a` with respect to variable `var` (from 0).
pub fn discriminant(a: &Elem, var: usize) -> GrResult<Elem> {
    let s = Spec::new(a.ctx())?;
    let (x, mut r) = (s.convert(a), s.zero());
    let v = var as sys::slong;
    let ok = unsafe {
        match (&mut r.raw, &x.raw, &s.c) {
            (Raw::Z(r), Raw::Z(a), SCtx::Z(c)) => sys::fmpz_mpoly_discriminant(r, a, v, &**c),
            (Raw::Q(r), Raw::Q(a), SCtx::Q(c)) => sys::fmpq_mpoly_discriminant(r, a, v, &**c),
            (Raw::Nmod(r), Raw::Nmod(a), SCtx::Nmod(c)) => sys::nmod_mpoly_discriminant(r, a, v, &**c),
            (Raw::FmpzMod(r), Raw::FmpzMod(a), SCtx::FmpzMod(c)) => sys::fmpz_mod_mpoly_discriminant(r, a, v, &**c),
            (Raw::Fq(r), Raw::Fq(a), SCtx::Fq(c, _)) => sys::fq_nmod_mpoly_discriminant(r, a, v, &**c),
            _ => unreachable!("polynomials of another context"),
        }
    };
    if ok == 0 {
        return Err(GrError::Unable);
    }
    Ok(s.to_gr(&r))
}

/// The factorization of a non-zero polynomial into irreducibles (with
/// `squarefree`, into squarefree coprime factors): a constant of the
/// coefficient ring and the factors with their multiplicities. Over the
/// integers the factors are primitive with positive leading coefficient and
/// the constant is the signed content; over fields they are monic.
pub fn factor(a: &Elem, squarefree: bool) -> GrResult<(Elem, Vec<(Elem, u64)>)> {
    let s = Spec::new(a.ctx())?;
    let x = s.convert(a);
    let mut out = Vec::new();
    // Run `factor` into a factorization structure `f`, then read the
    // constant (`get_constant` writes it to a temporary) and the factors.
    macro_rules! run {
        ($f:ty, $init:ident, $clear:ident, $fac:ident, $sqf:ident, $len:ident, $base:ident, $exp:ident, $p:expr, $c:expr, $raw:ident, $konst:expr) => {{
            let mut f = <$f>::default();
            sys::$init(&mut f, $c);
            let ok = if squarefree { sys::$sqf(&mut f, $p, $c) } else { sys::$fac(&mut f, $p, $c) };
            if ok == 0 {
                sys::$clear(&mut f, $c);
                return Err(GrError::Unable);
            }
            let konst = $konst(&f);
            for i in 0..sys::$len(&f, $c) {
                let mut b = s.zero();
                let Raw::$raw(bp) = &mut b.raw else { unreachable!() };
                sys::$base(bp, &f, i, $c);
                out.push((s.to_gr(&b), sys::$exp(&mut f, i, $c) as u64));
            }
            sys::$clear(&mut f, $c);
            konst
        }};
    }
    let konst = unsafe {
        match (&x.raw, &s.c) {
            (Raw::Z(p), SCtx::Z(c)) => run!(sys::fmpz_mpoly_factor_struct, fmpz_mpoly_factor_init, fmpz_mpoly_factor_clear, fmpz_mpoly_factor,
                fmpz_mpoly_factor_squarefree, fmpz_mpoly_factor_length, fmpz_mpoly_factor_get_base, fmpz_mpoly_factor_get_exp_si, p, &**c, Z,
                |f: &sys::fmpz_mpoly_factor_struct| {
                    let mut k = Integer::zero();
                    sys::fmpz_mpoly_factor_get_constant_fmpz(k.raw_mut_ptr(), f, &**c);
                    s.constant(k.raw_ptr().cast())
                }),
            (Raw::Q(p), SCtx::Q(c)) => run!(sys::fmpq_mpoly_factor_struct, fmpq_mpoly_factor_init, fmpq_mpoly_factor_clear, fmpq_mpoly_factor,
                fmpq_mpoly_factor_squarefree, fmpq_mpoly_factor_length, fmpq_mpoly_factor_get_base, fmpq_mpoly_factor_get_exp_si, p, &**c, Q,
                |f: &sys::fmpq_mpoly_factor_struct| s.constant(f.constant.as_ptr().cast())),
            (Raw::Nmod(p), SCtx::Nmod(c)) => run!(sys::nmod_mpoly_factor_struct, nmod_mpoly_factor_init, nmod_mpoly_factor_clear, nmod_mpoly_factor,
                nmod_mpoly_factor_squarefree, nmod_mpoly_factor_length, nmod_mpoly_factor_get_base, nmod_mpoly_factor_get_exp_si, p, &**c, Nmod,
                |f: &sys::nmod_mpoly_factor_struct| s.constant((&f.constant as *const sys::ulong).cast())),
            (Raw::FmpzMod(p), SCtx::FmpzMod(c)) => run!(sys::fmpz_mod_mpoly_factor_struct, fmpz_mod_mpoly_factor_init, fmpz_mod_mpoly_factor_clear,
                fmpz_mod_mpoly_factor, fmpz_mod_mpoly_factor_squarefree, fmpz_mod_mpoly_factor_length, fmpz_mod_mpoly_factor_get_base,
                fmpz_mod_mpoly_factor_get_exp_si, p, &**c, FmpzMod, |f: &sys::fmpz_mod_mpoly_factor_struct| s.constant(f.constant.as_ptr().cast())),
            (Raw::Fq(p), SCtx::Fq(c, _)) => run!(sys::fq_nmod_mpoly_factor_struct, fq_nmod_mpoly_factor_init, fq_nmod_mpoly_factor_clear,
                fq_nmod_mpoly_factor, fq_nmod_mpoly_factor_squarefree, fq_nmod_mpoly_factor_length, fq_nmod_mpoly_factor_get_base,
                fq_nmod_mpoly_factor_get_exp_si, p, &**c, Fq, |f: &sys::fq_nmod_mpoly_factor_struct| s.constant(f.constant.as_ptr().cast())),
            _ => unreachable!("a polynomial of another context"),
        }
    };
    Ok((konst, out))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Rational;
    use crate::gr::Truth;

    /// The ring in two variables x, y (lex) over `base`.
    fn ring(base: &Rc<Ctx>) -> Rc<Ctx> {
        Ctx::mpoly(base, 2, MonomialOrder::Lex)
    }

    /// The polynomial with integer coefficients and exponents `terms` in
    /// `ctx`; elements that meet in one operation must share their context.
    fn mp(ctx: &Rc<Ctx>, terms: &[(i64, [u64; 2])]) -> Elem {
        let base = ctx.base().unwrap();
        let ts: Vec<(Elem, Vec<u64>)> = terms.iter().map(|(c, e)| (Elem::from_integer(base, &Integer::from_i64(*c)).unwrap(), e.to_vec())).collect();
        Elem::mpoly_from_terms(ctx, &ts).unwrap()
    }

    fn same(a: &Elem, b: &Elem) -> bool {
        a.equal(b) == Truth::True
    }

    #[test]
    fn integer_division_gcd_resultant() {
        let zz = ring(&Ctx::integers());
        let s = mp(&zz, &[(1, [1, 0]), (1, [0, 1])]); // x + y
        let t = mp(&zz, &[(1, [1, 0]), (-2, [0, 1]), (1, [0, 0])]); // x - 2y + 1
        let st = s.mul(&t).unwrap();
        assert!(same(&divides(&st, &s).unwrap().unwrap(), &t));
        assert!(divides(&mp(&zz, &[(1, [2, 0])]), &mp(&zz, &[(1, [0, 1])])).unwrap().is_none());
        // 2x divides 4x^2 over Z, 2x does not divide x over Z.
        assert!(divides(&mp(&zz, &[(1, [1, 0])]), &mp(&zz, &[(2, [1, 0])])).unwrap().is_none());
        let u = mp(&zz, &[(1, [1, 0]), (3, [0, 0])]); // x + 3
        assert!(same(&gcd(&st, &s.mul(&u).unwrap()).unwrap(), &s));
        // Res_x(x^2 + y^2 - 1, x - y) = 2y^2 - 1.
        let f = mp(&zz, &[(1, [2, 0]), (1, [0, 2]), (-1, [0, 0])]);
        let g = mp(&zz, &[(1, [1, 0]), (-1, [0, 1])]);
        assert!(same(&resultant(&f, &g, 0).unwrap(), &mp(&zz, &[(2, [0, 2]), (-1, [0, 0])])));
        // Disc_x(x^2 + y) = -4y.
        assert!(same(&discriminant(&mp(&zz, &[(1, [2, 0]), (1, [0, 1])]), 0).unwrap(), &mp(&zz, &[(-4, [0, 1])])));
    }

    #[test]
    fn integer_factorization() {
        let zz = ring(&Ctx::integers());
        let s = mp(&zz, &[(1, [1, 0]), (1, [0, 1])]);
        let d = mp(&zz, &[(1, [1, 0]), (-1, [0, 1])]);
        let f = s.mul(&s).unwrap().mul(&d).unwrap().mul(&mp(&zz, &[(-6, [0, 0])])).unwrap();
        let (k, fs) = factor(&f, false).unwrap();
        assert_eq!(k.to_integer().unwrap(), Integer::from_i64(-6));
        assert_eq!(fs.len(), 2);
        assert!(fs.iter().any(|(p, e)| *e == 2 && same(p, &s)));
        assert!(fs.iter().any(|(p, e)| *e == 1 && same(p, &d)));
        let (_, sq) = factor(&f, true).unwrap();
        assert!(sq.iter().all(|(_, e)| *e <= 2));
    }

    #[test]
    fn rationals() {
        let qq = Ctx::rationals();
        let ctx = Ctx::mpoly(&qq, 2, MonomialOrder::Lex);
        let half = Elem::from_rational(&qq, &Rational::new(&Integer::from_i64(1), &Integer::from_i64(2)).unwrap()).unwrap();
        let one = Elem::from_integer(&qq, &Integer::from_i64(1)).unwrap();
        let a = Elem::mpoly_from_terms(&ctx, &[(half.clone(), vec![1, 0]), (one.clone(), vec![0, 1])]).unwrap(); // x/2 + y
        let a2 = a.mul(&a).unwrap();
        assert!(same(&divides(&a2, &a).unwrap().unwrap(), &a));
        // The gcd is monic: x + 2y.
        let two = Elem::from_integer(&qq, &Integer::from_i64(2)).unwrap();
        let b = Elem::mpoly_from_terms(&ctx, &[(one.clone(), vec![1, 0]), (two, vec![0, 1])]).unwrap();
        let x1 = Elem::mpoly_from_terms(&ctx, &[(one.clone(), vec![1, 0]), (one.clone(), vec![0, 0])]).unwrap();
        assert!(same(&gcd(&a2.mul(&x1).unwrap(), &a).unwrap(), &b));
        let (k, fs) = factor(&a2, false).unwrap();
        assert_eq!(k.to_rational().unwrap(), Rational::new(&Integer::from_i64(1), &Integer::from_i64(4)).unwrap());
        assert!(fs.len() == 1 && fs[0].1 == 2 && same(&fs[0].0, &b));
        // Zero converts both ways.
        let z = Elem::new(&ctx);
        assert!(same(&gcd(&z, &z).unwrap(), &z));
    }

    #[test]
    fn finite_fields() {
        let f5 = ring(&Ctx::residue_ring(&Integer::from_i64(5)));
        let f = mp(&f5, &[(1, [2, 0]), (-1, [0, 2])]); // x^2 - y^2
        let (k, fs) = factor(&f, false).unwrap();
        assert_eq!(k.to_integer().unwrap(), Integer::from_i64(1));
        assert!(fs.iter().any(|(p, _)| same(p, &mp(&f5, &[(1, [1, 0]), (4, [0, 1])]))));
        // GF(9) = GF(3)[a]/(a^2 + 2a + 2), with Zech logarithms and without.
        let m: Vec<Integer> = [2, 2, 1].iter().map(|&c| Integer::from_i64(c)).collect();
        for zech in [true, false] {
            let f9 = Ctx::finite_field(&Integer::from_i64(3), &m, zech).unwrap();
            let a = f9.generator().unwrap();
            let ctx = Ctx::mpoly(&f9, 2, MonomialOrder::Lex);
            let one = Elem::from_integer(&f9, &Integer::from_i64(1)).unwrap();
            let s = Elem::mpoly_from_terms(&ctx, &[(one.clone(), vec![1, 0]), (a.clone(), vec![0, 1])]).unwrap(); // x + a*y
            let t = Elem::mpoly_from_terms(&ctx, &[(a.clone(), vec![1, 1]), (one.clone(), vec![0, 0])]).unwrap(); // a*x*y + 1
            let st = s.mul(&t).unwrap();
            assert!(same(&divides(&st, &s).unwrap().unwrap(), &t));
            let (k, fs) = factor(&st, false).unwrap();
            assert!(same(&k, &a));
            assert_eq!(fs.len(), 2);
        }
        // Composite moduli are refused.
        let z6 = ring(&Ctx::residue_ring(&Integer::from_i64(6)));
        assert!(matches!(gcd(&mp(&z6, &[(1, [1, 0])]), &mp(&z6, &[(1, [0, 1])])), Err(GrError::Unable)));
    }
}
