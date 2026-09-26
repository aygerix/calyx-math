//! Finite fields: fast coordinates of elements and Zech logarithms, and
//! irreducibility and factorisation of polynomials over finite fields
//! (through `upoly`).

use std::rc::Rc;

use flint3_sys as sys;

use crate::Integer;
use crate::gr::{Ctx, CtxKind, Elem, GrResult};

/// The coefficients of an `nmod_poly`, padded to `degree`.
fn nmod_words(a: &sys::nmod_poly_struct, degree: usize) -> Vec<u64> {
    (0..degree).map(|i| if (i as i64) < a.length as i64 { (unsafe { *a.coeffs.add(i) }) as u64 } else { 0 }).collect()
}

/// The FLINT context behind a `gr` finite field context.
fn fq_ctx_ptr<T>(ctx: &Ctx) -> *const T {
    unsafe { *((*ctx.ptr()).data.as_ptr() as *const *const T) }
}

impl Elem {
    /// The coordinates of an element of a finite field of word-sized
    /// characteristic in the power basis of its generator (constant term
    /// first, padded to the degree); the residue of a prime field element.
    pub fn fq_coords_u64(&self) -> Vec<u64> {
        match *self.ctx().kind() {
            CtxKind::Nmod(_) => vec![self.to_word().unwrap_or(0)],
            CtxKind::FqNmod { degree, .. } => {
                nmod_words(unsafe { &*(self.as_ptr() as *const sys::nmod_poly_struct) }, degree as usize)
            }
            CtxKind::FqZech { degree, .. } => {
                let zctx = fq_ctx_ptr::<sys::fq_zech_ctx_struct>(self.ctx());
                let nctx = unsafe { (*zctx).fq_nmod_ctx };
                let mut a = sys::nmod_poly_struct::default();
                unsafe {
                    sys::fq_nmod_init(&mut a, nctx);
                    sys::fq_zech_get_fq_nmod(&mut a, self.as_ptr() as *const sys::fq_zech_struct, zctx);
                }
                let out = nmod_words(&a, degree as usize);
                unsafe { sys::fq_nmod_clear(&mut a, nctx) };
                out
            }
            _ => self.fq_coords().iter().map(|c| c.to_u64().unwrap_or(0)).collect(),
        }
    }

    /// The element of a finite field of word-sized characteristic with the
    /// given coordinates (each below p; missing ones are zero).
    pub fn fq_from_coords_u64(ctx: &Rc<Ctx>, coords: &[u64]) -> Elem {
        let mut e = Elem::zero(ctx);
        match *ctx.kind() {
            CtxKind::Nmod(_) => return Elem::from_word(ctx, coords.first().copied().unwrap_or(0)),
            CtxKind::FqNmod { degree, .. } => {
                let a = e.as_mut_ptr() as *mut sys::nmod_poly_struct;
                for (i, &c) in coords.iter().enumerate().take(degree as usize).rev() {
                    if c != 0 {
                        unsafe { sys::nmod_poly_set_coeff_ui(a, i as sys::slong, c as sys::ulong) };
                    }
                }
            }
            CtxKind::FqZech { degree, .. } => {
                let zctx = fq_ctx_ptr::<sys::fq_zech_ctx_struct>(ctx);
                let nctx = unsafe { (*zctx).fq_nmod_ctx };
                let mut a = sys::nmod_poly_struct::default();
                unsafe {
                    sys::fq_nmod_init(&mut a, nctx);
                    for (i, &c) in coords.iter().enumerate().take(degree as usize).rev() {
                        if c != 0 {
                            sys::nmod_poly_set_coeff_ui(&mut a, i as sys::slong, c as sys::ulong);
                        }
                    }
                    sys::fq_zech_set_fq_nmod(e.as_mut_ptr() as *mut sys::fq_zech_struct, &a, zctx);
                    sys::fq_nmod_clear(&mut a, nctx);
                }
            }
            _ => {
                let cs: Vec<Integer> = coords.iter().map(|&c| Integer::from_u64(c)).collect();
                return Elem::fq_from_coords(ctx, &cs).expect("coordinates of a finite field element");
            }
        }
        e
    }

    /// The element `g^k` of a field with Zech logarithms, where g is its
    /// generator (`k < q - 1`).
    pub fn fq_from_zech_log(ctx: &Rc<Ctx>, k: u64) -> Option<Elem> {
        let CtxKind::FqZech { .. } = ctx.kind() else { return None };
        let mut e = Elem::zero(ctx);
        unsafe { (*(e.as_mut_ptr() as *mut sys::fq_zech_struct)).value = k as sys::ulong };
        Some(e)
    }

    /// The number q - 1 for a field with Zech logarithms.
    pub fn zech_order(ctx: &Ctx) -> Option<u64> {
        match ctx.kind() {
            CtxKind::FqZech { .. } => Some(unsafe { (*fq_ctx_ptr::<sys::fq_zech_ctx_struct>(ctx)).qm1 } as u64),
            _ => None,
        }
    }

    /// Whether a polynomial over a finite field (a prime field included) is
    /// irreducible. Constants are not.
    pub fn poly_is_irreducible(&self) -> GrResult<bool> {
        crate::upoly::is_irreducible(self)
    }

    /// The factorisation of a non-zero polynomial over a finite field: its
    /// leading coefficient and its monic irreducible factors with their
    /// multiplicities, in FLINT's order.
    pub fn poly_factor(&self) -> GrResult<(Elem, Vec<(Elem, u64)>)> {
        let f = crate::upoly::factor(self)?;
        Ok((f.unit, f.factors))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gr::conway_polynomial;

    fn int(v: i64) -> Integer {
        Integer::from_i64(v)
    }

    #[test]
    fn coordinates() {
        let c = conway_polynomial(7, 4).unwrap();
        for zech in [true, false] {
            let f = Ctx::finite_field(&int(7), &c, zech).unwrap();
            let x = Elem::fq_from_coords_u64(&f, &[3, 0, 5, 1]);
            assert_eq!(x.fq_coords_u64(), vec![3, 0, 5, 1]);
            let g = f.generator().unwrap();
            let y = g.pow_i64(3).unwrap().add(&g.sqr().unwrap().mul_integer(&int(5)).unwrap()).unwrap().add(&Elem::from_i64(&f, 3).unwrap()).unwrap();
            assert!(x.equal(&y) == crate::gr::Truth::True);
        }
        let f = Ctx::finite_field(&int(7), &c, true).unwrap();
        assert_eq!(Elem::zech_order(&f), Some(2400));
        let g5 = Elem::fq_from_zech_log(&f, 5).unwrap();
        assert!(g5.equal(&f.generator().unwrap().pow_i64(5).unwrap()) == crate::gr::Truth::True);
    }

    #[test]
    fn irreducibility_and_factors() {
        // x^2 + 1 is irreducible over GF(7) and splits over GF(49).
        let fp = Ctx::residue_ring(&int(7));
        let px = Ctx::poly(&fp);
        let one = Elem::one(&fp).unwrap();
        let f = Elem::poly_from_coeffs(&px, &[one.clone(), Elem::zero(&fp), one.clone()]).unwrap();
        assert!(f.poly_is_irreducible().unwrap());
        let (lc, fs) = f.poly_factor().unwrap();
        assert!(lc.is_one() == crate::gr::Truth::True);
        assert_eq!(fs.len(), 1);
        for zech in [true, false] {
            let k = Ctx::finite_field(&int(7), &conway_polynomial(7, 2).unwrap(), zech).unwrap();
            let kx = Ctx::poly(&k);
            let o = Elem::one(&k).unwrap();
            let g = Elem::poly_from_coeffs(&kx, &[o.clone(), Elem::zero(&k), o.clone()]).unwrap();
            assert!(!g.poly_is_irreducible().unwrap());
            let (_, fs) = g.poly_factor().unwrap();
            assert_eq!(fs.iter().map(|(h, e)| (h.poly_len(), *e)).collect::<Vec<_>>(), vec![(2, 1), (2, 1)]);
        }
        // Over a prime field of multi-word characteristic.
        let p = Integer::from_i64(2).pow(89) - Integer::one();
        let fp = Ctx::residue_ring(&p);
        let px = Ctx::poly(&fp);
        let o = Elem::one(&fp).unwrap();
        let x2m1 = Elem::poly_from_coeffs(&px, &[o.neg().unwrap(), Elem::zero(&fp), o]).unwrap();
        assert!(!x2m1.poly_is_irreducible().unwrap());
        assert_eq!(x2m1.poly_factor().unwrap().1.len(), 2);
    }
}
