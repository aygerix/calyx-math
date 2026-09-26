//! Dense matrices over FLINT's generic rings (`gr_mat`).
//!
//! A [`Mat`] keeps its entries as elements of a [`Ctx`], row after row.
//! FLINT's own matrix types (`fmpz_mat`, `fmpq_mat`, `nmod_mat`,
//! `fq_zech_mat`, ...) have the same layout, and the generic functions
//! hand the work to them where the ring's context says so: a product of
//! matrices over the integers is `fmpz_mat_mul`, one over `Z/nZ` is
//! `nmod_mat_mul`.

use std::ffi::c_void;
use std::rc::Rc;

use flint3_sys as sys;

use crate::gr::{Ctx, CtxKind, Elem, GrResult, Truth, check};
use crate::{Integer, Rational};

pub struct Mat {
    ctx: Rc<Ctx>,
    raw: sys::gr_mat_struct,
}

impl Drop for Mat {
    fn drop(&mut self) {
        unsafe { sys::gr_mat_clear(&mut self.raw, self.ctx.ptr()) };
    }
}

impl Clone for Mat {
    fn clone(&self) -> Mat {
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        let st = unsafe { sys::gr_mat_set(&mut m.raw, &self.raw, self.ctx.ptr()) };
        assert_eq!(st, 0, "gr_mat_set failed");
        m
    }
}

impl std::fmt::Debug for Mat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Mat({} x {} over {:?})", self.nrows(), self.ncols(), self.ctx.kind())
    }
}

impl Mat {
    /// The r by c zero matrix over `ctx`.
    pub fn zero(ctx: &Rc<Ctx>, r: usize, c: usize) -> Mat {
        let mut raw = sys::gr_mat_struct::default();
        unsafe { sys::gr_mat_init(&mut raw, r as sys::slong, c as sys::slong, ctx.ptr()) };
        Mat { ctx: ctx.clone(), raw }
    }

    /// The n by n identity matrix.
    pub fn identity(ctx: &Rc<Ctx>, n: usize) -> GrResult<Mat> {
        let mut m = Mat::zero(ctx, n, n);
        check(unsafe { sys::gr_mat_one(&mut m.raw, ctx.ptr()) })?;
        Ok(m)
    }

    /// The n by n matrix with `x` on the diagonal.
    pub fn scalar(n: usize, x: &Elem) -> GrResult<Mat> {
        let mut m = Mat::zero(x.ctx(), n, n);
        check(unsafe { sys::gr_mat_set_scalar(&mut m.raw, x.as_ptr(), m.ctx.ptr()) })?;
        Ok(m)
    }

    pub fn ctx(&self) -> &Rc<Ctx> {
        &self.ctx
    }

    #[inline]
    pub fn nrows(&self) -> usize {
        self.raw.r as usize
    }

    #[inline]
    pub fn ncols(&self) -> usize {
        self.raw.c as usize
    }

    #[inline]
    fn ptr(&self, i: usize, j: usize) -> *const c_void {
        debug_assert!(i < self.nrows() && j < self.ncols());
        let k = i * self.raw.stride as usize + j;
        unsafe { self.raw.entries.cast::<u8>().add(k * self.ctx.elem_size()).cast() }
    }

    #[inline]
    fn ptr_mut(&mut self, i: usize, j: usize) -> *mut c_void {
        self.ptr(i, j).cast_mut()
    }

    /// The entry in row i and column j (from 0).
    pub fn entry(&self, i: usize, j: usize) -> Elem {
        let mut e = Elem::new(&self.ctx);
        let st = unsafe { sys::gr_set(e.as_mut_ptr(), self.ptr(i, j), self.ctx.ptr()) };
        assert_eq!(st, 0, "gr_set failed");
        e
    }

    /// Set an entry to `x`, an element of the matrix's ring.
    pub fn set_entry(&mut self, i: usize, j: usize, x: &Elem) {
        debug_assert!(Rc::ptr_eq(x.ctx(), &self.ctx));
        let st = unsafe { sys::gr_set(self.ptr_mut(i, j), x.as_ptr(), self.ctx.ptr()) };
        assert_eq!(st, 0, "gr_set failed");
    }

    pub fn set_integer(&mut self, i: usize, j: usize, x: &Integer) -> GrResult<()> {
        check(unsafe { sys::gr_set_fmpz(self.ptr_mut(i, j), x.raw_ptr(), self.ctx.ptr()) })
    }

    pub fn set_rational(&mut self, i: usize, j: usize, x: &Rational) -> GrResult<()> {
        check(unsafe { sys::gr_set_fmpq(self.ptr_mut(i, j), x.raw_ptr(), self.ctx.ptr()) })
    }

    pub fn set_si(&mut self, i: usize, j: usize, x: i64) -> GrResult<()> {
        check(unsafe { sys::gr_set_si(self.ptr_mut(i, j), x as sys::slong, self.ctx.ptr()) })
    }

    /// The residue in an entry of a matrix over integers modulo a word.
    #[inline]
    pub fn word(&self, i: usize, j: usize) -> u64 {
        debug_assert!(matches!(self.ctx.kind(), CtxKind::Nmod(_)));
        unsafe { *self.ptr(i, j).cast::<u64>() }
    }

    /// Set an entry of a matrix over integers modulo a word to a residue.
    #[inline]
    pub fn set_word(&mut self, i: usize, j: usize, v: u64) {
        debug_assert!(matches!(self.ctx.kind(), CtxKind::Nmod(n) if v < *n));
        unsafe { *self.ptr_mut(i, j).cast::<u64>() = v };
    }

    /// An entry of a matrix over the integers.
    pub fn integer(&self, i: usize, j: usize) -> Integer {
        debug_assert!(matches!(self.ctx.kind(), CtxKind::Integers));
        let mut z = Integer::zero();
        unsafe { sys::fmpz_set(z.raw_mut_ptr(), self.ptr(i, j).cast()) };
        z
    }

    pub fn entry_is_zero(&self, i: usize, j: usize) -> bool {
        unsafe { sys::gr_is_zero(self.ptr(i, j), self.ctx.ptr()) == sys::truth_t_T_TRUE }
    }

    pub fn equal(&self, o: &Mat) -> Truth {
        if self.nrows() != o.nrows() || self.ncols() != o.ncols() {
            return Truth::False;
        }
        Truth::from_raw(unsafe { sys::gr_mat_equal(&self.raw, &o.raw, self.ctx.ptr()) })
    }

    pub fn is_zero(&self) -> Truth {
        Truth::from_raw(unsafe { sys::gr_mat_is_zero(&self.raw, self.ctx.ptr()) })
    }

    /// The number of entries that are not zero.
    pub fn count_nonzero(&self) -> usize {
        let mut n = 0;
        for i in 0..self.nrows() {
            for j in 0..self.ncols() {
                n += !self.entry_is_zero(i, j) as usize;
            }
        }
        n
    }

    /// The same entries over another context (`gr_set_other` on each).
    pub fn change_ring(&self, ctx: &Rc<Ctx>) -> GrResult<Mat> {
        let mut m = Mat::zero(ctx, self.nrows(), self.ncols());
        for i in 0..self.nrows() {
            for j in 0..self.ncols() {
                check(unsafe { sys::gr_set_other(m.ptr_mut(i, j), self.ptr(i, j), self.ctx.ptr(), ctx.ptr()) })?;
            }
        }
        Ok(m)
    }

    // ----- blocks and rearrangements ------------------------------------------

    /// The r by c block whose top left entry is (i, j).
    pub fn block(&self, i: usize, j: usize, r: usize, c: usize) -> Mat {
        assert!(i + r <= self.nrows() && j + c <= self.ncols(), "block out of range");
        let mut m = Mat::zero(&self.ctx, r, c);
        if r > 0 && c > 0 {
            let mut w = sys::gr_mat_struct::default();
            unsafe {
                sys::gr_mat_window_init(&mut w, &self.raw, i as sys::slong, j as sys::slong, (i + r) as sys::slong, (j + c) as sys::slong, self.ctx.ptr());
                let st = sys::gr_mat_set(&mut m.raw, &w, self.ctx.ptr());
                sys::gr_mat_window_clear(&mut w, self.ctx.ptr());
                assert_eq!(st, 0, "gr_mat_set failed");
            }
        }
        m
    }

    /// The matrix of the given rows and columns (from 0), in that order.
    pub fn select(&self, rows: &[usize], cols: &[usize]) -> Mat {
        let mut m = Mat::zero(&self.ctx, rows.len(), cols.len());
        for (a, &i) in rows.iter().enumerate() {
            for (b, &j) in cols.iter().enumerate() {
                let st = unsafe { sys::gr_set(m.ptr_mut(a, b), self.ptr(i, j), self.ctx.ptr()) };
                assert_eq!(st, 0, "gr_set failed");
            }
        }
        m
    }

    /// Copy `b` into the block whose top left entry is (i, j).
    pub fn insert(&mut self, b: &Mat, i: usize, j: usize) {
        assert!(i + b.nrows() <= self.nrows() && j + b.ncols() <= self.ncols(), "block out of range");
        if b.nrows() == 0 || b.ncols() == 0 {
            return;
        }
        let mut w = sys::gr_mat_struct::default();
        unsafe {
            sys::gr_mat_window_init(&mut w, &self.raw, i as sys::slong, j as sys::slong, (i + b.nrows()) as sys::slong, (j + b.ncols()) as sys::slong, self.ctx.ptr());
            let st = sys::gr_mat_set(&mut w, &b.raw, self.ctx.ptr());
            sys::gr_mat_window_clear(&mut w, self.ctx.ptr());
            assert_eq!(st, 0, "gr_mat_set failed");
        }
    }

    pub fn swap_rows(&mut self, i: usize, j: usize) {
        if i != j {
            unsafe { sys::gr_mat_swap_rows(&mut self.raw, std::ptr::null_mut(), i as sys::slong, j as sys::slong, self.ctx.ptr()) };
        }
    }

    pub fn swap_cols(&mut self, i: usize, j: usize) {
        if i != j {
            unsafe { sys::gr_mat_swap_cols(&mut self.raw, std::ptr::null_mut(), i as sys::slong, j as sys::slong, self.ctx.ptr()) };
        }
    }

    pub fn transpose(&self) -> Mat {
        let mut m = Mat::zero(&self.ctx, self.ncols(), self.nrows());
        let st = unsafe { sys::gr_mat_transpose(&mut m.raw, &self.raw, self.ctx.ptr()) };
        assert_eq!(st, 0, "gr_mat_transpose failed");
        m
    }

    /// `self` with `b` to its right.
    pub fn concat_horizontal(&self, b: &Mat) -> Mat {
        assert_eq!(self.nrows(), b.nrows());
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols() + b.ncols());
        m.insert(self, 0, 0);
        m.insert(b, 0, self.ncols());
        m
    }

    /// `self` with `b` below it.
    pub fn concat_vertical(&self, b: &Mat) -> Mat {
        assert_eq!(self.ncols(), b.ncols());
        let mut m = Mat::zero(&self.ctx, self.nrows() + b.nrows(), self.ncols());
        m.insert(self, 0, 0);
        m.insert(b, self.nrows(), 0);
        m
    }

    // ----- arithmetic ---------------------------------------------------------

    pub fn add(&self, b: &Mat) -> GrResult<Mat> {
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        check(unsafe { sys::gr_mat_add(&mut m.raw, &self.raw, &b.raw, self.ctx.ptr()) })?;
        Ok(m)
    }

    pub fn sub(&self, b: &Mat) -> GrResult<Mat> {
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        check(unsafe { sys::gr_mat_sub(&mut m.raw, &self.raw, &b.raw, self.ctx.ptr()) })?;
        Ok(m)
    }

    pub fn neg(&self) -> GrResult<Mat> {
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        check(unsafe { sys::gr_mat_neg(&mut m.raw, &self.raw, self.ctx.ptr()) })?;
        Ok(m)
    }

    pub fn mul(&self, b: &Mat) -> GrResult<Mat> {
        assert_eq!(self.ncols(), b.nrows());
        let mut m = Mat::zero(&self.ctx, self.nrows(), b.ncols());
        check(unsafe { sys::gr_mat_mul(&mut m.raw, &self.raw, &b.raw, self.ctx.ptr()) })?;
        Ok(m)
    }

    /// `x * self`.
    pub fn scalar_mul(&self, x: &Elem) -> GrResult<Mat> {
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        check(unsafe { sys::gr_mat_scalar_mul(&mut m.raw, x.as_ptr(), &self.raw, self.ctx.ptr()) })?;
        Ok(m)
    }

    /// `self * x`.
    pub fn mul_scalar(&self, x: &Elem) -> GrResult<Mat> {
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        check(unsafe { sys::gr_mat_mul_scalar(&mut m.raw, &self.raw, x.as_ptr(), self.ctx.ptr()) })?;
        Ok(m)
    }

    /// `self / x`, for a unit x.
    pub fn div_scalar(&self, x: &Elem) -> GrResult<Mat> {
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        check(unsafe { sys::gr_mat_div_scalar(&mut m.raw, &self.raw, x.as_ptr(), self.ctx.ptr()) })?;
        Ok(m)
    }

    /// `self^e` for a square matrix (e < 0 needs an invertible one).
    pub fn pow(&self, e: &Integer) -> GrResult<Mat> {
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        check(unsafe { sys::gr_mat_pow_fmpz(&mut m.raw, &self.raw, e.raw_ptr(), self.ctx.ptr()) })?;
        Ok(m)
    }

    /// The inverse of a square matrix; `Domain` if it has none.
    pub fn inv(&self) -> GrResult<Mat> {
        let mut m = Mat::zero(&self.ctx, self.nrows(), self.ncols());
        check(unsafe { sys::gr_mat_inv(&mut m.raw, &self.raw, self.ctx.ptr()) })?;
        Ok(m)
    }

    pub fn trace(&self) -> GrResult<Elem> {
        let mut e = Elem::new(&self.ctx);
        check(unsafe { sys::gr_mat_trace(e.as_mut_ptr(), &self.raw, self.ctx.ptr()) })?;
        Ok(e)
    }
}
