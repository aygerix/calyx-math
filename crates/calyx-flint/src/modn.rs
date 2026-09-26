//! Arithmetic modulo a fixed modulus for the factoring methods (ECM, p - 1
//! and p + 1): residues on limbs, polynomials and their middle products,
//! and products of polynomial values.
//!
//! A residue is a slice of `size` little-endian limbs holding `x << norm`
//! for some `0 <= x < n`, where `n << norm` fills its top limb: the
//! normalised form of FLINT's `flint_mpn_mulmod_preinvn`, as in FLINT's own
//! ECM. Nothing allocates once the modulus is set up.

use std::rc::Rc;

use flint3_sys as sys;

use crate::Integer;

// Exported by FLINT but missing from its bindings.
unsafe extern "C" {
    fn flint_mpn_preinvn(dinv: *mut sys::ulong, d: *const sys::ulong, n: sys::slong);
    fn flint_mpn_mulmod_preinvn(
        r: *mut sys::ulong,
        a: *const sys::ulong,
        b: *const sys::ulong,
        n: sys::slong,
        d: *const sys::ulong,
        dinv: *const sys::ulong,
        norm: sys::ulong,
    );
}

/// A modulus `n > 1` for residues on limbs.
pub struct ModN {
    n: Integer,
    norm: u32,
    /// `n << norm`, and FLINT's precomputed inverse of it.
    d: Vec<u64>,
    dinv: Vec<u64>,
}

impl ModN {
    /// # Panics
    /// If `n < 2`.
    pub fn new(n: &Integer) -> ModN {
        assert!(n.sign() > 0 && !n.is_one(), "the modulus must exceed 1");
        let mut d = n.to_limbs();
        let norm = d[d.len() - 1].leading_zeros();
        shl(&mut d, norm);
        let mut dinv = vec![0; d.len()];
        unsafe { flint_mpn_preinvn(dinv.as_mut_ptr().cast(), d.as_ptr().cast(), d.len() as sys::slong) };
        ModN { n: n.clone(), norm, d, dinv }
    }

    pub fn modulus(&self) -> &Integer {
        &self.n
    }

    /// The number of limbs of a residue.
    pub fn size(&self) -> usize {
        self.d.len()
    }

    pub fn zero(&self) -> Vec<u64> {
        vec![0; self.size()]
    }

    pub fn one(&self) -> Vec<u64> {
        let mut r = self.zero();
        r[0] = 1 << self.norm;
        r
    }

    /// The residue of `x`.
    pub fn residue(&self, x: &Integer) -> Vec<u64> {
        let (_, r) = x.div_rem_euclid(&self.n).expect("the modulus is positive");
        let mut v = r.to_limbs();
        v.resize(self.size(), 0);
        shl(&mut v, self.norm);
        v
    }

    /// The integer in `[0, n)` that a residue stands for.
    pub fn value(&self, x: &[u64]) -> Integer {
        let mut v = x.to_vec();
        shr(&mut v, self.norm);
        Integer::from_limbs(&v, false)
    }

    /// `gcd(x, n)`.
    pub fn gcd(&self, x: &[u64]) -> Integer {
        self.value(x).gcd(&self.n)
    }

    /// The inverse of `x`, or `gcd(x, n)` when there is none.
    pub fn inverse(&self, x: &[u64]) -> Result<Vec<u64>, Integer> {
        let v = self.value(x);
        match v.invmod(&self.n) {
            Some(i) => Ok(self.residue(&i)),
            None => Err(v.gcd(&self.n)),
        }
    }

    pub fn is_zero(&self, x: &[u64]) -> bool {
        x.iter().all(|&l| l == 0)
    }

    /// `r = a b`.
    #[inline]
    pub fn mul(&self, r: &mut [u64], a: &[u64], b: &[u64]) {
        debug_assert!(r.len() == self.size() && a.len() == self.size() && b.len() == self.size());
        unsafe { self.mulmod(r.as_mut_ptr(), a.as_ptr(), b.as_ptr()) }
    }

    /// `r = r b`.
    #[inline]
    pub fn mul_assign(&self, r: &mut [u64], b: &[u64]) {
        debug_assert!(r.len() == self.size() && b.len() == self.size());
        let p = r.as_mut_ptr();
        unsafe { self.mulmod(p, p, b.as_ptr()) }
    }

    /// `r = a^2`.
    #[inline]
    pub fn sqr(&self, r: &mut [u64], a: &[u64]) {
        debug_assert!(r.len() == self.size() && a.len() == self.size());
        unsafe { self.mulmod(r.as_mut_ptr(), a.as_ptr(), a.as_ptr()) }
    }

    /// `r = r^2`.
    #[inline]
    pub fn sqr_assign(&self, r: &mut [u64]) {
        debug_assert!(r.len() == self.size());
        let p = r.as_mut_ptr();
        unsafe { self.mulmod(p, p, p) }
    }

    /// FLINT squares when `a` and `b` are the same, and `r` may be either.
    #[inline]
    unsafe fn mulmod(&self, r: *mut u64, a: *const u64, b: *const u64) {
        let (n, d, dinv) = (self.d.len() as sys::slong, self.d.as_ptr().cast(), self.dinv.as_ptr().cast());
        unsafe { flint_mpn_mulmod_preinvn(r.cast(), a.cast(), b.cast(), n, d, dinv, self.norm as sys::ulong) }
    }

    /// `r = a + b`.
    pub fn add(&self, r: &mut [u64], a: &[u64], b: &[u64]) {
        let mut carry = false;
        for i in 0..self.d.len() {
            let (s, c1) = a[i].overflowing_add(b[i]);
            let (s, c2) = s.overflowing_add(carry as u64);
            r[i] = s;
            carry = c1 | c2;
        }
        if carry || !self.below_d(r) {
            sub_in_place(r, &self.d);
        }
    }

    /// `r = r + b`.
    pub fn add_assign(&self, r: &mut [u64], b: &[u64]) {
        let mut carry = false;
        for i in 0..self.d.len() {
            let (s, c1) = r[i].overflowing_add(b[i]);
            let (s, c2) = s.overflowing_add(carry as u64);
            r[i] = s;
            carry = c1 | c2;
        }
        if carry || !self.below_d(r) {
            sub_in_place(r, &self.d);
        }
    }

    /// `r = a - b`.
    pub fn sub(&self, r: &mut [u64], a: &[u64], b: &[u64]) {
        let mut borrow = false;
        for i in 0..self.d.len() {
            let (s, b1) = a[i].overflowing_sub(b[i]);
            let (s, b2) = s.overflowing_sub(borrow as u64);
            r[i] = s;
            borrow = b1 | b2;
        }
        if borrow {
            add_in_place(r, &self.d);
        }
    }

    /// `r = r - b`.
    pub fn sub_assign(&self, r: &mut [u64], b: &[u64]) {
        let mut borrow = false;
        for i in 0..self.d.len() {
            let (s, b1) = r[i].overflowing_sub(b[i]);
            let (s, b2) = s.overflowing_sub(borrow as u64);
            r[i] = s;
            borrow = b1 | b2;
        }
        if borrow {
            add_in_place(r, &self.d);
        }
    }

    fn below_d(&self, r: &[u64]) -> bool {
        for i in (0..self.d.len()).rev() {
            if r[i] != self.d[i] {
                return r[i] < self.d[i];
            }
        }
        false
    }
}

/// `x -= y`, wrapping.
fn sub_in_place(x: &mut [u64], y: &[u64]) {
    let mut borrow = false;
    for (a, &b) in x.iter_mut().zip(y) {
        let (s, b1) = a.overflowing_sub(b);
        let (s, b2) = s.overflowing_sub(borrow as u64);
        *a = s;
        borrow = b1 | b2;
    }
}

/// `x += y`, wrapping.
fn add_in_place(x: &mut [u64], y: &[u64]) {
    let mut carry = false;
    for (a, &b) in x.iter_mut().zip(y) {
        let (s, c1) = a.overflowing_add(b);
        let (s, c2) = s.overflowing_add(carry as u64);
        *a = s;
        carry = c1 | c2;
    }
}

/// Shift left by `s < 64` bits; the bits shifted out must be zero.
fn shl(x: &mut [u64], s: u32) {
    if s == 0 {
        return;
    }
    for i in (1..x.len()).rev() {
        x[i] = (x[i] << s) | (x[i - 1] >> (64 - s));
    }
    x[0] <<= s;
}

fn shr(x: &mut [u64], s: u32) {
    if s == 0 {
        return;
    }
    let last = x.len() - 1;
    for i in 0..last {
        x[i] = (x[i] >> s) | (x[i + 1] << (64 - s));
    }
    x[last] >>= s;
}

/// A vector of `fmpz` for FLINT's vector functions.
struct FmpzVec {
    ptr: *mut sys::fmpz,
    len: usize,
}

impl FmpzVec {
    fn zeroed(len: usize) -> FmpzVec {
        FmpzVec { ptr: unsafe { sys::_fmpz_vec_init(len as sys::slong) }, len }
    }

    fn from(xs: &[Integer]) -> FmpzVec {
        let v = FmpzVec::zeroed(xs.len());
        for (i, x) in xs.iter().enumerate() {
            unsafe { sys::fmpz_set(v.ptr.add(i), x.as_raw()) };
        }
        v
    }
}

impl Drop for FmpzVec {
    fn drop(&mut self) {
        unsafe { sys::_fmpz_vec_clear(self.ptr, self.len as sys::slong) };
    }
}

/// A modulus for polynomials, shared by them: FLINT's `fmpz_mod` context.
pub struct ModCtx {
    ctx: sys::fmpz_mod_ctx_struct,
}

impl ModCtx {
    /// # Panics
    /// If `n < 2`.
    pub fn new(n: &Integer) -> Rc<ModCtx> {
        assert!(n.sign() > 0 && !n.is_one(), "the modulus must exceed 1");
        let mut ctx = sys::fmpz_mod_ctx_struct::default();
        unsafe { sys::fmpz_mod_ctx_init(&mut ctx, n.as_raw()) };
        Rc::new(ModCtx { ctx })
    }
}

impl Drop for ModCtx {
    fn drop(&mut self) {
        unsafe { sys::fmpz_mod_ctx_clear(&mut self.ctx) };
    }
}

/// A polynomial modulo `n`.
pub struct ModPoly {
    f: sys::fmpz_mod_poly_struct,
    ctx: Rc<ModCtx>,
}

impl ModPoly {
    /// The polynomial with the coefficients `cs`, from the constant term on
    /// (reduced modulo `n`).
    pub fn new(ctx: &Rc<ModCtx>, cs: &[Integer]) -> ModPoly {
        let mut p = ModPoly::zero(ctx);
        for (i, c) in cs.iter().enumerate().rev() {
            unsafe { sys::fmpz_mod_poly_set_coeff_fmpz(&mut p.f, i as sys::slong, c.as_raw(), &ctx.ctx) };
        }
        p
    }

    fn zero(ctx: &Rc<ModCtx>) -> ModPoly {
        let mut f = sys::fmpz_mod_poly_struct::default();
        unsafe { sys::fmpz_mod_poly_init(&mut f, &ctx.ctx) };
        ModPoly { f, ctx: ctx.clone() }
    }

    /// The number of coefficients up to the leading one.
    pub fn len(&self) -> usize {
        self.f.length as usize
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn mul(&self, o: &ModPoly) -> ModPoly {
        let mut r = ModPoly::zero(&self.ctx);
        unsafe { sys::fmpz_mod_poly_mul(&mut r.f, &self.f, &o.f, &self.ctx.ctx) };
        r
    }

    pub fn add(&self, o: &ModPoly) -> ModPoly {
        let mut r = ModPoly::zero(&self.ctx);
        unsafe { sys::fmpz_mod_poly_add(&mut r.f, &self.f, &o.f, &self.ctx.ctx) };
        r
    }

    /// The coefficients of degree `lo` to `hi - 1` of the product with `o`,
    /// computed alone (FLINT's middle product).
    pub fn mulmid(&self, o: &ModPoly, lo: usize, hi: usize) -> Vec<Integer> {
        let mut r = ModPoly::zero(&self.ctx);
        if !self.is_empty() && !o.is_empty() {
            let hi = hi.min(self.len() + o.len() - 1);
            if lo < hi {
                unsafe { sys::fmpz_mod_poly_mulmid(&mut r.f, &self.f, &o.f, lo as sys::slong, hi as sys::slong, &self.ctx.ctx) };
            }
        }
        r.coeffs(0, hi - lo.min(hi))
    }

    /// The coefficients of degree `lo` to `hi - 1`.
    pub fn coeffs(&self, lo: usize, hi: usize) -> Vec<Integer> {
        (lo..hi)
            .map(|i| {
                let mut c = Integer::zero();
                unsafe { sys::fmpz_mod_poly_get_coeff_fmpz(c.as_raw_mut(), &self.f, i as sys::slong, &self.ctx.ctx) };
                c
            })
            .collect()
    }
}

impl Drop for ModPoly {
    fn drop(&mut self) {
        unsafe { sys::fmpz_mod_poly_clear(&mut self.f, &self.ctx.ctx) };
    }
}

/// The monic polynomial with given roots modulo `n`, for the product of its
/// values at many points. FLINT's product and remainder trees divide only by
/// monic polynomials, so `n` need not be prime.
pub struct RootPoly {
    ctx: sys::fmpz_mod_ctx_struct,
    f: sys::fmpz_mod_poly_struct,
}

impl RootPoly {
    /// The roots must lie in `[0, n)`.
    pub fn new(n: &Integer, roots: &[Integer]) -> RootPoly {
        let mut ctx = sys::fmpz_mod_ctx_struct::default();
        let mut f = sys::fmpz_mod_poly_struct::default();
        let xs = FmpzVec::from(roots);
        unsafe {
            sys::fmpz_mod_ctx_init(&mut ctx, n.as_raw());
            sys::fmpz_mod_poly_init(&mut f, &ctx);
            sys::fmpz_mod_poly_product_roots_fmpz_vec(&mut f, xs.ptr, xs.len as sys::slong, &ctx);
        }
        RootPoly { ctx, f }
    }

    /// The product of the values at the points (in `[0, n)`), modulo `n`.
    pub fn product_at(&self, points: &[Integer]) -> Integer {
        let mut acc = Integer::one();
        if points.is_empty() {
            return acc;
        }
        let (xs, ys) = (FmpzVec::from(points), FmpzVec::zeroed(points.len()));
        unsafe {
            sys::fmpz_mod_poly_evaluate_fmpz_vec_fast(ys.ptr, &self.f, xs.ptr, xs.len as sys::slong, &self.ctx);
            for i in 0..ys.len {
                sys::fmpz_mod_mul(acc.as_raw_mut(), acc.as_raw(), ys.ptr.add(i), &self.ctx);
            }
        }
        acc
    }
}

impl Drop for RootPoly {
    fn drop(&mut self) {
        unsafe {
            sys::fmpz_mod_poly_clear(&mut self.f, &self.ctx);
            sys::fmpz_mod_ctx_clear(&mut self.ctx);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn residues_match_integers() {
        for n in [Integer::from_u64(1000003), Integer::from_u64(u64::MAX - 58), Integer::one().mul_2exp(200) - Integer::from_u64(189)] {
            let m = ModN::new(&n);
            let a = Integer::from_u64(0x1234_5678_9abc_def1).pow(3);
            let b = Integer::from_u64(0xfeed_beef_dead_f00d).pow(2);
            let (ra, rb) = (m.residue(&a), m.residue(&b));
            let mut r = m.zero();
            m.mul(&mut r, &ra, &rb);
            assert_eq!(m.value(&r), (&a * &b).div_rem_euclid(&n).unwrap().1);
            m.sqr(&mut r, &ra);
            assert_eq!(m.value(&r), (&a * &a).div_rem_euclid(&n).unwrap().1);
            m.add(&mut r, &ra, &rb);
            assert_eq!(m.value(&r), (&a + &b).div_rem_euclid(&n).unwrap().1);
            m.sub(&mut r, &ra, &rb);
            assert_eq!(m.value(&r), (&a - &b).div_rem_euclid(&n).unwrap().1);
            m.sub(&mut r, &rb, &ra);
            assert_eq!(m.value(&r), (&b - &a).div_rem_euclid(&n).unwrap().1);
            assert_eq!(m.value(&m.one()), Integer::one());
        }
    }

    #[test]
    fn middle_products_are_slices() {
        let n = Integer::from_u64(1_000_000_007) * Integer::from_u64(998_244_353);
        let ctx = ModCtx::new(&n);
        let (mut s, mut rand) = (0x243f_6a88_85a3_08d3u64, Vec::new());
        for _ in 0..400 {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            rand.push(Integer::from_u64(s).div_rem_euclid(&n).unwrap().1);
        }
        let (a, b) = (ModPoly::new(&ctx, &rand[..150]), ModPoly::new(&ctx, &rand[150..]));
        let full = a.mul(&b).coeffs(0, 399);
        for (lo, hi) in [(0, 399), (149, 250), (100, 300), (398, 399), (10, 10), (300, 500)] {
            let want: Vec<Integer> = (lo..hi).map(|i| full.get(i).cloned().unwrap_or_else(Integer::zero)).collect();
            assert_eq!(b.mulmid(&a, lo, hi), want, "[{lo}, {hi})");
            assert_eq!(a.mulmid(&b, lo, hi), want, "[{lo}, {hi})");
        }
        let sums: Vec<Integer> = (0..3).map(|i| (&rand[i] + &rand[150 + i]).div_rem_euclid(&n).unwrap().1).collect();
        assert_eq!(a.add(&b).coeffs(0, 3), sums);
    }

    #[test]
    fn products_of_values() {
        let n = Integer::from_u64(1000003) * Integer::from_u64(999983);
        let roots: Vec<Integer> = (1..=5u64).map(|r| Integer::from_u64(r * r)).collect();
        let points: Vec<Integer> = (10..=13u64).map(Integer::from_u64).collect();
        let f = RootPoly::new(&n, &roots);
        let mut want = Integer::one();
        for x in &points {
            for r in &roots {
                want = (&want * &(x - r)).div_rem_euclid(&n).unwrap().1;
            }
        }
        assert_eq!(f.product_at(&points), want);
    }
}

