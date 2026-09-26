//! Correctly rounded values from FLINT's ball arithmetic (`arb`, `acb`): a
//! function is evaluated at increasing working precision until its
//! enclosure determines the value rounded to nearest at the target
//! precision (Ziv's strategy). This gives the same results as MPFR and MPC,
//! which round correctly.

use flint3_sys as sys;

use crate::mpfr as m;
use crate::{Complex, Integer, Real};

/// A real ball.
pub struct Arb(pub sys::arb_struct);

/// A complex ball.
pub struct Acb(pub sys::acb_struct);

impl Arb {
    pub fn new() -> Arb {
        let mut b: sys::arb_struct = unsafe { std::mem::zeroed() };
        unsafe { sys::arb_init(&mut b) };
        Arb(b)
    }

    /// The exact value of a finite real (signed zeros become zero).
    pub fn from_real(x: &Real) -> Arb {
        let mut b = Arb::new();
        unsafe {
            m::arf_set_mpfr(&mut b.0.mid, x.raw());
            sys::mag_zero(&mut b.0.rad);
        }
        b
    }

    pub fn from_integer(n: &Integer) -> Arb {
        let mut b = Arb::new();
        unsafe { sys::arb_set_fmpz(&mut b.0, n.raw_ptr()) };
        b
    }

    pub fn ptr(&self) -> *const sys::arb_struct {
        &self.0
    }

    pub fn mut_ptr(&mut self) -> *mut sys::arb_struct {
        &mut self.0
    }

    /// The value rounded to `bits`, if the ball determines it.
    pub fn rounded(&self, bits: u64) -> Option<Real> {
        round_ball(&self.0, bits)
    }

    /// The midpoint rounded to `bits`.
    pub fn mid(&self, bits: u64) -> Real {
        let mut r = Real::zero(bits);
        unsafe { m::arf_to_mpfr(r.raw_mut(), &self.0.mid) };
        r
    }
}

impl Default for Arb {
    fn default() -> Arb {
        Arb::new()
    }
}

impl Drop for Arb {
    fn drop(&mut self) {
        unsafe { sys::arb_clear(&mut self.0) };
    }
}

impl Acb {
    pub fn new() -> Acb {
        let mut b: sys::acb_struct = unsafe { std::mem::zeroed() };
        unsafe { sys::acb_init(&mut b) };
        Acb(b)
    }

    pub fn from_parts(re: &Real, im: &Real) -> Acb {
        let mut b = Acb::new();
        unsafe {
            m::arf_set_mpfr(&mut b.0.real.mid, re.raw());
            m::arf_set_mpfr(&mut b.0.imag.mid, im.raw());
            sys::mag_zero(&mut b.0.real.rad);
            sys::mag_zero(&mut b.0.imag.rad);
        }
        b
    }

    pub fn ptr(&self) -> *const sys::acb_struct {
        &self.0
    }

    pub fn mut_ptr(&mut self) -> *mut sys::acb_struct {
        &mut self.0
    }
}

impl Default for Acb {
    fn default() -> Acb {
        Acb::new()
    }
}

impl Drop for Acb {
    fn drop(&mut self) {
        unsafe { sys::acb_clear(&mut self.0) };
    }
}

/// The value of a ball rounded to nearest at `bits`, if every point of the
/// ball rounds to the same number.
pub(crate) fn round_ball(b: &sys::arb_struct, bits: u64) -> Option<Real> {
    unsafe {
        if sys::arb_is_finite(b) == 0 {
            return None;
        }
        let mut lo = Real::zero(bits);
        if sys::mag_is_zero(&b.rad) != 0 {
            m::arf_to_mpfr(lo.raw_mut(), &b.mid);
            return Some(lo);
        }
        let mut hi = Real::zero(bits);
        let mut a: sys::arf_struct = std::mem::zeroed();
        sys::arf_init(&mut a);
        let wp = (sys::arf_bits(&b.mid) as u64).max(bits) + 64;
        sys::arb_get_lbound_arf(&mut a, b, wp as sys::slong);
        m::arf_to_mpfr(lo.raw_mut(), &a);
        sys::arb_get_ubound_arf(&mut a, b, wp as sys::slong);
        m::arf_to_mpfr(hi.raw_mut(), &a);
        sys::arf_clear(&mut a);
        (lo == hi && lo.is_zero() == hi.is_zero()).then_some(lo)
    }
}

/// The largest working precision tried for a result of `bits` bits.
pub fn max_precision(bits: u64) -> u64 {
    16 * bits + 4096
}

/// Working precisions to try for a result of `bits` bits.
pub(crate) fn precisions(bits: u64) -> impl Iterator<Item = u64> {
    let mut wp = bits + 32;
    let max = max_precision(bits);
    std::iter::from_fn(move || {
        let w = wp;
        wp = wp * 2;
        (w <= max).then_some(w)
    })
}

/// A real function correctly rounded to `bits`: `f(out, wp)` writes an
/// enclosure of the value computed at working precision `wp`. If no
/// precision determines the value, the midpoint of the last enclosure is
/// used (NaN if it is not finite).
pub fn eval_real(bits: u64, mut f: impl FnMut(*mut sys::arb_struct, i64)) -> Real {
    let mut out = Arb::new();
    for wp in precisions(bits) {
        f(out.mut_ptr(), wp as i64);
        if let Some(r) = round_ball(&out.0, bits) {
            return r;
        }
    }
    if unsafe { sys::arf_is_finite(&out.0.mid) } == 0 { Real::nan(bits) } else { out.mid(bits) }
}

/// A complex function correctly rounded to `bits` (each part), as
/// `eval_real`.
pub fn eval_complex(bits: u64, mut f: impl FnMut(*mut sys::acb_struct, i64)) -> (Real, Real) {
    let mut out = Acb::new();
    for wp in precisions(bits) {
        f(out.mut_ptr(), wp as i64);
        if let Ok(z) = round_acb(&out.0, bits) {
            return (z.re, z.im);
        }
    }
    let z = round_acb(&out.0, bits).unwrap_or_else(|mid| mid);
    (z.re, z.im)
}

/// A complex ball rounded to `bits` in each part, or its midpoint (NaN
/// parts where not finite) if the ball does not determine the rounding.
pub(crate) fn round_acb(b: &sys::acb_struct, bits: u64) -> Result<Complex, Complex> {
    if let (Some(re), Some(im)) = (round_ball(&b.real, bits), round_ball(&b.imag, bits)) {
        return Ok(Complex::new(re, im));
    }
    let part = |b: &sys::arb_struct| {
        let mut r = Real::nan(bits);
        if unsafe { sys::arf_is_finite(&b.mid) } != 0 {
            unsafe { m::arf_to_mpfr(r.raw_mut(), &b.mid) };
        }
        r
    };
    Err(Complex::new(part(&b.real), part(&b.imag)))
}

/// As `eval_complex`, but `None` if no precision determines the value.
pub fn try_eval_complex(bits: u64, mut f: impl FnMut(*mut sys::acb_struct, i64)) -> Option<(Real, Real)> {
    let mut out = Acb::new();
    for wp in precisions(bits) {
        f(out.mut_ptr(), wp as i64);
        if let (Some(re), Some(im)) = (round_ball(&out.0.real, bits), round_ball(&out.0.imag, bits)) {
            return Some((re, im));
        }
    }
    None
}
