//! Declarations for the parts of MPFR used by calyx. MPFR is a dependency
//! of FLINT (and linked with it), but flint3-sys does not bind it.
//!
//! Only functions present in MPFR 4.1 are declared (the reference VM has
//! 4.1; macOS has 4.2).

#![allow(dead_code)]

use std::os::raw::{c_char, c_double, c_int, c_long, c_ulong};

use flint3_sys as sys;

/// `__mpfr_struct`: precision, sign, exponent and significand limbs.
#[repr(C)]
pub struct Mpfr {
    pub prec: c_long,
    pub sign: c_int,
    pub exp: c_long,
    pub d: *mut u64,
}

/// The special exponents of zero, NaN and infinity (`__MPFR_EXP_*`).
pub const EXP_ZERO: c_long = 0 - c_long::MAX;
pub const EXP_NAN: c_long = 1 - c_long::MAX;
pub const EXP_INF: c_long = 2 - c_long::MAX;

pub type Rnd = c_int;
pub const RNDN: Rnd = 0;
pub const RNDZ: Rnd = 1;
pub const RNDU: Rnd = 2;
pub const RNDD: Rnd = 3;
pub const RNDA: Rnd = 4;

pub type Unary = unsafe extern "C" fn(*mut Mpfr, *const Mpfr, Rnd) -> c_int;
pub type Binary = unsafe extern "C" fn(*mut Mpfr, *const Mpfr, *const Mpfr, Rnd) -> c_int;
pub type Constant = unsafe extern "C" fn(*mut Mpfr, Rnd) -> c_int;

unsafe extern "C" {
    pub fn mpfr_init2(x: *mut Mpfr, prec: c_long);
    pub fn mpfr_clear(x: *mut Mpfr);
    pub fn mpfr_set(r: *mut Mpfr, x: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_set_si(r: *mut Mpfr, v: c_long, rnd: Rnd) -> c_int;
    pub fn mpfr_set_ui(r: *mut Mpfr, v: c_ulong, rnd: Rnd) -> c_int;
    pub fn mpfr_set_d(r: *mut Mpfr, v: c_double, rnd: Rnd) -> c_int;
    pub fn mpfr_set_si_2exp(r: *mut Mpfr, v: c_long, e: c_long, rnd: Rnd) -> c_int;
    pub fn mpfr_set_zero(r: *mut Mpfr, sign: c_int);
    pub fn mpfr_set_nan(r: *mut Mpfr);
    pub fn mpfr_set_inf(r: *mut Mpfr, sign: c_int);
    pub fn mpfr_set_str(r: *mut Mpfr, s: *const c_char, base: c_int, rnd: Rnd) -> c_int;
    pub fn mpfr_setsign(r: *mut Mpfr, x: *const Mpfr, neg: c_int, rnd: Rnd) -> c_int;
    pub fn mpfr_get_d(x: *const Mpfr, rnd: Rnd) -> c_double;
    pub fn mpfr_get_si(x: *const Mpfr, rnd: Rnd) -> c_long;
    pub fn mpfr_get_str(s: *mut c_char, exp: *mut c_long, base: c_int, n: usize, x: *const Mpfr, rnd: Rnd) -> *mut c_char;
    pub fn mpfr_free_str(s: *mut c_char);
    pub fn mpfr_integer_p(x: *const Mpfr) -> c_int;
    pub fn mpfr_cmp(a: *const Mpfr, b: *const Mpfr) -> c_int;
    pub fn mpfr_cmpabs(a: *const Mpfr, b: *const Mpfr) -> c_int;
    pub fn mpfr_cmp_si(a: *const Mpfr, b: c_long) -> c_int;
    pub fn mpfr_min_prec(x: *const Mpfr) -> c_long;
    pub fn mpfr_nextabove(x: *mut Mpfr);
    pub fn mpfr_nextbelow(x: *mut Mpfr);

    pub fn mpfr_add(r: *mut Mpfr, a: *const Mpfr, b: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_sub(r: *mut Mpfr, a: *const Mpfr, b: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_mul(r: *mut Mpfr, a: *const Mpfr, b: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_div(r: *mut Mpfr, a: *const Mpfr, b: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_add_si(r: *mut Mpfr, a: *const Mpfr, b: c_long, rnd: Rnd) -> c_int;
    pub fn mpfr_mul_si(r: *mut Mpfr, a: *const Mpfr, b: c_long, rnd: Rnd) -> c_int;
    pub fn mpfr_div_si(r: *mut Mpfr, a: *const Mpfr, b: c_long, rnd: Rnd) -> c_int;
    pub fn mpfr_si_div(r: *mut Mpfr, a: c_long, b: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_mul_2si(r: *mut Mpfr, a: *const Mpfr, e: c_long, rnd: Rnd) -> c_int;
    pub fn mpfr_fmma(r: *mut Mpfr, a: *const Mpfr, b: *const Mpfr, c: *const Mpfr, d: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_fmms(r: *mut Mpfr, a: *const Mpfr, b: *const Mpfr, c: *const Mpfr, d: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_neg(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_abs(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_sqr(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_sqrt(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_rec_sqrt(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_cbrt(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_rootn_ui(r: *mut Mpfr, a: *const Mpfr, n: c_ulong, rnd: Rnd) -> c_int;
    pub fn mpfr_pow(r: *mut Mpfr, a: *const Mpfr, b: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_pow_si(r: *mut Mpfr, a: *const Mpfr, b: c_long, rnd: Rnd) -> c_int;
    pub fn mpfr_hypot(r: *mut Mpfr, a: *const Mpfr, b: *const Mpfr, rnd: Rnd) -> c_int;

    pub fn mpfr_rint(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_round(r: *mut Mpfr, a: *const Mpfr) -> c_int;
    pub fn mpfr_trunc(r: *mut Mpfr, a: *const Mpfr) -> c_int;
    pub fn mpfr_floor(r: *mut Mpfr, a: *const Mpfr) -> c_int;
    pub fn mpfr_ceil(r: *mut Mpfr, a: *const Mpfr) -> c_int;
    pub fn mpfr_frac(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;

    pub fn mpfr_const_pi(r: *mut Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_const_euler(r: *mut Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_const_catalan(r: *mut Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_const_log2(r: *mut Mpfr, rnd: Rnd) -> c_int;

    pub fn mpfr_exp(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_expm1(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_log(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_log1p(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_log2(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_log10(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_sin(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_cos(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_tan(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_sec(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_csc(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_cot(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_sin_cos(s: *mut Mpfr, c: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_asin(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_acos(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_atan(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_atan2(r: *mut Mpfr, y: *const Mpfr, x: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_sinh(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_cosh(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_tanh(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_sech(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_csch(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_coth(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_asinh(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_acosh(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_atanh(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_gamma(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_lngamma(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_lgamma(r: *mut Mpfr, sign: *mut c_int, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_digamma(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_zeta(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_zeta_ui(r: *mut Mpfr, n: c_ulong, rnd: Rnd) -> c_int;
    pub fn mpfr_erf(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_erfc(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_eint(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_li2(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_j0(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_j1(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_jn(r: *mut Mpfr, n: c_long, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_y0(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_y1(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_yn(r: *mut Mpfr, n: c_long, a: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_agm(r: *mut Mpfr, a: *const Mpfr, b: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_gamma_inc(r: *mut Mpfr, a: *const Mpfr, b: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_beta(r: *mut Mpfr, a: *const Mpfr, b: *const Mpfr, rnd: Rnd) -> c_int;
    pub fn mpfr_ai(r: *mut Mpfr, a: *const Mpfr, rnd: Rnd) -> c_int;

    // FLINT's conversions between `arf` and MPFR.
    pub fn arf_get_mpfr(r: *mut Mpfr, x: *const sys::arf_struct, rnd: Rnd) -> c_int;
    pub fn arf_set_mpfr(r: *mut sys::arf_struct, x: *const Mpfr);
}
