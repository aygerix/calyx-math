use std::cmp::Ordering;
use std::ffi::{CStr, CString};
use std::fmt;
use std::hash::Hasher;
use std::os::raw::{c_int, c_long};

use flint3_sys as sys;

use crate::mpfr::{self as m, Mpfr};
use crate::{Integer, Rational};

/// An arbitrary-precision binary floating-point number (MPFR), with MPFR's
/// semantics: operations are correctly rounded to nearest, and there are
/// signed zeros, infinities and NaN. The precision in bits is part of the
/// value.
pub struct Real {
    raw: Mpfr,
}

/// Bits of precision for `digits` decimal digits: `⌈digits·log2(10)⌉`.
pub fn bits_for_digits(digits: u64) -> u64 {
    let f = digits as f64 * std::f64::consts::LOG2_10;
    if digits > 0 && (f - f.round()).abs() < 1e-6 {
        // 10^d is not a power of two, so the answer is its bit length.
        return Integer::from_u64(10).pow(digits).bits();
    }
    f.ceil() as u64
}

/// Decimal digits of precision for `bits` bits: `⌊bits·log10(2)⌋`.
pub fn digits_for_bits(bits: u64) -> u64 {
    let f = bits as f64 * std::f64::consts::LOG10_2;
    if bits > 0 && (f - f.round()).abs() < 1e-6 {
        return Integer::one().mul_2exp(bits).to_string().len() as u64 - 1;
    }
    f.floor() as u64
}

/// A scratch `arf`, for conversions through FLINT.
struct Arf(sys::arf_struct);

impl Arf {
    fn new() -> Arf {
        let mut a: sys::arf_struct = unsafe { std::mem::zeroed() };
        unsafe { sys::arf_init(&mut a) };
        Arf(a)
    }
}

impl Drop for Arf {
    fn drop(&mut self) {
        unsafe { sys::arf_clear(&mut self.0) };
    }
}

impl Real {
    /// A NaN of the given precision (what `mpfr_init2` makes).
    fn alloc(prec: u64) -> Real {
        let mut raw = Mpfr { prec: 0, sign: 0, exp: 0, d: std::ptr::null_mut() };
        unsafe { m::mpfr_init2(&mut raw, prec.max(1) as c_long) };
        Real { raw }
    }

    pub(crate) fn raw(&self) -> *const Mpfr {
        &self.raw
    }

    pub(crate) fn raw_mut(&mut self) -> *mut Mpfr {
        &mut self.raw
    }

    /// Positive zero.
    pub fn zero(prec: u64) -> Real {
        let mut r = Real::alloc(prec);
        unsafe { m::mpfr_set_zero(&mut r.raw, 1) };
        r
    }

    pub fn signed_zero(prec: u64, negative: bool) -> Real {
        let mut r = Real::alloc(prec);
        unsafe { m::mpfr_set_zero(&mut r.raw, if negative { -1 } else { 1 }) };
        r
    }

    pub fn nan(prec: u64) -> Real {
        Real::alloc(prec)
    }

    pub fn infinity(prec: u64, negative: bool) -> Real {
        let mut r = Real::alloc(prec);
        unsafe { m::mpfr_set_inf(&mut r.raw, if negative { -1 } else { 1 }) };
        r
    }

    pub fn prec(&self) -> u64 {
        self.raw.prec as u64
    }

    /// Decimal digits of precision.
    pub fn digits(&self) -> u64 {
        digits_for_bits(self.prec())
    }

    pub fn from_i64(v: i64, prec: u64) -> Real {
        let mut r = Real::alloc(prec);
        unsafe { m::mpfr_set_si(&mut r.raw, v as c_long, m::RNDN) };
        r
    }

    fn from_arf(a: &Arf, prec: u64) -> Real {
        let mut r = Real::alloc(prec);
        unsafe { m::arf_to_mpfr(&mut r.raw, &a.0) };
        r
    }

    fn to_arf(&self) -> Arf {
        let mut a = Arf::new();
        unsafe { m::arf_set_mpfr(&mut a.0, &self.raw) };
        a
    }

    pub fn from_integer(n: &Integer, prec: u64) -> Real {
        if let Some(v) = n.to_i64() {
            return Real::from_i64(v, prec);
        }
        let mut a = Arf::new();
        unsafe { sys::arf_set_fmpz(&mut a.0, n.raw_ptr()) };
        Real::from_arf(&a, prec)
    }

    pub fn from_rational(q: &Rational, prec: u64) -> Real {
        let mut a = Arf::new();
        unsafe { sys::arf_set_fmpq(&mut a.0, q.raw_ptr(), prec as sys::slong, sys::arf_rnd_t_ARF_RND_NEAR) };
        Real::from_arf(&a, prec)
    }

    pub fn from_f64(d: f64, prec: u64) -> Real {
        let mut r = Real::alloc(prec);
        unsafe { m::mpfr_set_d(&mut r.raw, d, m::RNDN) };
        r
    }

    /// `x·2^e` for an integer `x`, rounded.
    pub fn from_integer_2exp(x: &Integer, e: i64, prec: u64) -> Real {
        let mut a = Arf::new();
        unsafe {
            sys::arf_set_fmpz(&mut a.0, x.raw_ptr());
            sys::arf_mul_2exp_si(&mut a.0, &a.0, e as sys::slong);
        }
        Real::from_arf(&a, prec)
    }

    /// Parse a decimal literal such as `1.25`, `-3e-4` or `2.5E10`,
    /// correctly rounded.
    pub fn parse(s: &str, prec: u64) -> Option<Real> {
        let c = CString::new(s.trim()).ok()?;
        let mut r = Real::alloc(prec);
        (unsafe { m::mpfr_set_str(&mut r.raw, c.as_ptr(), 10, m::RNDN) } == 0).then_some(r)
    }

    /// The exact value, if finite.
    pub fn to_rational(&self) -> Option<Rational> {
        if !self.is_finite() {
            return None;
        }
        let a = self.to_arf();
        let mut fq = sys::fmpq { num: 0, den: 1 };
        unsafe { sys::arf_get_fmpq(&mut fq, &a.0) };
        let mut n = Integer::zero();
        let mut d = Integer::zero();
        unsafe {
            sys::fmpz_set(n.as_raw_mut(), &fq.num);
            sys::fmpz_set(d.as_raw_mut(), &fq.den);
            sys::fmpq_clear(&mut fq);
        }
        Rational::new(&n, &d)
    }

    /// The value as an integer, if it is a finite integer.
    pub fn to_integer(&self) -> Option<Integer> {
        if !self.is_integer() {
            return None;
        }
        let a = self.to_arf();
        let mut n = Integer::zero();
        unsafe { sys::arf_get_fmpz(n.as_raw_mut(), &a.0, sys::arf_rnd_t_ARF_RND_DOWN) };
        Some(n)
    }

    /// `(m, e)` with `self = m·2^e` and `m` an integer of `prec` bits (0 for
    /// zero and the special values).
    pub fn mantissa_exponent(&self) -> (Integer, i64) {
        if !self.is_regular() {
            return (Integer::zero(), 0);
        }
        let e = self.raw.exp as i64 - self.prec() as i64;
        let mut r = Real::alloc(self.prec());
        unsafe { m::mpfr_mul_2si(&mut r.raw, &self.raw, -(e as c_long), m::RNDN) };
        (r.to_integer().unwrap_or_default(), e)
    }

    pub fn to_f64(&self) -> f64 {
        unsafe { m::mpfr_get_d(&self.raw, m::RNDN) }
    }

    // ----- predicates ------------------------------------------------------

    pub fn is_zero(&self) -> bool {
        self.raw.exp == m::EXP_ZERO
    }

    pub fn is_nan(&self) -> bool {
        self.raw.exp == m::EXP_NAN
    }

    pub fn is_inf(&self) -> bool {
        self.raw.exp == m::EXP_INF
    }

    /// Neither NaN nor infinite.
    pub fn is_finite(&self) -> bool {
        !self.is_nan() && !self.is_inf()
    }

    /// Finite and non-zero.
    pub fn is_regular(&self) -> bool {
        self.raw.exp > m::EXP_INF
    }

    pub fn is_integer(&self) -> bool {
        unsafe { m::mpfr_integer_p(&self.raw) != 0 }
    }

    /// The sign as -1, 0 or 1 (0 for zeros and NaN).
    pub fn sign(&self) -> i32 {
        if self.is_zero() || self.is_nan() { 0 } else { self.raw.sign }
    }

    /// Whether the sign bit is set (so also for -0).
    pub fn is_sign_negative(&self) -> bool {
        self.raw.sign < 0
    }

    /// The exponent `e` with `2^(e-1) <= |x| < 2^e` (for regular values).
    pub fn exponent(&self) -> i64 {
        self.raw.exp as i64
    }

    /// The decimal exponent `e` with `10^e <= |x| < 10^(e+1)` (for
    /// regular values).
    pub fn decimal_exponent(&self) -> i64 {
        self.digit_string(2, m::RNDZ).1 - 1
    }

    // ----- rounding and arithmetic ------------------------------------------

    pub fn round_to(&self, prec: u64) -> Real {
        let mut r = Real::alloc(prec);
        unsafe { m::mpfr_set(&mut r.raw, &self.raw, m::RNDN) };
        r
    }

    /// Both operands at the smaller of their precisions. Magma first
    /// rounds the more precise operand to the smaller precision.
    fn common<'a>(&'a self, o: &'a Real, tmp: &'a mut Option<Real>) -> (&'a Real, &'a Real, u64) {
        let p = self.prec().min(o.prec());
        if self.prec() > p {
            *tmp = Some(self.round_to(p));
            (tmp.as_ref().unwrap(), o, p)
        } else if o.prec() > p {
            *tmp = Some(o.round_to(p));
            (self, tmp.as_ref().unwrap(), p)
        } else {
            (self, o, p)
        }
    }

    /// A binary MPFR function at the smaller precision.
    pub fn binary(&self, o: &Real, f: m::Binary) -> Real {
        let mut tmp = None;
        let (a, b, p) = self.common(o, &mut tmp);
        let mut r = Real::alloc(p);
        unsafe { f(&mut r.raw, &a.raw, &b.raw, m::RNDN) };
        r
    }

    /// A unary MPFR function at the same precision.
    pub fn unary(&self, f: m::Unary) -> Real {
        let mut r = Real::alloc(self.prec());
        unsafe { f(&mut r.raw, &self.raw, m::RNDN) };
        r
    }

    pub fn add(&self, o: &Real) -> Real {
        self.binary(o, m::mpfr_add)
    }

    pub fn sub(&self, o: &Real) -> Real {
        self.binary(o, m::mpfr_sub)
    }

    pub fn mul(&self, o: &Real) -> Real {
        self.binary(o, m::mpfr_mul)
    }

    /// Division; `None` when dividing by zero (of either sign).
    pub fn div(&self, o: &Real) -> Option<Real> {
        (!o.is_zero()).then(|| self.binary(o, m::mpfr_div))
    }

    pub fn add_i64(&self, v: i64) -> Real {
        let mut r = Real::alloc(self.prec());
        unsafe { m::mpfr_add_si(&mut r.raw, &self.raw, v as c_long, m::RNDN) };
        r
    }

    pub fn mul_i64(&self, v: i64) -> Real {
        let mut r = Real::alloc(self.prec());
        unsafe { m::mpfr_mul_si(&mut r.raw, &self.raw, v as c_long, m::RNDN) };
        r
    }

    pub fn div_i64(&self, v: i64) -> Real {
        let mut r = Real::alloc(self.prec());
        unsafe { m::mpfr_div_si(&mut r.raw, &self.raw, v as c_long, m::RNDN) };
        r
    }

    /// `x·n` for an integer `n`, rounded once at the precision of `x`.
    pub fn mul_integer(&self, n: &Integer) -> Real {
        let y = Real::from_integer(n, n.bits().max(2));
        let mut r = Real::alloc(self.prec());
        unsafe { m::mpfr_mul(&mut r.raw, &self.raw, &y.raw, m::RNDN) };
        r
    }

    /// `x + n` for an integer `n`, rounded once at the precision of `x`.
    pub fn add_integer(&self, n: &Integer) -> Real {
        let y = Real::from_integer(n, n.bits().max(2));
        let mut r = Real::alloc(self.prec());
        unsafe { m::mpfr_add(&mut r.raw, &self.raw, &y.raw, m::RNDN) };
        r
    }

    /// `x·2^e`.
    pub fn mul_2exp(&self, e: i64) -> Real {
        let mut r = Real::alloc(self.prec());
        unsafe { m::mpfr_mul_2si(&mut r.raw, &self.raw, e as c_long, m::RNDN) };
        r
    }

    /// `a·b + c·d` (`sub`: `a·b - c·d`) with a single rounding, at the
    /// precision of `a`.
    pub fn fmma(a: &Real, b: &Real, c: &Real, d: &Real, sub: bool) -> Real {
        let mut r = Real::alloc(a.prec());
        let f = if sub { m::mpfr_fmms } else { m::mpfr_fmma };
        unsafe { f(&mut r.raw, &a.raw, &b.raw, &c.raw, &d.raw, m::RNDN) };
        r
    }

    pub fn neg(&self) -> Real {
        self.unary(m::mpfr_neg)
    }

    pub fn abs(&self) -> Real {
        self.unary(m::mpfr_abs)
    }

    pub fn sqr(&self) -> Real {
        self.unary(m::mpfr_sqr)
    }

    /// Square root (NaN for negative input; `sqrt(-0) = -0`).
    pub fn sqrt(&self) -> Real {
        self.unary(m::mpfr_sqrt)
    }

    /// The n-th root (`n > 0`).
    pub fn root(&self, n: u64) -> Real {
        let mut r = Real::alloc(self.prec());
        unsafe { m::mpfr_rootn_ui(&mut r.raw, &self.raw, n as _, m::RNDN) };
        r
    }

    /// `x^e`, correctly rounded (`0^e` is infinite for `e < 0`).
    pub fn pow_i64(&self, e: i64) -> Real {
        let mut r = Real::alloc(self.prec());
        unsafe { m::mpfr_pow_si(&mut r.raw, &self.raw, e as c_long, m::RNDN) };
        r
    }

    /// `x^e` for any integer `e`.
    pub fn pow_integer(&self, e: &Integer) -> Real {
        match e.to_i64() {
            Some(e) => self.pow_i64(e),
            None => {
                let y = Real::from_integer(e, e.bits().max(2));
                let mut r = Real::alloc(self.prec());
                unsafe { m::mpfr_pow(&mut r.raw, &self.raw, &y.raw, m::RNDN) };
                r
            }
        }
    }

    /// `x^y` (after reducing both to the smaller precision).
    pub fn pow(&self, y: &Real) -> Real {
        self.binary(y, m::mpfr_pow)
    }

    /// A constant (pi, Euler's constant, ...) at the given precision.
    pub fn constant(f: m::Constant, prec: u64) -> Real {
        let mut r = Real::alloc(prec);
        unsafe { f(&mut r.raw, m::RNDN) };
        r
    }

    /// `sin x` and `cos x`.
    pub fn sin_cos(&self) -> (Real, Real) {
        let mut s = Real::alloc(self.prec());
        let mut c = Real::alloc(self.prec());
        unsafe { m::mpfr_sin_cos(&mut s.raw, &mut c.raw, &self.raw, m::RNDN) };
        (s, c)
    }

    /// Round to an integral value with the given function (`mpfr_floor`,
    /// ...), then convert; 0 for NaN and infinities, as in Magma.
    fn to_int_with(&self, f: unsafe extern "C" fn(*mut Mpfr, *const Mpfr) -> c_int) -> Integer {
        if !self.is_finite() {
            return Integer::zero();
        }
        let mut r = Real::alloc(self.prec());
        unsafe { f(&mut r.raw, &self.raw) };
        r.to_integer().unwrap_or_default()
    }

    pub fn floor(&self) -> Integer {
        self.to_int_with(m::mpfr_floor)
    }

    pub fn ceil(&self) -> Integer {
        self.to_int_with(m::mpfr_ceil)
    }

    /// The nearest integer, halves rounded away from zero.
    pub fn round(&self) -> Integer {
        self.to_int_with(m::mpfr_round)
    }

    pub fn trunc(&self) -> Integer {
        self.to_int_with(m::mpfr_trunc)
    }

    /// Compare as Magma does: after rounding to the smaller precision, and
    /// with NaN comparing equal to everything (MPFR's `mpfr_cmp`).
    pub fn cmp_magma(&self, o: &Real) -> Ordering {
        let mut tmp = None;
        let (a, b, _) = self.common(o, &mut tmp);
        unsafe { m::mpfr_cmp(&a.raw, &b.raw) }.cmp(&0)
    }

    /// Compare absolute values exactly (NaN compares equal).
    pub fn cmp_abs(&self, o: &Real) -> Ordering {
        unsafe { m::mpfr_cmpabs(&self.raw, &o.raw) }.cmp(&0)
    }

    /// A hash of the value, the same for equal values of any precision.
    pub fn hash_u64(&self) -> u64 {
        let mut h = rustc_hash_like::Fx::default();
        if !self.is_regular() {
            h.write_u8(if self.is_zero() { 0 } else if self.is_nan() { 1 } else if self.raw.sign > 0 { 2 } else { 3 });
            return h.finish();
        }
        h.write_i32(self.raw.sign);
        h.write_i64(self.raw.exp as i64);
        let n = self.prec().div_ceil(64) as usize;
        // Least significant limb first; the low zero limbs depend on the
        // precision.
        let limbs = unsafe { std::slice::from_raw_parts(self.raw.d, n) };
        let start = limbs.iter().position(|&l| l != 0).unwrap_or(0);
        for &l in limbs[start..].iter().rev() {
            h.write_u64(l);
        }
        h.finish()
    }

    // ----- printing ------------------------------------------------------------

    /// `k` decimal digits of `|x|` (for regular `x`, `k >= 2`) rounded
    /// with `rnd`, and the exponent `e` with `|x| ≈ 0.d1d2...dk · 10^e`.
    fn digit_string(&self, k: usize, rnd: m::Rnd) -> (String, i64) {
        let mut exp: c_long = 0;
        let p = unsafe { m::mpfr_get_str(std::ptr::null_mut(), &mut exp, 10, k.max(2), &self.raw, rnd) };
        let s = unsafe { CStr::from_ptr(p) }.to_string_lossy().trim_start_matches('-').to_string();
        unsafe { m::mpfr_free_str(p) };
        (s, exp as i64)
    }

    /// `k >= 1` digits rounded to nearest. A single digit comes from
    /// rounding two digits half up, as Magma does (MPFR's `mpfr_get_str`
    /// used to need at least two digits).
    fn digits_rounded(&self, k: usize) -> (String, i64) {
        if k >= 2 {
            return self.digit_string(k, m::RNDN);
        }
        let (s, exp) = self.digit_string(2, m::RNDN);
        let b = s.as_bytes();
        if b[1] < b'5' {
            (s[..1].to_string(), exp)
        } else if b[0] == b'9' {
            ("1".to_string(), exp + 1)
        } else {
            (((b[0] + 1) as char).to_string(), exp)
        }
    }

    fn sign_str(&self) -> &'static str {
        if self.raw.sign < 0 { "-" } else { "" }
    }

    fn special_str(&self) -> Option<&'static str> {
        if self.is_nan() {
            Some("@NaN@")
        } else if self.is_inf() {
            Some(if self.raw.sign < 0 { "-@Inf@" } else { "@Inf@" })
        } else {
            None
        }
    }

    /// Magma's printing with `digits` significant digits (at least two):
    /// positional notation for decimal exponents from -4 to `digits - 1`,
    /// else `d.ddd...E<exponent>`; zeros keep their sign.
    pub fn format(&self, digits: u64) -> String {
        if let Some(s) = self.special_str() {
            return s.to_string();
        }
        let n = digits.max(2) as usize;
        if self.is_zero() {
            return format!("{}0.{}", self.sign_str(), "0".repeat(n));
        }
        let (s, exp) = self.digit_string(n, m::RNDN);
        let e = exp - 1;
        let body = if (-4..n as i64).contains(&e) {
            if e >= 0 {
                let (a, b) = s.split_at(e as usize + 1);
                format!("{a}.{b}")
            } else {
                format!("0.{}{s}", "0".repeat((-e - 1) as usize))
            }
        } else {
            format!("{}.{}E{e}", &s[..1], &s[1..])
        };
        format!("{}{body}", self.sign_str())
    }

    /// Magma's printing with `decimals` places (`printf "%.3o"`) of a real
    /// whose field has `digits` decimal digits of precision: positional
    /// with that many decimals when this shows a non-zero digit, else
    /// `d.ddd...E<exponent>` with `decimals + 1` significant digits;
    /// numbers beyond the precision of the field print like `%#g` with
    /// `decimals + 1` significant digits.
    pub fn format_decimals(&self, decimals: usize, digits: u64) -> String {
        if let Some(s) = self.special_str() {
            return s.to_string();
        }
        let sign = self.sign_str();
        if self.is_zero() {
            // Magma drops the sign of -0 with no decimals.
            return if decimals == 0 { "0.".to_string() } else { format!("{sign}0.{}", "0".repeat(decimals)) };
        }
        let e0 = self.decimal_exponent();
        let n = decimals as i64;
        let beyond = e0 >= digits as i64;
        let k = if beyond { n + 1 } else { (e0 + 1 + n).max(1) };
        let (s, exp) = self.digits_rounded(k as usize);
        let len = s.len() as i64;
        let fixed = if exp > 0 { exp <= len && (beyond || len - exp <= n) } else { !beyond && len - exp <= n };
        if !fixed {
            let (s, exp) = self.digits_rounded(decimals + 1);
            return format!("{sign}{}.{}E{}", &s[..1], &s[1..], exp - 1);
        }
        let (int, frac) = if exp > 0 { (s[..exp as usize].to_string(), s[exp as usize..].to_string()) } else { ("0".to_string(), format!("{}{s}", "0".repeat((-exp) as usize))) };
        let pad = if beyond { 0 } else { decimals.saturating_sub(frac.len()) };
        format!("{sign}{int}.{frac}{}", "0".repeat(pad))
    }

    /// Format with a fixed number of decimals after the point (for
    /// timings), correctly rounded.
    pub fn to_string_fixed(&self, decimals: usize) -> String {
        let Some(q) = self.to_rational() else { return self.format(2) };
        let scale = Integer::from_i64(10).pow(decimals as u64);
        let scaled = (&q * &Rational::from_integer(&scale)).round();
        let s = scaled.abs().to_string();
        let s = if s.len() <= decimals { format!("{}{}", "0".repeat(decimals + 1 - s.len()), s) } else { s };
        let (a, b) = s.split_at(s.len() - decimals);
        let body = if decimals == 0 { a.to_string() } else { format!("{a}.{b}") };
        if scaled.sign() < 0 { format!("-{body}") } else { body }
    }
}

/// A small Fx-style hasher (to avoid a dependency here).
mod rustc_hash_like {
    #[derive(Default)]
    pub struct Fx(u64);

    impl std::hash::Hasher for Fx {
        fn finish(&self) -> u64 {
            self.0
        }

        fn write(&mut self, bytes: &[u8]) {
            for &b in bytes {
                self.write_u64(b as u64);
            }
        }

        fn write_u64(&mut self, x: u64) {
            self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
        }
    }
}

/// Parse a decimal literal exactly.
pub fn parse_decimal(s: &str) -> Option<Rational> {
    let s = s.trim();
    let (neg, s) = match s.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, s.strip_prefix('+').unwrap_or(s)),
    };
    let (mant, exp) = match s.find(['e', 'E']) {
        Some(i) => (&s[..i], s[i + 1..].parse::<i64>().ok()?),
        None => (s, 0),
    };
    let (int_part, frac_part) = match mant.find('.') {
        Some(i) => (&mant[..i], &mant[i + 1..]),
        None => (mant, ""),
    };
    if int_part.is_empty() && frac_part.is_empty() {
        return None;
    }
    let digits = format!("{int_part}{frac_part}");
    let mut n = Integer::parse(if digits.is_empty() { "0" } else { &digits })?;
    if neg {
        n = -n;
    }
    let e = exp - frac_part.len() as i64;
    let ten = Integer::from_i64(10);
    if e >= 0 {
        Some(Rational::from_integer(&(&n * &ten.pow(e as u64))))
    } else {
        Rational::new(&n, &ten.pow((-e) as u64))
    }
}

impl Drop for Real {
    fn drop(&mut self) {
        unsafe { m::mpfr_clear(&mut self.raw) };
    }
}

impl Clone for Real {
    fn clone(&self) -> Self {
        let mut r = Real::alloc(self.prec());
        unsafe { m::mpfr_set(&mut r.raw, &self.raw, m::RNDN) };
        r
    }
}

/// Structural equality: equal values of any precision (with `-0 = 0`), and
/// NaN equal only to NaN.
impl PartialEq for Real {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Real {}

impl PartialOrd for Real {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// A total order: NaN first, then the numbers in order.
impl Ord for Real {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.is_nan(), other.is_nan()) {
            (true, true) => Ordering::Equal,
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            _ => unsafe { m::mpfr_cmp(&self.raw, &other.raw) }.cmp(&0),
        }
    }
}

impl fmt::Debug for Real {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.format(self.digits()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(s: &str, digits: u64) -> Real {
        Real::parse(s, bits_for_digits(digits)).unwrap()
    }

    #[test]
    fn precisions() {
        let bits: Vec<u64> = (1..=12).map(bits_for_digits).collect();
        assert_eq!(bits, [4, 7, 10, 14, 17, 20, 24, 27, 30, 34, 37, 40]);
        assert_eq!(bits_for_digits(30), 100);
        assert_eq!(bits_for_digits(100), 333);
        for (b, d) in [(2, 0), (3, 0), (4, 1), (10, 3), (33, 9), (34, 10), (35, 10), (53, 15), (64, 19), (100, 30)] {
            assert_eq!(digits_for_bits(b), d);
        }
        for d in 1..2000 {
            assert_eq!(digits_for_bits(bits_for_digits(d)), d);
        }
    }

    #[test]
    fn printing() {
        assert_eq!(lit("1.5", 30).format(30), "1.50000000000000000000000000000");
        assert_eq!(lit("0.0001", 30).format(30), "0.000100000000000000000000000000000");
        assert_eq!(lit("1e-5", 30).format(30), "1.00000000000000000000000000000E-5");
        assert_eq!(lit("1e29", 30).format(30), "100000000000000000000000000000.");
        assert_eq!(lit("1e30", 30).format(30), "1.00000000000000000000000000000E30");
        assert_eq!(Real::from_rational(&Rational::new(&Integer::from_i64(2), &Integer::from_i64(3)).unwrap(), 100).format(30), "0.666666666666666666666666666667");
        assert_eq!(lit("99999.5", 5).format(5), "1.0000E5");
        assert_eq!(lit("0.00009999951", 5).format(5), "0.00010000");
        assert_eq!(lit("123", 5).format(5), "123.00");
        assert_eq!(Real::signed_zero(34, true).format(10), "-0.0000000000");
        assert_eq!(Real::from_i64(123, 2).format(0), "1.3E2");
        assert_eq!(Real::from_i64(3, 2).format(0), "3.0");
        assert_eq!(Real::nan(100).format(30), "@NaN@");
        assert_eq!(Real::infinity(100, true).format(30), "-@Inf@");
        let two = Real::from_i64(2, bits_for_digits(20));
        assert_eq!(two.sqrt().format(20), "1.4142135623730950488");
        assert_eq!(lit("53.2114", 30).to_string_fixed(3), "53.211");
        assert_eq!(lit("0.07", 30).to_string_fixed(3), "0.070");
    }

    #[test]
    fn printing_decimals() {
        let f = |s: &str, n: usize| lit(s, 30).format_decimals(n, 30);
        assert_eq!(f("123.456", 3), "123.456");
        assert_eq!(f("123.456", 1), "123.5");
        assert_eq!(f("123.456", 0), "123.");
        assert_eq!(f("123.456", 40), "123.4559999999999999999999999999846519222280");
        assert_eq!(f("1e-10", 3), "1.000E-10");
        assert_eq!(f("1e40", 3), "1.000E40");
        assert_eq!(f("-0.0005", 3), "-5.000E-4");
        let z = Real::zero(100).neg();
        assert_eq!((z.format_decimals(0, 30), z.format_decimals(1, 30), f("-0.4", 0)), ("0.".to_string(), "-0.0".to_string(), "-4.E-1".to_string()));
        assert_eq!(f("0.0015", 3), "0.002");
        assert_eq!(f("0.125", 2), "0.12");
        assert_eq!(f("0.9999999", 3), "1.000");
        assert_eq!(f("0.00099999999", 3), "0.001");
        assert_eq!(f("9.96", 1), "10.0");
        assert_eq!(f("0.00996", 1), "1.0E-2");
        assert_eq!(f("0.0996", 1), "0.1");
        for (s, want) in [("0.000951", "0.001"), ("0.00095", "0.001"), ("0.000949", "0.001"), ("0.00099", "0.001"), ("0.0009", "9.000E-4")] {
            assert_eq!(f(s, 3), want);
        }
        for (s, want) in [("0.951", "1."), ("0.5", "5.E-1"), ("0.49", "5.E-1"), ("9.5", "1.E1"), ("99.5", "1.E2")] {
            assert_eq!(f(s, 0), want);
        }
        for (s, want) in [("0.00951", "0.01"), ("0.00499", "4.99E-3"), ("0.005", "5.00E-3"), ("1.23456789e-3", "1.23E-3")] {
            assert_eq!(f(s, 2), want);
        }
        assert_eq!(f("1.23456789e30", 8), "1.23456789E30");
        assert_eq!(f("1.23456789e29", 0), "123456789000000000000000000000.");
        // y*10^e in a field of 10 digits, as computed there.
        let g = |e: u64, n: usize| lit("1.23456789", 10).mul(&Real::from_integer(&Integer::from_i64(10).pow(e), 34)).format_decimals(n, 10);
        assert_eq!(g(10, 12), "12345678899.00");
        assert_eq!(g(12, 12), "1234567889920.");
        assert_eq!(g(10, 5), "1.23457E10");
        assert_eq!(g(9, 12), "1234567890.000000000000");
        assert_eq!(g(5, 12), "123456.788993835449");
    }

    #[test]
    fn semantics() {
        let a = lit("0.333333333333333333333333333333333", 10);
        let b = lit("0.333333333333333333333333333333333", 30);
        assert_eq!(a.sub(&b).format(10), "0.0000000000");
        assert_eq!(a.cmp_magma(&b), Ordering::Equal);
        let z = Real::zero(100);
        assert_eq!(z.neg().format(30), "-0.000000000000000000000000000000");
        assert!(z.neg() == z);
        assert_eq!(Real::from_i64(-1, 100).sqrt().format(30), "@NaN@");
        assert_eq!(lit("2.5", 30).round().to_i64(), Some(3));
        assert_eq!(lit("-2.5", 30).round().to_i64(), Some(-3));
        assert_eq!(lit("-2.5", 30).floor().to_i64(), Some(-3));
        assert_eq!(Real::infinity(100, false).floor().to_i64(), Some(0));
        let (mant, e) = lit("1.5", 10).mantissa_exponent();
        assert_eq!((mant.to_i64(), e), (Some(3 << 32), -33));
        assert_eq!(lit("1.5", 10).hash_u64(), lit("1.5", 30).hash_u64());
    }
}
