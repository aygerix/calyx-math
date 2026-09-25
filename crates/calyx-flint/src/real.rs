use std::cmp::Ordering;
use std::fmt;

use flint3_sys as sys;

use crate::{Integer, Rational};

const RND: sys::arf_rnd_t = sys::arf_rnd_t_ARF_RND_NEAR;

/// An arbitrary-precision binary floating-point number (FLINT `arf`),
/// carrying the working precision in bits.
pub struct Real {
    raw: sys::arf_struct,
    prec: u64,
}

/// Bits needed for `digits` decimal digits.
pub fn bits_for_digits(digits: u64) -> u64 {
    ((digits as f64) * std::f64::consts::LOG2_10).ceil() as u64 + 4
}

impl Real {
    /// Pointer to the underlying FLINT value (for other wrappers in this crate).
    pub(crate) fn raw_ptr(&self) -> *const sys::arf_struct {
        &self.raw
    }

    pub(crate) fn raw_mut_ptr(&mut self) -> *mut sys::arf_struct {
        &mut self.raw
    }

    pub fn zero(prec: u64) -> Real {
        let mut raw: sys::arf_struct = unsafe { std::mem::zeroed() };
        unsafe { sys::arf_init(&mut raw) };
        Real { raw, prec }
    }

    pub fn prec(&self) -> u64 {
        self.prec
    }

    pub fn from_integer(n: &Integer, prec: u64) -> Real {
        let mut r = Real::zero(prec);
        unsafe { sys::arf_set_round_fmpz(&mut r.raw, n.as_raw(), prec as sys::slong, RND) };
        r
    }

    pub fn from_rational(q: &Rational, prec: u64) -> Real {
        let mut r = Real::zero(prec);
        let num = q.numerator();
        let den = q.denominator();
        let mut fq = sys::fmpq { num: 0, den: 1 };
        unsafe {
            sys::fmpz_set(&mut fq.num, num.as_raw());
            sys::fmpz_set(&mut fq.den, den.as_raw());
            sys::arf_set_fmpq(&mut r.raw, &fq, prec as sys::slong, RND);
            sys::fmpq_clear(&mut fq);
        }
        r
    }

    pub fn from_f64(d: f64, prec: u64) -> Real {
        let mut r = Real::zero(prec);
        unsafe { sys::arf_set_d(&mut r.raw, d) };
        r
    }

    /// Parse a decimal literal such as `1.25`, `-3e-4` or `2.5E10`.
    pub fn parse(s: &str, prec: u64) -> Option<Real> {
        Some(Real::from_rational(&parse_decimal(s)?, prec))
    }

    /// The exact value, if finite.
    pub fn to_rational(&self) -> Option<Rational> {
        if unsafe { sys::arf_is_finite(&self.raw) } == 0 {
            return None;
        }
        let mut fq = sys::fmpq { num: 0, den: 1 };
        unsafe { sys::arf_get_fmpq(&mut fq, &self.raw) };
        let mut n = Integer::zero();
        let mut d = Integer::zero();
        unsafe {
            sys::fmpz_set(n.as_raw_mut(), &fq.num);
            sys::fmpz_set(d.as_raw_mut(), &fq.den);
            sys::fmpq_clear(&mut fq);
        }
        Rational::new(&n, &d)
    }

    pub fn to_f64(&self) -> f64 {
        unsafe { sys::arf_get_d(&self.raw, RND) }
    }

    pub fn is_zero(&self) -> bool {
        unsafe { sys::arf_is_zero(&self.raw) != 0 }
    }

    pub fn sign(&self) -> i32 {
        unsafe { sys::arf_sgn(&self.raw) }
    }

    fn with_prec(&self, prec: u64) -> Real {
        let mut r = Real::zero(prec);
        unsafe { sys::arf_set_round(&mut r.raw, &self.raw, prec as sys::slong, RND) };
        r
    }

    pub fn round_to(&self, prec: u64) -> Real {
        self.with_prec(prec)
    }

    pub fn add(&self, o: &Real) -> Real {
        let prec = self.prec.min(o.prec);
        let mut r = Real::zero(prec);
        unsafe { sys::arf_add(&mut r.raw, &self.raw, &o.raw, prec as sys::slong, RND) };
        r
    }

    pub fn sub(&self, o: &Real) -> Real {
        let prec = self.prec.min(o.prec);
        let mut r = Real::zero(prec);
        unsafe { sys::arf_sub(&mut r.raw, &self.raw, &o.raw, prec as sys::slong, RND) };
        r
    }

    pub fn mul(&self, o: &Real) -> Real {
        let prec = self.prec.min(o.prec);
        let mut r = Real::zero(prec);
        unsafe { sys::arf_mul_rnd_any(&mut r.raw, &self.raw, &o.raw, prec as sys::slong, RND) };
        r
    }

    /// Division; `None` when dividing by zero.
    pub fn div(&self, o: &Real) -> Option<Real> {
        if o.is_zero() {
            return None;
        }
        let prec = self.prec.min(o.prec);
        let mut r = Real::zero(prec);
        unsafe { sys::arf_div(&mut r.raw, &self.raw, &o.raw, prec as sys::slong, RND) };
        Some(r)
    }

    pub fn neg(&self) -> Real {
        let mut r = Real::zero(self.prec);
        unsafe { sys::arf_neg(&mut r.raw, &self.raw) };
        r
    }

    pub fn abs(&self) -> Real {
        if self.sign() < 0 { self.neg() } else { self.clone() }
    }

    /// Square root; `None` for negative input.
    pub fn sqrt(&self) -> Option<Real> {
        if self.sign() < 0 {
            return None;
        }
        let mut r = Real::zero(self.prec);
        unsafe { sys::arf_sqrt(&mut r.raw, &self.raw, self.prec as sys::slong, RND) };
        Some(r)
    }

    /// Integer power by repeated squaring; `None` for `0^e`, `e < 0`.
    pub fn pow(&self, e: i64) -> Option<Real> {
        if e < 0 {
            return Real::from_integer(&Integer::one(), self.prec).div(&self.pow(-e)?);
        }
        let work = self.with_prec(self.prec + 64);
        let mut result = Real::from_integer(&Integer::one(), self.prec + 64);
        let mut base = work;
        let mut e = e as u64;
        while e > 0 {
            if e & 1 == 1 {
                result = result.mul(&base);
            }
            base = base.mul(&base);
            e >>= 1;
        }
        Some(result.with_prec(self.prec))
    }

    pub fn floor(&self) -> Integer {
        self.to_rational().map(|q| q.floor()).unwrap_or_default()
    }

    pub fn ceil(&self) -> Integer {
        self.to_rational().map(|q| q.ceil()).unwrap_or_default()
    }

    pub fn round(&self) -> Integer {
        self.to_rational().map(|q| q.round()).unwrap_or_default()
    }

    pub fn trunc(&self) -> Integer {
        self.to_rational().map(|q| q.trunc()).unwrap_or_default()
    }

    /// Decimal digits of precision.
    pub fn digits(&self) -> u64 {
        ((self.prec.saturating_sub(4)) as f64 / std::f64::consts::LOG2_10).floor().max(1.0) as u64
    }

    /// Format with `digits` significant digits, switching to `E` notation
    /// for very large or very small magnitudes.
    pub fn to_string_digits(&self, digits: u64) -> String {
        let digits = digits.max(1) as usize;
        let Some(q) = self.to_rational() else { return "NaN".to_string() };
        if q.is_zero() {
            return format!("0.{}", "0".repeat(digits));
        }
        let neg = q.sign() < 0;
        let q = q.abs();
        let (mantissa, e) = sig_digits(&q, digits);
        let s = mantissa.to_string();
        let body = if e >= -4 && e < digits as i64 {
            if e >= 0 {
                let e = e as usize;
                let (a, b) = s.split_at(e + 1);
                if b.is_empty() { format!("{a}.") } else { format!("{a}.{b}") }
            } else {
                format!("0.{}{}", "0".repeat((-e - 1) as usize), s)
            }
        } else {
            let (a, b) = s.split_at(1);
            format!("{a}.{b}E{e}")
        };
        if neg { format!("-{body}") } else { body }
    }

    /// Format with a fixed number of decimals after the point.
    pub fn to_string_fixed(&self, decimals: usize) -> String {
        let Some(q) = self.to_rational() else { return "NaN".to_string() };
        let scale = Integer::from_i64(10).pow(decimals as u64);
        let scaled = (&q * &Rational::from_integer(&scale)).round();
        let neg = scaled.sign() < 0 || (scaled.is_zero() && q.sign() < 0 && false);
        let s = scaled.abs().to_string();
        let s = if s.len() <= decimals { format!("{}{}", "0".repeat(decimals + 1 - s.len()), s) } else { s };
        let (a, b) = s.split_at(s.len() - decimals);
        let body = if decimals == 0 { a.to_string() } else { format!("{a}.{b}") };
        if neg { format!("-{body}") } else { body }
    }
}

/// The `digits` leading decimal digits of `q > 0` (rounded) and the decimal
/// exponent of the leading digit.
fn sig_digits(q: &Rational, digits: usize) -> (Integer, i64) {
    let ten = Integer::from_i64(10);
    let mut e = q.to_f64().log10().floor() as i64;
    // Correct the estimate so that 10^e <= q < 10^(e+1).
    let pow10 = |k: i64| -> Rational {
        if k >= 0 {
            Rational::from_integer(&ten.pow(k as u64))
        } else {
            Rational::new(&Integer::one(), &ten.pow((-k) as u64)).unwrap()
        }
    };
    loop {
        if *q < pow10(e) {
            e -= 1;
        } else if *q >= pow10(e + 1) {
            e += 1;
        } else {
            break;
        }
    }
    let shift = digits as i64 - 1 - e;
    let scaled = (q * &pow10(shift)).round();
    if scaled >= ten.pow(digits as u64) {
        let scaled = (q * &pow10(shift - 1)).round();
        return (scaled, e + 1);
    }
    (scaled, e)
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
        unsafe { sys::arf_clear(&mut self.raw) };
    }
}

impl Clone for Real {
    fn clone(&self) -> Self {
        let mut r = Real::zero(self.prec);
        unsafe { sys::arf_set(&mut r.raw, &self.raw) };
        r
    }
}

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

impl Ord for Real {
    fn cmp(&self, other: &Self) -> Ordering {
        unsafe { sys::arf_cmp(&self.raw, &other.raw) }.cmp(&0)
    }
}

impl fmt::Debug for Real {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string_digits(self.digits()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn printing() {
        let p = bits_for_digits(30);
        let x = Real::parse("1.5", p).unwrap();
        assert_eq!(x.to_string_digits(30), "1.50000000000000000000000000000");
        let y = Real::parse("-0.00123", p).unwrap();
        assert_eq!(y.to_string_digits(5), "-0.0012300");
        let z = Real::parse("1e40", p).unwrap();
        assert_eq!(z.to_string_digits(5), "1.0000E40");
        let two = Real::from_integer(&Integer::from_i64(2), p);
        assert_eq!(two.sqrt().unwrap().to_string_digits(20), "1.4142135623730950488");
        assert_eq!(Real::parse("53.2114", p).unwrap().to_string_fixed(3), "53.211");
        assert_eq!(Real::parse("0.07", p).unwrap().to_string_fixed(3), "0.070");
    }
}
