use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops;

use flint3_sys as sys;

use crate::Integer;

/// An arbitrary-precision rational number backed by FLINT's `fmpq`.
///
/// Values are always kept in canonical form: the denominator is positive and
/// coprime to the numerator.
pub struct Rational {
    raw: sys::fmpq,
}

impl Rational {
    /// Pointer to the underlying FLINT value (for other wrappers in this crate).
    pub(crate) fn raw_ptr(&self) -> *const sys::fmpq {
        &self.raw
    }

    pub(crate) fn raw_mut_ptr(&mut self) -> *mut sys::fmpq {
        &mut self.raw
    }

    #[inline]
    pub fn zero() -> Self {
        Rational { raw: sys::fmpq { num: 0, den: 1 } }
    }

    pub fn one() -> Self {
        Rational::from_integer(&Integer::one())
    }

    pub fn from_integer(n: &Integer) -> Self {
        let mut q = Rational::zero();
        unsafe { sys::fmpz_set(&mut q.raw.num, n.as_raw()) };
        q
    }

    pub fn from_i64(n: i64) -> Self {
        Rational::from_integer(&Integer::from_i64(n))
    }

    /// `num / den` in lowest terms, or `None` if `den` is zero.
    pub fn new(num: &Integer, den: &Integer) -> Option<Self> {
        if den.is_zero() {
            return None;
        }
        let mut q = Rational::zero();
        unsafe { sys::fmpq_set_fmpz_frac(&mut q.raw, num.as_raw(), den.as_raw()) };
        Some(q)
    }

    /// Parse `a` or `a/b` in base 10.
    pub fn parse(s: &str) -> Option<Self> {
        match s.split_once('/') {
            Some((n, d)) => Rational::new(&Integer::parse(n)?, &Integer::parse(d)?),
            None => Some(Rational::from_integer(&Integer::parse(s)?)),
        }
    }

    pub fn numerator(&self) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_set(z.as_raw_mut(), &self.raw.num) };
        z
    }

    pub fn denominator(&self) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_set(z.as_raw_mut(), &self.raw.den) };
        z
    }

    #[inline]
    pub fn is_integral(&self) -> bool {
        self.raw.den == 1
    }

    #[inline]
    pub fn is_zero(&self) -> bool {
        self.raw.num == 0
    }

    pub fn is_one(&self) -> bool {
        self.raw.num == 1 && self.raw.den == 1
    }

    pub fn sign(&self) -> i32 {
        unsafe { sys::fmpq_sgn(&self.raw) }
    }

    pub fn abs(&self) -> Self {
        let mut q = Rational::zero();
        unsafe { sys::fmpq_abs(&mut q.raw, &self.raw) };
        q
    }

    /// Multiplicative inverse, `None` for zero.
    pub fn inv(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }
        let mut q = Rational::zero();
        unsafe { sys::fmpq_inv(&mut q.raw, &self.raw) };
        Some(q)
    }

    /// Division, `None` when dividing by zero.
    pub fn checked_div(&self, rhs: &Rational) -> Option<Self> {
        if rhs.is_zero() {
            return None;
        }
        let mut q = Rational::zero();
        unsafe { sys::fmpq_div(&mut q.raw, &self.raw, &rhs.raw) };
        Some(q)
    }

    /// `self^e`; `None` for `0^e` with `e < 0`.
    pub fn pow(&self, e: i64) -> Option<Self> {
        if e < 0 && self.is_zero() {
            return None;
        }
        let mut q = Rational::zero();
        unsafe { sys::fmpq_pow_si(&mut q.raw, &self.raw, e as sys::slong) };
        Some(q)
    }

    pub fn floor(&self) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_fdiv_q(z.as_raw_mut(), &self.raw.num, &self.raw.den) };
        z
    }

    pub fn ceil(&self) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_cdiv_q(z.as_raw_mut(), &self.raw.num, &self.raw.den) };
        z
    }

    /// Truncation toward zero.
    pub fn trunc(&self) -> Integer {
        let mut z = Integer::zero();
        unsafe { sys::fmpz_tdiv_q(z.as_raw_mut(), &self.raw.num, &self.raw.den) };
        z
    }

    /// Nearest integer, with halves rounded away from zero.
    pub fn round(&self) -> Integer {
        let half = Rational::new(&Integer::one(), &Integer::from_i64(2)).unwrap();
        if self.sign() >= 0 { (self + &half).floor() } else { (self - &half).ceil() }
    }

    pub fn to_f64(&self) -> f64 {
        unsafe { sys::fmpq_get_d(&self.raw) }
    }

    /// The fraction `n/d` with `|n| <= bound`, `0 < d <= bound` and
    /// `n = a*d (mod m)`, if there is one. Requires `2*bound^2 < m`, which
    /// makes it unique.
    pub fn reconstruct(a: &Integer, m: &Integer, bound: &Integer) -> Option<Self> {
        let a = a.div_rem_euclid(m)?.1;
        let mut q = Rational::zero();
        let found = unsafe { sys::fmpq_reconstruct_fmpz_2(&mut q.raw, a.as_raw(), m.as_raw(), bound.as_raw(), bound.as_raw()) };
        if found != 0 { Some(q) } else { None }
    }

    pub fn to_string_radix(&self, radix: u32) -> String {
        if self.is_integral() {
            return self.numerator().to_string_radix(radix);
        }
        format!(
            "{}/{}",
            self.numerator().to_string_radix(radix),
            self.denominator().to_string_radix(radix)
        )
    }

    pub fn hash_u64(&self) -> u64 {
        let n = self.numerator().hash_u64();
        if self.is_integral() {
            return n;
        }
        n.rotate_left(17) ^ self.denominator().hash_u64().wrapping_mul(0x9e3779b97f4a7c15)
    }
}

impl Drop for Rational {
    fn drop(&mut self) {
        unsafe { sys::fmpq_clear(&mut self.raw) };
    }
}

impl Clone for Rational {
    fn clone(&self) -> Self {
        let mut q = Rational::zero();
        unsafe { sys::fmpq_set(&mut q.raw, &self.raw) };
        q
    }
}

impl Default for Rational {
    fn default() -> Self {
        Rational::zero()
    }
}

impl PartialEq for Rational {
    fn eq(&self, other: &Self) -> bool {
        unsafe { sys::fmpq_equal(&self.raw, &other.raw) != 0 }
    }
}

impl Eq for Rational {}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Self) -> Ordering {
        unsafe { sys::fmpq_cmp(&self.raw, &other.raw) }.cmp(&0)
    }
}

impl Hash for Rational {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash_u64());
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_string_radix(10))
    }
}

impl fmt::Debug for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_string_radix(10))
    }
}

impl From<&Integer> for Rational {
    fn from(n: &Integer) -> Self {
        Rational::from_integer(n)
    }
}

macro_rules! binop {
    ($trait:ident, $method:ident, $ffi:ident) => {
        impl ops::$trait<&Rational> for &Rational {
            type Output = Rational;
            fn $method(self, rhs: &Rational) -> Rational {
                let mut q = Rational::zero();
                unsafe { sys::$ffi(&mut q.raw, &self.raw, &rhs.raw) };
                q
            }
        }
        impl ops::$trait<Rational> for Rational {
            type Output = Rational;
            fn $method(self, rhs: Rational) -> Rational {
                (&self).$method(&rhs)
            }
        }
    };
}

binop!(Add, add, fmpq_add);
binop!(Sub, sub, fmpq_sub);
binop!(Mul, mul, fmpq_mul);

impl ops::Neg for &Rational {
    type Output = Rational;
    fn neg(self) -> Rational {
        let mut q = Rational::zero();
        unsafe { sys::fmpq_neg(&mut q.raw, &self.raw) };
        q
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_form_and_ops() {
        let a = Rational::new(&Integer::from_i64(6), &Integer::from_i64(-4)).unwrap();
        assert_eq!(a.to_string(), "-3/2");
        let b = Rational::parse("1/3").unwrap();
        assert_eq!((&a + &b).to_string(), "-7/6");
        assert_eq!((&a * &b).to_string(), "-1/2");
        assert_eq!(a.checked_div(&b).unwrap().to_string(), "-9/2");
        assert_eq!(a.floor().to_i64(), Some(-2));
        assert_eq!(a.ceil().to_i64(), Some(-1));
        assert_eq!(a.round().to_i64(), Some(-2));
        assert_eq!(b.pow(-2).unwrap().to_string(), "9");
        assert!(Rational::new(&Integer::one(), &Integer::zero()).is_none());
        assert_eq!(Rational::parse("4/2").unwrap().hash_u64(), Integer::from_i64(2).hash_u64());
    }
}
