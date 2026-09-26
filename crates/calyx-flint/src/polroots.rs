//! Roots of polynomials with Gaussian integer coefficients, each part rounded
//! to nearest at a given precision (as MPFR rounds the exact value).
//!
//! An exact squarefree factorisation gives the multiplicities. FLINT
//! isolates the roots of each factor in disjoint balls, which are refined at
//! increasing precision until every part of every root rounds unambiguously
//! (Ziv's strategy). A part that is exactly zero, or exactly halfway between
//! two numbers of the target precision, never does: it is recognised
//! exactly instead, from the roots of the factor on the line where that part
//! has that value (`Lines`).

use std::cell::UnsafeCell;
use std::cmp::Ordering;

use flint3_sys as sys;

use crate::ball::{precisions, round_ball};
use crate::mpfr as m;
use crate::{Complex, Integer, Rational, Real};

/// An integer polynomial.
struct ZPoly(sys::fmpz_poly_struct);

impl ZPoly {
    fn new() -> ZPoly {
        let mut p = sys::fmpz_poly_struct::default();
        unsafe { sys::fmpz_poly_init(&mut p) };
        ZPoly(p)
    }

    fn from_coeffs(cs: &[Integer]) -> ZPoly {
        let mut p = ZPoly::new();
        for (i, c) in cs.iter().enumerate() {
            unsafe { sys::fmpz_poly_set_coeff_fmpz(&mut p.0, i as sys::slong, c.raw_ptr()) };
        }
        p
    }

    fn len(&self) -> usize {
        self.0.length as usize
    }

    fn coeff(&self, i: usize) -> Integer {
        let mut c = Integer::zero();
        unsafe { sys::fmpz_poly_get_coeff_fmpz(c.raw_mut_ptr(), &self.0, i as sys::slong) };
        c
    }

    /// `a·self + b·other`.
    fn combine(&self, a: &Integer, other: &ZPoly, b: &Integer) -> ZPoly {
        let (mut x, mut y) = (ZPoly::new(), ZPoly::new());
        unsafe {
            sys::fmpz_poly_scalar_mul_fmpz(&mut x.0, &self.0, a.raw_ptr());
            sys::fmpz_poly_scalar_mul_fmpz(&mut y.0, &other.0, b.raw_ptr());
            sys::fmpz_poly_add(&mut x.0, &x.0, &y.0);
        }
        x
    }

    /// The squarefree part (up to a constant).
    fn squarefree_part(&self) -> ZPoly {
        let (mut d, mut g, mut q) = (ZPoly::new(), ZPoly::new(), ZPoly::new());
        unsafe {
            sys::fmpz_poly_derivative(&mut d.0, &self.0);
            sys::fmpz_poly_gcd(&mut g.0, &self.0, &d.0);
            sys::fmpz_poly_divexact(&mut q.0, &self.0, &g.0);
        }
        q
    }

    /// Whether the rational `b` is a root.
    fn vanishes_at(&self, b: &Rational) -> bool {
        let mut v = Rational::zero();
        unsafe { sys::fmpz_poly_evaluate_fmpq(v.raw_mut_ptr(), &self.0, b.raw_ptr()) };
        v.is_zero()
    }
}

impl Clone for ZPoly {
    fn clone(&self) -> ZPoly {
        let mut p = ZPoly::new();
        unsafe { sys::fmpz_poly_set(&mut p.0, &self.0) };
        p
    }
}

impl Drop for ZPoly {
    fn drop(&mut self) {
        unsafe { sys::fmpz_poly_clear(&mut self.0) };
    }
}

/// A polynomial with Gaussian integer coefficients `re + i·im`.
#[derive(Clone)]
struct GPoly {
    re: ZPoly,
    im: ZPoly,
}

impl GPoly {
    fn len(&self) -> usize {
        self.re.len().max(self.im.len())
    }

    fn is_real(&self) -> bool {
        self.im.len() == 0
    }

    /// The product with `l0 + l1·y` for Gaussian integers `l0`, `l1`.
    fn mul_linear(&self, l0: [&Integer; 2], l1: [&Integer; 2]) -> GPoly {
        let part = |a: [&Integer; 2], b: [&Integer; 2]| {
            let mut hi = self.re.combine(b[0], &self.im, b[1]);
            let lo = self.re.combine(a[0], &self.im, a[1]);
            unsafe {
                sys::fmpz_poly_shift_left(&mut hi.0, &hi.0, 1);
                sys::fmpz_poly_add(&mut hi.0, &hi.0, &lo.0);
            }
            hi
        };
        let (n0, n1) = (-l0[1], -l1[1]);
        GPoly { re: part([l0[0], &n0], [l1[0], &n1]), im: part([l0[1], l0[0]], [l1[1], l1[0]]) }
    }

    fn add_constant(&mut self, re: &Integer, im: &Integer) {
        for (p, c) in [(&mut self.re, re), (&mut self.im, im)] {
            let c = &p.coeff(0) + c;
            unsafe { sys::fmpz_poly_set_coeff_fmpz(&mut p.0, 0, c.raw_ptr()) };
        }
    }
}

/// The Gaussian rationals as a FLINT generic ring, for exact gcds.
struct Qi {
    q: Box<UnsafeCell<sys::gr_ctx_struct>>,
    c: Box<UnsafeCell<sys::gr_ctx_struct>>,
}

impl Qi {
    fn new() -> Qi {
        let q = Box::new(UnsafeCell::new(sys::gr_ctx_struct::default()));
        let c = Box::new(UnsafeCell::new(sys::gr_ctx_struct::default()));
        unsafe {
            sys::gr_ctx_init_fmpq(q.get());
            sys::gr_ctx_init_gr_complex(c.get(), q.get());
            assert_eq!((*c.get()).sizeof_elem as usize, 2 * std::mem::size_of::<sys::fmpq>());
        }
        Qi { q, c }
    }

    fn ctx(&self) -> *mut sys::gr_ctx_struct {
        self.c.get()
    }
}

impl Drop for Qi {
    fn drop(&mut self) {
        unsafe {
            sys::gr_ctx_clear(self.c.get());
            sys::gr_ctx_clear(self.q.get());
        }
    }
}

/// A polynomial over `Qi`; the operations fail only if FLINT does.
struct QiPoly<'a> {
    p: sys::gr_poly_struct,
    qi: &'a Qi,
}

impl<'a> QiPoly<'a> {
    fn new(qi: &'a Qi) -> QiPoly<'a> {
        let mut p = sys::gr_poly_struct::default();
        unsafe { sys::gr_poly_init(&mut p, qi.ctx()) };
        QiPoly { p, qi }
    }

    fn from_gpoly(qi: &'a Qi, g: &GPoly) -> QiPoly<'a> {
        let mut f = QiPoly::new(qi);
        let n = g.len();
        let one = Integer::one();
        unsafe {
            sys::gr_poly_fit_length(&mut f.p, n as sys::slong, qi.ctx());
            for k in 0..n {
                let c = sys::gr_poly_coeff_ptr(&mut f.p, k as sys::slong, qi.ctx()) as *mut sys::fmpq;
                sys::fmpq_set_fmpz_frac(c, g.re.coeff(k).raw_ptr(), one.raw_ptr());
                sys::fmpq_set_fmpz_frac(c.add(1), g.im.coeff(k).raw_ptr(), one.raw_ptr());
            }
            sys::_gr_poly_set_length(&mut f.p, n as sys::slong, qi.ctx());
            sys::_gr_poly_normalise(&mut f.p, qi.ctx());
        }
        f
    }

    /// The polynomial times the least common denominator of its coefficients.
    fn to_gpoly(&self) -> GPoly {
        let n = self.p.length as usize;
        let parts: Vec<&sys::fmpq> = (0..n).flat_map(|k| unsafe {
            let c = (self.p.coeffs as *const sys::fmpq).add(2 * k);
            [&*c, &*c.add(1)]
        }).collect();
        let mut den = Integer::one();
        let mut t = Integer::zero();
        for q in &parts {
            unsafe { sys::fmpz_lcm(den.raw_mut_ptr(), den.raw_ptr(), &q.den) };
        }
        let mut cs = parts.iter().map(|q| {
            let mut c = Integer::zero();
            unsafe {
                sys::fmpz_divexact(t.raw_mut_ptr(), den.raw_ptr(), &q.den);
                sys::fmpz_mul(c.raw_mut_ptr(), &q.num, t.raw_ptr());
            }
            c
        });
        let (mut re, mut im) = (Vec::with_capacity(n), Vec::with_capacity(n));
        while let (Some(a), Some(b)) = (cs.next(), cs.next()) {
            re.push(a);
            im.push(b);
        }
        GPoly { re: ZPoly::from_coeffs(&re), im: ZPoly::from_coeffs(&im) }
    }

    fn len(&self) -> usize {
        self.p.length as usize
    }

    fn op(&self, f: impl FnOnce(*mut sys::gr_poly_struct, *mut sys::gr_ctx_struct) -> i32) -> Option<QiPoly<'a>> {
        let mut r = QiPoly::new(self.qi);
        (f(&mut r.p, self.qi.ctx()) == 0).then_some(r)
    }

    fn derivative(&self) -> Option<QiPoly<'a>> {
        self.op(|r, c| unsafe { sys::gr_poly_derivative(r, &self.p, c) })
    }

    fn gcd(&self, o: &QiPoly) -> Option<QiPoly<'a>> {
        self.op(|r, c| unsafe { sys::gr_poly_gcd(r, &self.p, &o.p, c) })
    }

    fn div(&self, o: &QiPoly) -> Option<QiPoly<'a>> {
        self.op(|r, c| unsafe { sys::gr_poly_div(r, &self.p, &o.p, c) })
    }

    fn sub(&self, o: &QiPoly) -> Option<QiPoly<'a>> {
        self.op(|r, c| unsafe { sys::gr_poly_sub(r, &self.p, &o.p, c) })
    }
}

impl Drop for QiPoly<'_> {
    fn drop(&mut self) {
        unsafe { sys::gr_poly_clear(&mut self.p, self.qi.ctx()) };
    }
}

/// The squarefree factorisation of `g` (with `g(0) != 0`): the factors of
/// positive degree with their multiplicities.
fn squarefree(g: &GPoly) -> Option<Vec<(GPoly, u64)>> {
    let mut out = Vec::new();
    if g.is_real() {
        let mut fac = sys::fmpz_poly_factor_struct::default();
        unsafe {
            sys::fmpz_poly_factor_init(&mut fac);
            sys::fmpz_poly_factor_squarefree(&mut fac, &g.re.0);
            for k in 0..fac.num as usize {
                let mut f = ZPoly::new();
                sys::fmpz_poly_set(&mut f.0, fac.p.add(k));
                out.push((GPoly { re: f, im: ZPoly::new() }, *fac.exp.add(k) as u64));
            }
            sys::fmpz_poly_factor_clear(&mut fac);
        }
        return Some(out);
    }
    // Yun's algorithm over Q(i).
    let qi = Qi::new();
    let f = QiPoly::from_gpoly(&qi, g);
    let df = f.derivative()?;
    let a = f.gcd(&df)?;
    let mut b = f.div(&a)?;
    let mut d = df.div(&a)?.sub(&b.derivative()?)?;
    for i in 1.. {
        let a = b.gcd(&d)?;
        if a.len() > 1 {
            out.push((a.to_gpoly(), i));
        }
        b = b.div(&a)?;
        if b.len() <= 1 {
            break;
        }
        d = d.div(&a)?.sub(&b.derivative()?)?;
    }
    Some(out)
}

/// A vector of complex balls.
struct AcbVec(sys::acb_ptr, usize);

impl AcbVec {
    fn new(n: usize) -> AcbVec {
        AcbVec(unsafe { sys::_acb_vec_init(n as sys::slong) }, n)
    }

    fn get(&self, k: usize) -> &sys::acb_struct {
        unsafe { &*self.0.add(k) }
    }
}

impl Drop for AcbVec {
    fn drop(&mut self) {
        unsafe { sys::_acb_vec_clear(self.0, self.1 as sys::slong) };
    }
}

/// The real roots of a squarefree integer polynomial of positive degree,
/// enclosed at precision `prec`.
fn real_roots_of(p: &ZPoly, prec: u64) -> Vec<sys::arb_struct> {
    let n = p.len() - 1;
    let rs = AcbVec::new(n);
    unsafe { sys::arb_fmpz_poly_complex_roots(rs.0, &p.0, 0, prec as sys::slong) };
    (0..n).map(|k| rs.get(k)).take_while(|z| unsafe { sys::arb_is_zero(&z.imag) } != 0).map(|z| unsafe {
        let mut x: sys::arb_struct = std::mem::zeroed();
        sys::arb_init(&mut x);
        sys::arb_set(&mut x, &z.real);
        x
    }).collect()
}

/// The real roots of the restrictions of a squarefree factor to lines
/// `Re z = b` or `Im z = b`, computed as needed.
struct Lines<'a> {
    g: &'a GPoly,
    found: Vec<(Rational, bool, u64, Vec<sys::arb_struct>)>,
}

impl Drop for Lines<'_> {
    fn drop(&mut self) {
        for (_, _, _, xs) in &mut self.found {
            for x in xs {
                unsafe { sys::arb_clear(x) };
            }
        }
    }
}

impl<'a> Lines<'a> {
    fn new(g: &'a GPoly) -> Lines<'a> {
        Lines { g, found: Vec::new() }
    }

    /// Whether the root of `g` whose other part lies in `other` (a ball
    /// that isolates it) has the part `b`: its real part if `vertical`,
    /// else its imaginary part. `None` if `other` is too wide to tell.
    fn on(&mut self, b: &Rational, vertical: bool, other: &sys::arb_struct, prec: u64) -> Option<bool> {
        let prec = 2 * prec;
        if !self.found.iter().any(|(c, v, p, _)| c == b && *v == vertical && *p >= prec) {
            let ys = self.restriction(b, vertical);
            let xs = if ys.len() > 1 { real_roots_of(&ys, prec) } else { Vec::new() };
            self.found.push((b.clone(), vertical, prec, xs));
        }
        let (_, _, _, xs) = self.found.iter().rev().find(|(c, v, p, _)| c == b && *v == vertical && *p >= prec)?;
        let mut unsure = false;
        for x in xs {
            if unsafe { sys::arb_contains(other, x) } != 0 {
                return Some(true);
            }
            unsure |= unsafe { sys::arb_overlaps(other, x) } != 0;
        }
        (!unsure).then_some(false)
    }

    /// The squarefree part of the gcd of the real and imaginary parts of
    /// `g(b + i·y)` (`vertical`) or `g(y + i·b)`, whose real roots `y` give
    /// the roots of `g` on that line: with `b = n/q` and `d` the degree,
    /// Horner's rule on `q^d·g(x)` with `q·x = n + i·q·y` or `q·y + i·n`.
    fn restriction(&self, b: &Rational, vertical: bool) -> ZPoly {
        let g = self.g;
        let (n, q) = (b.numerator(), b.denominator());
        let zero = Integer::zero();
        let (l0, l1) = if vertical { ([&n, &zero], [&zero, &q]) } else { ([&zero, &n], [&q, &zero]) };
        let d = g.len() - 1;
        let mut h = GPoly { re: ZPoly::from_coeffs(&[g.re.coeff(d)]), im: ZPoly::from_coeffs(&[g.im.coeff(d)]) };
        let mut qk = Integer::one();
        for k in (0..d).rev() {
            h = h.mul_linear(l0, l1);
            qk = &qk * &q;
            h.add_constant(&(&g.re.coeff(k) * &qk), &(&g.im.coeff(k) * &qk));
        }
        let mut c = ZPoly::new();
        unsafe { sys::fmpz_poly_gcd(&mut c.0, &h.re.0, &h.im.0) };
        if c.len() > 1 { c.squarefree_part() } else { c }
    }
}

/// A part of a root rounded to `bits`, if its enclosure `x` determines it or
/// it is exactly the one number the enclosure leaves in doubt (zero, or the
/// point halfway between the roundings of its ends), as `exact` decides.
fn round_part(x: &sys::arb_struct, bits: u64, exact: &mut dyn FnMut(&Rational) -> Option<bool>) -> Option<Real> {
    if let Some(r) = round_ball(x, bits) {
        return Some(r);
    }
    let b = if unsafe { sys::arb_contains_zero(x) } != 0 {
        Rational::zero()
    } else {
        let end = |upper: bool| unsafe {
            let mut a: sys::arf_struct = std::mem::zeroed();
            sys::arf_init(&mut a);
            let wp = (sys::arf_bits(&x.mid) as u64).max(bits) + 64;
            if upper { sys::arb_get_ubound_arf(&mut a, x, wp as sys::slong) } else { sys::arb_get_lbound_arf(&mut a, x, wp as sys::slong) };
            let mut r = Real::zero(bits);
            m::arf_to_mpfr(r.raw_mut(), &a);
            sys::arf_clear(&mut a);
            r.to_rational()
        };
        let b = &(&end(false)? + &end(true)?) * &Rational::new(&Integer::one(), &Integer::from_i64(2))?;
        // Only a point halfway between two adjacent numbers is in doubt; a
        // wider enclosure just needs more precision.
        let at = |p: u64| Real::from_rational(&b, p).to_rational().as_ref() == Some(&b);
        if at(bits) || !at(bits + 1) {
            return None;
        }
        b
    };
    exact(&b)?.then(|| Real::from_rational(&b, bits))
}

/// The midpoint of a ball, for ordering roots that round alike.
fn mid(x: &sys::arb_struct) -> Real {
    let mut r = Real::zero(unsafe { sys::arf_bits(&x.mid) }.max(2) as u64);
    unsafe { m::arf_to_mpfr(r.raw_mut(), &x.mid) };
    r
}

/// A root found: its parts rounded, and the midpoints of their enclosures.
struct Found {
    re: Real,
    im: Real,
    key: (Real, Real),
}

/// The roots of the squarefree `g` of positive degree with `g(0) != 0`
/// (only the real ones if `real_only`, for real `g`), rounded to `bits`.
fn factor_roots(g: &GPoly, bits: u64, real_only: bool) -> Vec<Found> {
    let n = g.len() - 1;
    let roots = AcbVec::new(n);
    let start = AcbVec::new(n);
    let mut poly = sys::acb_poly_struct::default();
    unsafe {
        sys::acb_poly_init(&mut poly);
        if !g.is_real() {
            for k in 0..=n {
                let mut c = sys::acb_struct::default();
                sys::acb_init(&mut c);
                sys::acb_set_fmpz_fmpz(&mut c, g.re.coeff(k).raw_ptr(), g.im.coeff(k).raw_ptr());
                sys::acb_poly_set_coeff_acb(&mut poly, k as sys::slong, &c);
                sys::acb_clear(&mut c);
            }
        }
    }
    let mut lines = Lines::new(g);
    let mut started = false;
    let mut found = Vec::new();
    let mut done = false;
    for wp in precisions(bits) {
        if g.is_real() {
            unsafe { sys::arb_fmpz_poly_complex_roots(roots.0, &g.re.0, 0, wp as sys::slong) };
        } else {
            let init = if started { start.0 as *const sys::acb_struct } else { std::ptr::null() };
            let isolated = unsafe { sys::acb_poly_find_roots(roots.0, &poly, init, 0, wp as sys::slong) };
            unsafe { sys::_acb_vec_set(start.0, roots.0, n as sys::slong) };
            started = true;
            if isolated < n as sys::slong {
                continue;
            }
        }
        found.clear();
        done = true;
        for k in 0..n {
            let z = roots.get(k);
            let real = g.is_real() && unsafe { sys::arb_is_zero(&z.imag) } != 0;
            if real_only && !real {
                continue;
            }
            let im = if real { Some(Real::zero(bits)) } else { round_part(&z.imag, bits, &mut |b| lines.on(b, false, &z.real, wp)) };
            let re = match real {
                true => round_part(&z.real, bits, &mut |b| Some(g.re.vanishes_at(b))),
                false => round_part(&z.real, bits, &mut |b| lines.on(b, true, &z.imag, wp)),
            };
            match (re, im) {
                (Some(re), Some(im)) => found.push(Found { re, im, key: (mid(&z.real), mid(&z.imag)) }),
                _ => {
                    done = false;
                    break;
                }
            }
        }
        if done {
            break;
        }
    }
    if !done {
        // Unresolved at the largest precision: the midpoints.
        let real = |z: &sys::acb_struct| g.is_real() && unsafe { sys::arb_is_zero(&z.imag) } != 0;
        found = (0..n).map(|k| roots.get(k)).filter(|z| !real_only || real(z)).map(|z| {
            let (re, im) = (mid(&z.real).round_to(bits), mid(&z.imag).round_to(bits));
            Found { re, im, key: (mid(&z.real), mid(&z.imag)) }
        }).collect();
    }
    unsafe { sys::acb_poly_clear(&mut poly) };
    found
}

/// The roots of the nonzero polynomial `re + i·im` (coefficients constant
/// term first) with their multiplicities: zero first if it is a root, then
/// the roots of the squarefree factors. `None` if FLINT fails.
fn roots(re: &[Integer], im: &[Integer], bits: u64, real_only: bool) -> Option<Vec<(Found, u64)>> {
    let len = re.len().max(im.len());
    let zero = Integer::zero();
    let coeff = |v: &[Integer], k: usize| v.get(k).unwrap_or(&zero).clone();
    let low = (0..len).take_while(|&k| coeff(re, k).is_zero() && coeff(im, k).is_zero()).count();
    let mut out = Vec::new();
    if low > 0 {
        out.push((Found { re: Real::zero(bits), im: Real::zero(bits), key: (Real::zero(2), Real::zero(2)) }, low as u64));
    }
    if low + 1 >= len {
        return Some(out);
    }
    let part = |v: &[Integer]| ZPoly::from_coeffs(&(low..len).map(|k| coeff(v, k)).collect::<Vec<_>>());
    let g = GPoly { re: part(re), im: part(im) };
    for (f, e) in squarefree(&g)? {
        out.extend(factor_roots(&f, bits, real_only).into_iter().map(|r| (r, e)));
    }
    Some(out)
}

/// The real roots of the nonzero integer polynomial `f` (constant term
/// first), rounded to nearest at `bits`, in increasing order, with their
/// multiplicities.
pub fn real_roots(f: &[Integer], bits: u64) -> Vec<(Real, u64)> {
    let mut rs = roots(f, &[], bits, true).expect("integer squarefree factorisation");
    rs.sort_by(|(a, _), (b, _)| a.re.cmp(&b.re).then_with(|| a.key.0.cmp(&b.key.0)));
    rs.into_iter().map(|(r, e)| (r.re, e)).collect()
}

/// The order in which `complex_roots` lists roots: by real part, then by
/// imaginary part.
fn complex_order(a: &Found, b: &Found) -> Ordering {
    a.re.cmp(&b.re).then_with(|| a.im.cmp(&b.im)).then_with(|| a.key.0.cmp(&b.key.0)).then_with(|| a.key.1.cmp(&b.key.1))
}

/// The complex roots of the nonzero polynomial with Gaussian integer
/// coefficients `re + i·im` (constant term first), each part rounded to
/// nearest at `bits`, with their multiplicities, in `complex_order`. `None`
/// if FLINT fails.
pub fn complex_roots(re: &[Integer], im: &[Integer], bits: u64) -> Option<Vec<(Complex, u64)>> {
    let mut rs = roots(re, im, bits, false)?;
    rs.sort_by(|(a, _), (b, _)| complex_order(a, b));
    Some(rs.into_iter().map(|(r, e)| (Complex::new(r.re, r.im), e)).collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ints(v: &[i64]) -> Vec<Integer> {
        v.iter().map(|&x| Integer::from_i64(x)).collect()
    }

    fn show(x: &Real) -> String {
        x.format(20)
    }

    #[test]
    fn real_roots_and_multiplicities() {
        // (x - 1)^2 (x - 2) x^3 (x^2 + 1)
        let f = [0, 0, 0, -2, 5, -6, 6, -4, 1];
        let rs = real_roots(&ints(&f), 67);
        let got: Vec<(String, u64)> = rs.iter().map(|(r, e)| (show(r), *e)).collect();
        assert_eq!(got, vec![("0.00000000000000000000".into(), 3), ("1.0000000000000000000".into(), 2), ("2.0000000000000000000".into(), 1)]);
        let rs = real_roots(&ints(&[-2, 0, 1]), 67);
        assert_eq!(rs.iter().map(|(r, _)| show(r)).collect::<Vec<_>>(), vec!["-1.4142135623730950488", "1.4142135623730950488"]);
        assert!(real_roots(&ints(&[1, 0, 1]), 67).is_empty());
    }

    #[test]
    fn ties_are_recognised() {
        // 2^68 x - (2^67 + 1): the root 1/2 + 2^-68 is halfway between two
        // numbers of 67 bits and rounds to even.
        let f = [-(&Integer::one().mul_2exp(67) + &Integer::one()), Integer::one().mul_2exp(68)];
        let rs = real_roots(&f, 67);
        assert_eq!(rs.len(), 1);
        assert_eq!(rs[0].0, Real::from_i64(1, 67).mul_2exp(-1));
    }

    #[test]
    fn complex_roots_exact_parts() {
        // z^4 - 1: -1, -i, i, 1 with exact zero parts.
        let rs = complex_roots(&ints(&[-1, 0, 0, 0, 1]), &[], 67).unwrap();
        let got: Vec<(String, String)> = rs.iter().map(|(z, _)| (show(&z.re), show(&z.im))).collect();
        let (z, o, m) = ("0.00000000000000000000", "1.0000000000000000000", "-1.0000000000000000000");
        assert_eq!(got, vec![(m.into(), z.into()), (z.into(), m.into()), (z.into(), o.into()), (o.into(), z.into())]);
        assert!(rs.iter().all(|(z, e)| *e == 1 && !(z.re.is_zero() && z.re.is_sign_negative()) && !(z.im.is_zero() && z.im.is_sign_negative())));
        // (z - (2 + i))^2 (z - i): exact double root over Q(i).
        // (z^2 - (4 + 2i) z + (3 + 4i)) (z - i) = z^3 - (4 + 3i) z^2 + (1 + 8i) z + (4 - 3i)
        let rs = complex_roots(&ints(&[4, 1, -4, 1]), &ints(&[-3, 8, -3, 0]), 67).unwrap();
        let got: Vec<(String, String, u64)> = rs.iter().map(|(z, e)| (show(&z.re), show(&z.im), *e)).collect();
        assert_eq!(got, vec![(z.into(), o.into(), 1), ("2.0000000000000000000".into(), o.into(), 2)]);
        // z^2 + (1 + 2i) z + (3 - i) = (z - i)(z + 1 + 3i)
        let rs = complex_roots(&ints(&[3, 1, 1]), &ints(&[-1, 2, 0]), 67).unwrap();
        let got: Vec<(String, String)> = rs.iter().map(|(z, _)| (show(&z.re), show(&z.im))).collect();
        assert_eq!(got, vec![(m.into(), "-3.0000000000000000000".into()), (z.into(), o.into())]);
    }
}
