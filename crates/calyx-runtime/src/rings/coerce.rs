//! Coercion into and between rings.
//!
//! Automatic coercion (used for arithmetic between elements of different
//! rings) happens only along obvious embeddings: the integers into every
//! ring, the rationals into characteristic-zero rings, a coefficient ring
//! into its polynomial rings, a finite field into a known overfield, and so
//! on. Forced coercion (`R ! x`) additionally allows maps that depend on
//! the element, such as reducing a rational modulo m or taking the
//! constant term of a polynomial.

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{Ctx, Elem, GrError, Truth, is_irreducible_mod_p};

use super::{FiniteField, Ring, RingKind, ZECH_LIMIT, make_elt, ring_of, small};
use crate::error::{RResult, RuntimeError};
use crate::interp::Interp;
use crate::value::{Struct, StructKind, Value};

/// A deterministic irreducible polynomial of degree `n` over `F_p` (primitive
/// when the field is small enough for Zech logarithms), used when no Conway
/// polynomial is known. Candidates are tried in order of their low-order
/// coefficients, so sparse polynomials come first.
pub fn default_irreducible(p: &Integer, n: u64) -> RResult<Vec<Integer>> {
    let small = p.pow(n).to_u64().is_some_and(|q| q <= ZECH_LIMIT);
    let mut counter = Integer::one();
    loop {
        let mut coeffs = Vec::with_capacity(n as usize + 1);
        let mut c = counter.clone();
        for _ in 0..n {
            let (q, r) = c.div_rem_euclid(p).unwrap();
            coeffs.push(r);
            c = q;
        }
        if !c.is_zero() {
            return Err(RuntimeError::runtime("No irreducible polynomial found"));
        }
        coeffs.push(Integer::one());
        if !coeffs[0].is_zero() && is_irreducible_mod_p(p, &coeffs) && (!small || Ctx::finite_field(p, &coeffs, true).is_ok()) {
            return Ok(coeffs);
        }
        counter = &counter + &Integer::one();
    }
}

/// Whether elements of the finite field `from` embed automatically into
/// `to`: from the prime field, or between fields defined by Conway
/// polynomials whose degrees divide.
fn ff_embeds(from: &FiniteField, to: &FiniteField) -> bool {
    from.p == to.p && (from.degree == 1 || (from.conway && to.conway && to.degree % from.degree == 0))
}

impl Interp {
    /// Whether elements of structure `from` coerce automatically into
    /// structure `to`.
    pub fn auto_coerces(&self, from: &Value, to: &Value) -> bool {
        if from == to {
            return true;
        }
        let (Some(fk), Some(tk)) = (from.as_struct(), to.as_struct()) else {
            return false;
        };
        use StructKind::*;
        match (fk, tk) {
            (Integers, Rationals | Reals(_) | Ring(_)) => match tk {
                Ring(r) => !matches!(&r.kind, RingKind::MPoly { .. } | RingKind::UPoly { .. }) || self.auto_coerces(from, r.base().unwrap()),
                _ => true,
            },
            (Rationals, Reals(_)) => true,
            (Reals(_), Reals(_)) => true,
            (Rationals | Reals(_), Ring(r)) => match &r.kind {
                RingKind::Complex(_) => true,
                RingKind::UPoly { base, .. } | RingKind::MPoly { base, .. } | RingKind::UPolyRes { base, .. } => self.auto_coerces(from, base),
                _ => false,
            },
            (Ring(a), Ring(b)) => match (&a.kind, &b.kind) {
                (RingKind::Complex(_), RingKind::Complex(_)) => true,
                (RingKind::Finite(f), RingKind::Finite(g)) => ff_embeds(f, g),
                (RingKind::UPoly { base: b1, .. }, RingKind::UPoly { base: b2, .. }) => self.auto_coerces(b1, b2),
                (RingKind::MPoly { base: b1, rank: r1, .. }, RingKind::MPoly { base: b2, rank: r2, .. }) => r1 <= r2 && self.auto_coerces(b1, b2),
                (_, RingKind::UPoly { base, .. } | RingKind::MPoly { base, .. } | RingKind::UPolyRes { base, .. }) => self.auto_coerces(from, base),
                _ => false,
            },
            _ => false,
        }
    }

    /// A ring containing both structures `a` and `b`, for arithmetic
    /// between their elements. As in Magma, a polynomial ring and a real or
    /// complex field meet in the polynomial ring over that field (created
    /// when needed); no other rings are made.
    pub fn common_ring(&mut self, a: &Value, b: &Value) -> RResult<Option<Value>> {
        if self.auto_coerces(b, a) {
            return Ok(Some(a.clone()));
        }
        if self.auto_coerces(a, b) {
            return Ok(Some(b.clone()));
        }
        let base_of = |v: &Value| ring_of(v).and_then(|(_, r)| match &r.kind {
            RingKind::UPoly { base, .. } => Some(base.clone()),
            _ => None,
        });
        let (ba, bb) = (base_of(a), base_of(b));
        let (x, y) = match (&ba, &bb) {
            (Some(p), None) => (p.clone(), b.clone()),
            (None, Some(q)) => (a.clone(), q.clone()),
            _ => return Ok(None),
        };
        let real = |v: &Value| match v.as_struct() {
            Some(StructKind::Reals(_)) => true,
            Some(StructKind::Ring(r)) => matches!(r.kind, RingKind::Complex(_)),
            _ => false,
        };
        match self.common_ring(&x, &y)? {
            Some(c) if real(&c) => Ok(Some(self.poly_ring(&c, true)?)),
            _ => Ok(None),
        }
    }

    /// The structure-level helper for aggregates (no new rings are made).
    pub fn common_ring_existing(&self, a: &Value, b: &Value) -> Option<Value> {
        if self.auto_coerces(b, a) {
            Some(a.clone())
        } else if self.auto_coerces(a, b) {
            Some(b.clone())
        } else {
            None
        }
    }

    /// Convert `x` to an element of the FLINT context of the structure `s`
    /// (the integers, rationals, reals or a ring). With `forced`, all the
    /// conversions of `s ! x` are allowed; otherwise only automatic ones.
    pub fn to_structure_elem(&mut self, s: &Value, x: &Value, forced: bool) -> RResult<Option<Elem>> {
        if let Value::Struct(st) = s {
            if let StructKind::Ring(_) = &st.kind {
                return self.to_ring_elem(st, x, forced);
            }
        }
        let Some(ctx) = self.ctx_of(s) else { return Ok(None) };
        let v = if forced {
            match self.try_coerce(s, x)? {
                Ok(v) => v,
                Err(_) => return Ok(None),
            }
        } else {
            let px = self.parent_of(x)?;
            if !self.auto_coerces(&px, s) {
                return Ok(None);
            }
            match self.try_coerce(s, x)? {
                Ok(v) => v,
                Err(_) => return Ok(None),
            }
        };
        Ok(match &v {
            Value::Int(i) => Elem::from_integer(&ctx, i).ok(),
            Value::Rat(q) => Elem::from_rational(&ctx, q).ok(),
            Value::Real(r) => Elem::from_real(&ctx, &r.x).ok(),
            _ => None,
        })
    }

    /// Convert `x` to an element of the ring `st`.
    pub fn to_ring_elem(&mut self, st: &Rc<Struct>, x: &Value, forced: bool) -> RResult<Option<Elem>> {
        let StructKind::Ring(r) = &st.kind else { return Ok(None) };
        if let Value::Elt(e) = x {
            if e.ring().id == r.id {
                return Ok(Some(e.x.clone()));
            }
        }
        if let Value::Small(s, v) = x {
            if r.small == Some(*s) {
                return Ok(Some(Elem::from_word(&r.ctx, *v)));
            }
        }
        let expanded;
        let x = if matches!(x, Value::Small(..)) {
            expanded = small::expand(x);
            &expanded
        } else {
            x
        };
        let ctx = r.ctx.clone();
        // A constant polynomial coerces by force like its constant term.
        if forced && !matches!(r.kind, RingKind::UPoly { .. }) {
            if let Value::Elt(e) = x {
                if let RingKind::UPoly { base, .. } | RingKind::UPolyRes { base, .. } = &e.ring().kind {
                    if e.x.poly_len() <= 1 {
                        let c = if e.x.poly_len() == 0 { Elem::zero(e.x.ctx().base().expect("a polynomial")) } else { e.x.poly_coeff(0) };
                        let v = self.elem_to_value(&base.clone(), c);
                        return self.to_ring_elem(st, &v, true);
                    }
                }
            }
        }
        match &r.kind {
            RingKind::Residue(m) => Ok(match x {
                Value::Int(i) => Elem::from_integer(&ctx, i).ok(),
                Value::Rat(q) if forced => Elem::from_rational(&ctx, q).ok(),
                Value::Elt(e) if forced => match &e.ring().kind {
                    RingKind::Residue(n) if divides(n, m) || divides(m, n) => e.residue().and_then(|i| Elem::from_integer(&ctx, &i).ok()),
                    RingKind::Finite(f) if f.degree == 1 && &f.p == m => e.residue().and_then(|i| Elem::from_integer(&ctx, &i).ok()),
                    _ => None,
                },
                _ => None,
            }),
            RingKind::Finite(f) => self.to_field_elem(r, f, x, forced),
            RingKind::UPoly { base, .. } => {
                let base = base.clone();
                // Elements of the coefficient ring (and of rings embedding in
                // it) are constants; otherwise a polynomial over another
                // coefficient ring maps coefficient by coefficient, and a
                // sequence (a tuple from `elt< P | a0, ..., ad >`) gives the
                // coefficients.
                let px = self.parent_of(x)?;
                if !self.auto_coerces(&px, &base) {
                    if let Value::Elt(e) = x {
                        // Elements of a quotient by force as their representatives.
                        if let RingKind::UPoly { base: b2, .. } | RingKind::UPolyRes { base: b2, .. } = &e.ring().kind {
                            if !forced && (!self.auto_coerces(b2, &base) || matches!(e.ring().kind, RingKind::UPolyRes { .. })) {
                                return Ok(None);
                            }
                            let b2 = b2.clone();
                            let mut coeffs = Vec::with_capacity(e.x.poly_len());
                            for i in 0..e.x.poly_len() {
                                let c = self.elem_to_value(&b2, e.x.poly_coeff(i));
                                match self.to_structure_elem(&base, &c, forced)? {
                                    Some(c) => coeffs.push(c),
                                    None => return Ok(None),
                                }
                            }
                            return Ok(Elem::poly_from_coeffs(&ctx, &coeffs).ok());
                        }
                    }
                    let elems = match x {
                        Value::Seq(s) if forced => Some(&s.elems),
                        Value::Tuple(t) if forced => Some(&t.elems),
                        _ => None,
                    };
                    if let Some(elems) = elems {
                        let mut coeffs = Vec::with_capacity(elems.len());
                        for v in elems {
                            match self.to_structure_elem(&base, v, true)? {
                                Some(c) => coeffs.push(c),
                                None => return Ok(None),
                            }
                        }
                        return Ok(Elem::poly_from_coeffs(&ctx, &coeffs).ok());
                    }
                }
                // A constant.
                Ok(match self.to_structure_elem(&base, x, forced)? {
                    Some(c) => Elem::poly_from_coeffs(&ctx, &[c]).ok(),
                    None => None,
                })
            }
            RingKind::UPolyRes { base, preimage, modulus } => {
                // Elements of the coefficient ring are constants; by force,
                // elements of the preimage ring (and coefficient sequences)
                // are reduced modulo the modulus.
                let (base, preimage, modulus) = (base.clone(), preimage.clone(), modulus.clone());
                let px = self.parent_of(x)?;
                let y = if !forced || self.auto_coerces(&px, &base) {
                    match self.to_structure_elem(&base, x, forced)? {
                        Some(c) => Elem::poly_from_coeffs(&ctx, &[c])?,
                        None => return Ok(None),
                    }
                } else if matches!(x, Value::Seq(_) | Value::Tuple(_)) || self.auto_coerces(&px, &Value::Struct(preimage.clone())) {
                    match self.to_ring_elem(&preimage, x, true)? {
                        Some(y) => y,
                        None => return Ok(None),
                    }
                } else {
                    return Ok(None);
                };
                Ok(Some(crate::intrinsics::upoly::res_reduce(&modulus, y)?))
            }
            RingKind::MPoly { base, .. } => {
                let base = base.clone();
                Ok(match self.to_structure_elem(&base, x, forced)? {
                    Some(c) => {
                        let mut e = Elem::zero(&ctx);
                        if Elem::mpoly_set_scalar(&mut e, &c).is_ok() { Some(e) } else { None }
                    }
                    None => None,
                })
            }
            RingKind::Complex(_) => Ok(match x {
                Value::Int(i) => Elem::from_integer(&ctx, i).ok(),
                Value::Rat(q) => Elem::from_rational(&ctx, q).ok(),
                Value::Real(re) => Elem::from_real(&ctx, &re.x).ok(),
                Value::Elt(e) => match &e.ring().kind {
                    RingKind::Complex(_) => {
                        let (re, im) = e.x.to_complex_parts().unwrap();
                        Elem::from_complex_parts(&ctx, &re, &im).ok()
                    }
                    _ => None,
                },
                _ => None,
            }),
        }
    }

    /// Convert `x` to an element of the finite field `f`.
    fn to_field_elem(&mut self, r: &Ring, f: &FiniteField, x: &Value, forced: bool) -> RResult<Option<Elem>> {
        let ctx = &r.ctx;
        Ok(match x {
            Value::Int(i) => Elem::from_integer(ctx, i).ok(),
            Value::Rat(q) if forced => Elem::from_rational(ctx, q).ok(),
            Value::Elt(e) => match &e.ring().kind {
                RingKind::Residue(n) if forced && n == &f.p => e.residue().and_then(|i| Elem::from_integer(ctx, &i).ok()),
                RingKind::Finite(g) if g.p == f.p => {
                    if ff_embeds(g, f) {
                        Some(embed_field_elem(&e.x, g, &e.ring().ctx, f, ctx))
                    } else if forced && ff_embeds(f, g) {
                        restrict_field_elem(&e.x, g, &e.ring().ctx, f, ctx)
                    } else {
                        None
                    }
                }
                _ => None,
            },
            Value::Seq(s) if forced && s.elems.len() as u64 == f.degree => {
                let mut coords = Vec::with_capacity(s.elems.len());
                for v in &s.elems {
                    let c = match v {
                        Value::Int(i) => i.clone(),
                        Value::Small(s, c) if Integer::from_u64(s.modulus().modulus()) == f.p => Integer::from_u64(*c),
                        Value::Elt(e) => match e.residue() {
                            Some(i) if e.ring().finite_field().is_some_and(|g| g.p == f.p && g.degree == 1) || matches!(&e.ring().kind, RingKind::Residue(n) if n == &f.p) => i,
                            _ => return Ok(None),
                        },
                        _ => return Ok(None),
                    };
                    coords.push(c);
                }
                if f.degree == 1 { Elem::from_integer(ctx, &coords[0]).ok() } else { Elem::fq_from_coords(ctx, &coords).ok() }
            }
            _ => None,
        })
    }

    /// Coerce into a ring structure `s` (the `!` operator for rings).
    pub fn coerce_into_ring(&mut self, st: &Rc<Struct>, x: &Value) -> RResult<Result<Value, Option<String>>> {
        if let StructKind::Ring(r) = &st.kind {
            if let Some(s) = r.small {
                match x {
                    Value::Int(i) => return Ok(Ok(Value::Small(s, s.modulus().reduce_integer(i)))),
                    Value::Small(t, _) if *t == s => return Ok(Ok(x.clone())),
                    _ => {}
                }
            }
        }
        match self.to_ring_elem(st, x, true)? {
            Some(e) => Ok(Ok(make_elt(st, e))),
            None => {
                // Name the coefficient that fails to coerce into a
                // polynomial ring.
                if let (Value::Seq(s), StructKind::Ring(r)) = (x, &st.kind) {
                    if let RingKind::UPoly { base, .. } = &r.kind {
                        let base = base.clone();
                        for (i, v) in s.elems.iter().enumerate() {
                            if self.to_structure_elem(&base, v, true)?.is_none() {
                                return Ok(Err(Some(format!("Cannot coerce sequence element {} into the coefficient ring", i + 1))));
                            }
                        }
                    }
                }
                // Explain failed coercions of rationals.
                if let (Value::Rat(q), StructKind::Ring(r)) = (x, &st.kind) {
                    let den = q.denominator();
                    match &r.kind {
                        RingKind::Finite(f) if den.div_rem_euclid(&f.p).is_some_and(|(_, rem)| rem.is_zero()) => return Ok(Err(Some("Division by zero".into()))),
                        RingKind::Residue(m) if den.is_divisible_by(m) => return Ok(Err(Some("Denominator is zero".into()))),
                        RingKind::Residue(m) if !den.gcd(m).is_one() => return Ok(Err(Some("Denominator is not a unit".into()))),
                        _ => {}
                    }
                }
                Ok(Err(None))
            }
        }
    }

    /// Coerce a ring element into the integers, rationals or reals (`Z ! x`).
    pub fn coerce_ring_elt_down(&mut self, target: &StructKind, e: &super::Elt) -> Option<Value> {
        // Constant polynomials behave like their coefficient.
        if let RingKind::UPoly { base, .. } | RingKind::UPolyRes { base, .. } = &e.ring().kind {
            if e.x.poly_len() <= 1 {
                let base = base.clone();
                let c = if e.x.poly_len() == 0 { Elem::zero(e.x.ctx().base().unwrap()) } else { e.x.poly_coeff(0) };
                let v = self.elem_to_value(&base, c);
                let t = Value::Struct(Struct::new(target.clone()));
                return self.try_coerce(&t, &v).ok()?.ok();
            }
            return None;
        }
        match target {
            StructKind::Integers | StructKind::Rationals => {
                let i = match &e.ring().kind {
                    // Residues lift to Z, but not to Q.
                    RingKind::Residue(_) | RingKind::Finite(_) if matches!(target, StructKind::Rationals) => return None,
                    RingKind::Residue(_) => e.residue()?,
                    RingKind::Finite(_) => e.residue()?,
                    RingKind::Complex(_) => {
                        let (re, im) = e.x.to_complex_parts()?;
                        if !im.is_zero() {
                            return None;
                        }
                        let q = re.to_rational()?;
                        return match target {
                            StructKind::Integers if q.is_integral() => Some(Value::Int(q.numerator())),
                            StructKind::Rationals => Some(Value::rat(q)),
                            _ => None,
                        };
                    }
                    _ => return None,
                };
                Some(match target {
                    StructKind::Integers => Value::Int(i),
                    _ => Value::rat(calyx_flint::Rational::from_integer(&i)),
                })
            }
            StructKind::Reals(d) => match &e.ring().kind {
                RingKind::Complex(_) => {
                    let (re, im) = e.x.to_complex_parts()?;
                    if !im.is_zero() {
                        return None;
                    }
                    Some(Value::real(re.round_to(calyx_flint::bits_for_digits(*d as u64)), *d))
                }
                _ => None,
            },
            _ => None,
        }
    }
}

fn divides(a: &Integer, b: &Integer) -> bool {
    !a.is_zero() && b.div_rem_euclid(a).is_some_and(|(_, r)| r.is_zero())
}

/// The image in `to` of the generator of the subfield `from`: for Conway
/// fields, `alpha^((p^n - 1)/(p^d - 1))`.
fn subfield_generator(from: &FiniteField, to: &FiniteField, to_ctx: &Rc<Ctx>) -> Elem {
    let one = Integer::one();
    let k = (&(&to.order() - &one)).div_rem_euclid(&(&from.order() - &one)).unwrap().0;
    to_ctx.generator().unwrap().pow(&k).unwrap()
}

/// Map an element of the subfield `from` into `to`.
pub fn embed_field_elem(x: &Elem, from: &FiniteField, _from_ctx: &Rc<Ctx>, to: &FiniteField, to_ctx: &Rc<Ctx>) -> Elem {
    if from.degree == 1 {
        let i = x.to_integer().unwrap_or_default();
        return Elem::from_integer(to_ctx, &i).unwrap();
    }
    if from.degree == to.degree {
        // Same Conway polynomial: the same coordinates.
        return Elem::fq_from_coords(to_ctx, &x.fq_coords()).unwrap();
    }
    let g = subfield_generator(from, to, to_ctx);
    let mut acc = Elem::zero(to_ctx);
    let mut pw = Elem::one(to_ctx).unwrap();
    for c in x.fq_coords() {
        if !c.is_zero() {
            acc = acc.add(&pw.mul_integer(&c).unwrap()).unwrap();
        }
        pw = pw.mul(&g).unwrap();
    }
    acc
}

/// Map an element of `from` that lies in its subfield `to` into `to`.
fn restrict_field_elem(x: &Elem, from: &FiniteField, from_ctx: &Rc<Ctx>, to: &FiniteField, to_ctx: &Rc<Ctx>) -> Option<Elem> {
    // x lies in the subfield of order q iff x^q = x.
    let q = to.order();
    if x.pow(&q).ok()?.equal(x) != Truth::True {
        return None;
    }
    if to.degree == 1 {
        return Elem::from_integer(to_ctx, &x.fq_prime_value()?).ok();
    }
    // Solve for the coordinates of x in the basis g^i of the subfield,
    // where g is the image of the generator of `to`.
    let g = subfield_generator(to, from, from_ctx);
    let n = from.degree as usize;
    let d = to.degree as usize;
    let mut cols: Vec<Vec<Integer>> = Vec::with_capacity(d);
    let mut pw = Elem::one(from_ctx).ok()?;
    for _ in 0..d {
        cols.push(pw.fq_coords());
        pw = pw.mul(&g).ok()?;
    }
    let rhs = x.fq_coords();
    let sol = solve_mod_p(&from.p, &cols, &rhs, n)?;
    Elem::fq_from_coords(to_ctx, &sol).ok()
}

/// Solve `sum_j c_j * cols[j] = rhs` over `F_p` (a consistent system with a
/// unique solution).
fn solve_mod_p(p: &Integer, cols: &[Vec<Integer>], rhs: &[Integer], n: usize) -> Option<Vec<Integer>> {
    let d = cols.len();
    // Augmented matrix, rows = coordinates.
    let modp = |x: &Integer| x.div_rem_euclid(p).unwrap().1;
    let mut m: Vec<Vec<Integer>> = (0..n).map(|i| (0..d).map(|j| modp(&cols[j][i])).chain(std::iter::once(modp(&rhs[i]))).collect()).collect();
    let mut row = 0;
    let mut pivots = Vec::new();
    for col in 0..d {
        let Some(r) = (row..n).find(|&r| !m[r][col].is_zero()) else { continue };
        m.swap(row, r);
        let inv = m[row][col].invmod(p)?;
        for k in col..=d {
            m[row][k] = modp(&(&m[row][k] * &inv));
        }
        for r2 in 0..n {
            if r2 != row && !m[r2][col].is_zero() {
                let f = m[r2][col].clone();
                for k in col..=d {
                    let v = &m[r2][k] - &(&f * &m[row][k]);
                    m[r2][k] = modp(&v);
                }
            }
        }
        pivots.push(col);
        row += 1;
    }
    if (row..n).any(|r| !m[r][d].is_zero()) {
        return None;
    }
    let mut sol = vec![Integer::zero(); d];
    for (i, &c) in pivots.iter().enumerate() {
        sol[c] = m[i][d].clone();
    }
    Some(sol)
}

impl From<GrError> for RuntimeError {
    fn from(e: GrError) -> RuntimeError {
        super::gr_error(e, "Arithmetic error")
    }
}
