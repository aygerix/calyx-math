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
use calyx_flint::gr::{Ctx, Elem, GrError, is_irreducible_mod_p, is_irreducible_word};

use super::{FiniteField, Ring, RingKind, ZECH_LIMIT, finite, make_elt, ring_of, small};
use crate::error::{RResult, RuntimeError};
use crate::interp::Interp;
use crate::value::{Struct, StructKind, Value};

/// A deterministic irreducible polynomial of degree `n` over `F_p` (primitive
/// when the field is small enough for Zech logarithms), used when no Conway
/// polynomial is known. Candidates are tried in order of their low-order
/// coefficients, so sparse polynomials come first. As in Magma, for p > 127
/// the binomials x^n + c are passed over unless n divides p - 1, so that
/// the search starts at x^n + x + 1.
pub fn default_irreducible(p: &Integer, n: u64) -> RResult<Vec<Integer>> {
    let small = p.pow(n).to_u64().is_some_and(|q| q <= ZECH_LIMIT);
    let no_binomials = *p > Integer::from_u64(127) && (p - &Integer::one()).mod_u64(n) != 0;
    if let Some(pw) = p.to_u64() {
        // Over GF(2) this is the least g with x^n + g irreducible.
        if let Some(g) = (pw == 2 && !small).then(|| calyx_flint::gf2x::least_low_term(n as usize)).flatten() {
            return Ok((0..=n).map(|i| Integer::from_u64(if i == n { 1 } else if i < 64 { g >> i & 1 } else { 0 })).collect());
        }
        // The same order, counting in words.
        let mut digits = vec![0u64; n as usize + 1];
        digits[n as usize] = 1;
        if no_binomials {
            digits[1] = 1;
        }
        loop {
            let Some(i) = (0..n as usize).find(|&i| digits[i] + 1 < pw) else {
                return Err(RuntimeError::runtime("No irreducible polynomial found"));
            };
            digits[i] += 1;
            digits[..i].iter_mut().for_each(|d| *d = 0);
            if digits[0] != 0 && is_irreducible_word(pw, &digits) {
                let coeffs: Vec<Integer> = digits.iter().map(|&d| Integer::from_u64(d)).collect();
                if !small || Ctx::finite_field(p, &coeffs, true).is_ok() {
                    return Ok(coeffs);
                }
            }
        }
    }
    let mut counter = if no_binomials { p + &Integer::one() } else { Integer::one() };
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
                (RingKind::Finite(_), RingKind::Finite(_)) => finite::is_subfield(finite::field_struct(from).unwrap(), finite::field_struct(to).unwrap()),
                (RingKind::UPoly { base: b1, .. }, RingKind::UPoly { base: b2, .. }) => self.auto_coerces(b1, b2),
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
        if let (Some(fa), Some(fb)) = (finite::field_struct(a), finite::field_struct(b)) {
            let (fa, fb) = (fa.clone(), fb.clone());
            return Ok(self.ff_cover(&fa, &fb)?.map(Value::Struct));
        }
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
        // A constant polynomial coerces by force like its constant term, into
        // the coefficient ring of a polynomial ring (univariate polynomials
        // map to univariate ones coefficient by coefficient).
        if let (true, Value::Elt(e)) = (forced, x) {
            let univariate = |k: &RingKind| matches!(k, RingKind::UPoly { .. } | RingKind::UPolyRes { .. });
            if !(matches!(r.kind, RingKind::UPoly { .. }) && univariate(&e.ring().kind)) {
                if let Some(v) = self.poly_constant(e) {
                    let (RingKind::UPoly { base, .. } | RingKind::MPoly { base, .. }) = &r.kind else { return self.to_ring_elem(st, &v, true) };
                    if let Some(c) = self.to_structure_elem(&base.clone(), &v, true)? {
                        let mut y = Elem::zero(&ctx);
                        return Ok(match r.kind {
                            RingKind::UPoly { .. } => Elem::poly_from_coeffs(&ctx, &[c]).ok(),
                            _ => Elem::mpoly_set_scalar(&mut y, &c).ok().map(|_| y),
                        });
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
            RingKind::Finite(f) => self.to_field_elem(st, r, f, x, forced),
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
            RingKind::MPoly { base, rank, .. } => {
                let (base, rank) = (base.clone(), *rank);
                // By force, a polynomial of another ring of the same rank maps
                // variable to variable, coefficient by coefficient; otherwise
                // elements of the coefficient ring are constants.
                if let Value::Elt(e) = x {
                    if let RingKind::MPoly { base: b2, rank: r2, .. } = &e.ring().kind {
                        let px = e.parent_value();
                        if forced && !self.auto_coerces(&px, &base) {
                            if *r2 != rank {
                                return Ok(None);
                            }
                            let b2 = b2.clone();
                            let mut terms = Vec::with_capacity(e.x.mpoly_len());
                            for i in 0..e.x.mpoly_len() {
                                let (c, exps) = e.x.mpoly_term(i);
                                let c = self.elem_to_value(&b2, c);
                                match self.to_structure_elem(&base, &c, true)? {
                                    Some(c) => terms.push((c, exps)),
                                    None => return Ok(None),
                                }
                            }
                            return Ok(Elem::mpoly_from_terms(&ctx, &terms).ok());
                        }
                    }
                }
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
                Value::Complex(c) => Elem::from_complex_parts(&ctx, &c.re, &c.im).ok(),
                _ => None,
            }),
        }
    }

    /// Convert `x` to an element of the finite field `f`.
    fn to_field_elem(&mut self, st: &Rc<Struct>, r: &Ring, f: &FiniteField, x: &Value, forced: bool) -> RResult<Option<Elem>> {
        let ctx = &r.ctx;
        Ok(match x {
            Value::Int(i) => Elem::from_integer(ctx, i).ok(),
            // (Automatic only in arithmetic: see `ring_binop`.)
            Value::Rat(q) => Elem::from_rational(ctx, q).ok(),
            Value::Elt(e) => match &e.ring().kind {
                RingKind::Residue(n) if forced && n == &f.p => e.residue().and_then(|i| Elem::from_integer(ctx, &i).ok()),
                RingKind::Finite(g) if g.p == f.p => {
                    if forced {
                        self.ff_convert(&e.x, &e.parent, st)?
                    } else {
                        self.ff_emb_image(&e.parent, st)?.map(|img| finite::embed_with(&e.x, g.degree, &img))
                    }
                }
                _ => None,
            },
            // The sum of the entries times the powers of F.1.
            Value::Seq(s) if forced && f.degree > 1 && !s.elems.is_empty() && s.elems.len() as u64 <= finite::rel_degree(f) => {
                return self.field_from_coeffs(st, r, f, &s.elems.clone());
            }
            Value::Seq(s) if forced && f.degree == 1 && s.elems.len() == 1 => return self.to_field_elem(st, r, f, &s.elems[0].clone(), forced),
            // elt< F | a0, ..., am >
            Value::Tuple(t) if forced => {
                if t.elems.len() as u64 > finite::rel_degree(f) {
                    return Err(RuntimeError::runtime("Rhs argument 1 is invalid for this constructor"));
                }
                return self.field_from_coeffs(st, r, f, &t.elems.clone());
            }
            _ => None,
        })
    }

    /// The sum of the coefficients times the powers of `F.1`.
    fn field_from_coeffs(&mut self, st: &Rc<Struct>, r: &Ring, f: &FiniteField, elems: &[Value]) -> RResult<Option<Elem>> {
        let mut cs = Vec::with_capacity(elems.len());
        for v in elems {
            match self.to_structure_elem(&Value::Struct(st.clone()), v, true)? {
                Some(c) => cs.push(c),
                None => return Ok(None),
            }
        }
        let g1 = finite::gen1(r, f);
        let mut acc = Elem::zero(&r.ctx);
        for c in cs.iter().rev() {
            acc = acc.mul(&g1)?.add(c)?;
        }
        Ok(Some(acc))
    }

    /// Coerce into a ring structure `s` (the `!` operator for rings).
    pub fn coerce_into_ring(&mut self, st: &Rc<Struct>, x: &Value) -> RResult<Result<Value, Option<String>>> {
        if let StructKind::Ring(r) = &st.kind {
            if let RingKind::Complex(bits) = r.kind {
                return Ok(crate::intrinsics::complex::coerce_complex(x, bits));
            }
            if let Some(s) = r.small {
                match x {
                    Value::Int(i) => return Ok(Ok(Value::Small(s, s.modulus().reduce_integer(i)))),
                    Value::Small(t, _) if *t == s => return Ok(Ok(x.clone())),
                    _ => {}
                }
            }
        }
        if let (Some((_, f)), Value::Seq(s)) = (finite::field_of(st), x) {
            let n = finite::rel_degree(f);
            if s.elems.len() as u64 > n {
                return Ok(Err(Some(format!("Sequence must have length {n} to lift into this finite field"))));
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
                if finite::field_of(st).is_some() && crate::rings::small::elt_of(x).is_some_and(|e| e.ring().finite_field().is_some()) {
                    return Ok(Err(Some("No embedding known into LHS field".into())));
                }
                // Explain failed coercions between multivariate rings.
                if let (Value::Elt(e), StructKind::Ring(r)) = (x, &st.kind) {
                    if let (RingKind::MPoly { rank, .. }, RingKind::MPoly { rank: r2, .. }) = (&r.kind, &e.ring().kind) {
                        if rank != r2 {
                            return Ok(Err(Some(format!("LHS rank ({rank}) does not equal RHS rank ({r2})"))));
                        }
                        return Ok(Err(Some("Coefficient cannot be coerced".into())));
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

    /// The constant term of a constant polynomial, as an element of the
    /// coefficient ring.
    pub fn poly_constant(&mut self, e: &super::Elt) -> Option<Value> {
        let base = e.ring().base()?.clone();
        let c = match e.ring().kind {
            RingKind::MPoly { .. } => match e.x.mpoly_len() {
                0 => Elem::zero(e.x.ctx().base()?),
                1 => match e.x.mpoly_term(0) {
                    (c, exps) if exps.iter().all(|&k| k == 0) => c,
                    _ => return None,
                },
                _ => return None,
            },
            _ => match e.x.poly_len() {
                0 => Elem::zero(e.x.ctx().base()?),
                1 => e.x.poly_coeff(0),
                _ => return None,
            },
        };
        Some(self.elem_to_value(&base, c))
    }

    /// Coerce a ring element into the integers, rationals or reals (`Z ! x`).
    pub fn coerce_ring_elt_down(&mut self, target: &StructKind, e: &super::Elt) -> Option<Value> {
        // Constant polynomials behave like their coefficient.
        if e.ring().base().is_some() {
            let v = self.poly_constant(e)?;
            let t = Value::Struct(Struct::new(target.clone()));
            return self.try_coerce(&t, &v).ok()?.ok();
        }
        match target {
            StructKind::Integers | StructKind::Rationals => {
                let i = match &e.ring().kind {
                    // Residues lift to Z, but not to Q.
                    RingKind::Residue(_) | RingKind::Finite(_) if matches!(target, StructKind::Rationals) => return None,
                    RingKind::Residue(_) => e.residue()?,
                    RingKind::Finite(_) => e.residue()?,
                    _ => return None,
                };
                Some(match target {
                    StructKind::Integers => Value::Int(i),
                    _ => Value::rat(calyx_flint::Rational::from_integer(&i)),
                })
            }
            _ => None,
        }
    }
}

fn divides(a: &Integer, b: &Integer) -> bool {
    !a.is_zero() && b.div_rem_euclid(a).is_some_and(|(_, r)| r.is_zero())
}

impl From<GrError> for RuntimeError {
    fn from(e: GrError) -> RuntimeError {
        super::gr_error(e, "Arithmetic error")
    }
}
