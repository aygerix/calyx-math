//! Printing of rings and their elements in Magma's format.

use calyx_flint::Integer;
use calyx_flint::gr::{CtxKind, Elem, Truth};
use calyx_groebner::{Order, OrderArg};

use super::{Elt, Ring, RingKind, finite};
use crate::error::RResult;
use crate::interp::Interp;
use crate::print::Level;
use crate::value::Value;

/// One term `coef*mono` of a sum, with Magma's conventions for unit and
/// compound coefficients.
fn term(coef: &str, mono: &str) -> String {
    if mono.is_empty() {
        coef.to_string()
    } else if coef == "1" {
        mono.to_string()
    } else if coef == "-1" {
        format!("-{mono}")
    } else if is_compound(coef) {
        format!("({coef})*{mono}")
    } else {
        format!("{coef}*{mono}")
    }
}

/// Whether printed text is a sum or difference (and so needs brackets as a
/// factor).
fn is_compound(s: &str) -> bool {
    s.contains(" + ") || s.contains(" - ")
}

/// Join terms with ` + ` and ` - `.
fn join_terms(terms: &[String]) -> String {
    if terms.is_empty() {
        return "0".to_string();
    }
    let mut out = String::new();
    for (i, t) in terms.iter().enumerate() {
        if i == 0 {
            out.push_str(t);
        } else if let Some(rest) = t.strip_prefix('-') {
            out.push_str(" - ");
            out.push_str(rest);
        } else {
            out.push_str(" + ");
            out.push_str(t);
        }
    }
    out
}

fn power(name: &str, k: u64) -> String {
    match k {
        0 => String::new(),
        1 => name.to_string(),
        _ => format!("{name}^{k}"),
    }
}

fn join<T: std::fmt::Display>(xs: impl Iterator<Item = T>) -> String {
    xs.map(|x| x.to_string()).collect::<Vec<_>>().join(", ")
}

/// A monomial order as the tuple of MonomialOrder at the Magma level, whose
/// sequences Magma escapes as `\[ 1, 2 ]`.
fn order_tuple(o: &Order) -> String {
    let (name, args) = o.tuple();
    let mut parts = vec![format!("\"{name}\"")];
    for arg in args {
        parts.push(match arg {
            OrderArg::Int(k) => k.to_string(),
            OrderArg::Seq(q) => format!("\\[ {} ]", join(q.iter())),
            OrderArg::Other => unreachable!("an order argument"),
        });
    }
    parts.join(", ")
}

/// A polynomial in `name` with integer coefficients (constant term first).
fn int_poly(coeffs: &[Integer], name: &str) -> String {
    let terms: Vec<String> = coeffs.iter().enumerate().rev().filter(|(_, c)| !c.is_zero()).map(|(k, c)| term(&c.to_string(), &power(name, k as u64))).collect();
    join_terms(&terms)
}

/// The printing name of the i-th generator of the ring of `e`: its assigned
/// name, else `F.i` for a field or univariate polynomial ring assigned to
/// `F`, else `$.i`.
fn gen_name(e: &Elt, i: usize) -> String {
    let ring = e.ring();
    if !ring.has_names() && matches!(ring.kind, RingKind::Finite(_) | RingKind::UPoly { .. }) {
        if let Some(n) = *e.parent.name.borrow() {
            return format!("{n}.{i}");
        }
    }
    ring.gen_name(i)
}

/// A coefficient of a polynomial as text; real and complex coefficients
/// equal to 1 or -1 of a term with a monomial print as `1` and `-1` so
/// that `term` leaves them out.
fn coeff_text(it: &mut Interp, base: &Value, c: Elem, monomial: bool, level: Level) -> RResult<String> {
    if monomial && matches!(c.ctx().kind(), CtxKind::RealFloat(_) | CtxKind::ComplexFloat(_)) {
        if c.is_one() == Truth::True {
            return Ok("1".to_string());
        }
        if c.is_neg_one() == Truth::True {
            return Ok("-1".to_string());
        }
    }
    let cv = it.elem_to_value(base, c);
    it.format_flat(&cv, level)
}

/// A term `c*mono` of a polynomial over `base`, with the coefficient as
/// `coeff_text`, except that a complex coefficient with a negative real
/// part is printed negated: `-(1.0 - 2.0*i)*t`.
fn coef_term(it: &mut Interp, base: &Value, c: Elem, mono: &str, level: Level) -> RResult<String> {
    if level != Level::Magma && !mono.is_empty() && matches!(c.ctx().kind(), CtxKind::ComplexFloat(_)) {
        if let Some((re, im)) = c.to_complex_parts().filter(|(re, im)| !im.is_zero() && re.sign() < 0) {
            let s = crate::intrinsics::complex::format_complex(it, &calyx_flint::Complex::new(re, im).neg(), level);
            return Ok(format!("-({s})*{mono}"));
        }
    }
    Ok(term(&coeff_text(it, base, c, !mono.is_empty(), level)?, mono))
}

/// A univariate polynomial over `base` as text in the variable `name`.
pub fn upoly_text(it: &mut Interp, base: &Value, f: &Elem, name: &str, level: Level) -> RResult<String> {
    let mut terms = Vec::new();
    for k in (0..f.poly_len()).rev() {
        let c = f.poly_coeff(k);
        if c.is_zero() == Truth::True {
            continue;
        }
        terms.push(coef_term(it, base, c, &power(name, k as u64), level)?);
    }
    Ok(join_terms(&terms))
}

/// A univariate polynomial at the Magma level: its coefficients (constant
/// term first) as a sequence, in Magma's compact integer form `\[...]` over
/// the integers, prime fields and residue rings, with coefficients that
/// are polynomials given by their own coefficients.
fn upoly_magma(it: &mut Interp, base: &Value, f: &Elem) -> RResult<String> {
    let base_ring = super::ring_of(base).map(|(_, r)| r);
    let int_coeffs = |f: &Elem| -> Vec<String> { (0..f.poly_len()).map(|k| f.poly_coeff(k).to_integer().unwrap_or_default().to_string()).collect() };
    if matches!(base.as_struct(), Some(crate::value::StructKind::Integers)) {
        return Ok(format!("Polynomial(\\[{}])", int_coeffs(f).join(", ")));
    }
    let b = it.format_flat(base, Level::Magma)?;
    if base_ring.is_some_and(|r| matches!(&r.kind, RingKind::Residue(_)) || r.finite_field().is_some_and(|g| g.degree == 1)) {
        let cs: Vec<String> = (0..f.poly_len()).map(|k| it.format_structure_elem(base, f.poly_coeff(k))).collect::<RResult<_>>()?;
        return Ok(format!("Polynomial({b}, \\[{}])", cs.join(", ")));
    }
    let mut cs = Vec::with_capacity(f.poly_len());
    for k in 0..f.poly_len() {
        let c = f.poly_coeff(k);
        cs.push(match base_ring.map(|r| &r.kind) {
            Some(RingKind::UPoly { base: b2, .. }) => {
                let b2 = b2.clone();
                let inner: Vec<String> = (0..c.poly_len()).map(|j| it.format_structure_elem(&b2, c.poly_coeff(j))).collect::<RResult<_>>()?;
                format!("[{}]", inner.join(", "))
            }
            _ => {
                let v = it.elem_to_value(base, c);
                it.format_flat(&v, Level::Magma)?
            }
        });
    }
    Ok(if cs.is_empty() { format!("Polynomial([{b} |])") } else { format!("Polynomial([{b} | {}])", cs.join(", ")) })
}

/// Format an element of a ring.
pub fn format_ring_elt(it: &mut Interp, e: &Elt, level: Level) -> RResult<String> {
    let ring = e.ring();
    Ok(match &ring.kind {
        RingKind::Residue(_) => e.residue().unwrap_or_default().to_string(),
        RingKind::Finite(f) => {
            if f.degree == 1 {
                return Ok(e.residue().unwrap_or_default().to_string());
            }
            let name = gen_name(e, 1);
            if f.power_printing.get() {
                let Some(k) = finite::log_gen1(f, &e.x) else { return Ok("0".to_string()) };
                // Elements of the prime field print as integers.
                let q1 = &f.order() - &Integer::one();
                let step = q1.divexact(&(&f.p - &Integer::one()));
                if Integer::from_u64(k).is_divisible_by(&step) {
                    return Ok(e.x.fq_prime_value().unwrap_or_default().to_string());
                }
                return Ok(power(&name, k));
            }
            match &f.ground {
                None => int_poly(&finite::ground_coords(&e.parent, &e.x).integers(), &name),
                Some(g) => {
                    // A polynomial in F.1 with coefficients in the ground field.
                    let cs = finite::ground_elems(&e.parent, &e.x, &ring.ctx);
                    let mut terms = Vec::new();
                    for (i, c) in cs.into_iter().enumerate().rev() {
                        if c.is_zero() == Truth::True {
                            continue;
                        }
                        let cv = super::make_elt(&g.field, c);
                        let cs = it.format_flat(&cv, level)?;
                        terms.push(term(&cs, &power(&name, i as u64)));
                    }
                    join_terms(&terms)
                }
            }
        }
        RingKind::UPoly { base, .. } | RingKind::UPolyRes { base, .. } => {
            let base = base.clone();
            if level == Level::Magma {
                return upoly_magma(it, &base, &e.x);
            }
            upoly_text(it, &base, &e.x, &gen_name(e, 1), level)?
        }
        RingKind::MPoly { base, rank, .. } | RingKind::MPolyRes { base, rank, .. } => {
            let base = base.clone();
            let names: Vec<String> = (1..=*rank).map(|i| ring.gen_name(i)).collect();
            let mut terms = Vec::new();
            for (c, exps) in crate::intrinsics::mpoly::ordered_terms(&ring, &e.x) {
                let mono: Vec<String> = exps.iter().enumerate().filter(|(_, k)| **k > 0).map(|(j, k)| power(&names[j], *k)).collect();
                terms.push(coef_term(it, &base, c, &mono.join("*"), level)?);
            }
            join_terms(&terms)
        }
        // Complex numbers are `Value::Complex`, not ring elements.
        RingKind::Complex(_) => {
            let (re, im) = e.x.to_complex_parts().unwrap();
            crate::intrinsics::complex::format_complex(it, &calyx_flint::Complex::new(re, im), level)
        }
    })
}

impl Interp {
    /// A ring (the structure itself) as lines of text. Coefficient rings are
    /// named briefly (at the minimal level).
    pub fn format_ring(&mut self, r: &Ring, level: Level) -> RResult<Vec<String>> {
        if level == Level::Magma {
            return Ok(vec![match &r.kind {
                RingKind::Residue(m) => format!("IntegerRing({m})"),
                RingKind::Finite(f) => {
                    if f.degree == 1 {
                        format!("GF({})", f.p)
                    } else if f.default {
                        format!("GF({}, {})", f.p, f.degree)
                    } else {
                        let cs: Vec<String> = f.modulus.iter().map(|c| c.to_string()).collect();
                        format!("ext<GF({}) | Polynomial(GF({}), [{}])>", f.p, f.p, cs.join(", "))
                    }
                }
                RingKind::UPoly { base, .. } => {
                    let b = self.format_flat(&base.clone(), level)?;
                    format!("PolynomialRing({b})")
                }
                RingKind::UPolyRes { base, modulus, .. } => {
                    let b = self.format_flat(&base.clone(), level)?;
                    let m = self.format_res_modulus(r, modulus)?;
                    format!("Univariate Quotient Polynomial Algebra in {} over {b}\nwith modulus {m}", r.gen_name(1))
                }
                RingKind::MPoly { base, rank, order, grading } => {
                    let b = self.format_flat(&base.clone(), level)?;
                    match (order, grading) {
                        (o, Some(w)) => format!("PolynomialRing({b}, [ {} ], <{}>)", join(w.iter()), order_tuple(o)),
                        (Order::Lex, None) => format!("PolynomialRing({b}, {rank})"),
                        (Order::GLex, None) => format!("PolynomialRing({b}, {rank}, \"glex\")"),
                        (Order::GRevLex, None) => format!("PolynomialRing({b}, {rank}, \"grevlex\")"),
                        (o, None) => format!("PolynomialRing({b}, {rank}, <{}>)", order_tuple(o)),
                    }
                }
                RingKind::Complex(b) => format!("ComplexField({})", calyx_flint::digits_for_bits(*b)),
                RingKind::MPolyRes { .. } => return crate::intrinsics::poly_ideals::format_affine(self, r, level),
            }]);
        }
        let minimal = level == Level::Minimal;
        Ok(match &r.kind {
            RingKind::Residue(m) if minimal => vec![format!("IntegerRing({m})")],
            RingKind::Residue(m) => vec![format!("Residue class ring of integers modulo {m}")],
            RingKind::Finite(f) => {
                let size = if f.degree == 1 { f.p.to_string() } else { format!("{}^{}", f.p, f.degree) };
                vec![if minimal { format!("GF({size})") } else { format!("Finite field of size {size}") }]
            }
            RingKind::UPoly { base, .. } => {
                let b = self.format_flat(&base.clone(), Level::Minimal)?;
                vec![if r.has_names() { format!("Univariate Polynomial Ring in {} over {b}", r.gen_name(1)) } else { format!("Univariate Polynomial Ring over {b}") }]
            }
            RingKind::MPoly { base, rank, order, grading } => {
                let b = self.format_flat(&base.clone(), Level::Minimal)?;
                let graded = if grading.is_some() { "Graded " } else { "" };
                let mut lines = vec![format!("{graded}Polynomial ring of rank {rank} over {b}")];
                if !minimal {
                    let vars: Vec<String> = (1..=*rank).map(|i| r.gen_name(i)).collect();
                    lines.push(format!("Order: {}", order.describe()));
                    lines.push(format!("Variables: {}", vars.join(", ")));
                    if let Some(w) = grading {
                        lines.push(format!("Variable weights: [{}]", join(w.iter())));
                    }
                }
                lines
            }
            RingKind::UPolyRes { base, modulus, .. } => {
                let b = self.format_flat(&base.clone(), Level::Default)?;
                let m = self.format_res_modulus(r, modulus)?;
                vec![format!("Univariate Quotient Polynomial Algebra in {} over {b}", r.gen_name(1)), format!("with modulus {m}")]
            }
            RingKind::Complex(b) => vec![format!("Complex field of precision {}", calyx_flint::digits_for_bits(*b))],
            RingKind::MPolyRes { .. } => crate::intrinsics::poly_ideals::format_affine(self, r, level)?,
        })
    }

    /// The modulus of a polynomial quotient ring, in the name of its
    /// generator.
    fn format_res_modulus(&mut self, r: &Ring, f: &Elem) -> RResult<String> {
        let RingKind::UPolyRes { base, .. } = &r.kind else { unreachable!() };
        upoly_text(self, &base.clone(), f, &r.gen_name(1), Level::Default)
    }

    /// Print an element of a ring given as a FLINT element of the structure
    /// `s` (used for coefficients).
    pub fn format_structure_elem(&mut self, s: &Value, e: Elem) -> RResult<String> {
        let v = self.elem_to_value(s, e);
        self.format_flat(&v, Level::Default)
    }
}
