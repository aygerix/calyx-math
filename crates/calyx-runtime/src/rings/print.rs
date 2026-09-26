//! Printing of rings and their elements in Magma's format.

use calyx_flint::Integer;
use calyx_flint::gr::{CtxKind, Elem, MonomialOrder, Truth};

use super::{Elt, Ring, RingKind};
use crate::error::RResult;
use crate::interp::Interp;
use crate::print::{Level, format_real};
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
                if let Some(k) = e.x.zech_log() {
                    // Elements of the prime field print as integers.
                    let q = f.order();
                    let step = (&(&q - &Integer::one())).div_rem_euclid(&(&f.p - &Integer::one())).unwrap().0;
                    let k_int = Integer::from_u64(k);
                    if k_int.div_rem_euclid(&step).is_some_and(|(_, r)| r.is_zero()) {
                        return Ok(e.x.fq_prime_value().unwrap_or_default().to_string());
                    }
                    return Ok(power(&name, k));
                }
                return Ok("0".to_string());
            }
            int_poly(&e.x.fq_coords(), &name)
        }
        RingKind::UPoly { base, .. } => {
            let base = base.clone();
            let name = gen_name(e, 1);
            let mut terms = Vec::new();
            for k in (0..e.x.poly_len()).rev() {
                let c = e.x.poly_coeff(k);
                if c.is_zero() == Truth::True {
                    continue;
                }
                terms.push(term(&coeff_text(it, &base, c, k > 0, level)?, &power(&name, k as u64)));
            }
            join_terms(&terms)
        }
        RingKind::MPoly { base, rank, .. } => {
            let base = base.clone();
            let names: Vec<String> = (1..=*rank).map(|i| ring.gen_name(i)).collect();
            let mut terms = Vec::new();
            for i in 0..e.x.mpoly_len() {
                let (c, exps) = e.x.mpoly_term(i);
                let mono: Vec<String> = exps.iter().enumerate().filter(|(_, k)| **k > 0).map(|(j, k)| power(&names[j], *k)).collect();
                terms.push(term(&coeff_text(it, &base, c, !mono.is_empty(), level)?, &mono.join("*")));
            }
            join_terms(&terms)
        }
        RingKind::Complex(d) => {
            let (re, im) = e.x.to_complex_parts().unwrap();
            let name = ring.gen_name(1);
            let rs = format_real(&re, *d);
            if im.is_zero() {
                return Ok(rs);
            }
            let is = format_real(&im.abs(), *d);
            let neg = im.sign() < 0;
            if re.is_zero() {
                return Ok(format!("{}{is}*{name}", if neg { "-" } else { "" }));
            }
            format!("{rs} {} {is}*{name}", if neg { "-" } else { "+" })
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
                RingKind::MPoly { base, rank, order } => {
                    let b = self.format_flat(&base.clone(), level)?;
                    match order {
                        MonomialOrder::Lex => format!("PolynomialRing({b}, {rank})"),
                        MonomialOrder::DegLex => format!("PolynomialRing({b}, {rank}, \"glex\")"),
                        MonomialOrder::DegRevLex => format!("PolynomialRing({b}, {rank}, \"grevlex\")"),
                    }
                }
                RingKind::Complex(d) => format!("ComplexField({d})"),
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
            RingKind::MPoly { base, rank, order } => {
                let b = self.format_flat(&base.clone(), Level::Minimal)?;
                let mut lines = vec![format!("Polynomial ring of rank {rank} over {b}")];
                if !minimal {
                    let o = match order {
                        MonomialOrder::Lex => "Lexicographical",
                        MonomialOrder::DegLex => "Graded Lexicographical",
                        MonomialOrder::DegRevLex => "Graded Reverse Lexicographical",
                    };
                    let vars: Vec<String> = (1..=*rank).map(|i| r.gen_name(i)).collect();
                    lines.push(format!("Order: {o}"));
                    lines.push(format!("Variables: {}", vars.join(", ")));
                }
                lines
            }
            RingKind::Complex(d) => vec![format!("Complex field of precision {d}")],
        })
    }

    /// Print an element of a ring given as a FLINT element of the structure
    /// `s` (used for coefficients).
    pub fn format_structure_elem(&mut self, s: &Value, e: Elem) -> RResult<String> {
        let v = self.elem_to_value(s, e);
        self.format_flat(&v, Level::Default)
    }
}
