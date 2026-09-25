//! Printing of rings and their elements in Magma's format.

use calyx_flint::Integer;
use calyx_flint::gr::{Elem, MonomialOrder, Truth};

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

/// Format an element of a ring.
pub fn format_ring_elt(it: &mut Interp, e: &Elt, level: Level) -> RResult<String> {
    let ring = e.ring();
    Ok(match &ring.kind {
        RingKind::Residue(_) => e.residue().unwrap_or_default().to_string(),
        RingKind::Finite(f) => {
            if f.degree == 1 {
                return Ok(e.residue().unwrap_or_default().to_string());
            }
            let name = ring.gen_name(1);
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
            let name = ring.gen_name(1);
            let mut terms = Vec::new();
            for k in (0..e.x.poly_len()).rev() {
                let c = e.x.poly_coeff(k);
                if c.is_zero() == Truth::True {
                    continue;
                }
                let cv = it.elem_to_value(&base, c);
                let cs = it.format_flat(&cv, level)?;
                terms.push(term(&cs, &power(&name, k as u64)));
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
                let cv = it.elem_to_value(&base, c);
                let cs = it.format_flat(&cv, level)?;
                terms.push(term(&cs, &mono.join("*")));
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
    /// Format a ring (the structure itself).
    pub fn format_ring(&mut self, r: &Ring, level: Level) -> RResult<String> {
        if level == Level::Magma {
            return Ok(match &r.kind {
                RingKind::Residue(m) => format!("ResidueClassRing({m})"),
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
                    let o = match order {
                        MonomialOrder::Lex => "\"lex\"",
                        MonomialOrder::DegLex => "\"glex\"",
                        MonomialOrder::DegRevLex => "\"grevlex\"",
                    };
                    format!("PolynomialRing({b}, {rank}, {o})")
                }
                RingKind::Complex(d) => format!("ComplexField({d})"),
            });
        }
        Ok(match &r.kind {
            RingKind::Residue(m) => format!("Residue class ring of integers modulo {m}"),
            RingKind::Finite(f) => {
                if f.degree == 1 {
                    format!("Finite field of size {}", f.p)
                } else {
                    format!("Finite field of size {}^{}", f.p, f.degree)
                }
            }
            RingKind::UPoly { base, .. } => {
                let b = self.format_flat(&base.clone(), level)?;
                if r.has_names() { format!("Univariate Polynomial Ring in {} over {b}", r.gen_name(1)) } else { format!("Univariate Polynomial Ring over {b}") }
            }
            RingKind::MPoly { base, rank, order } => {
                let b = self.format_flat(&base.clone(), level)?;
                let o = match order {
                    MonomialOrder::Lex => "Lexicographical Order",
                    MonomialOrder::DegLex => "Graded Lexicographical Order",
                    MonomialOrder::DegRevLex => "Graded Reverse Lexicographical Order",
                };
                let vars: Vec<String> = (1..=*rank).map(|i| r.gen_name(i)).collect();
                format!("Polynomial ring of rank {rank} over {b}\n{o}\nVariables: {}", vars.join(", "))
            }
            RingKind::Complex(d) => format!("Complex field of precision {d}"),
        })
    }

    /// Print an element of a ring given as a FLINT element of the structure
    /// `s` (used for coefficients).
    pub fn format_structure_elem(&mut self, s: &Value, e: Elem) -> RResult<String> {
        let v = self.elem_to_value(s, e);
        self.format_flat(&v, Level::Default)
    }
}
