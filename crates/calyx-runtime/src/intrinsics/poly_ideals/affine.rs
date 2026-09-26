//! Affine algebras (the handbook's Affine Algebras chapter): the quotients
//! P/J of a multivariate polynomial ring P by an ideal J, rings of type
//! RngMPolRes (`RingKind::MPolyRes`).
//!
//! An element is the normal form of a polynomial of P modulo the reduced
//! Gröbner basis of J in P's order, kept in P's context: sums need nothing
//! more, products and powers are reduced, inverses come from a Gröbner
//! basis with one more variable, and other quotients from linear algebra
//! on the monomial basis. J is the quotient's own copy of the ideal
//! given, whose basis Magma prints as the "quotient relations": as given
//! until an element needs the Gröbner basis, which then replaces it (so
//! naming the generators, which makes them, computes it).

use std::cell::OnceCell;
use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::{Elem, Truth};
use calyx_flint::mpoly as fm;
use calyx_groebner::{self as gb, Order, Terms};

use crate::intrinsics::groebner::{engine, shape, terms};
use super::{MPolIdeal, coercion_map, fmt_basis, generators, ideals_equal};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::{boolv, intv, none, one};
use crate::print::{Level, Printer};
use crate::rings::{Ring, RingKind, make_elt, ring_of};
use crate::value::*;

/// The affine algebra P/J.
pub struct Affine {
    /// The polynomial ring P.
    pub preimage: Rc<Struct>,
    /// The ideal J of P, a structure of kind `MPolIdeal`.
    pub ideal: Rc<Struct>,
    /// The reduced Gröbner basis of J in P's order, as terms, once computed.
    basis: OnceCell<Rc<[Terms]>>,
}

impl Affine {
    /// P, as a ring.
    pub fn poly_ring(&self) -> &Ring {
        match &self.preimage.kind {
            StructKind::Ring(r) => r,
            _ => unreachable!("a polynomial ring"),
        }
    }

    /// The ideal J.
    pub fn divisor(&self) -> &Rc<MPolIdeal> {
        match &self.ideal.kind {
            StructKind::MPolIdeal(id) => id,
            _ => unreachable!("an ideal"),
        }
    }

    /// The monomial order of P.
    pub fn order(&self) -> &Order {
        shape(self.poly_ring()).2
    }

    /// The reduced Gröbner basis of J, computed once (it then becomes the
    /// basis of J).
    fn groebner(&self) -> RResult<Rc<[Terms]>> {
        if let Some(g) = self.basis.get() {
            return Ok(g.clone());
        }
        let g: Rc<[Terms]> = self.divisor().groebner()?.iter().map(terms).collect();
        Ok(self.basis.get_or_init(|| g).clone())
    }

    /// Whether J is the whole of P (P/J is the zero ring).
    fn is_zero_ring(&self) -> RResult<bool> {
        Ok(matches!(&*self.groebner()?, [t] if is_constant_terms(t)))
    }

    /// The normal form of `x`, a polynomial of P, modulo J.
    pub fn reduce(&self, x: Elem) -> RResult<Elem> {
        let g = self.groebner()?;
        if x.mpoly_len() == 0 || g.is_empty() {
            return Ok(x);
        }
        let r = self.poly_ring();
        let (base, n, order) = shape(r);
        let nf = engine(r, gb::normal_form(base, n, order, &terms(&x), &g))?;
        Ok(Elem::mpoly_from_terms(&r.ctx, &nf)?)
    }

    /// The constant `c` of the coefficient ring, reduced.
    fn constant(&self, c: &Elem) -> RResult<Elem> {
        let mut e = Elem::zero(&self.poly_ring().ctx);
        Elem::mpoly_set_scalar(&mut e, c)?;
        self.reduce(e)
    }

    /// Magma finds inverses and quotients by linear algebra, in algebras of
    /// finite dimension only.
    fn need_finite(&self) -> RResult<()> {
        match self.finite_dimensional()? {
            true => Ok(()),
            false => Err(RuntimeError::runtime("Quotient does not have finite dimension")),
        }
    }

    /// Whether P/J has finite dimension over the coefficient field: each
    /// variable has a pure power among the leading monomials of J (or J is
    /// P, whose leading monomial 1 counts for all).
    fn finite_dimensional(&self) -> RResult<bool> {
        let g = self.groebner()?;
        let n = shape(self.poly_ring()).1;
        let pure = |i: usize| g.iter().any(|t| t[0].1.iter().enumerate().all(|(j, &k)| k == 0 || j == i));
        Ok((0..n).all(pure))
    }

    /// The inverse of `x`, an element of P/J (of finite dimension), if it is
    /// a unit (in the zero ring, as in Magma, nothing is). When it is, the
    /// reduced Gröbner basis of J + (x t - 1) in P[t], for grevlex on t and
    /// then on the variables of P, has an element t - g, and g is the
    /// inverse modulo J; a unit modulo J : x^∞ only has one too, so the
    /// inverse is checked.
    pub fn inverse(&self, x: &Elem) -> RResult<Option<Elem>> {
        self.need_finite()?;
        if self.is_zero_ring()? || x.mpoly_len() == 0 {
            return Ok(None);
        }
        let r = self.poly_ring();
        let (base, n, _) = shape(r);
        if x.mpoly_len() == 1 {
            let (c, e) = x.mpoly_term(0);
            if e.iter().all(|&k| k == 0) {
                return match c.is_invertible() {
                    Truth::True => Ok(Some(self.constant(&c.inv()?)?)),
                    _ => Ok(None),
                };
            }
        }
        let lift = |t: &Terms, k: u64| -> Terms { t.iter().map(|(c, e)| (c.clone(), std::iter::once(k).chain(e.iter().copied()).collect())).collect() };
        let mut gens: Vec<Terms> = self.groebner()?.iter().map(|t| lift(t, 0)).collect();
        let mut xt = lift(&terms(x), 1);
        xt.push((Elem::one(base)?.neg()?, vec![0; n + 1]));
        gens.push(xt);
        let h = engine(r, gb::groebner(base, n + 1, &Order::ElimK(1), &gens))?;
        let t: Vec<u64> = std::iter::once(1).chain(std::iter::repeat_n(0, n)).collect();
        let Some(p) = h.iter().find(|p| p.first().is_some_and(|(_, e)| *e == t)) else { return Ok(None) };
        let g: Terms = p[1..].iter().map(|(c, e)| Ok((c.neg()?, e[1..].to_vec()))).collect::<RResult<_>>()?;
        let y = self.reduce(Elem::mpoly_from_terms(&r.ctx, &g)?)?;
        let check = self.reduce(x.mul(&y)?)?;
        Ok((check.is_one() == Truth::True).then_some(y))
    }

    /// `x^k` for an element x of P/J (`k < 0` for units).
    pub fn pow(&self, x: &Elem, k: &Integer) -> RResult<Elem> {
        let (mut b, k) = if k.sign() < 0 {
            match self.inverse(x).map_err(|e| e.in_context("^"))? {
                Some(y) => (y, -k),
                None => return Err(RuntimeError::runtime("Argument 1 is not invertible").in_context("^")),
            }
        } else {
            (x.clone(), k.clone())
        };
        let mut acc = self.constant(&Elem::one(self.poly_ring().ctx.base().expect("a polynomial ring"))?)?;
        let bits = k.bits();
        for i in 0..bits {
            if !k.bitand(&Integer::one().mul_2exp(i)).is_zero() {
                acc = self.reduce(acc.mul(&b)?)?;
            }
            if i + 1 < bits {
                b = self.reduce(b.mul(&b)?)?;
            }
        }
        Ok(acc)
    }

    /// `x / y` for elements of P/J, as Magma computes it (in an algebra of
    /// finite dimension): `x` times the inverse of `y`, or else the exact
    /// quotient of the polynomials, or else a solution of `q y = x`.
    pub fn divide(&self, x: &Elem, y: &Elem) -> RResult<Elem> {
        self.need_finite()?;
        if y.mpoly_len() == 0 {
            return Err(RuntimeError::runtime("Argument 2 is not a unit"));
        }
        if let Some(z) = self.inverse(y)? {
            return self.reduce(x.mul(&z)?);
        }
        if let Ok(Some(q)) = fm::divides(x, y) {
            return self.reduce(q);
        }
        self.solve(x, y)?.ok_or_else(|| RuntimeError::runtime("Element is not divisible by other element"))
    }

    /// A solution q of `q y = x` in P/J (of finite dimension), by linear
    /// algebra on the coordinates in the monomial basis: the images of the
    /// basis monomials, from the largest, that are independent of those
    /// before them carry the solution (as the quotients Magma gives show).
    fn solve(&self, x: &Elem, y: &Elem) -> RResult<Option<Elem>> {
        let r = self.poly_ring();
        let base = r.ctx.base().expect("a polynomial ring").clone();
        let Some(mut ms) = standard_monomials(self)? else { return Ok(None) };
        ms.reverse();
        let d = ms.len();
        let index: std::collections::HashMap<&[u64], usize> = ms.iter().enumerate().map(|(i, m)| (m.as_slice(), i)).collect();
        let coords = |f: &Elem| -> RResult<Vec<Elem>> {
            let mut v = vec![Elem::zero(&base); d];
            for (c, e) in terms(f) {
                v[index[e.as_slice()]] = c;
            }
            Ok(v)
        };
        let unit = Elem::one(&base)?;
        // Reduced columns, each with its pivot (a coordinate where it is 1
        // and the later columns 0) and the combination of the original
        // columns that makes it.
        let mut reduced: Vec<(usize, Vec<Elem>, Vec<Elem>)> = Vec::new();
        let axpy = |v: &mut [Elem], a: &Elem, w: &[Elem]| -> RResult<()> {
            for (x, y) in v.iter_mut().zip(w) {
                if y.is_zero() != Truth::True {
                    *x = x.sub(&a.mul(y)?)?;
                }
            }
            Ok(())
        };
        for (j, m) in ms.iter().enumerate() {
            let mono = Elem::mpoly_from_terms(&r.ctx, &[(unit.clone(), m.clone())])?;
            let mut v = coords(&self.reduce(y.mul(&mono)?)?)?;
            let mut combo = vec![Elem::zero(&base); d];
            combo[j] = unit.clone();
            for (p, w, c) in &reduced {
                let a = v[*p].clone();
                if a.is_zero() != Truth::True {
                    axpy(&mut v, &a, w)?;
                    axpy(&mut combo, &a, c)?;
                }
            }
            let Some(p) = v.iter().position(|c| c.is_zero() != Truth::True) else { continue };
            let inv = v[p].inv()?;
            let v: Vec<Elem> = v.iter().map(|c| c.mul(&inv)).collect::<Result<_, _>>()?;
            let combo: Vec<Elem> = combo.iter().map(|c| c.mul(&inv)).collect::<Result<_, _>>()?;
            reduced.push((p, v, combo));
        }
        let mut b = coords(x)?;
        let mut q = vec![Elem::zero(&base); d];
        for (p, w, c) in &reduced {
            let a = b[*p].clone();
            if a.is_zero() != Truth::True {
                axpy(&mut b, &a, w)?;
                let neg = a.neg()?;
                axpy(&mut q, &neg, c)?;
            }
        }
        if b.iter().any(|c| c.is_zero() != Truth::True) {
            return Ok(None);
        }
        let ts: Terms = q.into_iter().zip(ms).filter(|(c, _)| c.is_zero() != Truth::True).collect();
        Ok(Some(Elem::mpoly_from_terms(&r.ctx, &ts)?))
    }
}

/// Whether a polynomial as terms is a non-zero constant.
fn is_constant_terms(t: &Terms) -> bool {
    matches!(t.as_slice(), [(_, e)] if e.iter().all(|&k| k == 0))
}

/// The affine algebra of a ring.
pub fn affine_of(r: &Ring) -> Option<&Rc<Affine>> {
    match &r.kind {
        RingKind::MPolyRes { affine, .. } => Some(affine),
        _ => None,
    }
}

fn affine_arg(a: &CallArgs, i: usize) -> (Rc<Struct>, Rc<Affine>) {
    let Value::Struct(st) = &a.args[i] else { unreachable!("an affine algebra") };
    let StructKind::Ring(r) = &st.kind else { unreachable!("an affine algebra") };
    (st.clone(), affine_of(r).expect("an affine algebra").clone())
}

fn elt_arg(a: &CallArgs, i: usize) -> Rc<crate::rings::Elt> {
    match &a.args[i] {
        Value::Elt(e) => e.clone(),
        _ => unreachable!("an element of an affine algebra"),
    }
}

// ----- construction ----------------------------------------------------------------

/// The quotient of the multivariate polynomial ring `p` by the ideal
/// generated by `gens`, with the names of the variables of `p`.
pub fn quotient(it: &mut Interp, p: &Rc<Struct>, gens: Vec<Elem>) -> Value {
    let ideal = Struct::new(StructKind::MPolIdeal(Rc::new(MPolIdeal::new(p.clone(), gens, false))));
    it.mpoly_res(p, Rc::new(Affine { preimage: p.clone(), ideal, basis: OnceCell::new() }))
}

/// `quo<P | ...>` for a multivariate polynomial ring P: the quotient by the
/// ideal generated as by `ideal<P | ...>`, and the quotient map.
pub fn quo_constructor(it: &mut Interp, base: &Value, right: &[Value]) -> RResult<Option<Vec<Value>>> {
    let Some((pst, _)) = ring_of(base).filter(|(_, r)| matches!(r.kind, RingKind::MPoly { .. })) else { return Ok(None) };
    let pst = pst.clone();
    let gens = generators(it, &pst, right, "quo< ... >")?;
    let q = quotient(it, &pst, gens);
    Ok(Some(vec![q.clone(), coercion_map(base.clone(), q)]))
}

/// The affine algebra of the multivariate polynomial ring `p` with the
/// relations `relations` (elements of `p`, ideals of it, and sets and
/// sequences of these, as in `quo<P | ...>`); the entry point of
/// `AffineAlgebra< R, X | L >`, whose names are those of `p`.
pub fn affine_algebra(it: &mut Interp, p: &Value, relations: &[Value]) -> RResult<Value> {
    let Some((pst, _)) = ring_of(p).filter(|(_, r)| matches!(r.kind, RingKind::MPoly { .. })) else {
        return Err(RuntimeError::runtime("A multivariate polynomial ring is needed").in_context("AffineAlgebra< ... >"));
    };
    let pst = pst.clone();
    let gens = generators(it, &pst, relations, "AffineAlgebra< ... >")?;
    Ok(quotient(it, &pst, gens))
}

/// `P / J` for an ideal J of P (or P itself).
pub fn quotient_of(it: &mut Interp, p: &Rc<Struct>, j: &Option<Rc<MPolIdeal>>) -> RResult<Value> {
    let gens = match j {
        Some(id) => id.basis(),
        None => vec![Elem::one(&shape_ring(p).ctx)?],
    };
    Ok(quotient(it, p, gens))
}

fn shape_ring(p: &Rc<Struct>) -> &Ring {
    match &p.kind {
        StructKind::Ring(r) => r,
        _ => unreachable!("a polynomial ring"),
    }
}

/// Whether two affine algebras are equal: quotients of one ring by equal
/// ideals.
pub fn algebras_equal(a: &Affine, b: &Affine) -> RResult<bool> {
    if Rc::ptr_eq(&a.ideal, &b.ideal) {
        return Ok(true);
    }
    if !struct_eq(&a.preimage, &b.preimage) {
        return Ok(false);
    }
    ideals_equal(&Some(a.divisor().clone()), &Some(b.divisor().clone()))
}

// ----- coercion --------------------------------------------------------------------

/// `x` as an element of the affine algebra `st`: elements of the coefficient
/// ring (and those coercing into it) as constants, and by force elements of
/// P (and what else `P ! x` accepts but polynomials of other rings and
/// elements of other quotients), reduced.
pub fn coerce_into(it: &mut Interp, st: &Rc<Struct>, x: &Value, forced: bool) -> RResult<Option<Elem>> {
    let StructKind::Ring(r) = &st.kind else { return Ok(None) };
    let (Some(affine), Some(base)) = (affine_of(r).cloned(), r.base().cloned()) else { return Ok(None) };
    let y = if !forced {
        match it.to_structure_elem(&base, x, false)? {
            Some(c) => {
                let mut e = Elem::zero(&r.ctx);
                Elem::mpoly_set_scalar(&mut e, &c)?;
                e
            }
            None => return Ok(None),
        }
    } else {
        if let Value::Elt(e) = x {
            let other = match e.ring().kind {
                RingKind::MPolyRes { .. } => true,
                RingKind::MPoly { .. } => e.ring().id != affine.poly_ring().id,
                _ => false,
            };
            if other {
                return Ok(None);
            }
        }
        match it.to_ring_elem(&affine.preimage, x, true)? {
            Some(y) => y,
            None => return Ok(None),
        }
    };
    Ok(Some(affine.reduce(y)?))
}

// ----- printing --------------------------------------------------------------------

/// The order line of an affine algebra (`Lexicographical Order`).
fn order_line(affine: &Affine) -> String {
    format!("{} Order", affine.order().describe())
}

/// Print an affine algebra: at the minimal level `Affine Algebra of rank n
/// over R`, and otherwise (the Magma level too, as in Magma) also its
/// order, the names of its variables and the basis of its ideal (in those
/// names).
pub fn fmt_affine(it: &mut Interp, p: &mut Printer, s: &Rc<Struct>, indent: usize) -> RResult<()> {
    let StructKind::Ring(r) = &s.kind else { unreachable!("an affine algebra") };
    let RingKind::MPolyRes { base, rank, affine } = &r.kind else { unreachable!("an affine algebra") };
    let (base, rank, affine) = (base.clone(), *rank, affine.clone());
    let b = it.format_flat(&base, Level::Minimal)?;
    p.write(&format!("Affine Algebra of rank {rank} over {b}"));
    if p.level == Level::Minimal {
        return Ok(());
    }
    p.newline(indent);
    p.write(&order_line(&affine));
    p.newline(indent);
    let vars: Vec<String> = (1..=rank).map(|i| r.gen_name(i)).collect();
    p.write(&format!("Variables: {}", vars.join(", ")));
    if let RingKind::MPoly { grading: Some(w), .. } = &affine.poly_ring().kind {
        p.newline(indent);
        p.write(&format!("Variable weights: {}", w.iter().map(|k| k.to_string()).collect::<Vec<_>>().join(" ")));
    }
    p.newline(indent);
    p.write("Quotient relations:");
    fmt_basis(it, p, s, &affine.divisor().basis(), indent)
}

/// An affine algebra as lines of text, for `format_ring` (its relations
/// flat, one per line).
pub fn format_affine(it: &mut Interp, r: &Ring, level: Level) -> RResult<Vec<String>> {
    let RingKind::MPolyRes { base, rank, affine } = &r.kind else { unreachable!("an affine algebra") };
    let (base, rank, affine) = (base.clone(), *rank, affine.clone());
    let b = it.format_flat(&base, Level::Minimal)?;
    let mut lines = vec![format!("Affine Algebra of rank {rank} over {b}")];
    if level == Level::Minimal {
        return Ok(lines);
    }
    lines.push(order_line(&affine));
    let vars: Vec<String> = (1..=rank).map(|i| r.gen_name(i)).collect();
    lines.push(format!("Variables: {}", vars.join(", ")));
    if let RingKind::MPoly { grading: Some(w), .. } = &affine.poly_ring().kind {
        lines.push(format!("Variable weights: {}", w.iter().map(|k| k.to_string()).collect::<Vec<_>>().join(" ")));
    }
    lines.push("Quotient relations:".into());
    lines.push("[".into());
    let basis = affine.divisor().basis();
    for (i, g) in basis.iter().enumerate() {
        let text = it.format_flat(&make_elt(&affine.preimage, g.clone()), Level::Default)?;
        lines.push(format!("    {text}{}", if i + 1 < basis.len() { "," } else { "" }));
    }
    lines.push("]".into());
    Ok(lines)
}

// ----- finite dimension ------------------------------------------------------------

/// The monomials of P outside the ideal of the leading monomials of J (a
/// basis of P/J), in increasing order; `None` if there are infinitely many.
fn standard_monomials(affine: &Affine) -> RResult<Option<Vec<Vec<u64>>>> {
    if !affine.finite_dimensional()? {
        return Ok(None);
    }
    let g = affine.groebner()?;
    let n = shape(affine.poly_ring()).1;
    let lms: Vec<&[u64]> = g.iter().map(|t| t[0].1.as_slice()).collect();
    if affine.is_zero_ring()? {
        return Ok(Some(Vec::new()));
    }
    // The monomials outside the ideal form an order ideal: fill in the
    // exponents one variable at a time, stopping where the monomial so far
    // (the rest 0) is in the ideal.
    fn fill(i: usize, e: &mut Vec<u64>, lms: &[&[u64]], out: &mut Vec<Vec<u64>>) {
        if i == e.len() {
            out.push(e.clone());
            return;
        }
        loop {
            if lms.iter().any(|m| m.iter().zip(e.iter()).all(|(a, b)| a <= b)) {
                break;
            }
            fill(i + 1, e, lms, out);
            e[i] += 1;
        }
        e[i] = 0;
    }
    let mut out = Vec::new();
    fill(0, &mut vec![0; n], &lms, &mut out);
    let order = affine.order();
    out.sort_by(|a, b| order.cmp(a, b));
    Ok(Some(out))
}

/// The dimension of P/J over the coefficient field, if it is finite.
pub fn vector_dimension(affine: &Affine) -> RResult<Option<usize>> {
    Ok(standard_monomials(affine)?.map(|m| m.len()))
}

/// The minimal polynomial of `x` over the coefficient field, as its
/// coefficients (constant term first), in an algebra of finite dimension
/// (the only ones where Magma finds it): the element of the reduced
/// Gröbner basis of J + (T - x) in P[T] free of the variables of P, for
/// the elimination order on them.
fn minimal_polynomial(affine: &Affine, x: &Elem) -> RResult<Vec<Elem>> {
    affine.need_finite()?;
    let r = affine.poly_ring();
    let (base, n, _) = shape(r);
    let lift = |t: &Terms, k: u64| -> Terms { t.iter().map(|(c, e)| (c.clone(), e.iter().copied().chain(std::iter::once(k)).collect())).collect() };
    let mut gens: Vec<Terms> = affine.groebner()?.iter().map(|t| lift(t, 0)).collect();
    let mut tx: Terms = lift(&terms(x), 0).into_iter().map(|(c, e)| Ok((c.neg()?, e))).collect::<RResult<_>>()?;
    tx.push((Elem::one(base)?, std::iter::repeat_n(0, n).chain(std::iter::once(1)).collect()));
    gens.push(tx);
    let h = engine(r, gb::groebner(base, n + 1, &Order::ElimK(n), &gens))?;
    let p = h.iter().find(|p| p.iter().all(|(_, e)| e[..n].iter().all(|&k| k == 0))).expect("a minimal polynomial in finite dimension");
    let d = p[0].1[n] as usize;
    let mut cs = vec![Elem::zero(base); d + 1];
    for (c, e) in p {
        cs[e[n] as usize] = c.clone();
    }
    Ok(cs)
}

// ----- intrinsics ------------------------------------------------------------------

fn generator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, affine) = affine_arg(a, 0);
    let (k, n) = (a.int(1)?, shape(affine.poly_ring()).1);
    let Some(i) = k.to_i64().filter(|&k| k >= 1 && k as usize <= n).map(|k| k as usize) else {
        return Err(RuntimeError::runtime(format!("Value for name index ({k}) should be in the range [1..{n}]")));
    };
    let x = affine.poly_ring().ctx.mpoly_gen(i - 1)?;
    one(make_elt(&st, affine.reduce(x)?))
}

/// `AssignNames(~Q, N)`: the names given, and `$.i` for the others.
fn assign_names(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::Struct(st) = &a.args[0] else { unreachable!("an affine algebra") };
    let StructKind::Ring(r) = &st.kind else { unreachable!("an affine algebra") };
    let names = a.seq(1)?;
    let n = r.ngens();
    if names.elems.len() > n {
        return Err(RuntimeError::runtime(format!("Argument 2 should have length at most {n}")));
    }
    let mut out: Vec<Rc<str>> = Vec::with_capacity(n);
    for v in names.elems.iter() {
        match v {
            Value::Str(s) => out.push(Rc::from(s.as_str())),
            _ => return Err(RuntimeError::runtime("Names must be strings")),
        }
    }
    for i in out.len()..n {
        out.push(Rc::from(format!("$.{}", i + 1).as_str()));
    }
    *r.names.borrow_mut() = out;
    none()
}

fn ngens(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, affine) = affine_arg(a, 0);
    intv(Integer::from_u64(shape(affine.poly_ring()).1 as u64))
}

fn preimage_ring(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, affine) = affine_arg(a, 0);
    one(Value::Struct(affine.preimage.clone()))
}

fn divisor_ideal(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, affine) = affine_arg(a, 0);
    one(Value::Struct(affine.ideal.clone()))
}

fn is_finite(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, affine) = affine_arg(a, 0);
    match cardinality(&affine)? {
        Some(q) => Ok(vals![Value::Bool(true), Value::Int(q)]),
        None => boolv(false),
    }
}

/// The number of elements of P/J, if finite: q^d over a field of q
/// elements where P/J has dimension d.
pub fn cardinality(affine: &Affine) -> RResult<Option<Integer>> {
    let base = affine.poly_ring().base().expect("a coefficient ring");
    let Some(q) = crate::rings::props::ring_props(base).and_then(|p| p.cardinality) else {
        return Ok(if affine.is_zero_ring()? { Some(Integer::one()) } else { None });
    };
    Ok(vector_dimension(affine)?.map(|d| q.pow(d as u64)))
}

fn has_finite_dimension(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, affine) = affine_arg(a, 0);
    boolv(vector_dimension(&affine)?.is_some())
}

fn dimension(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, affine) = affine_arg(a, 0);
    match vector_dimension(&affine)? {
        Some(d) => intv(Integer::from_u64(d as u64)),
        None => Err(RuntimeError::runtime("Quotient does not have finite dimension")),
    }
}

fn monomial_basis(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, affine) = affine_arg(a, 0);
    let Some(ms) = standard_monomials(&affine)? else { return Err(RuntimeError::runtime("Quotient does not have finite dimension")) };
    let r = affine.poly_ring();
    let unit = Elem::one(r.ctx.base().expect("a polynomial ring"))?;
    let mut out = VSet::default();
    for e in ms {
        out.insert(make_elt(&st, Elem::mpoly_from_terms(&r.ctx, &[(unit.clone(), e)])?));
    }
    one(Value::ISet(Rc::new(SetIndx { universe: Some(Value::Struct(st)), elems: out, name: Default::default() })))
}

fn minimal_polynomial_of(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = elt_arg(a, 0);
    let affine = affine_of(f.ring()).expect("an affine algebra").clone();
    let cs = minimal_polynomial(&affine, &f.x)?;
    let base = f.ring().base().expect("a coefficient ring").clone();
    let u = it.poly_ring(&base, true)?;
    let Value::Struct(ust) = &u else { unreachable!("a polynomial ring") };
    let StructKind::Ring(ur) = &ust.kind else { unreachable!("a polynomial ring") };
    one(make_elt(ust, Elem::poly_from_coeffs(&ur.ctx, &cs)?))
}

fn is_nilpotent(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = elt_arg(a, 0);
    let affine = affine_of(f.ring()).expect("an affine algebra").clone();
    let cs = minimal_polynomial(&affine, &f.x)?;
    // x is nilpotent when its minimal polynomial is a power of T.
    let d = cs.len() - 1;
    if cs[..d].iter().all(|c| c.is_zero() == Truth::True) {
        return Ok(vals![Value::Bool(true), Value::int(d as i64)]);
    }
    boolv(false)
}

fn is_unit(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = elt_arg(a, 0);
    let affine = affine_of(f.ring()).expect("an affine algebra").clone();
    boolv(affine.inverse(&f.x)?.is_some())
}

fn is_zero(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(elt_arg(a, 0).x.is_zero() == Truth::True)
}

fn is_one(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(elt_arg(a, 0).x.is_one() == Truth::True)
}

fn is_minus_one(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(elt_arg(a, 0).x.is_neg_one() == Truth::True)
}

pub fn register(it: &mut Interp) {
    for name in [".", "Name"] {
        it.def(name, "Q::RngMPolRes, i::RngIntElt -> RngMPolResElt", "The i-th variable of Q.", generator);
    }
    it.def("AssignNames", "~Q::RngMPolRes, N::[MonStgElt]", "Name the variables of Q (for printing), $.i those not named.", assign_names);
    for name in ["Ngens", "Rank"] {
        it.def(name, "Q::RngMPolRes -> RngIntElt", "The number of variables of Q.", ngens);
    }
    for name in ["PreimageRing", "OriginalRing"] {
        it.def(name, "Q::RngMPolRes -> RngMPol", "The polynomial ring P of which Q is the quotient P/J.", preimage_ring);
    }
    it.def("DivisorIdeal", "Q::RngMPolRes -> RngMPol", "The ideal J of P with Q = P/J.", divisor_ideal);
    it.def("PreimageIdeal", "Q::RngMPolRes -> RngMPol", "The preimage in P of Q as an ideal of itself: P.", preimage_ring);
    it.def("IsFinite", "Q::RngMPolRes -> BoolElt, RngIntElt", "Whether Q is finite, and if so its cardinality.", is_finite);
    it.def("HasFiniteDimension", "Q::RngMPolRes -> BoolElt", "Whether Q has finite dimension over its coefficient field.", has_finite_dimension);
    it.def("Dimension", "Q::RngMPolRes -> RngIntElt", "The dimension of Q over its coefficient field.", dimension);
    it.def("MonomialBasis", "Q::RngMPolRes -> SetIndx", "The monomials forming a basis of Q over its coefficient field, increasing.", monomial_basis);
    it.def("MinimalPolynomial", "f::RngMPolResElt -> RngUPolElt", "The minimal polynomial of f over the coefficient field.", minimal_polynomial_of);
    it.def("IsNilpotent", "f::RngMPolResElt -> BoolElt, RngIntElt", "Whether f is nilpotent, and if so the least k with f^k = 0.", is_nilpotent);
    it.def("IsUnit", "f::RngMPolResElt -> BoolElt", "Whether f is a unit.", is_unit);
    it.def("IsZero", "f::RngMPolResElt -> BoolElt", "Whether f is zero.", is_zero);
    it.def("IsOne", "f::RngMPolResElt -> BoolElt", "Whether f is one.", is_one);
    it.def("IsMinusOne", "f::RngMPolResElt -> BoolElt", "Whether f is minus one.", is_minus_one);
}
