//! Functional decomposition of univariate polynomials over a field
//! (Decomposition). A right component h of f (f = g(h)) is a field
//! k(f) ⊆ k(h) ⊆ k(t), and the complete decompositions of f are the maximal
//! chains of these fields, found as the handbook describes Magma's method
//! [ACvHS17]: as the intersections of the principal fields (van Hoeij,
//! Klüners and Novocin), one for each irreducible factor φ of
//! (f(x) - f(y))/(x - y), the polynomials h with φ(x, y) | h(x) - h(y).
//! When the characteristic does not divide the degree n there is at most one
//! right component of each degree r | n, the approximate (n/r)-th root of f,
//! and the fields are found from those instead. When f is a polynomial in
//! x^p the Frobenius x^p also enters the chains.
//!
//! Components are normalized monic with no constant term; the outermost one
//! takes the leading coefficient and constant term of f.

use std::rc::Rc;

use calyx_flint::gr::{Ctx, CtxKind, Elem, GrResult, MonomialOrder, Truth};
use calyx_flint::mpoly as fm;
use calyx_flint::upoly as fu;

use super::{base_of, len, like, pol};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::one;
use crate::rings::props::ring_props;
use crate::value::*;

fn nonzero(c: &Elem) -> bool {
    c.is_zero() != Truth::True
}

/// A basis of the kernel of the matrix `rows` (`ncols` columns over the
/// field `k`).
fn kernel(k: &Rc<Ctx>, mut rows: Vec<Vec<Elem>>, ncols: usize) -> GrResult<Vec<Vec<Elem>>> {
    let mut pivots = Vec::new();
    for c in 0..ncols {
        let r = pivots.len();
        let Some(p) = (r..rows.len()).find(|&i| nonzero(&rows[i][c])) else { continue };
        rows.swap(r, p);
        let inv = rows[r][c].inv()?;
        for j in c..ncols {
            rows[r][j] = rows[r][j].mul(&inv)?;
        }
        for i in 0..rows.len() {
            if i != r && nonzero(&rows[i][c]) {
                let m = rows[i][c].clone();
                for j in c..ncols {
                    let d = m.mul(&rows[r][j])?;
                    rows[i][j] = rows[i][j].sub(&d)?;
                }
            }
        }
        pivots.push(c);
    }
    let mut out = Vec::new();
    for free in (0..ncols).filter(|c| !pivots.contains(c)) {
        let mut v = vec![Elem::zero(k); ncols];
        v[free] = Elem::one(k)?;
        for (i, &p) in pivots.iter().enumerate() {
            v[p] = rows[i][free].neg()?;
        }
        out.push(v);
    }
    Ok(out)
}

/// The monic polynomial of least degree in the span of `vs`, coefficient
/// vectors of t, ..., t^n (so with no constant term).
fn least(kx: &Rc<Ctx>, mut vs: Vec<Vec<Elem>>) -> GrResult<Option<Elem>> {
    let n = vs.first().map_or(0, |v| v.len());
    // Echelon form from the top degree down; the last pivot row leads with
    // the least degree.
    let mut best = None;
    let mut r = 0;
    for c in (0..n).rev() {
        let Some(p) = (r..vs.len()).find(|&i| nonzero(&vs[i][c])) else { continue };
        vs.swap(r, p);
        for i in 0..vs.len() {
            if i != r && nonzero(&vs[i][c]) {
                let m = vs[i][c].div(&vs[r][c])?;
                for j in 0..=c {
                    let d = m.mul(&vs[r][j])?;
                    vs[i][j] = vs[i][j].sub(&d)?;
                }
            }
        }
        best = Some(r);
        r += 1;
    }
    let Some(b) = best else { return Ok(None) };
    let k = kx.base().expect("a polynomial ring");
    let cs: Vec<Elem> = std::iter::once(Elem::zero(k)).chain(vs[b].iter().cloned()).collect();
    Ok(Some(fu::make_monic(&Elem::poly_from_coeffs(kx, &cs)?)?))
}

/// The coefficients of t, ..., t^n in h.
fn vector(h: &Elem, n: usize) -> Vec<Elem> {
    let k = h.ctx().base().expect("a polynomial ring");
    (1..=n).map(|i| if i < h.poly_len() { h.poly_coeff(i) } else { Elem::zero(k) }).collect()
}

/// The powers h, h^2, ... of degree at most n, as vectors.
fn powers(h: &Elem, n: usize) -> GrResult<Vec<Vec<Elem>>> {
    let s = h.poly_len() - 1;
    let mut out = Vec::new();
    let mut p = h.clone();
    for i in 1..=n / s {
        out.push(vector(&p, n));
        if i < n / s {
            p = p.mul(h)?;
        }
    }
    Ok(out)
}

/// The generator of k(a) ∩ k(b), for a and b generating fields that contain
/// k(f) with f of degree n: the least element of k[a] ∩ k[b].
fn meet(kx: &Rc<Ctx>, a: &Elem, b: &Elem, n: usize) -> GrResult<Elem> {
    let k = kx.base().expect("a polynomial ring");
    let (pa, pb) = (powers(a, n)?, powers(b, n)?);
    // Σ α_i a^i = Σ β_j b^j, row by row of the coefficients.
    let mut rows = Vec::with_capacity(n);
    for r in 0..n {
        let mut row: Vec<Elem> = pa.iter().map(|v| v[r].clone()).collect();
        for v in &pb {
            row.push(v[r].neg()?);
        }
        rows.push(row);
    }
    let mut vs = Vec::new();
    for sol in kernel(k, rows, pa.len() + pb.len())? {
        let mut v = vec![Elem::zero(k); n];
        for (i, p) in pa.iter().enumerate() {
            if nonzero(&sol[i]) {
                for r in 0..n {
                    let d = sol[i].mul(&p[r])?;
                    v[r] = v[r].add(&d)?;
                }
            }
        }
        vs.push(v);
    }
    Ok(least(kx, vs)?.expect("k(f) lies in both"))
}

/// g with b = g(a), if there is one.
fn expand(a: &Elem, b: &Elem) -> GrResult<Option<Elem>> {
    let k = a.ctx().base().expect("a polynomial ring");
    let mut digits = Vec::new();
    let mut q = b.clone();
    while q.poly_len() > 0 {
        let (q2, r) = fu::divrem(&q, a)?;
        if r.poly_len() > 1 {
            return Ok(None);
        }
        digits.push(if r.poly_len() == 0 { Elem::zero(k) } else { r.poly_coeff(0) });
        q = q2;
    }
    Ok(Some(Elem::poly_from_coeffs(a.ctx(), &digits)?))
}

// ----- the fields ----------------------------------------------------------------------

/// f g mod x^n.
fn mullow(f: &Elem, g: &Elem, n: usize) -> GrResult<Elem> {
    fu::truncate(&f.mul(g)?, n)
}

/// f^e mod x^n.
fn pow_low(f: &Elem, mut e: u64, n: usize) -> GrResult<Elem> {
    let mut r = Elem::one(f.ctx())?;
    let mut b = fu::truncate(f, n)?;
    while e > 0 {
        if e & 1 == 1 {
            r = mullow(&r, &b, n)?;
        }
        e >>= 1;
        if e > 0 {
            b = mullow(&b, &b, n)?;
        }
    }
    Ok(r)
}

/// 1/g mod x^n, for g(0) a unit, by Newton's iteration.
fn inv_series(g: &Elem, n: usize) -> GrResult<Elem> {
    let kx = g.ctx();
    let mut v = Elem::poly_from_coeffs(kx, &[g.poly_coeff(0).inv()?])?;
    let two = Elem::from_i64(kx, 2)?;
    let mut m = 1;
    while m < n {
        m = (2 * m).min(n);
        let gv = mullow(&fu::truncate(g, m)?, &v, m)?;
        v = mullow(&v, &two.sub(&gv)?, m)?;
    }
    Ok(v)
}

/// The u with u(0) = 1 and u^s = F mod x^n, for F(0) = 1 and s a unit, by
/// Newton's iteration.
fn root_series(ff: &Elem, s: u64, n: usize) -> GrResult<Elem> {
    let kx = ff.ctx();
    let k = kx.base().expect("a polynomial ring");
    let si = Elem::from_i64(k, s as i64)?.inv()?;
    let mut u = Elem::one(kx)?;
    let mut m = 1;
    while m < n {
        m = (2 * m).min(n);
        let us1 = pow_low(&u, s - 1, m)?;
        let d = fu::truncate(ff, m)?.sub(&mullow(&us1, &u, m)?)?;
        u = u.add(&mullow(&d, &inv_series(&us1, m)?, m)?.poly_mul_scalar(&si)?)?;
    }
    Ok(u)
}

/// The right component of degree r of the monic f of degree n with no
/// constant term, when n/r is a unit: its approximate (n/r)-th root, the h
/// with deg(f - h^(n/r)) < n - r, if f is a polynomial in it.
fn approximate_root(f: &Elem, r: usize) -> GrResult<Option<Elem>> {
    let n = f.poly_len() - 1;
    let u = root_series(&fu::reverse(f, n + 1)?, (n / r) as u64, r)?;
    let k = f.ctx().base().expect("a polynomial ring");
    let mut cs: Vec<Elem> = (0..=r).map(|i| if i == 0 || r - i >= u.poly_len() { Elem::zero(k) } else { u.poly_coeff(r - i) }).collect();
    cs[r] = Elem::one(k)?;
    let h = Elem::poly_from_coeffs(f.ctx(), &cs)?;
    Ok(expand(&h, f)?.map(|_| h))
}

/// The principal fields of the separable monic f with no constant term, by
/// their generators: for each irreducible factor φ of (f(x) - f(y))/(x - y)
/// the h of least degree with φ(x, y) | h(x) - h(y).
fn principal(kx: &Rc<Ctx>, f: &Elem) -> GrResult<Vec<Elem>> {
    let k = kx.base().expect("a polynomial ring").clone();
    let n = f.poly_len() - 1;
    // (f(x) - f(y))/(x - y) = Σ f_i Σ_{u+v=i-1} x^u y^v.
    let kxy = Ctx::mpoly(&k, 2, MonomialOrder::Lex);
    let mut terms = Vec::new();
    for i in 1..=n {
        let a = f.poly_coeff(i);
        if nonzero(&a) {
            for u in 0..i {
                terms.push((a.clone(), vec![u as u64, (i - 1 - u) as u64]));
            }
        }
    }
    let (_, factors) = fm::factor(&Elem::mpoly_from_terms(&kxy, &terms)?, false)?;
    let ky = Ctx::poly(&k);
    let kyx = Ctx::poly(&ky);
    let x = Elem::poly_from_coeffs(&kyx, &[Elem::zero(&ky), Elem::one(&ky)?])?;
    let mut out: Vec<Elem> = Vec::new();
    for (q, _) in factors {
        // φ in k[y][x]: its degree in x is its total degree, and its leading
        // coefficient in x a constant.
        let dx = (0..q.mpoly_len()).map(|i| q.mpoly_term(i).1[0]).max().unwrap_or(0) as usize;
        let mut cx = vec![vec![Elem::zero(&k); n + 1]; dx + 1];
        for i in 0..q.mpoly_len() {
            let (c, e) = q.mpoly_term(i);
            cx[e[0] as usize][e[1] as usize] = c;
        }
        let lc = cx[dx][0].inv()?;
        let mut coeffs = Vec::with_capacity(dx + 1);
        for ys in &cx {
            let ys = ys.iter().map(|c| c.mul(&lc)).collect::<GrResult<Vec<_>>>()?;
            coeffs.push(Elem::poly_from_coeffs(&ky, &ys)?);
        }
        let phi = Elem::poly_from_coeffs(&kyx, &coeffs)?;
        // Column j: x^j mod φ - y^j, over the monomials x^a y^b (a < dx).
        let width = n + 1;
        let mut cols = Vec::with_capacity(n);
        let mut rj = Elem::one(&kyx)?;
        for j in 1..=n {
            rj = fu::divrem(&rj.mul(&x)?, &phi)?.1;
            let mut col = vec![Elem::zero(&k); dx * width];
            for a in 0..rj.poly_len() {
                let ya = rj.poly_coeff(a);
                for b in 0..ya.poly_len() {
                    col[a * width + b] = ya.poly_coeff(b);
                }
            }
            col[j] = col[j].sub(&Elem::one(&k)?)?;
            cols.push(col);
        }
        let rows: Vec<Vec<Elem>> = (0..dx * width).map(|r| cols.iter().map(|c| c[r].clone()).collect::<Vec<_>>()).filter(|row| row.iter().any(nonzero)).collect();
        if let Some(h) = least(kx, kernel(&k, rows, n)?)? {
            if !out.iter().any(|g| g.equal(&h) == Truth::True) {
                out.push(h);
            }
        }
    }
    Ok(out)
}

/// The generator t of k(t).
fn gen_t(kx: &Rc<Ctx>) -> GrResult<Elem> {
    let k = kx.base().expect("a polynomial ring");
    Elem::poly_from_coeffs(kx, &[Elem::zero(k), Elem::one(k)?])
}

/// The principal fields of f (degree n) and their intersections, after t
/// and f.
fn lattice(kx: &Rc<Ctx>, f: &Elem) -> GrResult<Vec<Elem>> {
    let n = f.poly_len() - 1;
    let mut fs = vec![gen_t(kx)?, f.clone()];
    for h in principal(kx, f)? {
        if !fs.iter().any(|g| g.equal(&h) == Truth::True) {
            fs.push(h);
        }
    }
    let mut i = 2;
    while i < fs.len() {
        for j in 2..i {
            let m = meet(kx, &fs[i], &fs[j], n)?;
            if !fs.iter().any(|g| g.equal(&m) == Truth::True) {
                fs.push(m);
            }
        }
        i += 1;
    }
    Ok(fs)
}

/// The fields between k(f) and k(t) for the separable monic f with no
/// constant term, by their generators in increasing degree (t first, f
/// last): in the tame case the approximate roots, otherwise the principal
/// fields and their intersections.
fn fields(kx: &Rc<Ctx>, f: &Elem, p: u64) -> GrResult<Vec<Elem>> {
    let n = f.poly_len() - 1;
    if p == 0 || n as u64 % p != 0 {
        let mut fs = vec![gen_t(kx)?];
        for r in (2..n).filter(|r| n % r == 0) {
            if let Some(h) = approximate_root(f, r)? {
                fs.push(h);
            }
        }
        fs.push(f.clone());
        return Ok(fs);
    }
    let mut fs = lattice(kx, f)?;
    fs.sort_by_key(|h| h.poly_len());
    Ok(fs)
}

/// The maximal chains of the fields `fs` (increasing degree, t first, f
/// last), as the components [f1, ..., fr] with f = fr(...(f1)).
fn chains(fs: &[Elem]) -> GrResult<Vec<Vec<Elem>>> {
    let m = fs.len();
    let deg = |i: usize| fs[i].poly_len() - 1;
    // comp[a][b]: the g with fs[b] = g(fs[a]), where fs[b] lies in fs[a].
    let mut comp: Vec<Vec<Option<Elem>>> = vec![vec![None; m]; m];
    for a in 0..m {
        for b in a + 1..m {
            if deg(b) > deg(a) && deg(b) % deg(a) == 0 {
                comp[a][b] = expand(&fs[a], &fs[b])?;
            }
        }
    }
    let covers = |a: usize, b: usize| comp[a][b].is_some() && !(a + 1..b).any(|c| comp[a][c].is_some() && comp[c][b].is_some());
    let below: Vec<Vec<usize>> = (0..m).map(|a| (a + 1..m).filter(|&b| covers(a, b)).collect()).collect();
    let mut out = Vec::new();
    let mut stack: Vec<(usize, Vec<Elem>)> = vec![(0, Vec::new())];
    while let Some((a, cs)) = stack.pop() {
        if a == m - 1 {
            out.push(cs);
            continue;
        }
        for &b in below[a].iter().rev() {
            let mut c = cs.clone();
            c.push(comp[a][b].clone().expect("a subfield"));
            stack.push((b, c));
        }
    }
    Ok(out)
}

/// The complete decompositions of the monic f of degree at least 2 with no
/// constant term over a field of characteristic p: f = g(x^q) with g
/// separable, and the q = p^e Frobenius components x^p interleaved with
/// those of g, every component of g with Frobenius components outside it
/// twisted by their inverse (g(x^p) = x^p ∘ g^(1/p)).
fn decompositions(kx: &Rc<Ctx>, f: &Elem, p: u64) -> GrResult<Vec<Vec<Elem>>> {
    let k = kx.base().expect("a polynomial ring").clone();
    let mut g = f.clone();
    let mut e = 0;
    while p > 0 && g.poly_derivative()?.poly_len() == 0 {
        let cs: Vec<Elem> = (0..g.poly_len()).step_by(p as usize).map(|i| g.poly_coeff(i)).collect();
        g = Elem::poly_from_coeffs(kx, &cs)?;
        e += 1;
    }
    let base = if g.poly_len() > 2 { chains(&fields(kx, &g, p)?)? } else { vec![Vec::new()] };
    if e == 0 {
        return Ok(base);
    }
    let mut xp = vec![Elem::zero(&k); p as usize + 1];
    xp[p as usize] = Elem::one(&k)?;
    let xp = Elem::poly_from_coeffs(kx, &xp)?;
    let degree = match k.kind() {
        CtxKind::FqZech { degree, .. } | CtxKind::FqNmod { degree, .. } | CtxKind::Fq { degree, .. } | CtxKind::FqPacked { degree, .. } => *degree,
        _ => 1,
    };
    let twist = |h: &Elem, l: usize| -> GrResult<Elem> {
        let j = (-(l as i64)).rem_euclid(degree as i64);
        if j == 0 {
            return Ok(h.clone());
        }
        let cs = (0..h.poly_len()).map(|i| h.poly_coeff(i).fq_frobenius(j)).collect::<GrResult<Vec<_>>>()?;
        Elem::poly_from_coeffs(kx, &cs)
    };
    let mut out = Vec::new();
    for comps in base {
        let r = comps.len() + e;
        // The positions of the Frobenius components, in lexicographic order.
        let mut pos: Vec<usize> = (0..e).collect();
        loop {
            let mut seq = Vec::with_capacity(r);
            let (mut gi, mut inner) = (0, 0);
            for slot in 0..r {
                if pos.get(inner) == Some(&slot) {
                    seq.push(xp.clone());
                    inner += 1;
                } else {
                    seq.push(twist(&comps[gi], e - inner)?);
                    gi += 1;
                }
            }
            out.push(seq);
            let Some(i) = (0..e).rev().find(|&i| pos[i] < r - e + i) else { break };
            pos[i] += 1;
            for j in i + 1..e {
                pos[j] = pos[j - 1] + 1;
            }
        }
    }
    Ok(out)
}

// ----- Magma's form ---------------------------------------------------------------------

/// The order of Magma's list of decompositions.
// TODO(2.29): check against the calculator; this keeps the order of the
// chains, by the degrees of the fields from the inside out.
fn magma_order(_ds: &mut [Vec<Elem>]) {}

/// Decomposition(f : All): the complete decompositions of f over a field,
/// or with All false the first of them.
pub(super) fn decomposition_fn(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    let all = match a.param("All") {
        None | Some(Value::Undef) => true,
        Some(Value::Bool(b)) => *b,
        Some(v) => return Err(RuntimeError::runtime(format!("Parameter 'All' should be a boolean (got {})", it.type_name_ext(v)))),
    };
    let props = ring_props(&base_of(&f)).filter(|p| p.field && p.exact);
    let Some(props) = props else { return Err(RuntimeError::runtime("Argument 1 must be defined over a field")) };
    if len(&f) < 2 {
        return Err(RuntimeError::runtime("Argument 1 must be non-constant"));
    }
    let kx = f.x.ctx();
    let mut ds = if len(&f) == 2 {
        vec![vec![f.x.clone()]]
    } else {
        // f = lc f~ + c0 with f~ monic with no constant term; the outermost
        // component takes lc and c0 back.
        let lc = fu::lead(&f.x);
        let c0 = Elem::poly_from_coeffs(kx, &[f.x.poly_coeff(0)])?;
        let g = fu::make_monic(&f.x.sub(&c0)?)?;
        // A characteristic beyond a word exceeds the degree, as if 0.
        let p = props.characteristic.to_u64().unwrap_or(0);
        let mut ds = decompositions(kx, &g, p).map_err(|_| RuntimeError::runtime("Decomposition is not available over this coefficient ring"))?;
        for d in ds.iter_mut() {
            let last = d.last_mut().expect("a non-empty decomposition");
            *last = last.poly_mul_scalar(&lc)?.add(&c0)?;
        }
        magma_order(&mut ds);
        ds
    };
    if !all {
        ds.truncate(1);
    }
    let inner = Value::structure(StructKind::PowerSeq(Some(f.parent_value())));
    let seqs = ds.into_iter().map(|d| Value::seq(Some(f.parent_value()), d.into_iter().map(|x| like(&f, x)).collect())).collect();
    one(Value::seq(Some(inner), seqs))
}

#[cfg(test)]
mod tests {
    use super::*;
    use calyx_flint::Integer;
    use calyx_flint::gr::conway_polynomial;

    fn poly(kx: &Rc<Ctx>, cs: &[i64]) -> Elem {
        let k = kx.base().unwrap();
        Elem::poly_from_coeffs(kx, &cs.iter().map(|&c| Elem::from_i64(k, c).unwrap()).collect::<Vec<_>>()).unwrap()
    }

    fn compose(d: &[Elem]) -> Elem {
        let mut f = gen_t(d[0].ctx()).unwrap();
        for g in d {
            f = g.poly_compose(&f).unwrap();
        }
        f
    }

    /// The decompositions of the monic associate of f: `count` of them,
    /// all composing to it, with normalized components.
    fn check(kx: &Rc<Ctx>, f: &Elem, p: u64, count: usize) -> Vec<Vec<Elem>> {
        let f = fu::make_monic(f).unwrap();
        let ds = decompositions(kx, &f, p).unwrap();
        assert_eq!(ds.len(), count, "{f:?}: {ds:?}");
        for d in &ds {
            assert_eq!(compose(d).equal(&f), Truth::True, "{d:?}");
            assert!(d.iter().all(|g| g.poly_len() > 2 && fu::lead(g).is_one() == Truth::True && g.poly_coeff(0).is_zero() == Truth::True));
        }
        ds
    }

    fn gf(p: u64, d: u64) -> Rc<Ctx> {
        Ctx::poly(&Ctx::finite_field(&Integer::from_u64(p), &conway_polynomial(p, d).unwrap(), false).unwrap())
    }

    #[test]
    fn rational_decompositions() {
        let qx = Ctx::poly(&Ctx::rationals());
        let mut x12 = vec![0; 13];
        x12[12] = 1;
        check(&qx, &poly(&qx, &x12), 0, 3);
        check(&qx, &poly(&qx, &[0, 1, 0, 0, 0, 1]), 0, 1);
        // T6 = T2(T3) = T3(T2), less its constant term.
        check(&qx, &poly(&qx, &[0, 0, 18, 0, -48, 0, 32]), 0, 2);
        // x^2 (x^2 + 1)^2 = x^2 ∘ (x^3 + x) = (x^3 + 2x^2 + x) ∘ x^2.
        check(&qx, &poly(&qx, &[0, 0, 1, 0, 2, 0, 1]), 0, 2);
        // (x^3 + x)^3 has one right component of degree 3.
        check(&qx, &poly(&qx, &[0, 0, 0, 1, 0, 3, 0, 3, 0, 1]), 0, 1);
    }

    #[test]
    fn finite_field_decompositions() {
        let f3 = gf(3, 1);
        // x^9 - x over GF(3): (x^3 + x)(x^3 - x) and (x^3 - x)(x^3 + x).
        check(&f3, &poly(&f3, &[0, -1, 0, 0, 0, 0, 0, 0, 0, 1]), 3, 2);
        // x^6 = x^2(x^3) = x^3(x^2).
        check(&f3, &poly(&f3, &[0, 0, 0, 0, 0, 0, 1]), 3, 2);
        let f2 = gf(2, 1);
        check(&f2, &poly(&f2, &[0, 1, 0, 0, 1]), 2, 1);
        check(&gf(2, 2), &poly(&gf(2, 2), &[0, 1, 0, 0, 1]), 2, 3);
        // The handbook's x^9 - x over GF(9).
        let f9 = gf(3, 2);
        check(&f9, &poly(&f9, &[0, -1, 0, 0, 0, 0, 0, 0, 0, 1]), 3, 4);
        // (x^3 + w x)(x^3) = x^3 ∘ (x^3 + w^3 x): the Frobenius twists.
        let w = f9.base().unwrap().generator().unwrap();
        let mut cs: Vec<Elem> = (0..10).map(|_| Elem::zero(f9.base().unwrap())).collect();
        cs[3] = w;
        cs[9] = Elem::one(f9.base().unwrap()).unwrap();
        check(&f9, &Elem::poly_from_coeffs(&f9, &cs).unwrap(), 3, 2);
    }

    #[test]
    fn tame_agrees_with_principal() {
        let f7 = gf(7, 1);
        let mut x12 = vec![0; 13];
        x12[12] = 1;
        for cs in [&[0i64, 0, 18, 0, -48, 0, 32][..], &x12, &[0, 3, 1, 4, 1, 5, 9, 2, 6], &[0, 0, 1, 0, 2, 0, 1]] {
            let f = fu::make_monic(&poly(&f7, cs)).unwrap();
            let degrees = |fs: Vec<Elem>| {
                let mut d: Vec<usize> = fs.iter().map(|h| h.poly_len()).collect();
                d.sort();
                d
            };
            assert_eq!(degrees(fields(&f7, &f, 7).unwrap()), degrees(lattice(&f7, &f).unwrap()), "{f:?}");
        }
    }
}
