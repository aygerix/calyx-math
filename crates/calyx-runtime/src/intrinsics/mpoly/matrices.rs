//! The matrices of multivariate polynomials (text/246): the Jacobian matrix
//! of a sequence of polynomials, and the symmetric bilinear form and the
//! diagonal form of a polynomial of degree 2. They are made through the
//! matrices module. The Gram orthogonalization behind the diagonal form uses
//! FLINT alone, so that the Lattices chapter can move it and build
//! OrthogonalizeGram (text/339) on it.

use std::ops::Range;
use std::rc::Rc;

use calyx_flint::gr::{CtxKind, Elem, GrResult, Truth};
use calyx_flint::mat::Mat;
use calyx_flint::{Integer, Rational};

use super::{base_of, like, mpol, partial, rank, terms};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::matrices::{self, Mtrx, Shape};
use crate::intrinsics::one;
use crate::intrinsics::upoly::put_entry;
use crate::rings::props::ring_props;
use crate::rings::{Elt, ring_of};
use crate::value::*;

/// The matrix of the partial derivatives d f_i / d x_j of the polynomials
/// f_i of S by the variables x_j of their ring, over that ring: in the
/// matrix algebra when it is square, in the matrix space otherwise (with no
/// rows for an empty S).
pub(super) fn jacobian_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = a.seq(0)?.clone();
    let Some(ring) = s.universe.clone() else { return Err(RuntimeError::runtime("Bad argument types")) };
    let n = match ring_of(&ring) {
        Some((_, r)) => rank(r),
        None => return Err(RuntimeError::runtime("Bad argument types")),
    };
    let ctx = matrices::entry_ctx(it, &ring)?;
    let mut m = Mat::zero(&ctx, s.elems.len(), n);
    for (i, f) in s.elems.iter().enumerate() {
        let Value::Elt(f) = f else { unreachable!("a polynomial") };
        for j in 0..n {
            put_entry(it, &ring, &mut m, i, j, &partial(&f.x, j, 1)?)?;
        }
    }
    one(matrices::mat_value(it, &ring, m)?)
}

/// The symmetric matrix B with f = v B v^T for f of total degree 2, where v
/// holds the variables and, unless f is homogeneous, 1 after them: the
/// coefficient of x_i^2 at (i, i) and half that of x_i x_j at (i, j) and
/// (j, i). Magma wants 2 to be a unit. Also the rank n of the ring of f.
fn form(f: &Elt) -> RResult<(Vec<Vec<Elem>>, usize)> {
    let ts = terms(&f.x);
    let degs: Vec<u64> = ts.iter().map(|(_, e)| e.iter().sum()).collect();
    if degs.iter().max() != Some(&2) {
        return Err(RuntimeError::runtime("The polynomial must have degree 2"));
    }
    let base = f.x.ctx().base().expect("a polynomial ring").clone();
    let Ok(half) = Elem::from_integer(&base, &Integer::from_u64(2))?.inv() else {
        return Err(RuntimeError::runtime("2 must have an inverse"));
    };
    let n = rank(f.ring());
    let size = if degs.iter().all(|&d| d == 2) { n } else { n + 1 };
    let mut b = vec![vec![Elem::zero(&base); size]; size];
    for (c, e) in &ts {
        // The two variables of the term, the constant 1 counting as variable n.
        let mut vs: Vec<usize> = e.iter().enumerate().flat_map(|(i, &k)| (0..k).map(move |_| i)).collect();
        vs.resize(2, n);
        let (i, j) = (vs[0], vs[1]);
        if i == j {
            b[i][i] = c.clone();
        } else {
            let h = c.mul(&half)?;
            b[i][j] = h.clone();
            b[j][i] = h;
        }
    }
    Ok((b, n))
}

/// The square matrix with the given rows in the matrix space over `ring`,
/// where Magma puts forms (not in the matrix algebra).
fn space_matrix(it: &mut Interp, ring: &Value, rows: &[Vec<Elem>]) -> RResult<Value> {
    let size = rows.len();
    let ctx = matrices::entry_ctx(it, ring)?;
    let mut m = Mat::zero(&ctx, size, size);
    for (i, row) in rows.iter().enumerate() {
        for (j, x) in row.iter().enumerate() {
            put_entry(it, ring, &mut m, i, j, x)?;
        }
    }
    let p = matrices::parent(it, ring, size, size, Shape::Space)?;
    Ok(Value::Mat(Rc::new(Mtrx { parent: p, m })))
}

pub(super) fn symmetric_bilinear_form(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let (b, _) = form(&f)?;
    one(space_matrix(it, &base_of(&f), &b)?)
}

/// The diagonal form of f of total degree 2 over a field: the sum of the
/// q_i x_i^2 for the rows T_i of norm q_i that orthogonalize the symmetric
/// bilinear form of f (x_(n+1) = 1), and T. A bare call prints the form
/// alone, as in Magma.
pub(super) fn diagonal_form(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let ring = base_of(&f);
    if !ring_props(&ring).is_some_and(|p| p.field) {
        return Err(RuntimeError::runtime("Coefficient ring must be a field"));
    }
    let (b, n) = form(&f)?;
    let t = orthogonalize_gram(&b, matches!(b[0][0].ctx().kind(), CtxKind::Rationals))?;
    let mut ts = Vec::new();
    for (i, row) in t.iter().enumerate() {
        let q = gram_norm(&b, row)?;
        if q.is_zero() != Truth::True {
            let mut e = vec![0; n];
            if i < n {
                e[i] = 2;
            }
            ts.push((q, e));
        }
    }
    let d = like(&f, Elem::mpoly_from_terms(f.x.ctx(), &ts)?);
    if a.nresults < 2 {
        return one(d);
    }
    Ok(vals![d, space_matrix(it, &ring, &t)?])
}

// ----- Gram orthogonalization ------------------------------------------------------

/// Rows T with T B T^t diagonal, for a symmetric matrix B over a field of
/// characteristic other than 2, made as Magma's DiagonalForm makes them
/// (found by black-box runs of Magma 2.22). Each row starts as a unit vector
/// and is made orthogonal to the rows done before it:
///
/// - Over Q (`rational`) fraction-free, w := q(v) w - B(w, v) v for each
///   earlier row v with q(v) = B(v, v) != 0 and B(w, v) != 0, then scaled to
///   an integral primitive row. A row of norm 0 is combined with the first
///   later row y it is not orthogonal to, into q(y) w - B(w, y) y (w - y if
///   q(y) = 0). A row orthogonal to all later rows (in the radical) swaps
///   places with the last row still to do; at the end the rows go back to
///   the places they started in.
/// - Over other fields by Gram-Schmidt, w := w - B(w, v)/q(v) v. A row of
///   norm 0 swaps places with the first later row of non-zero norm, or else
///   is added to the first later row it is not orthogonal to. A row in the
///   radical swaps places with the last row still to do, and the rows stay
///   in the places they end in.
pub fn orthogonalize_gram(b: &[Vec<Elem>], rational: bool) -> GrResult<Vec<Vec<Elem>>> {
    let m = b.len();
    let ctx = b[0][0].ctx().clone();
    let (zero, unit) = (Elem::zero(&ctx), Elem::one(&ctx)?);
    let mut w: Vec<Vec<Elem>> = (0..m).map(|i| (0..m).map(|j| if i == j { unit.clone() } else { zero.clone() }).collect()).collect();
    // The place in B of the unit vector each row started as.
    let mut start: Vec<usize> = (0..m).collect();
    let nonzero = |x: &Elem| x.is_zero() != Truth::True;
    // The rows before k are done; those from `end` on are in the radical.
    let (mut k, mut end) = (0, m);
    while k < m {
        if k < end && !nonzero(&gram_norm(b, &w[k])?) {
            if !rational {
                if let Some(j) = find(k + 1..end, |j| Ok(nonzero(&gram_norm(b, &w[j])?)))? {
                    w.swap(k, j);
                    start.swap(k, j);
                    continue;
                }
            }
            let bw = gram_apply(b, &w[k])?;
            match find(k + 1..end, |j| Ok(nonzero(&dot(&w[j], &bw)?)))? {
                Some(j) => {
                    let y = w[j].clone();
                    w[k] = if rational {
                        let (qy, c) = (gram_norm(b, &y)?, dot(&y, &bw)?);
                        let (s, c) = if nonzero(&qy) { (qy, c) } else { (unit.clone(), unit.clone()) };
                        primitive(combine(&s, &w[k], &c, &y)?)?
                    } else {
                        w[k].iter().zip(&y).map(|(s, t)| s.add(t)).collect::<GrResult<_>>()?
                    };
                }
                None => {
                    end -= 1;
                    if k < end {
                        w.swap(k, end);
                        start.swap(k, end);
                        continue;
                    }
                }
            }
        }
        // The row in place k is done: make the later rows orthogonal to it.
        let v = w[k].clone();
        let bv = gram_apply(b, &v)?;
        let q = dot(&v, &bv)?;
        if nonzero(&q) {
            for row in &mut w[k + 1..] {
                let c = dot(row, &bv)?;
                if nonzero(&c) {
                    *row = if rational { primitive(combine(&q, row, &c, &v)?)? } else { combine(&unit, row, &c.div(&q)?, &v)? };
                }
            }
        }
        k += 1;
    }
    if !rational {
        return Ok(w);
    }
    let mut t = vec![Vec::new(); m];
    for (row, s) in w.into_iter().zip(start) {
        t[s] = row;
    }
    Ok(t)
}

/// The first j in `r` with `p(j)`.
fn find(r: Range<usize>, mut p: impl FnMut(usize) -> GrResult<bool>) -> GrResult<Option<usize>> {
    for j in r {
        if p(j)? {
            return Ok(Some(j));
        }
    }
    Ok(None)
}

/// B v.
fn gram_apply(b: &[Vec<Elem>], v: &[Elem]) -> GrResult<Vec<Elem>> {
    let mut out = vec![Elem::zero(v[0].ctx()); b.len()];
    for (j, x) in v.iter().enumerate() {
        if x.is_zero() == Truth::True {
            continue;
        }
        for (o, row) in out.iter_mut().zip(b) {
            if row[j].is_zero() != Truth::True {
                *o = o.add(&row[j].mul(x)?)?;
            }
        }
    }
    Ok(out)
}

fn dot(u: &[Elem], v: &[Elem]) -> GrResult<Elem> {
    let mut s = Elem::zero(u[0].ctx());
    for (x, y) in u.iter().zip(v) {
        if x.is_zero() != Truth::True && y.is_zero() != Truth::True {
            s = s.add(&x.mul(y)?)?;
        }
    }
    Ok(s)
}

/// The norm v B v^t.
fn gram_norm(b: &[Vec<Elem>], v: &[Elem]) -> GrResult<Elem> {
    dot(v, &gram_apply(b, v)?)
}

/// a x - c y.
fn combine(a: &Elem, x: &[Elem], c: &Elem, y: &[Elem]) -> GrResult<Vec<Elem>> {
    x.iter().zip(y).map(|(s, t)| a.mul(s)?.sub(&c.mul(t)?)).collect()
}

/// The positive multiple of the non-zero rational vector x that is integral
/// and primitive.
fn primitive(x: Vec<Elem>) -> GrResult<Vec<Elem>> {
    let ctx = x[0].ctx().clone();
    let rs: Vec<Rational> = x.iter().map(Elem::to_rational).collect::<GrResult<_>>()?;
    let den = rs.iter().fold(Integer::one(), |d, r| d.lcm(&r.denominator()));
    let ns: Vec<Integer> = rs.iter().map(|r| (&r.numerator() * &den).divexact(&r.denominator())).collect();
    let g = ns.iter().fold(Integer::default(), |g, n| g.gcd(n));
    if g.is_zero() {
        return Ok(x);
    }
    ns.iter().map(|n| Elem::from_integer(&ctx, &n.divexact(&g))).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use calyx_flint::gr::Ctx;

    /// The matrix with entries n/d.
    fn gram(k: &Rc<Ctx>, rows: &[&[(i64, i64)]]) -> Vec<Vec<Elem>> {
        let e = |(n, d): (i64, i64)| Elem::from_i64(k, n).unwrap().div(&Elem::from_i64(k, d).unwrap()).unwrap();
        rows.iter().map(|r| r.iter().map(|&x| e(x)).collect()).collect()
    }

    fn check(k: &Rc<Ctx>, b: &[&[(i64, i64)]], rational: bool, want: &[&[&str]]) {
        let t = orthogonalize_gram(&gram(k, b), rational).unwrap();
        let want: Vec<Vec<Elem>> = want.iter().map(|r| r.iter().map(|s| Elem::from_integer(k, &Integer::parse(s).unwrap()).unwrap()).collect()).collect();
        assert_eq!(t.len(), want.len());
        assert!(t.iter().flatten().zip(want.iter().flatten()).all(|(x, y)| x.equal(y) == Truth::True), "{t:?}");
    }

    const H: (i64, i64) = (1, 2);
    const O: (i64, i64) = (0, 1);
    const I: (i64, i64) = (1, 1);

    #[test]
    fn rational_rows() {
        let q = Ctx::rationals();
        // xy + xz + yz: zero pivots paired with the next row.
        check(&q, &[&[O, H, H], &[H, O, H], &[H, H, O]], true, &[&["1", "-1", "0"], &["-1", "-1", "0"], &["-1", "-1", "1"]]);
        // yz: the radical row x swaps with the last and comes back.
        check(&q, &[&[O, O, O], &[O, O, H], &[O, H, O]], true, &[&["1", "0", "0"], &["0", "-1", "-1"], &["0", "-1", "1"]]);
        // xy + y^2: a zero pivot paired with a row of non-zero norm.
        check(&q, &[&[O, H], &[H, I]], true, &[&["2", "-1"], &["0", "1"]]);
        // x^2 + 2xy + y^2 + zw: a row that becomes radical.
        let b: &[&[(i64, i64)]] = &[&[I, I, O, O], &[I, I, O, O], &[O, O, O, H], &[O, O, H, O]];
        check(&q, b, true, &[&["1", "0", "0", "0"], &["-1", "1", "0", "0"], &["0", "0", "-1", "-1"], &["0", "0", "-1", "1"]]);
    }

    #[test]
    fn handbook_rows() {
        // The handbook example H25E7: the form of g in x, y, z and 1.
        let q = Ctx::rationals();
        let b: &[&[(i64, i64)]] = &[
            &[(119, 44), (-93759, 82880), (390935, 182854), (106, 243)],
            &[(-93759, 82880), (-3, 17), (26404, 172227), (-287, 454)],
            &[(390935, 182854), (26404, 172227), (537, 934), (-127, 844)],
            &[(106, 243), (-287, 454), (-127, 844), O],
        ];
        let want: &[&[&str]] = &[
            &["1", "0", "0", "0"],
            &["1031349", "2465680", "0", "0"],
            &["936458306655970560", "-13015163140580701600", "-8071354934357376321", "0"],
            &[
                "4272017094412295488226667293533666880",
                "-16756200849001340228209073757909867360",
                "-13020667698386124239704978179787654959",
                "-6125019434462670681779428620271599954",
            ],
        ];
        check(&q, b, true, want);
    }

    #[test]
    fn field_rows() {
        let k = Ctx::residue_ring(&Integer::from_u64(5));
        let h = (3, 1);
        // vw: the radical row u swaps with the last and stays there.
        check(&k, &[&[O, O, O], &[O, O, h], &[O, h, O]], false, &[&["0", "1", "1"], &["0", "3", "2"], &["1", "0", "0"]]);
        // uv + v^2: a zero pivot swaps with a row of non-zero norm.
        check(&k, &[&[O, h, O], &[h, I, O], &[O, O, O]], false, &[&["0", "1", "0"], &["1", "2", "0"], &["0", "0", "1"]]);
        // uw + v^2: a swap, then a zero pivot added to its partner.
        check(&k, &[&[O, O, h], &[O, I, O], &[h, O, O]], false, &[&["0", "1", "0"], &["1", "0", "1"], &["2", "0", "3"]]);
    }
}
