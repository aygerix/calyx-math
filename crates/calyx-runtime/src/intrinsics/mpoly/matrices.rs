//! The matrices of multivariate polynomials (text/246): the Jacobian matrix
//! of a sequence of polynomials and the symmetric bilinear form of a
//! polynomial of degree 2. They are made through the matrices module.

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::Elem;
use calyx_flint::mat::Mat;

use super::{base_of, mpol, partial, rank, terms};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::matrices::{self, Mtrx, Shape};
use crate::intrinsics::one;
use crate::intrinsics::upoly::put_entry;
use crate::rings::ring_of;
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
/// (j, i). Magma puts B in the matrix space over the coefficient ring (not
/// the algebra), and wants 2 to be a unit there.
pub(super) fn symmetric_bilinear_form(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = mpol(a, 0);
    let ts = terms(&f.x);
    let degs: Vec<u64> = ts.iter().map(|(_, e)| e.iter().sum()).collect();
    if degs.iter().max() != Some(&2) {
        return Err(RuntimeError::runtime("The polynomial must have degree 2"));
    }
    let base = f.x.ctx().base().expect("a polynomial ring").clone();
    let Ok(half) = Elem::from_integer(&base, &Integer::from_u64(2))?.inv() else {
        return Err(RuntimeError::runtime("2 must have an inverse"));
    };
    let ring = base_of(&f);
    let n = rank(f.ring());
    let size = if degs.iter().all(|&d| d == 2) { n } else { n + 1 };
    let ctx = matrices::entry_ctx(it, &ring)?;
    let mut m = Mat::zero(&ctx, size, size);
    for (c, e) in &ts {
        // The two variables of the term, the constant 1 counting as variable n.
        let mut vs: Vec<usize> = e.iter().enumerate().flat_map(|(i, &k)| (0..k).map(move |_| i)).collect();
        vs.resize(2, n);
        let (i, j) = (vs[0], vs[1]);
        if i == j {
            put_entry(it, &ring, &mut m, i, i, c)?;
        } else {
            let h = c.mul(&half)?;
            put_entry(it, &ring, &mut m, i, j, &h)?;
            put_entry(it, &ring, &mut m, j, i, &h)?;
        }
    }
    let p = matrices::parent(it, &ring, size, size, Shape::Space)?;
    one(Value::Mat(Rc::new(Mtrx { parent: p, m })))
}
