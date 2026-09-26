//! The matrices of univariate polynomials (text/237): the Berlekamp
//! Q-matrix, the Sylvester matrix and the companion matrix. They are made
//! through the matrices module, over the coefficient ring.

use std::rc::Rc;

use calyx_flint::gr::{Elem, Truth};
use calyx_flint::mat::Mat;
use calyx_flint::upoly as fu;

use super::roots::finite_field_order;
use super::{base_of, len, pol};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::{arg_not, matrices, one};
use crate::value::*;

/// Set the entry (i, j) of `m`, a matrix over `ring`, to `c`, an element of
/// the context of `ring` as a coefficient ring (or as a polynomial ring).
/// Zeros are set too: over the reals and the complex field a zero may be
/// negative.
pub(crate) fn put_entry(it: &mut Interp, ring: &Value, m: &mut Mat, i: usize, j: usize, c: &Elem) -> RResult<()> {
    if Rc::ptr_eq(c.ctx(), m.ctx()) {
        m.set_entry(i, j, c);
    } else {
        let v = it.elem_to_value(ring, c.clone());
        let ok = matrices::set_entry(it, ring, m, i, j, &v)?;
        debug_assert!(ok, "a coefficient outside the matrix ring");
    }
    Ok(())
}

/// The Berlekamp Q-matrix of f of degree d over a finite field of q
/// elements: row i (from 0) holds the coefficients of x^(q i) mod f,
/// constant term first. f need not be monic or squarefree.
pub(super) fn q_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    if len(&f) < 2 {
        return Err(arg_not(1, "non-constant"));
    }
    let Some((q, _)) = finite_field_order(&f) else {
        return Err(RuntimeError::runtime("Coefficient ring of argument 1 is not a finite field"));
    };
    let ring = base_of(&f);
    let ctx = matrices::entry_ctx(it, &ring)?;
    let d = len(&f) - 1;
    let h = fu::powmod(&f.x.ctx().generator()?, &q, &f.x)?;
    let mut m = Mat::zero(&ctx, d, d);
    let mut r = Elem::one(f.x.ctx())?;
    for i in 0..d {
        if i > 0 {
            r = fu::divrem(&r.mul(&h)?, &f.x)?.1;
        }
        for j in 0..r.poly_len() {
            put_entry(it, &ring, &mut m, i, j, &r.poly_coeff(j))?;
        }
    }
    one(matrices::mat_value(it, &ring, m)?)
}

/// The Sylvester matrix of f and g of degrees m and n: n rows with the
/// coefficients of f (leading first), each shifted one column right of the
/// one above, then m rows with those of g. Magma gives the 0 by 0 matrix
/// when f or g is zero, and wants f and g in one ring.
pub(super) fn sylvester_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (f, g) = (pol(a, 0), pol(a, 1));
    if f.ring().id != g.ring().id {
        let types = format!("{}, {}", it.type_name_ext(&a.args[0]), it.type_name_ext(&a.args[1]));
        return Err(RuntimeError::runtime(format!("Arguments are not compatible\nArgument types given: {types}")));
    }
    let ring = base_of(&f);
    let ctx = matrices::entry_ctx(it, &ring)?;
    let (lf, lg) = (len(&f), len(&g));
    let size = if lf == 0 || lg == 0 { 0 } else { lf + lg - 2 };
    let mut m = Mat::zero(&ctx, size, size);
    if size > 0 {
        let (df, dg) = (lf - 1, lg - 1);
        for i in 0..dg {
            for k in 0..=df {
                put_entry(it, &ring, &mut m, i, i + k, &f.x.poly_coeff(df - k))?;
            }
        }
        for i in 0..df {
            for k in 0..=dg {
                put_entry(it, &ring, &mut m, dg + i, i + k, &g.x.poly_coeff(dg - k))?;
            }
        }
    }
    one(matrices::mat_value(it, &ring, m)?)
}

/// The companion matrix of a monic f = a0 + ... + a(d-1) x^(d-1) + x^d:
/// ones above the diagonal and -a0, ..., -a(d-1) in the last row.
pub(super) fn companion_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = pol(a, 0);
    if len(&f) < 2 {
        return Err(arg_not(1, "non-constant"));
    }
    if fu::lead(&f.x).is_one() != Truth::True {
        return Err(arg_not(1, "monic"));
    }
    let ring = base_of(&f);
    let ctx = matrices::entry_ctx(it, &ring)?;
    let d = len(&f) - 1;
    let mut m = Mat::zero(&ctx, d, d);
    let unit = fu::lead(&f.x);
    for i in 0..d - 1 {
        put_entry(it, &ring, &mut m, i, i + 1, &unit)?;
    }
    for j in 0..d {
        put_entry(it, &ring, &mut m, d - 1, j, &f.x.poly_coeff(j).neg()?)?;
    }
    one(matrices::mat_value(it, &ring, m)?)
}
