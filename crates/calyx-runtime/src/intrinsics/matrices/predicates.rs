//! Predicates on matrices: identity, scalar, diagonal, symmetric and
//! Hermitian matrices, triangular ones and integral symplectic ones.
//! (`IsZero`, `IsUnit` and `IsSingular` are with the entries and the
//! determinants.)

use calyx_flint::gr::Truth;
use calyx_flint::mat::Mat;

use super::{entry_value, mat_arg, set_entry, square};
use crate::error::{RResult, RuntimeError};
use crate::intrinsics::{boolv, hidden_inner};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

fn truth(t: Truth) -> RResult<Vals> {
    boolv(t == Truth::True)
}

fn is_one(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    truth(square(a, 0)?.m.is_one())
}

fn is_minus_one(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    truth(square(a, 0)?.m.is_neg_one())
}

fn is_scalar(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    truth(square(a, 0)?.m.is_scalar())
}

fn is_diagonal(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    truth(square(a, 0)?.m.is_diagonal())
}

fn is_symmetric(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = square(a, 0)?;
    truth(x.m.equal(&x.m.transpose()))
}

/// `IsHermitian(A, f)`: whether A is f applied to the entries of its
/// transpose.
fn is_hermitian(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = square(a, 0)?;
    let Value::Map(f) = a.args[1].clone() else { unreachable!() };
    let (ring, n) = (x.ring().clone(), x.m.nrows());
    let mut m = Mat::zero(x.m.ctx(), n, n);
    for i in 0..n {
        for j in 0..n {
            let e = entry_value(it, &x, j, i);
            let y = it.apply_map(&f, &e)?;
            if !set_entry(it, &ring, &mut m, i, j, &y)? {
                return boolv(false);
            }
        }
    }
    truth(m.equal(&x.m))
}

fn is_upper_triangular(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    truth(mat_arg(a, 0)?.m.is_upper_triangular())
}

/// `IsLowerTriangular(A)`, whose code in Magma fails on vectors longer
/// than 1.
fn is_lower_triangular(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?;
    if x.is_vector() && x.m.ncols() > 1 {
        return Err(hidden_inner(RuntimeError::runtime("Bad argument types").in_context("[]")));
    }
    truth(x.m.is_lower_triangular())
}

/// `IsSymplecticMatrix(A)`: whether A·J·A^T = J for J = [0 I; -I 0].
fn is_symplectic_matrix(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let x = mat_arg(a, 0)?;
    let n = x.m.nrows();
    if n % 2 == 1 {
        return boolv(false);
    }
    let g = n / 2;
    let gr = |e| crate::rings::gr_error(e, "Arithmetic failed");
    let mut j = Mat::zero(x.m.ctx(), n, n);
    for i in 0..g {
        j.set_si(i, g + i, 1).map_err(gr)?;
        j.set_si(g + i, i, -1).map_err(gr)?;
    }
    let p = x.m.mul(&j).and_then(|p| p.mul(&x.m.transpose())).map_err(gr)?;
    truth(p.equal(&j))
}

pub fn register(it: &mut Interp) {
    it.def("IsOne", "A::Mtrx -> BoolElt", "Whether A is the identity matrix.", is_one);
    it.def("IsMinusOne", "A::Mtrx -> BoolElt", "Whether A is minus the identity matrix.", is_minus_one);
    it.def("IsScalar", "A::Mtrx -> BoolElt", "Whether A is a scalar multiple of the identity.", is_scalar);
    it.def("IsDiagonal", "A::Mtrx -> BoolElt", "Whether the only non-zero entries of A are on the diagonal.", is_diagonal);
    it.def("IsSymmetric", "A::Mtrx -> BoolElt", "Whether A equals its transpose.", is_symmetric);
    it.def("IsHermitian", "A::Mtrx, f::Map -> BoolElt", "Whether A is f applied to its transpose.", is_hermitian);
    // Magma writes these in its own language.
    let package: [(&str, &str, &str, crate::intrinsics::NativeFn); 3] = [
        ("IsUpperTriangular", "A::Mtrx -> BoolElt", "Whether the entries of A below the diagonal are zero.", is_upper_triangular),
        ("IsLowerTriangular", "A::Mtrx -> BoolElt", "Whether the entries of A above the diagonal are zero.", is_lower_triangular),
        ("IsSymplecticMatrix", "A::AlgMatElt[RngInt] -> BoolElt", "Whether A is an integral symplectic matrix.", is_symplectic_matrix),
    ];
    for (name, sig, doc, f) in package {
        it.def(name, sig, doc, f).package = true;
    }
}
