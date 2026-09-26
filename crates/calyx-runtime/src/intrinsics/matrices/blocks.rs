//! Building block matrices: joining matrices horizontally, vertically or
//! diagonally, block matrices from their blocks, and Kronecker products.
//!
//! The results are matrices in the algebra or space of their shape, even
//! when the arguments are vectors.

use std::rc::Rc;

use calyx_flint::mat::Mat;

use super::{Mtrx, mat_arg, mat_value};
use crate::error::{RResult, RuntimeError};
use crate::intrinsics::{hidden, hidden_inner, one};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

fn incompatible_rings() -> RuntimeError {
    RuntimeError::runtime("Arguments have incompatible coefficient rings")
}

#[derive(Clone, Copy, PartialEq)]
enum Join {
    Horizontal,
    Vertical,
    Diagonal,
}

/// The matrices to join: the two arguments, or the entries of a sequence
/// or tuple, over one ring.
fn operands(a: &CallArgs) -> RResult<Vec<Rc<Mtrx>>> {
    if a.args.len() == 2 {
        let (x, y) = (mat_arg(a, 0)?, mat_arg(a, 1)?);
        if x.ring() != y.ring() {
            return Err(incompatible_rings());
        }
        return Ok(vec![x.clone(), y.clone()]);
    }
    let elems = match &a.args[0] {
        Value::Seq(s) if s.elems.is_empty() => return Err(RuntimeError::runtime("Illegal null sequence")),
        Value::Seq(s) => &s.elems,
        Value::Tuple(t) if t.elems.is_empty() => return Err(RuntimeError::runtime("Argument 1 is not non-empty")),
        Value::Tuple(t) => &t.elems,
        _ => unreachable!(),
    };
    let ms = elems
        .iter()
        .enumerate()
        .map(|(i, v)| match v {
            Value::Mat(m) => Ok(m.clone()),
            _ => Err(RuntimeError::runtime(format!("Entry {} is not a matrix", i + 1))),
        })
        .collect::<RResult<Vec<_>>>()?;
    if ms.iter().any(|m| m.ring() != ms[0].ring()) {
        return Err(RuntimeError::runtime("Elements of tuple have incompatible base rings"));
    }
    Ok(ms)
}

fn join(it: &mut Interp, a: &CallArgs, how: Join) -> RResult<Vals> {
    let ms = operands(a)?;
    let (r0, c0) = (ms[0].m.nrows(), ms[0].m.ncols());
    if how == Join::Horizontal && ms.iter().any(|m| m.m.nrows() != r0) {
        return Err(RuntimeError::runtime("Matrices have incompatible numbers of rows"));
    }
    if how == Join::Vertical && ms.iter().any(|m| m.m.ncols() != c0) {
        return Err(RuntimeError::runtime("Matrices have incompatible numbers of columns"));
    }
    let rows: usize = ms.iter().map(|m| m.m.nrows()).sum();
    let cols: usize = ms.iter().map(|m| m.m.ncols()).sum();
    let (r, c) = match how {
        Join::Horizontal => (r0, cols),
        Join::Vertical => (rows, c0),
        Join::Diagonal => (rows, cols),
    };
    let mut out = Mat::zero(ms[0].m.ctx(), r, c);
    let (mut i, mut j) = (0, 0);
    for m in &ms {
        out.insert(&m.m, i, j);
        if how != Join::Horizontal {
            i += m.m.nrows();
        }
        if how != Join::Vertical {
            j += m.m.ncols();
        }
    }
    let ring = ms[0].ring().clone();
    one(mat_value(it, &ring, out)?)
}

fn horizontal_join(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    join(it, a, Join::Horizontal)
}

fn vertical_join(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    join(it, a, Join::Vertical)
}

fn diagonal_join(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    join(it, a, Join::Diagonal)
}

/// `KroneckerProduct(A, B)`: the blocks A[i, j]·B.
fn kronecker_product(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (x, y) = (mat_arg(a, 0)?.clone(), mat_arg(a, 1)?.clone());
    if x.ring() != y.ring() {
        return Err(incompatible_rings());
    }
    let (p, q) = (y.m.nrows(), y.m.ncols());
    let mut out = Mat::zero(x.m.ctx(), x.m.nrows() * p, x.m.ncols() * q);
    for i in 0..x.m.nrows() {
        for j in 0..x.m.ncols() {
            if !x.m.entry_is_zero(i, j) {
                let b = y.m.scalar_mul(&x.m.entry(i, j)).map_err(|e| crate::rings::gr_error(e, "Arithmetic failed"))?;
                out.insert(&b, i * p, j * q);
            }
        }
    }
    let ring = x.ring().clone();
    one(mat_value(it, &ring, out)?)
}

// ----- block matrices -----------------------------------------------------------

/// Magma's failed assertion in the code of `BlockMatrix`.
fn assertion() -> RuntimeError {
    hidden_inner(RuntimeError::statement("assert", "Assertion failed"))
}

/// The matrix of m by n blocks of one shape, row by row, the missing ones
/// zero; the first block gives the shape.
fn assemble(it: &mut Interp, m: usize, n: usize, rows: &[Vec<Rc<Mtrx>>]) -> RResult<Value> {
    let first = &rows[0][0];
    let (r, c) = (first.m.nrows(), first.m.ncols());
    let mut out = Mat::zero(first.m.ctx(), m * r, n * c);
    for (i, row) in rows.iter().enumerate() {
        for (j, b) in row.iter().enumerate() {
            if j >= n {
                let msg = format!("Argument 2 ({r} by {c}) does not fit into argument 1 ({} by {}) at position [{}, {}]", m * r, n * c, i * r + 1, j * c + 1);
                return Err(hidden(RuntimeError::runtime(msg).in_context("InsertBlock")));
            }
            out.insert(&b.m, i * r, j * c);
        }
    }
    let ring = first.ring().clone();
    mat_value(it, &ring, out)
}

/// Argument i as a number of blocks; a negative one fails as in Magma.
fn count(a: &CallArgs, i: usize) -> RResult<usize> {
    a.int(i)?.to_u64().map(|v| v as usize).ok_or_else(|| hidden(RuntimeError::runtime("Illegal null sequence").in_context("[]")))
}

fn matrices(q: &SeqEnum) -> Vec<Rc<Mtrx>> {
    q.elems.iter().map(|v| if let Value::Mat(m) = v { m.clone() } else { unreachable!() }).collect()
}

/// `BlockMatrix(m, n, blocks)`: the first m·n blocks in row-major order.
fn block_matrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (m, n) = (count(a, 0)?, count(a, 1)?);
    let blocks = matrices(a.seq(2)?);
    if blocks.is_empty() {
        return Err(hidden(RuntimeError::runtime("Illegal null sequence").in_context("[]")));
    }
    if blocks.len() < m * n {
        let msg = format!("Index 1 ({}) should be in the range [1 .. {}]", blocks.len() + 1, blocks.len());
        return Err(hidden_inner(RuntimeError::runtime(msg).in_context("[]")));
    }
    let rows: Vec<Vec<Rc<Mtrx>>> = (0..m).map(|i| blocks[i * n..(i + 1) * n].to_vec()).collect();
    if rows.is_empty() || n == 0 {
        // No blocks are placed: the shape is still that of the first.
        let (r, c) = (blocks[0].m.nrows(), blocks[0].m.ncols());
        let ring = blocks[0].ring().clone();
        return one(mat_value(it, &ring, Mat::zero(blocks[0].m.ctx(), m * r, n * c))?);
    }
    one(assemble(it, m, n, &rows)?)
}

/// `BlockMatrix(m, n, rows)` and `BlockMatrix(rows)`: m rows of blocks, the
/// first of them n long and the others no longer.
fn block_matrix_rows(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let k = a.args.len() - 1;
    let q = a.seq(k)?.clone();
    let rows: Vec<Vec<Rc<Mtrx>>> = q.elems.iter().map(|r| if let Value::Seq(s) = r { matrices(s) } else { unreachable!() }).collect();
    let (m, n) = if k == 2 { (count(a, 0)?, count(a, 1)?) } else { (rows.len(), rows.first().map_or(0, Vec::len)) };
    if rows.len() != m || rows.first().map_or(0, Vec::len) != n {
        return Err(assertion());
    }
    if rows.is_empty() || rows[0].is_empty() {
        return Err(hidden(RuntimeError::runtime("Illegal null sequence").in_context("[]")));
    }
    one(assemble(it, m, n, &rows)?)
}

pub fn register(it: &mut Interp) {
    let joins: [(&str, &str, crate::intrinsics::NativeFn); 3] = [
        ("HorizontalJoin", "with the columns of Y after those of X", horizontal_join),
        ("VerticalJoin", "with the rows of Y after those of X", vertical_join),
        ("DiagonalJoin", "with X and Y as its diagonal blocks", diagonal_join),
    ];
    for (name, what, f) in joins {
        it.def(name, "X::Mtrx, Y::Mtrx -> Mtrx", &format!("The matrix {what}."), f);
        it.def(name, "Q::[Mtrx] -> Mtrx", "The join of the matrices in Q, in order.", f);
        it.def(name, "T::Tup -> Mtrx", "The join of the matrices in T, in order.", f);
    }
    it.def("KroneckerProduct", "A::Mtrx, B::Mtrx -> Mtrx", "The Kronecker product of A and B.", kronecker_product);
    // Magma writes BlockMatrix in its own language.
    let blocks: [(&str, &str, crate::intrinsics::NativeFn); 3] = [
        ("m::RngIntElt, n::RngIntElt, blocks::[Mtrx] -> Mtrx", "The m by n block matrix of the blocks, listed across rows.", block_matrix),
        ("m::RngIntElt, n::RngIntElt, rows::[[Mtrx]] -> Mtrx", "The m by n block matrix with the given rows of blocks.", block_matrix_rows),
        ("rows::[[Mtrx]] -> Mtrx", "The block matrix with the given rows of blocks.", block_matrix_rows),
    ];
    for (sig, doc, f) in blocks {
        it.def("BlockMatrix", sig, doc, f).package = true;
    }
}
