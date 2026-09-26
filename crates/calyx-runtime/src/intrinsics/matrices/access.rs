//! Elementary properties of matrices, and accessing or modifying their
//! entries: indexing, blocks, and row and column operations.

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_flint::gr::Elem;
use calyx_flint::mat::Mat;

use super::{Mtrx, bad, entry_value, mat_arg, over_ring_of, scalar, set_entry, vec_value};
use crate::error::{RResult, RuntimeError};
use crate::intrinsics::{arg_range, bare, boolv, intv, none, one};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

// ----- indexing ----------------------------------------------------------------

/// `Index k (v) should be in the range [1 .. n]`, for the k-th index.
fn index_range(k: usize, v: &Integer, n: usize) -> RuntimeError {
    RuntimeError::runtime(format!("Index {k} ({v}) should be in the range [1 .. {n}]")).in_context("[]")
}

/// The k-th index, an integer in 1..=n, from 0.
fn index_at(it: &Interp, a: &Mtrx, ids: &[Value], k: usize, n: usize) -> RResult<usize> {
    match &ids[k] {
        Value::Int(v) => match v.to_u64() {
            Some(i) if (1..=n as u64).contains(&i) => Ok(i as usize - 1),
            _ => Err(index_range(k + 1, v, n)),
        },
        other => Err(index_types(it, a, other)),
    }
}

fn index_types(it: &Interp, a: &Mtrx, i: &Value) -> RuntimeError {
    let (t1, t2) = (it.type_name_ext(&Value::Mat(Rc::new(a.clone()))), it.type_name_ext(i));
    RuntimeError::runtime(format!("Bad argument types\nArgument types given: {t1}, {t2}")).in_context("[]")
}

/// Row i of `a` (from 0) as a vector.
fn row(it: &mut Interp, a: &Mtrx, i: usize) -> RResult<Value> {
    if a.is_vector() {
        return Ok(Value::Mat(Rc::new(a.clone())));
    }
    let ring = a.ring().clone();
    vec_value(it, &ring, a.m.block(i, 0, 1, a.m.ncols()))
}

/// `A[i]`, `A[i, j]` and `A[Q]` for a matrix (rows, entries and sequences
/// of rows), `v[i]` for a vector.
pub fn index(it: &mut Interp, a: &Rc<Mtrx>, ids: &[Value]) -> RResult<Value> {
    let (r, c) = (a.m.nrows(), a.m.ncols());
    match ids {
        [Value::Seq(q)] => {
            let mut rows = Vec::with_capacity(q.elems.len());
            for (k, x) in q.elems.iter().enumerate() {
                let i = match x {
                    Value::Int(v) => match v.to_u64() {
                        Some(i) if (1..=r as u64).contains(&i) => i as usize - 1,
                        _ => return Err(index_range(k + 1, v, r)),
                    },
                    _ => return Err(index_types(it, a, &ids[0])),
                };
                rows.push(row(it, a, i)?);
            }
            let ring = a.ring().clone();
            let u = Value::Struct(super::parent(it, &ring, 1, c, super::Shape::Tuples)?);
            Ok(Value::seq(Some(u), rows))
        }
        [_] if a.is_vector() => {
            let j = index_at(it, a, ids, 0, c)?;
            Ok(entry_value(it, a, 0, j))
        }
        [_] => {
            let i = index_at(it, a, ids, 0, r)?;
            row(it, a, i)
        }
        [_, _] if !a.is_vector() => {
            let i = index_at(it, a, ids, 0, r)?;
            let j = index_at(it, a, ids, 1, c)?;
            Ok(entry_value(it, a, i, j))
        }
        _ => Err(RuntimeError::runtime("Bad argument types").in_context("[]")),
    }
}

/// An error of an assignment to an entry or a row.
fn assign_error(msg: &str) -> RuntimeError {
    RuntimeError::statement(":=", msg)
}

/// The index `ids[k]` of an assignment, in 1..=n, from 0.
fn assign_index(ids: &[Value], k: usize, n: usize, what: &str) -> RResult<usize> {
    match &ids[k] {
        Value::Int(v) => match v.to_u64() {
            Some(i) if (1..=n as u64).contains(&i) => Ok(i as usize - 1),
            _ => Err(assign_error(&format!("{what} index is not in the range [1 .. {n}]"))),
        },
        _ => Err(assign_error("Bad argument types")),
    }
}

/// `A[i] := v`, `A[i, j] := x` and `v[i] := x`.
pub fn set_index(it: &mut Interp, cur: &mut Value, ids: &[Value], x: Value) -> RResult<()> {
    let Value::Mat(a) = cur else { unreachable!() };
    let (r, c) = (a.m.nrows(), a.m.ncols());
    let ring = a.ring().clone();
    let (i, j) = match ids {
        [_] if a.is_vector() => (0, assign_index(ids, 0, c, "Vector")?),
        [_] => {
            let i = assign_index(ids, 0, r, "Matrix row")?;
            let src = match &x {
                Value::Int(n) if n.is_zero() => Mat::zero(a.m.ctx(), 1, c),
                Value::Mat(v) if v.is_vector() => {
                    let incompatible = || assign_error("RHS vector is incompatible with the LHS matrix");
                    if v.m.ncols() != c {
                        return Err(incompatible());
                    }
                    if Rc::ptr_eq(v.m.ctx(), a.m.ctx()) {
                        v.m.clone()
                    } else {
                        let mut m = Mat::zero(a.m.ctx(), 1, c);
                        for j in 0..c {
                            let e = entry_value(it, v, 0, j);
                            if !set_entry(it, &ring, &mut m, 0, j, &e)? {
                                return Err(incompatible());
                            }
                        }
                        m
                    }
                }
                _ => return Err(assign_error("RHS is not a vector or zero")),
            };
            Rc::make_mut(a).m.insert(&src, i, 0);
            return Ok(());
        }
        [_, _] if !a.is_vector() => (assign_index(ids, 0, r, "Matrix row")?, assign_index(ids, 1, c, "Matrix column")?),
        _ => return Err(assign_error("Bad argument types")),
    };
    if !set_entry(it, &ring, &mut Rc::make_mut(a).m, i, j, &x)? {
        return Err(assign_error("RHS cannot be coerced into the coefficient ring"));
    }
    Ok(())
}

// ----- elementary properties ---------------------------------------------------------

fn nrows(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(mat_arg(a, 0)?.m.nrows() as u64))
}

fn ncols(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(mat_arg(a, 0)?.m.ncols() as u64))
}

fn nnz(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(Integer::from_u64(mat_arg(a, 0)?.m.count_nonzero() as u64))
}

fn density(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = &mat_arg(a, 0)?.m;
    let size = m.nrows() * m.ncols();
    let q = match size {
        0 => calyx_flint::Rational::zero(),
        _ => calyx_flint::Rational::new(&Integer::from_u64(m.count_nonzero() as u64), &Integer::from_u64(size as u64)).expect("a non-zero size"),
    };
    let reals = Value::reals(crate::intrinsics::reals::default_bits());
    one(it.coerce(&reals, &Value::rat(q))?)
}

fn base_ring(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(mat_arg(a, 0)?.ring().clone())
}

fn eltseq(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = mat_arg(a, 0)?.clone();
    let mut out = Vec::with_capacity(m.m.nrows() * m.m.ncols());
    for i in 0..m.m.nrows() {
        for j in 0..m.m.ncols() {
            out.push(entry_value(it, &m, i, j));
        }
    }
    one(Value::seq(Some(m.ring().clone()), out))
}

fn row_sequence(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = mat_arg(a, 0)?.clone();
    let ring = m.ring().clone();
    let rows = (0..m.m.nrows()).map(|i| Value::seq(Some(ring.clone()), (0..m.m.ncols()).map(|j| entry_value(it, &m, i, j)).collect())).collect();
    one(Value::seq(Some(Value::structure(StructKind::PowerSeq(Some(ring)))), rows))
}

// ----- blocks ------------------------------------------------------------------------

/// Argument i as an integer in lo..=hi, or Magma's range error.
fn int_in(a: &CallArgs, i: usize, lo: i64, hi: i64) -> RResult<usize> {
    let n = a.int(i)?;
    match n.to_i64() {
        Some(v) if v >= lo && v <= hi => Ok(v as usize),
        _ => Err(arg_range(i + 1, n, lo, hi)),
    }
}

/// `Submatrix(A, i, j, p, q)`: the p by q block at (i, j).
fn submatrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = mat_arg(a, 0)?.clone();
    let (r, c) = (m.m.nrows() as i64, m.m.ncols() as i64);
    let i = int_in(a, 1, 1, r + 1)?;
    let j = int_in(a, 2, 1, c + 1)?;
    let p = int_in(a, 3, 0, r + 1 - i as i64)?;
    let q = int_in(a, 4, 0, c + 1 - j as i64)?;
    one(over_ring_of(it, &m, m.m.block(i - 1, j - 1, p, q))?)
}

/// `SubmatrixRange(A, i, j, r, s)`: the block from (i, j) to (r, s).
fn submatrix_range(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = mat_arg(a, 0)?.clone();
    let (nr, nc) = (m.m.nrows() as i64, m.m.ncols() as i64);
    let i = int_in(a, 1, 1, nr + 1)?;
    let j = int_in(a, 2, 1, nc + 1)?;
    let r = int_in(a, 3, i as i64 - 1, nr)?;
    let s = int_in(a, 4, j as i64 - 1, nc)?;
    one(over_ring_of(it, &m, m.m.block(i - 1, j - 1, r + 1 - i, s + 1 - j))?)
}

/// Indices from a sequence of integers in 1..=n, from 0.
fn indices(a: &CallArgs, k: usize, n: usize, what: &str) -> RResult<Vec<usize>> {
    let q = a.seq(k)?;
    q.elems
        .iter()
        .map(|x| match x {
            Value::Int(v) => match v.to_u64() {
                Some(i) if (1..=n as u64).contains(&i) => Ok(i as usize - 1),
                _ => Err(bare(RuntimeError::runtime(format!("{what} index out of range")))),
            },
            _ => Err(bad()),
        })
        .collect()
}

/// `Submatrix(A, I, J)`.
fn submatrix_seqs(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = mat_arg(a, 0)?.clone();
    let rows = indices(a, 1, m.m.nrows(), "Row")?;
    let cols = indices(a, 2, m.m.ncols(), "Column")?;
    one(over_ring_of(it, &m, m.m.select(&rows, &cols))?)
}

fn row_submatrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = mat_arg(a, 0)?.clone();
    let r = m.m.nrows() as i64;
    let (i, k) = if a.args.len() == 3 {
        let i = int_in(a, 1, 1, r + 1)?;
        (i, int_in(a, 2, 0, r + 1 - i as i64)?)
    } else {
        (1, int_in(a, 1, 0, r)?)
    };
    one(over_ring_of(it, &m, m.m.block(i - 1, 0, k, m.m.ncols()))?)
}

fn row_submatrix_range(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = mat_arg(a, 0)?.clone();
    let r = m.m.nrows() as i64;
    let i = int_in(a, 1, 1, r + 1)?;
    let j = int_in(a, 2, i as i64 - 1, r)?;
    one(over_ring_of(it, &m, m.m.block(i - 1, 0, j + 1 - i, m.m.ncols()))?)
}

fn column_submatrix(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = mat_arg(a, 0)?.clone();
    let c = m.m.ncols() as i64;
    let (i, k) = if a.args.len() == 3 {
        let i = int_in(a, 1, 1, c + 1)?;
        (i, int_in(a, 2, 0, c + 1 - i as i64)?)
    } else {
        (1, int_in(a, 1, 0, c)?)
    };
    one(over_ring_of(it, &m, m.m.block(0, i - 1, m.m.nrows(), k))?)
}

fn column_submatrix_range(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = mat_arg(a, 0)?.clone();
    let c = m.m.ncols() as i64;
    let i = int_in(a, 1, 1, c + 1)?;
    let j = int_in(a, 2, i as i64 - 1, c)?;
    one(over_ring_of(it, &m, m.m.block(0, i - 1, m.m.nrows(), j + 1 - i))?)
}

/// The entries of `b` in the ring of `a`, or None if its ring does not
/// coerce into that of `a`.
fn entries_like(it: &mut Interp, a: &Mtrx, b: &Mtrx) -> RResult<Option<Mat>> {
    if Rc::ptr_eq(a.m.ctx(), b.m.ctx()) && a.ring() == b.ring() {
        return Ok(Some(b.m.clone()));
    }
    let ring = a.ring().clone();
    if !it.auto_coerces(b.ring(), &ring) {
        return Ok(None);
    }
    let mut m = Mat::zero(a.m.ctx(), b.m.nrows(), b.m.ncols());
    for i in 0..b.m.nrows() {
        for j in 0..b.m.ncols() {
            let x = entry_value(it, b, i, j);
            if !set_entry(it, &ring, &mut m, i, j, &x)? {
                return Ok(None);
            }
        }
    }
    Ok(Some(m))
}

/// `InsertBlock(~A, B, i, j)`, and the function returning the new matrix.
fn insert_block_in(it: &mut Interp, a: &mut CallArgs) -> RResult<()> {
    let b = mat_arg(a, 1)?.clone();
    let m = mat_arg(a, 0)?.clone();
    let (r, c) = (m.m.nrows(), m.m.ncols());
    let (i, j) = (a.int(2)?.clone(), a.int(3)?.clone());
    let fits = |x: &Integer, n: usize, k: usize| x.to_u64().is_some_and(|x| x >= 1 && x as usize + k <= n + 1);
    if !fits(&i, r, b.m.nrows()) || !fits(&j, c, b.m.ncols()) {
        let msg = format!("Argument 2 ({} by {}) does not fit into argument 1 ({r} by {c}) at position [{i}, {j}]", b.m.nrows(), b.m.ncols());
        return Err(RuntimeError::runtime(msg));
    }
    let (i, j) = (i.to_u64().unwrap() as usize, j.to_u64().unwrap() as usize);
    let Some(bm) = entries_like(it, &m, &b)? else { return Err(RuntimeError::runtime("Arguments have incompatible coefficient rings")) };
    let Value::Mat(x) = &mut a.args[0] else { unreachable!() };
    Rc::make_mut(x).m.insert(&bm, i - 1, j - 1);
    Ok(())
}

fn insert_block_proc(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    insert_block_in(it, a)?;
    none()
}

fn insert_block_func(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    insert_block_in(it, a)?;
    one(std::mem::take(&mut a.args[0]))
}

// ----- row and column operations ------------------------------------------------------

/// The matrix argument 0, to be modified in place.
fn target(a: &mut CallArgs) -> &mut Mtrx {
    let Value::Mat(x) = &mut a.args[0] else { unreachable!() };
    Rc::make_mut(x)
}

/// Argument i as a row (or column) number in 1..=n, from 0, or Magma's
/// `Value for row number k (v) should be in the range [1..n]`, with k the
/// place of the argument among those of the operation (none when it has
/// one).
fn row_number(a: &CallArgs, i: usize, what: &str, k: Option<usize>, n: usize) -> RResult<usize> {
    let v = a.int(i)?;
    match v.to_u64() {
        Some(x) if (1..=n as u64).contains(&x) => Ok(x as usize - 1),
        _ => {
            let k = k.map(|k| format!(" {k}")).unwrap_or_default();
            Err(RuntimeError::runtime(format!("Value for {what} number{k} ({v}) should be in the range [1..{n}]")))
        }
    }
}

/// Argument i as a row (or column) number in 1..=n of `Remove...`, which
/// Magma reports as argument 2.
fn removed(a: &CallArgs, i: usize, n: usize) -> RResult<usize> {
    let v = a.int(i)?;
    match v.to_u64() {
        Some(x) if (1..=n as u64).contains(&x) => Ok(x as usize - 1),
        _ => Err(arg_range(2, v, 1, n)),
    }
}

/// Define `F(~A, ...)` and `F(A, ...) -> Mtrx` from the procedure.
fn def_both(it: &mut Interp, name: &str, args: &str, doc: &str, proc_: crate::intrinsics::NativeFn, func: crate::intrinsics::NativeFn) {
    it.def(name, &format!("~A::Mtrx{args}"), doc, proc_);
    it.def(name, &format!("A::Mtrx{args} -> Mtrx"), doc, func);
}

macro_rules! row_op {
    ($proc:ident, $func:ident, $body:expr) => {
        fn $proc(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
            let f: fn(&mut Interp, &mut CallArgs) -> RResult<()> = $body;
            f(it, a)?;
            none()
        }

        fn $func(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
            let f: fn(&mut Interp, &mut CallArgs) -> RResult<()> = $body;
            f(it, a)?;
            one(std::mem::take(&mut a.args[0]))
        }
    };
}

row_op!(swap_rows_proc, swap_rows_func, |_, a| {
    let n = mat_arg(a, 0)?.m.nrows();
    let (i, j) = (row_number(a, 1, "row", Some(1), n)?, row_number(a, 2, "row", Some(2), n)?);
    target(a).m.swap_rows(i, j);
    Ok(())
});

row_op!(swap_cols_proc, swap_cols_func, |_, a| {
    let n = mat_arg(a, 0)?.m.ncols();
    let (i, j) = (row_number(a, 1, "column", Some(1), n)?, row_number(a, 2, "column", Some(2), n)?);
    target(a).m.swap_cols(i, j);
    Ok(())
});

row_op!(reverse_rows_proc, reverse_rows_func, |_, a| {
    let m = &mut target(a).m;
    let n = m.nrows();
    for i in 0..n / 2 {
        m.swap_rows(i, n - 1 - i);
    }
    Ok(())
});

row_op!(reverse_cols_proc, reverse_cols_func, |_, a| {
    let m = &mut target(a).m;
    let n = m.ncols();
    for i in 0..n / 2 {
        m.swap_cols(i, n - 1 - i);
    }
    Ok(())
});

/// The scalar argument k in the ring of the matrix.
fn scalar_arg(it: &mut Interp, a: &CallArgs, k: usize) -> RResult<Elem> {
    let m = mat_arg(a, 0)?;
    let (ring, ctx) = (m.ring().clone(), m.m.ctx().clone());
    match scalar(it, &ring, &ctx, &a.args[k])? {
        Some(e) => Ok(e),
        None => {
            let types: Vec<String> = a.args.iter().map(|v| it.type_name_ext(v)).collect();
            Err(RuntimeError::runtime(format!("Arguments are not compatible\nArgument types given: {}", types.join(", "))))
        }
    }
}

/// Row j plus c times row i (or columns, transposed).
fn add_line(m: &mut Mat, c: &Elem, i: usize, j: usize, rows: bool) -> RResult<()> {
    let n = if rows { m.ncols() } else { m.nrows() };
    for k in 0..n {
        let (src, dst) = if rows { ((i, k), (j, k)) } else { ((k, i), (k, j)) };
        let x = m.entry(src.0, src.1);
        if x.is_zero() == calyx_flint::gr::Truth::True {
            continue;
        }
        let y = m.entry(dst.0, dst.1).add(&c.mul(&x)?)?;
        m.set_entry(dst.0, dst.1, &y);
    }
    Ok(())
}

row_op!(add_row_proc, add_row_func, |it, a| {
    let c = scalar_arg(it, a, 1)?;
    let n = mat_arg(a, 0)?.m.nrows();
    let (i, j) = (row_number(a, 2, "row", Some(1), n)?, row_number(a, 3, "row", Some(2), n)?);
    add_line(&mut target(a).m, &c, i, j, true)
});

row_op!(add_col_proc, add_col_func, |it, a| {
    let c = scalar_arg(it, a, 1)?;
    let n = mat_arg(a, 0)?.m.ncols();
    let (i, j) = (row_number(a, 2, "column", Some(1), n)?, row_number(a, 3, "column", Some(2), n)?);
    add_line(&mut target(a).m, &c, i, j, false)
});

/// c times row (or column) i, on the left.
fn scale_line(m: &mut Mat, c: &Elem, i: usize, rows: bool) -> RResult<()> {
    let n = if rows { m.ncols() } else { m.nrows() };
    for k in 0..n {
        let (r, s) = if rows { (i, k) } else { (k, i) };
        let y = c.mul(&m.entry(r, s))?;
        m.set_entry(r, s, &y);
    }
    Ok(())
}

row_op!(mul_row_proc, mul_row_func, |it, a| {
    let c = scalar_arg(it, a, 1)?;
    let n = mat_arg(a, 0)?.m.nrows();
    let i = row_number(a, 2, "row", None, n)?;
    scale_line(&mut target(a).m, &c, i, true)
});

row_op!(mul_col_proc, mul_col_func, |it, a| {
    let c = scalar_arg(it, a, 1)?;
    let n = mat_arg(a, 0)?.m.ncols();
    let i = row_number(a, 2, "column", None, n)?;
    scale_line(&mut target(a).m, &c, i, false)
});

/// Replace argument 0 by the matrix of the given rows and columns.
fn keep(it: &mut Interp, a: &mut CallArgs, rows: &[usize], cols: &[usize]) -> RResult<()> {
    let m = mat_arg(a, 0)?.clone();
    a.args[0] = over_ring_of(it, &m, m.m.select(rows, cols))?;
    Ok(())
}

fn all_but(n: usize, i: Option<usize>) -> Vec<usize> {
    (0..n).filter(|&k| Some(k) != i).collect()
}

row_op!(remove_row_proc, remove_row_func, |it, a| {
    let (r, c) = (mat_arg(a, 0)?.m.nrows(), mat_arg(a, 0)?.m.ncols());
    let i = removed(a, 1, r)?;
    keep(it, a, &all_but(r, Some(i)), &all_but(c, None))
});

row_op!(remove_col_proc, remove_col_func, |it, a| {
    let (r, c) = (mat_arg(a, 0)?.m.nrows(), mat_arg(a, 0)?.m.ncols());
    let j = removed(a, 1, c)?;
    keep(it, a, &all_but(r, None), &all_but(c, Some(j)))
});

row_op!(remove_row_col_proc, remove_row_col_func, |it, a| {
    let (r, c) = (mat_arg(a, 0)?.m.nrows(), mat_arg(a, 0)?.m.ncols());
    let i = removed(a, 1, r)?;
    let j = removed(a, 2, c)?;
    keep(it, a, &all_but(r, Some(i)), &all_but(c, Some(j)))
});

row_op!(remove_zero_rows_proc, remove_zero_rows_func, |it, a| {
    let m = mat_arg(a, 0)?.clone();
    let rows: Vec<usize> = (0..m.m.nrows()).filter(|&i| (0..m.m.ncols()).any(|j| !m.m.entry_is_zero(i, j))).collect();
    keep(it, a, &rows, &all_but(m.m.ncols(), None))
});

fn is_zero(_: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(mat_arg(a, 0)?.m.is_zero() == calyx_flint::gr::Truth::True)
}

pub fn register(it: &mut Interp) {
    for name in ["NumberOfRows", "Nrows"] {
        it.def(name, "A::Mtrx -> RngIntElt", "The number of rows of A.", nrows);
    }
    for name in ["NumberOfColumns", "Ncols"] {
        it.def(name, "A::Mtrx -> RngIntElt", "The number of columns of A.", ncols);
    }
    for name in ["NumberOfNonZeroEntries", "NNZEntries"] {
        it.def(name, "A::Mtrx -> RngIntElt", "The number of non-zero entries of A.", nnz);
    }
    it.def("Density", "A::Mtrx -> FldReElt", "The proportion of non-zero entries of A.", density);
    for name in ["BaseRing", "CoefficientRing"] {
        it.def(name, "A::Mtrx -> Rng", "The ring of the entries of A.", base_ring);
    }
    for name in ["ElementToSequence", "Eltseq"] {
        it.def(name, "A::Mtrx -> SeqEnum", "The entries of A in row-major order.", eltseq);
    }
    it.def("RowSequence", "A::Mtrx -> SeqEnum", "The rows of A as sequences.", row_sequence);
    it.def("IsZero", "A::Mtrx -> BoolElt", "Whether A is the zero matrix.", is_zero);

    let block = "A::Mtrx, i::RngIntElt, j::RngIntElt, p::RngIntElt, q::RngIntElt -> Mtrx";
    for name in ["Submatrix", "ExtractBlock"] {
        it.def(name, block, "The p by q block of A at (i, j).", submatrix);
    }
    for name in ["SubmatrixRange", "ExtractBlockRange"] {
        it.def(name, block, "The block of A from (i, j) to (p, q).", submatrix_range);
    }
    it.def("Submatrix", "A::Mtrx, I::[RngIntElt], J::[RngIntElt] -> Mtrx", "The submatrix of A with rows I and columns J.", submatrix_seqs);
    it.def("InsertBlock", "~A::Mtrx, B::Mtrx, i::RngIntElt, j::RngIntElt", "Insert B into A at (i, j).", insert_block_proc);
    it.def("InsertBlock", "A::Mtrx, B::Mtrx, i::RngIntElt, j::RngIntElt -> Mtrx", "A with B inserted at (i, j).", insert_block_func);
    it.def("RowSubmatrix", "A::Mtrx, i::RngIntElt, k::RngIntElt -> Mtrx", "The k rows of A from row i.", row_submatrix);
    it.def("RowSubmatrix", "A::Mtrx, i::RngIntElt -> Mtrx", "The first i rows of A.", row_submatrix);
    it.def("RowSubmatrixRange", "A::Mtrx, i::RngIntElt, j::RngIntElt -> Mtrx", "Rows i to j of A.", row_submatrix_range);
    it.def("ColumnSubmatrix", "A::Mtrx, i::RngIntElt, k::RngIntElt -> Mtrx", "The k columns of A from column i.", column_submatrix);
    it.def("ColumnSubmatrix", "A::Mtrx, i::RngIntElt -> Mtrx", "The first i columns of A.", column_submatrix);
    it.def("ColumnSubmatrixRange", "A::Mtrx, i::RngIntElt, j::RngIntElt -> Mtrx", "Columns i to j of A.", column_submatrix_range);

    let ij = ", i::RngIntElt, j::RngIntElt";
    def_both(it, "SwapRows", ij, "Swap rows i and j of A.", swap_rows_proc, swap_rows_func);
    def_both(it, "SwapColumns", ij, "Swap columns i and j of A.", swap_cols_proc, swap_cols_func);
    def_both(it, "ReverseRows", "", "Reverse the order of the rows of A.", reverse_rows_proc, reverse_rows_func);
    def_both(it, "ReverseColumns", "", "Reverse the order of the columns of A.", reverse_cols_proc, reverse_cols_func);
    let cij = ", c::RngElt, i::RngIntElt, j::RngIntElt";
    def_both(it, "AddRow", cij, "Add c times row i of A to row j.", add_row_proc, add_row_func);
    def_both(it, "AddColumn", cij, "Add c times column i of A to column j.", add_col_proc, add_col_func);
    let ci = ", c::RngElt, i::RngIntElt";
    def_both(it, "MultiplyRow", ci, "Multiply row i of A by c.", mul_row_proc, mul_row_func);
    def_both(it, "MultiplyColumn", ci, "Multiply column i of A by c.", mul_col_proc, mul_col_func);
    def_both(it, "RemoveRow", ", i::RngIntElt", "Remove row i of A.", remove_row_proc, remove_row_func);
    def_both(it, "RemoveColumn", ", j::RngIntElt", "Remove column j of A.", remove_col_proc, remove_col_func);
    def_both(it, "RemoveRowColumn", ij, "Remove row i and column j of A.", remove_row_col_proc, remove_row_col_func);
    def_both(it, "RemoveZeroRows", "", "Remove the zero rows of A.", remove_zero_rows_proc, remove_zero_rows_func);
}
