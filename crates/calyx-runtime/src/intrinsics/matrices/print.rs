//! Printing matrices, vectors and their parents.
//!
//! Magma prints a matrix one row per line, in brackets (a vector in
//! parentheses), with the entries right-aligned to a common width: that of
//! the widest entry, or over a prime field below 2^30 or a field with Zech
//! logarithms, that of the widest element of the field. When a row does
//! not fit on a line that way, and over the real and complex fields, the
//! entries are not aligned, and long rows continue on further indented
//! lines.

use calyx_flint::gr::CtxKind;

use super::{Mtrx, Shape, entry_value, info};
use crate::error::RResult;
use crate::interp::Interp;
use crate::print::{Level, Printer};
use crate::rings::small::SmallKind;
use crate::value::*;

/// `Matrix with 0 rows and 6 columns`.
fn empty_text(r: usize, c: usize) -> String {
    let s = |n: usize| if n == 1 { "" } else { "s" };
    format!("Matrix with {r} row{} and {c} column{}", s(r), s(c))
}

/// The width of the widest element of a finite field whose elements are
/// all padded to it: a prime field below 2^30, or a field with Zech
/// logarithms.
fn field_width(it: &mut Interp, ring: &Value, level: Level) -> RResult<Option<usize>> {
    let Some(StructKind::Ring(r)) = ring.as_struct() else { return Ok(None) };
    let Some(s) = r.small else { return Ok(None) };
    let info = s.info();
    let widest = match info.kind {
        SmallKind::PrimeField if info.m.modulus() < 1 << 30 => info.m.modulus() - 1,
        SmallKind::Zech(z) => z.zero() - 1,
        _ => return Ok(None),
    };
    Ok(Some(it.format_flat(&Value::Small(s, widest), level)?.chars().count()))
}

/// The entries of `a` as text, row after row.
fn entry_texts(it: &mut Interp, a: &Mtrx, level: Level) -> RResult<Vec<String>> {
    let (r, c) = (a.m.nrows(), a.m.ncols());
    let mut out = Vec::with_capacity(r * c);
    for i in 0..r {
        for j in 0..c {
            let s = match a.m.ctx().kind() {
                CtxKind::Integers if level != Level::Hex => a.m.integer(i, j).to_string(),
                _ => {
                    let v = entry_value(it, a, i, j);
                    it.format_flat(&v, level)?
                }
            };
            out.push(s);
        }
    }
    Ok(out)
}

pub fn fmt_matrix(it: &mut Interp, p: &mut Printer, a: &Mtrx, indent: usize) -> RResult<()> {
    let (r, c) = (a.m.nrows(), a.m.ncols());
    if p.level == Level::Magma {
        return fmt_magma(it, p, a, indent);
    }
    if r == 0 || c == 0 {
        p.write(&empty_text(r, c));
        return Ok(());
    }
    let level = if p.level == Level::Hex { Level::Hex } else { Level::Default };
    let texts = entry_texts(it, a, level)?;
    let ring = a.ring().clone();
    let unaligned = matches!(a.m.ctx().kind(), CtxKind::RealFloat(_) | CtxKind::ComplexFloat(_));
    let mut w = texts.iter().map(|s| s.chars().count()).max().unwrap_or(0);
    if let Some(fw) = field_width(it, &ring, level)? {
        w = w.max(fw);
    }
    let aligned = !unaligned && 2 + c * w + (c - 1) < p.width;
    let (open, close) = if a.is_vector() { ('(', ')') } else { ('[', ']') };
    let saved = p.cont;
    p.cont = if aligned { indent } else { indent + 4 };
    for i in 0..r {
        if i > 0 {
            p.newline(indent);
        }
        let mut row = String::with_capacity(2 + c * (w + 1));
        row.push(open);
        for (j, s) in texts[i * c..(i + 1) * c].iter().enumerate() {
            if j > 0 {
                row.push(' ');
            }
            if aligned {
                for _ in s.chars().count()..w {
                    row.push(' ');
                }
            }
            row.push_str(s);
        }
        row.push(close);
        p.text(&row);
    }
    p.cont = saved;
    Ok(())
}

/// A matrix at the Magma level: its parent applied to its entries.
fn fmt_magma(it: &mut Interp, p: &mut Printer, a: &Mtrx, indent: usize) -> RResult<()> {
    let (r, c) = (a.m.nrows(), a.m.ncols());
    let parent = Value::Struct(a.parent.clone());
    it.fmt(p, &parent, indent)?;
    p.write(" ! ");
    let mut elems = Vec::with_capacity(r * c);
    for i in 0..r {
        for j in 0..c {
            elems.push(entry_value(it, a, i, j));
        }
    }
    // Entries of residue rings and prime fields show as integers.
    let ints = elems.iter().all(|v| matches!(v, Value::Int(_) | Value::Small(..)) && !matches!(v, Value::Small(s, _) if s.zech().is_some()));
    let seq = if ints {
        Value::int_seq(elems.iter().map(|v| match v {
            Value::Int(n) => n.clone(),
            Value::Small(_, w) => calyx_flint::Integer::from_u64(*w),
            _ => unreachable!(),
        }))
    } else {
        Value::seq(Some(a.ring().clone()), elems)
    };
    let shape = info(&a.parent).shape;
    if shape == Shape::Space {
        let ring = a.ring().clone();
        p.write("Matrix(");
        it.fmt(p, &ring, indent)?;
        p.write(&format!(", {r}, {c}, "));
        it.fmt(p, &seq, indent)?;
        p.write(")");
    } else {
        it.fmt(p, &seq, indent)?;
    }
    Ok(())
}

/// A full matrix algebra, matrix space or R-space. The coefficient ring
/// prints briefly.
pub fn fmt_parent(it: &mut Interp, p: &mut Printer, st: &Struct, indent: usize) -> RResult<()> {
    let mp = info(st);
    let ring = mp.ring.clone();
    if p.level == Level::Magma {
        let (name, dims) = match mp.shape {
            Shape::Algebra => ("MatrixAlgebra", format!("{}", mp.nrows)),
            Shape::Space => (if mp.field { "KMatrixSpace" } else { "RMatrixSpace" }, format!("{}, {}", mp.nrows, mp.ncols)),
            Shape::Tuples => (if mp.field { "VectorSpace" } else { "RSpace" }, format!("{}", mp.ncols)),
        };
        p.write(&format!("{name}("));
        it.fmt(p, &ring, indent)?;
        p.write(&format!(", {dims})"));
        return Ok(());
    }
    p.write(&match mp.shape {
        Shape::Algebra => format!("Full Matrix Algebra of degree {} over ", mp.nrows),
        Shape::Space => format!("Full {}MatrixSpace of {} by {} matrices over ", if mp.field { "K" } else { "R" }, mp.nrows, mp.ncols),
        Shape::Tuples if mp.field => format!("Full Vector space of degree {} over ", mp.ncols),
        Shape::Tuples => format!("Full RSpace of degree {} over ", mp.ncols),
    });
    let saved = p.level;
    p.level = Level::Minimal;
    let r = it.fmt(p, &ring, indent);
    p.level = saved;
    r
}
