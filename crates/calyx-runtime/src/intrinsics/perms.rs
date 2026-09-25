//! Symmetric groups and permutations (the parts Part II needs: `Sort`
//! returns its sorting permutation as an element of `Sym(n)`).

use std::rc::Rc;

use calyx_flint::Integer;

use super::{boolv, intv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::perms::{Perm, sym_degree};
use crate::value::*;

fn group_arg(a: &CallArgs, i: usize) -> usize {
    match &a.args[i] {
        Value::Struct(s) => sym_degree(s).unwrap(),
        _ => unreachable!(),
    }
}

fn perm_arg(a: &CallArgs, i: usize) -> Rc<Perm> {
    match &a.args[i] {
        Value::Perm(p) => p.clone(),
        _ => unreachable!(),
    }
}

fn sym(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = a.int(0)?;
    if n.sign() <= 0 {
        return Err(RuntimeError::runtime(format!("Argument 1 ({n}) should be >= 1")));
    }
    let n = n.to_u64().filter(|&n| n < u32::MAX as u64).ok_or_else(|| RuntimeError::runtime("Argument 1 is too large"))?;
    one(Value::Struct(it.sym_group(n as usize)))
}

fn ngens_count(n: usize) -> usize {
    n.min(3) - 1
}

fn ngens(_: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    one(Value::int(ngens_count(group_arg(a, 0)) as i64))
}

fn generator(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = group_arg(a, 0);
    let k = ngens_count(n) as i64;
    let i = a.int(1)?;
    let range_err = || RuntimeError::runtime(format!("Argument 2 ({i}) should be in the range [{} .. {k}]", -k));
    let i = i.to_i64().filter(|i| i.abs() <= k).ok_or_else(range_err)?;
    if i == 0 {
        return one(it.perm_identity(n));
    }
    let g = it.sym_generator(n, i.unsigned_abs() as usize);
    match (&g, i < 0) {
        (Value::Perm(p), true) => one(Value::Perm(Rc::new(p.inverse()))),
        _ => one(g),
    }
}

fn identity(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = group_arg(a, 0);
    one(it.perm_identity(n))
}

fn group_degree(_: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    one(Value::int(group_arg(a, 0) as i64))
}

fn group_order(_: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    intv(Integer::factorial(group_arg(a, 0) as u64))
}

fn degree(_: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    one(Value::int(perm_arg(a, 0).degree() as i64))
}

fn order(_: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    intv(perm_arg(a, 0).order())
}

fn eltseq(_: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    one(Value::int_seq(perm_arg(a, 0).images.iter().map(|&x| Integer::from_u64(x as u64 + 1))))
}

fn inverse(_: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    one(Value::Perm(Rc::new(perm_arg(a, 0).inverse())))
}

fn sign(_: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    one(Value::int(perm_arg(a, 0).sign()))
}

fn is_even(_: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    boolv(perm_arg(a, 0).sign() == 1)
}

fn is_odd(_: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    boolv(perm_arg(a, 0).sign() == -1)
}

fn is_identity(_: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    boolv(perm_arg(a, 0).is_identity())
}

/// `[ <length, count>, ... ]`, longest cycles first, fixed points included.
fn cycle_structure(_: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let mut lens: Vec<usize> = perm_arg(a, 0).cycles().iter().map(|c| c.len()).collect();
    lens.sort_unstable_by(|x, y| y.cmp(x));
    let mut out: Vec<(usize, usize)> = Vec::new();
    for l in lens {
        match out.last_mut() {
            Some((m, c)) if *m == l => *c += 1,
            _ => out.push((l, 1)),
        }
    }
    let elems = out.into_iter().map(|(l, c)| Value::tuple(vec![Value::int(l as i64), Value::int(c as i64)])).collect();
    one(Value::seq(None, elems))
}

/// The cycle of `p` through the point `i`, starting at `i`.
fn cycle(_: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let p = perm_arg(a, 0);
    let i = a.int(1)?.to_u64().filter(|&i| i >= 1 && i as usize <= p.degree()).ok_or_else(|| RuntimeError::runtime("Argument 2 not in support of group"))?;
    let start = i as usize - 1;
    let mut pts = vec![Value::int(i as i64)];
    let mut j = p.images[start] as usize;
    while j != start {
        pts.push(Value::int(j as i64 + 1));
        j = p.images[j] as usize;
    }
    one(Value::ISet(Rc::new(SetIndx { universe: Some(Value::integers()), elems: pts.into_iter().collect(), name: Default::default() })))
}

pub fn register(it: &mut Interp) {
    for name in ["Sym", "SymmetricGroup"] {
        it.def(name, "n::RngIntElt -> GrpPerm", "The symmetric group on {1, ..., n}.", sym);
    }
    it.def("Ngens", "G::GrpPerm -> RngIntElt", "The number of generators of G.", ngens);
    it.def(".", "G::GrpPerm, i::RngIntElt -> GrpPermElt", "The i-th generator of G (its inverse for negative i).", generator);
    for name in ["Id", "Identity"] {
        it.def(name, "G::GrpPerm -> GrpPermElt", "The identity of G.", identity);
    }
    it.def("Degree", "G::GrpPerm -> RngIntElt", "The number of points G acts on.", group_degree);
    it.def("Order", "G::GrpPerm -> RngIntElt", "The order of G.", group_order);
    it.def("Degree", "p::GrpPermElt -> RngIntElt", "The number of points p acts on.", degree);
    it.def("Order", "p::GrpPermElt -> RngIntElt", "The order of p.", order);
    for name in ["ElementToSequence", "Eltseq"] {
        it.def(name, "p::GrpPermElt -> [RngIntElt]", "The images of 1, ..., n under p.", eltseq);
    }
    it.def("Inverse", "p::GrpPermElt -> GrpPermElt", "The inverse of p.", inverse);
    it.def("Sign", "p::GrpPermElt -> RngIntElt", "1 if p is even, -1 if it is odd.", sign);
    it.def("IsEven", "p::GrpPermElt -> BoolElt", "Whether p is an even permutation.", is_even);
    it.def("IsOdd", "p::GrpPermElt -> BoolElt", "Whether p is an odd permutation.", is_odd);
    for name in ["IsIdentity", "IsId"] {
        it.def(name, "p::GrpPermElt -> BoolElt", "Whether p is the identity.", is_identity);
    }
    it.def("CycleStructure", "p::GrpPermElt -> [Tup]", "The lengths of the cycles of p with their multiplicities, longest first.", cycle_structure);
    it.def("Cycle", "p::GrpPermElt, i::RngIntElt -> SetIndx", "The cycle of p containing i, starting at i.", cycle);
}
