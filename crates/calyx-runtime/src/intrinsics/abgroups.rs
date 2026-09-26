//! Abelian groups and their elements, and the groups attached to residue
//! class rings and to the integers: `UnitGroup`, `AdditiveGroup`,
//! `MultiplicativeGroup` and `ClassGroup`, each with its map to the ring.

use std::rc::Rc;

use calyx_flint::Integer;

use super::dlog::{log_mod_prime, log_one_units};
use super::ints::primitive_root;
use super::residue::{Res, residue_value};
use super::{boolv, intv, one};
use crate::abgroups::{AbElt, AbGroup, elt, group_of, new_group, zero};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

fn group_arg(a: &CallArgs, i: usize) -> (Rc<Struct>, Rc<AbGroup>) {
    match &a.args[i] {
        Value::Struct(s) => (s.clone(), group_of(s).expect("an abelian group").clone()),
        _ => unreachable!(),
    }
}

fn elt_arg(a: &CallArgs, i: usize) -> Rc<AbElt> {
    match &a.args[i] {
        Value::AbElt(x) => x.clone(),
        _ => unreachable!(),
    }
}

fn generator(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, g) = group_arg(a, 0);
    let n = g.ngens() as i64;
    let i = a.int(1)?;
    let Some(i) = i.to_i64() else {
        return Err(RuntimeError::runtime(format!("Argument 2 ({i}) is too large")));
    };
    if i.abs() > n {
        return Err(RuntimeError::runtime(format!("Argument 2 ({i}) should be in the range [{} .. {n}]", -n)));
    }
    let mut coords = vec![Integer::zero(); n as usize];
    if i != 0 {
        coords[i.unsigned_abs() as usize - 1] = Integer::from_i64(i.signum());
    }
    one(elt(&st, coords))
}

fn group_order(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(group_arg(a, 0).1.order().map_or(Value::Infinity(true), Value::Int))
}

fn ngens(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int(group_arg(a, 0).1.ngens() as i64))
}

fn generators(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, g) = group_arg(a, 0);
    let n = g.ngens();
    let gens = (0..n).map(|i| {
        let mut c = vec![Integer::zero(); n];
        c[i] = Integer::one();
        elt(&st, c)
    });
    one(Value::Set(Rc::new(SetEnum::new(Some(Value::Struct(st.clone())), gens.collect()))))
}

fn invariants(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int_seq(group_arg(a, 0).1.invariants()))
}

fn is_cyclic(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(group_arg(a, 0).1.invariants().len() <= 1)
}

fn exponent(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(group_arg(a, 0).1.exponent())
}

fn is_finite(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(group_arg(a, 0).1.is_finite())
}

fn is_trivial(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(group_arg(a, 0).1.order().is_some_and(|n| n.is_one()))
}

fn identity(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(zero(&group_arg(a, 0).0))
}

fn random(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, g) = group_arg(a, 0);
    if !g.is_finite() {
        return Err(RuntimeError::runtime("Group is not finite"));
    }
    let coords = g.orders.iter().map(|n| it.rng.below(n)).collect();
    one(elt(&st, coords))
}

fn eltseq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int_seq(elt_arg(a, 0).coords.iter().cloned()))
}

fn elt_order(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(elt_arg(a, 0).order())
}

fn is_identity(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(elt_arg(a, 0).is_zero())
}

// ----- maps -----------------------------------------------------------------

fn map_failed() -> RuntimeError {
    RuntimeError::runtime("Application of map failed").in_context("map application")
}

fn no_preimage() -> RuntimeError {
    RuntimeError::runtime("Application of map failed").in_context("@@")
}

/// The coefficients of `x` if it is an element of the domain of `m`.
fn domain_coords(m: &MapObj, x: &Value) -> RResult<Box<[Integer]>> {
    match (x, &m.domain) {
        (Value::AbElt(e), Value::Struct(st)) if Rc::ptr_eq(&e.group, st) => Ok(e.coords.clone()),
        _ => Err(map_failed()),
    }
}

fn domain_elt(m: &MapObj, coords: Vec<Integer>) -> Value {
    let Value::Struct(st) = &m.domain else { unreachable!() };
    elt(st, coords)
}

fn native_map(domain: Rc<Struct>, codomain: Value, imp: impl NativeMap + 'static) -> Value {
    Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain: Value::Struct(domain), codomain, imp: MapImpl::Native(Rc::new(imp)) }))
}

/// One prime power `p^k` exactly dividing the modulus of a unit group,
/// with its generators (indices into the group's generators).
struct UnitPart {
    p: Integer,
    k: u64,
    pk: Integer,
    first: usize,
    /// Odd `p`: the generator modulo `p^k` and the factorisation of `p - 1`.
    odd: Option<(Integer, Vec<(Integer, u64)>)>,
}

/// The map from the unit group of `Z/mZ` onto the units of the ring.
struct UnitMap {
    ring: Rc<Struct>,
    m: Integer,
    gens: Vec<Integer>,
    parts: Vec<UnitPart>,
}

impl UnitMap {
    /// The coefficients of a unit `y` on the generators.
    fn log(&self, y: &Integer) -> Option<Vec<Integer>> {
        let mut coords = vec![Integer::zero(); self.gens.len()];
        for part in &self.parts {
            let y = y.div_rem_euclid(&part.pk)?.1;
            match &part.odd {
                None if part.k == 1 => {}
                None => {
                    // Generated by -1 and, for k >= 3, by 5.
                    let minus = y.mod_u64(4) == 3;
                    coords[part.first] = Integer::from_u64(minus as u64);
                    if part.k >= 3 {
                        let y = if minus { &part.pk - &y } else { y };
                        coords[part.first + 1] = log_one_units(&y, &Integer::from_u64(5), &part.p, part.k)?;
                    }
                }
                Some((g, pm1)) => {
                    let n = &part.p - &Integer::one();
                    let x1 = log_mod_prime(&y, g, &part.p, pm1)?;
                    if part.k == 1 {
                        coords[part.first] = x1;
                        continue;
                    }
                    // The p-part of the logarithm from the units 1 mod p.
                    let x2 = log_one_units(&y.powm(&n, &part.pk)?, &g.powm(&n, &part.pk)?, &part.p, part.k)?;
                    let pe = part.p.pow(part.k - 1);
                    let t = (&(&x2 - &x1) * &n.invmod(&pe)?).div_rem_euclid(&pe)?.1;
                    coords[part.first] = &x1 + &(&n * &t);
                }
            }
        }
        Some(coords)
    }
}

impl NativeMap for UnitMap {
    fn apply(&self, _it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        let coords = domain_coords(m, x)?;
        let mut y = Integer::one().div_rem_euclid(&self.m).unwrap().1;
        for (g, c) in self.gens.iter().zip(coords.iter()) {
            if !c.is_zero() {
                y = (&y * &g.powm(c, &self.m).unwrap()).div_rem_euclid(&self.m).unwrap().1;
            }
        }
        let StructKind::Ring(r) = &self.ring.kind else { unreachable!() };
        residue_value(&self.ring, r, &y)
    }

    fn preimage(&self, it: &mut Interp, m: &MapObj, y: &Value) -> RResult<Value> {
        let not_unit = || RuntimeError::runtime("Argument is not a unit").in_context("@@");
        let y = match it.try_coerce(&m.codomain, y)? {
            Ok(v) => Res::of(&v).ok_or_else(not_unit)?.x,
            Err(_) => return Err(not_unit()),
        };
        if !y.gcd(&self.m).is_one() {
            return Err(not_unit());
        }
        let coords = self.log(&y).ok_or_else(|| RuntimeError::runtime("Discrete logarithm is too hard").in_context("@@"))?;
        Ok(domain_elt(m, coords))
    }
}

/// Magma's generators of the unit group of `Z/mZ`: for each prime power in
/// turn, -1 and 5 for 2^k (only -1 for 4, none for 2), and for odd p^k the
/// least primitive root g modulo p (g + p if g^(p-1) = 1 mod p^2), each
/// lifted to 1 modulo the other prime powers.
fn unit_group(ring: &Rc<Struct>, m: &Integer) -> RResult<(Rc<Struct>, Value)> {
    let factors = match &ring.kind {
        StructKind::Ring(r) => r.modulus_factors().unwrap_or_else(|| Rc::from(Vec::new())),
        _ => unreachable!(),
    };
    let mut gens = Vec::new();
    let mut orders = Vec::new();
    let mut parts = Vec::new();
    for (p, k) in factors.iter() {
        let pk = p.pow(*k);
        let first = gens.len();
        let mut local = Vec::new();
        let mut odd = None;
        if p.to_u64() == Some(2) {
            if *k >= 2 {
                local.push((&pk - &Integer::one(), Integer::from_u64(2)));
            }
            if *k >= 3 {
                local.push((Integer::from_u64(5), Integer::from_u64(2).pow(k - 2)));
            }
        } else {
            let n = p - &Integer::one();
            let mut g = primitive_root(p).ok_or_else(|| RuntimeError::runtime("Cannot find a primitive root"))?;
            if *k >= 2 && g.powm(&n, &p.pow(2)).is_some_and(|x| x.is_one()) {
                g = &g + p;
            }
            local.push((g.clone(), &n * &p.pow(k - 1)));
            let pm1 = n.factor().map(|f| f.factors).unwrap_or_default();
            odd = Some((g, pm1));
        }
        // Lift each generator to 1 modulo the other prime powers.
        let co = m.divexact(&pk);
        let inv = co.invmod(&pk).unwrap_or_else(Integer::one);
        for (g, n) in local {
            let t = (&(&g - &Integer::one()) * &inv).div_rem_euclid(&pk).unwrap().1;
            gens.push((&Integer::one() + &(&co * &t)).div_rem_euclid(m).unwrap().1);
            orders.push(n);
        }
        parts.push(UnitPart { p: p.clone(), k: *k, pk, first, odd });
    }
    let group = new_group(orders);
    let map = native_map(group.clone(), Value::Struct(ring.clone()), UnitMap { ring: ring.clone(), m: m.clone(), gens, parts });
    Ok((group, map))
}

/// The map from `Z/m` (as an additive group) onto `Z/mZ`.
struct AddResMap {
    ring: Rc<Struct>,
}

impl NativeMap for AddResMap {
    fn apply(&self, _it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        let c = domain_coords(m, x)?;
        let StructKind::Ring(r) = &self.ring.kind else { unreachable!() };
        residue_value(&self.ring, r, &c[0])
    }

    fn preimage(&self, it: &mut Interp, m: &MapObj, y: &Value) -> RResult<Value> {
        match it.try_coerce(&m.codomain, y)? {
            Ok(v) => Ok(domain_elt(m, vec![Res::of(&v).ok_or_else(no_preimage)?.x])),
            Err(_) => Err(no_preimage()),
        }
    }
}

/// The residue class ring behind a `RngIntRes` argument (not an ideal).
fn residue_ring(a: &CallArgs) -> RResult<(Rc<Struct>, Integer)> {
    if let Value::Struct(st) = &a.args[0] {
        if let StructKind::Ring(r) = &st.kind {
            if let crate::rings::RingKind::Residue(m) = &r.kind {
                return Ok((st.clone(), m.clone()));
            }
        }
    }
    Err(RuntimeError::runtime("Bad argument types\nArgument types given: RngIntRes"))
}

/// A group with its map. A statement printing the call shows only the
/// group.
pub(super) fn with_map(a: &CallArgs, group: Rc<Struct>, map: Value) -> RResult<Vals> {
    if a.nresults < 2 { one(Value::Struct(group)) } else { Ok(vals![Value::Struct(group), map]) }
}

fn unit_group_res(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, m) = residue_ring(a)?;
    let (group, map) = unit_group(&st, &m)?;
    with_map(a, group, map)
}

fn additive_group_res(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, m) = residue_ring(a)?;
    let group = new_group(vec![m]);
    let map = native_map(group.clone(), Value::Struct(st.clone()), AddResMap { ring: st });
    with_map(a, group, map)
}

/// The integers as a free abelian group of rank 1.
struct AddIntMap;

impl NativeMap for AddIntMap {
    fn apply(&self, _it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        Ok(Value::Int(domain_coords(m, x)?[0].clone()))
    }

    fn preimage(&self, it: &mut Interp, m: &MapObj, y: &Value) -> RResult<Value> {
        match it.try_coerce(&Value::integers(), y)? {
            Ok(Value::Int(k)) => Ok(domain_elt(m, vec![k])),
            _ => Err(no_preimage()),
        }
    }
}

/// The units {1, -1} of the integers as Z/2.
struct SignMap;

impl NativeMap for SignMap {
    fn apply(&self, _it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        Ok(Value::int(if domain_coords(m, x)?[0].is_zero() { 1 } else { -1 }))
    }

    fn preimage(&self, _it: &mut Interp, m: &MapObj, y: &Value) -> RResult<Value> {
        match y {
            Value::Int(k) if k.abs().is_one() => Ok(domain_elt(m, vec![Integer::from_u64((k.sign() < 0) as u64)])),
            _ => Err(no_preimage()),
        }
    }
}

/// The trivial class group of the integers, onto its one ideal class.
struct ClassMap;

impl NativeMap for ClassMap {
    fn apply(&self, _it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        domain_coords(m, x)?;
        Ok(Value::integers())
    }

    fn preimage(&self, _it: &mut Interp, m: &MapObj, y: &Value) -> RResult<Value> {
        match y {
            Value::Struct(s) if matches!(s.kind, StructKind::Integers | StructKind::IntIdeal(_)) => Ok(domain_elt(m, Vec::new())),
            _ => Err(no_preimage()),
        }
    }
}

fn is_integers(a: &CallArgs) -> RResult<()> {
    match a.args[0].as_struct() {
        Some(StructKind::Integers) => Ok(()),
        _ => Err(RuntimeError::runtime("Bad argument types\nArgument types given: RngInt")),
    }
}

fn additive_group_z(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    is_integers(a)?;
    let group = new_group(vec![Integer::zero()]);
    let map = native_map(group.clone(), Value::integers(), AddIntMap);
    with_map(a, group, map)
}

fn multiplicative_group_z(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    is_integers(a)?;
    let group = new_group(vec![Integer::from_u64(2)]);
    let map = native_map(group.clone(), Value::integers(), SignMap);
    with_map(a, group, map)
}

/// The trivial class group of Z with its map onto the ideals.
pub(super) fn class_group_of_z() -> (Rc<Struct>, Value) {
    let group = new_group(Vec::new());
    let codomain = Value::structure(StructKind::PowerStructure(crate::types::t::RNG_INT));
    let map = native_map(group.clone(), codomain, ClassMap);
    (group, map)
}

fn class_group_z(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    is_integers(a)?;
    let (group, map) = class_group_of_z();
    with_map(a, group, map)
}

/// `hom< R -> S | >` for a residue class ring R: the representative in
/// `[0, m)` of each element, taken into S.
struct ResidueHom;

impl NativeMap for ResidueHom {
    fn apply(&self, it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        let x = match it.try_coerce(&m.domain, x)? {
            Ok(v) => v,
            Err(_) => return Err(RuntimeError::runtime("Element is not in the domain of the map").in_context("map application")),
        };
        let r = Res::of(&x).ok_or_else(map_failed)?;
        it.coerce(&m.codomain, &Value::Int(r.x)).map_err(|_| map_failed())
    }

    fn preimage(&self, _it: &mut Interp, _m: &MapObj, _y: &Value) -> RResult<Value> {
        Err(RuntimeError::runtime("Map has no inverse").in_context("@@"))
    }
}

/// `hom< R -> S | >` when R is a residue class ring.
pub fn residue_hom(domain: &Value, codomain: &Value) -> Option<Value> {
    let Value::Struct(st) = domain else { return None };
    let StructKind::Ring(r) = &st.kind else { return None };
    if !matches!(r.kind, crate::rings::RingKind::Residue(_)) {
        return None;
    }
    Some(Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain: domain.clone(), codomain: codomain.clone(), imp: MapImpl::Native(Rc::new(ResidueHom)) })))
}

pub fn register(it: &mut Interp) {
    it.def(".", "G::GrpAb, i::RngIntElt -> GrpAbElt", "The i-th generator of G (its negative for negative i, 0 for i = 0).", generator);
    it.def("Order", "G::GrpAb -> RngIntElt", "The order of G (Infinity if G is infinite).", group_order);
    it.def("Ngens", "G::GrpAb -> RngIntElt", "The number of generators of G.", ngens);
    it.def("Generators", "G::GrpAb -> SetEnum", "The set of generators of G.", generators);
    it.def("Invariants", "G::GrpAb -> [RngIntElt]", "The invariant factors of G, with 0 for each infinite cyclic factor.", invariants);
    it.def("IsCyclic", "G::GrpAb -> BoolElt", "Whether G is cyclic.", is_cyclic);
    it.def("Exponent", "G::GrpAb -> RngIntElt", "The exponent of G (0 if G is infinite).", exponent);
    it.def("IsFinite", "G::GrpAb -> BoolElt", "Whether G is finite.", is_finite);
    it.def("IsTrivial", "G::GrpAb -> BoolElt", "Whether G is the trivial group.", is_trivial);
    for name in ["Id", "Identity", "Zero"] {
        it.def(name, "G::GrpAb -> GrpAbElt", "The identity of G.", identity);
    }
    it.def("Random", "G::GrpAb -> GrpAbElt", "A random element of the finite group G.", random);
    for name in ["Eltseq", "ElementToSequence"] {
        it.def(name, "x::GrpAbElt -> [RngIntElt]", "The coefficients of x on the generators of its group.", eltseq);
    }
    it.def("Order", "x::GrpAbElt -> RngIntElt", "The order of x (0 if it is infinite).", elt_order);
    it.def("IsIdentity", "x::GrpAbElt -> BoolElt", "Whether x is the identity.", is_identity);

    for name in ["UnitGroup", "MultiplicativeGroup"] {
        it.def(name, "R::RngIntRes -> GrpAb, Map", "The unit group of R = Z/mZ as an abelian group, with the map onto the units of R.", unit_group_res);
    }
    it.def("AdditiveGroup", "R::RngIntRes -> GrpAb, Map", "The additive group of R = Z/mZ, with the map onto R.", additive_group_res);
    it.def("AdditiveGroup", "Z::RngInt -> GrpAb, Map", "The additive group of Z, free of rank 1, with the map onto Z.", additive_group_z);
    for name in ["UnitGroup", "MultiplicativeGroup"] {
        it.def(name, "Z::RngInt -> GrpAb, Map", "The unit group {1, -1} of Z as Z/2, with the map onto the units.", multiplicative_group_z);
    }
    it.def("ClassGroup", "Z::RngInt -> GrpAb, Map", "The (trivial) class group of Z, with the map onto its ideals.", class_group_z);
}
