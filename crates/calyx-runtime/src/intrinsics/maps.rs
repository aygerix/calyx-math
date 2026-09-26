//! Intrinsics for maps (handbook chapter "Mappings").

use std::rc::Rc;

use super::{none, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::value::*;

fn map_arg(a: &CallArgs, i: usize) -> Rc<MapObj> {
    match &a.args[i] {
        Value::Map(m) => m.clone(),
        _ => unreachable!(),
    }
}

fn coercion_map(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain: a.args[0].clone(), codomain: a.args[1].clone(), imp: MapImpl::Coercion })))
}

fn identity_map(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain: a.args[0].clone(), codomain: a.args[0].clone(), imp: MapImpl::Coercion })))
}

fn domain(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match &a.args[0] {
        Value::Map(m) => one(m.domain.clone()),
        Value::Struct(s) => match &s.kind {
            StructKind::Maps(d, _) => one(d.clone()),
            _ => Err(RuntimeError::runtime("Argument must be a map or a set of maps")),
        },
        _ => unreachable!(),
    }
}

fn codomain(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match &a.args[0] {
        Value::Map(m) => one(m.codomain.clone()),
        Value::Struct(s) => match &s.kind {
            StructKind::Maps(_, c) => one(c.clone()),
            _ => Err(RuntimeError::runtime("Argument must be a map or a set of maps")),
        },
        _ => unreachable!(),
    }
}

fn image(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = map_arg(a, 0);
    if let MapImpl::Native(n) = &m.imp {
        if let Some(im) = n.image(it, &m) {
            return one(im?);
        }
    }
    let dom = m.domain.clone();
    // The images of groups are subgroups, which calyx cannot build yet.
    if matches!(m.imp, MapImpl::Native(_)) && matches!(dom.as_struct(), Some(StructKind::AbGroup(_))) {
        return Err(RuntimeError::runtime("Image is not computable or representable"));
    }
    let mut iter = it.iter_value(&dom, false).map_err(|_| RuntimeError::runtime("The image can only be computed for maps with a finite domain"))?;
    let mut out = Vec::new();
    while let Some((_, x)) = iter.next_item() {
        out.push(it.apply_map(&m, &x)?);
    }
    one(it.build_aggregate(calyx_syntax::ast::AggKind::Set, Some(m.codomain.clone()), out, false)?)
}

fn inverse(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = map_arg(a, 0);
    if matches!(&m.imp, MapImpl::Native(n) if !n.has_inverse()) {
        return Err(RuntimeError::runtime("Map has no inverse"));
    }
    one(Value::Map(Rc::new(MapObj { kind: m.kind, domain: m.codomain.clone(), codomain: m.domain.clone(), imp: MapImpl::Inverse(m.clone()) })))
}

fn function(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = map_arg(a, 0);
    match &m.imp {
        MapImpl::Rule { f, .. } => one(f.clone()),
        _ => one(Value::Map(m.clone())),
    }
}

fn has_preimage(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let y = a.args[0].clone();
    let m = map_arg(a, 1);
    // The preimage is only returned when it is asked for.
    let want = a.nresults >= 2;
    match it.map_preimage(&m, &y) {
        Ok(x) if want => Ok(vals![Value::Bool(true), x]),
        Ok(_) => Ok(vals![Value::Bool(true)]),
        Err(_) => Ok(vals![Value::Bool(false), Value::Undef]),
    }
}

fn components(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = map_arg(a, 0);
    let parts: Vec<Value> = match &m.imp {
        MapImpl::Compose(ms) => ms.iter().map(|x| Value::Map(x.clone())).collect(),
        _ => vec![Value::Map(m.clone())],
    };
    one(Value::seq(None, parts))
}

fn maps(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::structure(StructKind::Maps(a.args[0].clone(), a.args[1].clone())))
}

fn aut(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::structure(StructKind::Maps(a.args[0].clone(), a.args[0].clone())))
}

fn is_injective(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = map_arg(a, 0);
    let dom = m.domain.clone();
    let mut iter = it.iter_value(&dom, false)?;
    let mut seen = VSet::default();
    while let Some((_, x)) = iter.next_item() {
        if !seen.insert(it.apply_map(&m, &x)?) {
            return Ok(vals![Value::Bool(false)]);
        }
    }
    Ok(vals![Value::Bool(true)])
}

fn is_surjective(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = map_arg(a, 0);
    let dom = m.domain.clone();
    let mut iter = it.iter_value(&dom, false)?;
    let mut seen = VSet::default();
    while let Some((_, x)) = iter.next_item() {
        seen.insert(it.apply_map(&m, &x)?);
    }
    let cod = m.codomain.clone();
    let mut iter = it.iter_value(&cod, false)?;
    while let Some((_, y)) = iter.next_item() {
        if !seen.contains(&y) {
            return Ok(vals![Value::Bool(false)]);
        }
    }
    Ok(vals![Value::Bool(true)])
}

fn is_bijective(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let inj = is_injective(it, a)?;
    if inj[0] == Value::Bool(false) {
        return Ok(inj);
    }
    is_surjective(it, a)
}

fn graph(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let m = map_arg(a, 0);
    let dom = m.domain.clone();
    let mut iter = it.iter_value(&dom, false)?;
    let mut out = Vec::new();
    while let Some((_, x)) = iter.next_item() {
        let y = it.apply_map(&m, &x)?;
        out.push(Value::tuple(vec![x, y]));
    }
    one(it.build_aggregate(calyx_syntax::ast::AggKind::Set, None, out, false)?)
}

pub fn register(it: &mut Interp) {
    it.def("Coercion", "D::., C::. -> Map", "The coercion map from D to C.", coercion_map);
    it.def("Bang", "D::., C::. -> Map", "The coercion map from D to C.", coercion_map);
    it.def("Iso", "D::., C::. -> PowMap", "The set of isomorphisms from D to C.", maps);
    it.def("Aut", "S::. -> PowMap", "The set of automorphisms of S.", aut);
    it.def("IdentityMap", "S::. -> Map", "The identity map on S.", identity_map);
    it.def("Domain", "f::Map -> .", "The domain of f.", domain);
    it.def("Codomain", "f::Map -> .", "The codomain of f.", codomain);
    it.def("Domain", "P::PowMap -> .", "The domain of the maps in P.", domain);
    it.def("Codomain", "P::PowMap -> .", "The codomain of the maps in P.", codomain);
    it.def("Image", "f::Map -> .", "The image of f (for a finite domain).", image);
    it.def("Inverse", "f::Map -> Map", "The inverse of f.", inverse);
    it.def("Function", "f::Map -> .", "The function underlying f.", function);
    it.def("HasPreimage", "y::., f::Map -> BoolElt, .", "Whether y has a preimage under f, and a preimage.", has_preimage);
    it.def("Components", "f::Map -> SeqEnum", "The maps whose composition is f.", components);
    it.def("Maps", "D::., C::. -> PowMap", "The set of maps from D to C.", maps);
    it.def("IsInjective", "f::Map -> BoolElt", "Whether f is injective (finite domain).", is_injective);
    it.def("IsSurjective", "f::Map -> BoolElt", "Whether f is surjective (finite structures).", is_surjective);
    it.def("IsBijective", "f::Map -> BoolElt", "Whether f is bijective (finite structures).", is_bijective);
    it.def("Graph", "f::Map -> SetEnum", "The graph of f as a set of pairs (finite domain).", graph);
    let _ = none;
}
