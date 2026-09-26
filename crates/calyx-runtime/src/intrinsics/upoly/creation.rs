//! Creating univariate polynomial rings and polynomials, and changing the
//! coefficient ring (the handbook's Creation Functions and Structure
//! Operations).

use std::rc::Rc;

use calyx_flint::gr::Elem;

use super::ideals::res_reduce;
use super::{cval, len, ring_arg};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::intrinsics::{bare, none, one};
use crate::rings::{RingKind, make_elt, ring_of};
use crate::value::*;

// ----- creation ------------------------------------------------------------------

pub(super) fn polynomial_seq(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Some(u) = a.seq(0)?.universe.clone() else {
        return Err(bare(RuntimeError::runtime("Argument 1 must be non-null")));
    };
    let p = it.poly_ring(&u, true)?;
    one(it.coerce(&p, &a.args[0])?)
}

pub(super) fn polynomial_over(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let p = it.poly_ring(&a.args[0], true)?;
    match it.try_coerce(&p, &a.args[1])? {
        Ok(v) => one(v),
        Err(_) => Err(bare(RuntimeError::runtime("Argument 2 is not coercible over argument 1"))),
    }
}

pub(super) fn identity(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, r) = ring_arg(a, 0);
    one(make_elt(&st, Elem::one(&r.ctx)?))
}

/// `P.i` and `Name(P, i)`: the indeterminate (of a quotient ring, its
/// image; of an ideal, its generator).
pub(super) fn indeterminate(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (st, r) = ring_arg(a, 0);
    let i = a.int(1)?;
    if !i.is_one() {
        return Err(RuntimeError::runtime(format!("Value for name index ({i}) should be in the range [1..1]")));
    }
    if let Some(StructKind::UPolIdeal(g)) = a.args[0].as_struct() {
        return one(Value::Elt(g.clone()));
    }
    let x = r.ctx.generator()?;
    let x = if let RingKind::UPolyRes { modulus, .. } = &r.kind { res_reduce(modulus, x)? } else { x };
    one(make_elt(&st, x))
}

pub(super) fn assign_names(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (_, r) = ring_arg(a, 0);
    let names = a.seq(1)?;
    if names.elems.len() != 1 {
        return Err(RuntimeError::runtime("Argument 2 must have length 1"));
    }
    let Value::Str(s) = &names.elems[0] else { return Err(RuntimeError::runtime("Names must be strings")) };
    *r.names.borrow_mut() = vec![Rc::from(s.as_str())];
    none()
}

// ----- changing rings ---------------------------------------------------------------

/// The map of `ChangeRing` between polynomial rings: coercion of the
/// coefficients, or a map applied to them.
struct CoefficientMap(Option<Rc<MapObj>>);

impl NativeMap for CoefficientMap {
    fn apply(&self, it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        let x = it.coerce(&m.domain, x).map_err(|_| RuntimeError::runtime("Element is not in the domain of the map").in_context("map application"))?;
        let Value::Elt(f) = &x else { unreachable!("a polynomial") };
        let Some((cst, cod)) = ring_of(&m.codomain) else { unreachable!("a polynomial ring") };
        let (cst, target, ctx) = (cst.clone(), cod.base().expect("a polynomial ring").clone(), cod.ctx.clone());
        let mut cs = Vec::with_capacity(len(f));
        for i in 0..len(f) {
            let mut c = cval(it, f, f.x.poly_coeff(i));
            if let Some(g) = &self.0 {
                c = it.apply_map(g, &c)?;
            }
            match it.to_structure_elem(&target, &c, true)? {
                Some(e) => cs.push(e),
                None => {
                    let msg = "Cannot coerce element from source coefficent ring into the destination coefficient ring";
                    return Err(RuntimeError::runtime(msg).in_context("map application"));
                }
            }
        }
        Ok(make_elt(&cst, Elem::poly_from_coeffs(&ctx, &cs)?))
    }

    fn preimage(&self, _it: &mut Interp, _m: &MapObj, _y: &Value) -> RResult<Value> {
        Err(RuntimeError::runtime("No inverse is known for the map").in_context("@@"))
    }
}

pub(super) fn change_ring(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let q = it.poly_ring(&a.args[1], true)?;
    let f = match a.args.get(2) {
        Some(Value::Map(m)) => Some(m.clone()),
        _ => None,
    };
    let h = MapObj { kind: MapKind::Map, domain: a.args[0].clone(), codomain: q.clone(), imp: MapImpl::Native(Rc::new(CoefficientMap(f))) };
    Ok(vals![q, Value::Map(Rc::new(h))])
}
