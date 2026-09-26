//! Creating relations: embeddings and isomorphisms between fields.

use super::*;

pub(super) fn embed(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (e, f) = (field_arg(a, 0)?, field_arg(a, 1)?);
    it.ff_embed_fields(&e, &f, a.args.get(2))?;
    none()
}

/// An isomorphism between fields of the same size, given by the image of
/// the generator of the context of its domain.
struct FieldIso {
    image: Elem,
    from: Rc<Struct>,
    to: Rc<Struct>,
}

impl NativeMap for FieldIso {
    fn apply(&self, it: &mut Interp, _m: &MapObj, x: &Value) -> RResult<Value> {
        let failed = || RuntimeError::runtime("Application of map failed").in_context("map application");
        let x = it.to_structure_elem(&Value::Struct(self.from.clone()), x, false)?.ok_or_else(failed)?;
        Ok(make_elt(&self.to, finite::embed_with(&x, degree(&self.from), &self.image)))
    }

    fn preimage(&self, it: &mut Interp, _m: &MapObj, y: &Value) -> RResult<Value> {
        let failed = || RuntimeError::runtime("Application of map failed").in_context("@@");
        let y = it.to_structure_elem(&Value::Struct(self.to.clone()), y, false)?.ok_or_else(failed)?;
        let x = finite::restrict_by(&y, &self.from, &self.image, &self.to).ok_or_else(failed)?;
        Ok(make_elt(&self.from, x))
    }

    fn image(&self, _it: &mut Interp, _m: &MapObj) -> Option<RResult<Value>> {
        Some(Ok(Value::Struct(self.to.clone())))
    }
}

pub(super) fn is_isomorphic(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (e, f) = (field_arg(a, 0)?, field_arg(a, 1)?);
    if ff(&e).1.p != ff(&f).1.p || degree(&e) != degree(&f) {
        return Ok(vals![Value::Bool(false), Value::Undef]);
    }
    let image = finite::iso_image(&e, &f).ok_or_else(|| RuntimeError::runtime("No isomorphism found"))?;
    let imp = FieldIso { image, from: e.clone(), to: f.clone() };
    let map = Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain: Value::Struct(e), codomain: Value::Struct(f), imp: MapImpl::Native(Rc::new(imp)) }));
    Ok(vals![Value::Bool(true), map])
}
