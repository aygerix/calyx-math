//! Homomorphisms: `hom< F -> R | x >`.

use super::*;

/// `hom< F -> R | x >` for a field F that is not prime: the sum of a_i g^i,
/// for g the generator of F over its prime field and a_i in the prime
/// field, goes to the sum of a_i x^i. (Magma leaves it to the user that
/// this is a homomorphism, and the map has no inverse.)
struct FieldHom {
    from: Rc<Struct>,
    /// Coordinates in the powers of g from those in the context of F.
    to_g: LinMap,
    image: Value,
}

impl NativeMap for FieldHom {
    fn apply(&self, it: &mut Interp, m: &MapObj, x: &Value) -> RResult<Value> {
        let failed = || RuntimeError::runtime("Element is not in the domain of the map").in_context("map application");
        let x = it.to_structure_elem(&Value::Struct(self.from.clone()), x, false)?.ok_or_else(failed)?;
        let cs = self.to_g.apply(&Coords::of(&x)).integers();
        // Horner's rule, with elements when R is a finite field.
        if let Value::Elt(y) = &self.image {
            if field_of(&y.parent).is_some() {
                let ctx = y.x.ctx();
                let mut acc = Elem::zero(ctx);
                for c in cs.iter().rev() {
                    acc = acc.mul(&y.x)?.add(&Elem::from_integer(ctx, c)?)?;
                }
                return Ok(make_elt(&y.parent, acc));
            }
        }
        let mut acc = it.coerce(&m.codomain, &Value::int(0))?;
        for c in cs.into_iter().rev() {
            acc = it.binop(BinOp::Mul, acc, self.image.clone())?;
            acc = it.binop(BinOp::Add, acc, Value::Int(c))?;
        }
        Ok(acc)
    }

    fn preimage(&self, _it: &mut Interp, _m: &MapObj, _y: &Value) -> RResult<Value> {
        Err(RuntimeError::runtime("Map has no inverse").in_context("@@"))
    }

    fn has_inverse(&self) -> bool {
        false
    }

    fn image(&self, _it: &mut Interp, _m: &MapObj) -> Option<RResult<Value>> {
        Some(Err(RuntimeError::runtime("Image is not computable or representable")))
    }
}

/// `hom< F -> R | x >` (or `iso< >`) for a finite field F that is not a
/// prime field (see `FieldHom`); `None` for other domains. A prime field
/// takes no images.
pub fn hom_images(it: &mut Interp, kind: MapKind, domain: &Value, codomain: &Value, images: &[Value]) -> RResult<Option<Value>> {
    let Some(f) = finite::field_struct(domain).cloned() else { return Ok(None) };
    let ctx = if kind == MapKind::Iso { "iso< ... >" } else { "hom< ... >" };
    let want = usize::from(degree(&f) > 1);
    if images.len() != want {
        let msg = format!("Wrong number of arguments to FldFin homomorphism element constructor (should be {want})");
        return Err(RuntimeError::runtime(msg).in_context(ctx));
    }
    let [x] = images else { return Ok(None) };
    let not_in = || RuntimeError::runtime("Element is not in the codomain of the map").in_context(ctx);
    let image = it.try_coerce(codomain, x)?.map_err(|_| not_in())?;
    let (p, n, ctx) = (ff(&f).1.p.clone(), degree(&f) as usize, ff(&f).0.ctx.clone());
    let k = it.default_field(&p, 1)?;
    let g = gen_over(it, &f, &k)?;
    let mut cols = Vec::with_capacity(n);
    let mut pw = Elem::one(&ctx)?;
    for _ in 0..n {
        cols.push(Coords::of(&pw));
        pw = pw.mul(&g)?;
    }
    let to_g = LinMap::from_columns(&p, &cols, n).inverse().ok_or_else(bad)?;
    let imp = FieldHom { from: f, to_g, image };
    let imp = MapImpl::Native(Rc::new(imp));
    Ok(Some(Value::Map(Rc::new(MapObj { kind: MapKind::Map, domain: domain.clone(), codomain: codomain.clone(), imp }))))
}
