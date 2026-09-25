//! Core intrinsics: operators as values, types, parents and coercion,
//! random numbers, error objects and user-defined types.

use std::rc::Rc;

use calyx_flint::Integer;
use calyx_syntax::ast::BinOp;

use super::{boolv, intv, none, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::sym::Sym;
use crate::types::{TypeArg, TypeVal, t};
use crate::value::*;

macro_rules! binop_fn {
    ($name:ident, $op:expr) => {
        fn $name(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
            let x = std::mem::take(&mut a.args[0]);
            let y = std::mem::take(&mut a.args[1]);
            one(it.binop($op, x, y)?)
        }
    };
}

binop_fn!(op_add, BinOp::Add);
binop_fn!(op_mul, BinOp::Mul);
binop_fn!(op_div, BinOp::Div);
binop_fn!(op_intdiv, BinOp::IntDiv);
binop_fn!(op_mod, BinOp::Mod);
binop_fn!(op_pow, BinOp::Pow);
binop_fn!(op_cat, BinOp::Cat);
binop_fn!(op_join, BinOp::Join);
binop_fn!(op_meet, BinOp::Meet);
binop_fn!(op_diff, BinOp::Diff);
binop_fn!(op_sdiff, BinOp::Sdiff);
binop_fn!(op_eq, BinOp::Eq);
binop_fn!(op_ne, BinOp::Ne);
binop_fn!(op_lt, BinOp::Lt);
binop_fn!(op_le, BinOp::Le);
binop_fn!(op_gt, BinOp::Gt);
binop_fn!(op_ge, BinOp::Ge);
binop_fn!(op_cmpeq, BinOp::Cmpeq);
binop_fn!(op_cmpne, BinOp::Cmpne);
binop_fn!(op_in, BinOp::In);
binop_fn!(op_notin, BinOp::Notin);
binop_fn!(op_subset, BinOp::Subset);
binop_fn!(op_notsubset, BinOp::Notsubset);
binop_fn!(op_and, BinOp::And);
binop_fn!(op_or, BinOp::Or);
binop_fn!(op_xor, BinOp::Xor);

fn op_sub(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    if a.args.len() == 1 {
        let x = std::mem::take(&mut a.args[0]);
        return one(it.negate(x)?);
    }
    let x = std::mem::take(&mut a.args[0]);
    let y = std::mem::take(&mut a.args[1]);
    one(it.binop(BinOp::Sub, x, y)?)
}

fn op_not(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    match &a.args[0] {
        Value::Bool(b) => boolv(!b),
        v => {
            let v = v.clone();
            one(it.unary_intrinsic("not", v)?)
        }
    }
}

fn op_card(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let v = a.args[0].clone();
    one(it.cardinality(&v)?)
}

fn op_coerce(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (s, x) = (a.args[0].clone(), a.args[1].clone());
    one(it.coerce(&s, &x)?)
}

fn op_image(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (x, m) = (a.args[0].clone(), a.args[1].clone());
    one(it.image(&x, &m)?)
}

fn op_preimage(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (x, m) = (a.args[0].clone(), a.args[1].clone());
    one(it.preimage(&x, &m)?)
}

fn op_index(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let base = a.args[0].clone();
    let idx: Vec<Value> = a.args[1..].to_vec();
    one(it.index_multi(base, &idx)?)
}

fn op_dot(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let s = a.args[0].clone();
    Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}, {}", it.type_name(&s), it.type_name(&a.args[1]))))
}

// ----- types --------------------------------------------------------------

fn type_of(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    one(Value::Cat(a.args[0].type_id()))
}

fn extended_type_of(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let v = a.args[0].clone();
    let tv = it.shown_extended_type(&v).unwrap_or(TypeVal::Cat(v.type_id()));
    one(Value::ECat(Rc::new(tv)))
}

fn as_typeval(v: &Value) -> Option<TypeVal> {
    match v {
        Value::Cat(t) => Some(TypeVal::Cat(*t)),
        Value::ECat(t) => Some((**t).clone()),
        _ => None,
    }
}

fn isa(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (Some(x), Some(y)) = (as_typeval(&a.args[0]), as_typeval(&a.args[1])) else {
        return Err(RuntimeError::runtime("Arguments must be types"));
    };
    let r = it.types.isa(x.base(), y.base())
        && (y.args().is_empty()
            || (x.args().len() == y.args().len()
                && x.args().iter().zip(y.args()).all(|(p, q)| match (p, q) {
                    (TypeArg::Type(p), TypeArg::Type(q)) => it.types.isa(p.base(), q.base()),
                    (TypeArg::Str(p), TypeArg::Str(q)) => p == q,
                    _ => false,
                })));
    boolv(r)
}

fn base_type(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let tv = as_typeval(&a.args[0]).unwrap();
    one(Value::Cat(tv.base()))
}

fn make_type(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let s = a.str(0)?;
    match it.types.lookup(s) {
        Some(t) => one(Value::Cat(t)),
        None => Err(RuntimeError::runtime(format!("Unknown type '{s}'"))),
    }
}

fn element_type(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let s = a.args[0].clone();
    let tv = it.element_type_of(&s);
    one(match tv {
        TypeVal::Cat(t) => Value::Cat(t),
        other => Value::ECat(Rc::new(other)),
    })
}

fn covering_structure(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    match it.common_universe(&a.args[0], &a.args[1]) {
        Some(c) => one(c),
        None => Err(RuntimeError::runtime("No covering structure exists")),
    }
}

fn exists_covering_structure(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    match it.common_universe(&a.args[0], &a.args[1]) {
        Some(c) => Ok(vec![Value::Bool(true), c]),
        None => Ok(vec![Value::Bool(false), Value::Undef]),
    }
}

fn parent(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let v = a.args[0].clone();
    one(it.parent_of(&v)?)
}

fn is_coercible(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (s, x) = (a.args[0].clone(), a.args[1].clone());
    match it.try_coerce(&s, &x)? {
        Ok(v) => Ok(vec![Value::Bool(true), v]),
        Err(_) => Ok(vec![Value::Bool(false), Value::Undef]),
    }
}

fn integers(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vec<Value>> {
    one(Value::integers())
}

fn rationals(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vec<Value>> {
    one(Value::rationals())
}

fn booleans(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vec<Value>> {
    one(Value::booleans())
}

fn zero(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let s = a.args[0].clone();
    one(it.coerce(&s, &Value::int(0))?)
}

fn one_of(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let s = a.args[0].clone();
    one(it.coerce(&s, &Value::int(1))?)
}

// ----- random -------------------------------------------------------------

fn random_elt(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let s = a.args[0].clone();
    match &s {
        // Infinite rings have no Random.
        _ if crate::rings::props::ring_props(&s).is_some_and(|p| p.cardinality.is_none()) => Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}", it.type_name_ext(&s)))),
        Value::Formal(_) => Err(RuntimeError::runtime("Cannot choose a random element of a formal set")),
        _ => {
            let (_, x) = it.random_element_indexed(&s)?;
            one(x)
        }
    }
}

fn random_bool(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vec<Value>> {
    boolv(it.rng.below_u64(2) == 1)
}

fn set_seed(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let s = a.int(0)?.to_u64().filter(|&s| s < (1 << 32)).ok_or_else(|| RuntimeError::runtime("Seed must be in the range [0, 2^32)"))?;
    let c = if a.args.len() > 1 { a.int(1)?.to_u64().ok_or_else(|| RuntimeError::runtime("Step count must be non-negative"))? } else { 0 };
    it.rng.set_seed(s, c);
    none()
}

fn get_seed(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vec<Value>> {
    let (s, c) = it.rng.seed();
    Ok(vec![Value::Int(Integer::from_u64(s)), Value::Int(Integer::from_u64(c))])
}

// ----- misc -----------------------------------------------------------------

fn is_intrinsic(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let s = Sym::new(a.str(0)?);
    if it.intrinsics.contains(s) { Ok(vec![Value::Bool(true), Value::Intr(s)]) } else { Ok(vec![Value::Bool(false), Value::Undef]) }
}

fn error_obj(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    one(Value::Err(Rc::new(ErrObj { object: a.args[0].clone(), kind: Rc::from("ErrUser"), position: None, traceback: None })))
}

fn nresults(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vec<Value>> {
    let n = it.nresults_stack.last().copied().unwrap_or(1);
    let b = Value::seq(Some(Value::booleans()), vec![Value::Bool(true); n]);
    Ok(vec![Value::int(n as i64), b])
}

fn hash(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    use std::hash::{Hash, Hasher};
    let mut h = rustc_hash::FxHasher::default();
    a.args[0].hash(&mut h);
    // Values of different types hash differently here (3 and 3/1 are equal
    // but have different hashes).
    a.args[0].type_id().hash(&mut h);
    intv(Integer::from_u64(h.finish() & ((1 << 62) - 1)))
}

fn new_object(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let Value::Cat(ty) = &a.args[0] else {
        return Err(RuntimeError::runtime("Argument must be a type"));
    };
    if !it.types.info(*ty).user {
        return Err(RuntimeError::runtime(format!("{} is not a user-defined type", it.types.name(*ty))));
    }
    one(Value::Obj(Rc::new(UserObj { ty: *ty, attrs: Default::default(), id: next_object_id() })))
}

fn clone_object(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    match &a.args[0] {
        Value::Obj(o) => one(Value::Obj(Rc::new(UserObj { ty: o.ty, attrs: std::cell::RefCell::new(o.attrs.borrow().clone()), id: next_object_id() }))),
        other => one(other.clone()),
    }
}

fn add_attribute(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let Value::Cat(ty) = &a.args[0] else {
        return Err(RuntimeError::runtime("Argument 1 must be a type"));
    };
    let name = Sym::new(a.str(1)?);
    it.types.add_attribute(*ty, name);
    none()
}

fn get_attributes(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let Value::Cat(ty) = &a.args[0] else {
        return Err(RuntimeError::runtime("Argument must be a type"));
    };
    let mut names: Vec<String> = it.types.info(*ty).attributes.iter().map(|s| s.to_string()).collect();
    names.sort();
    one(Value::seq(Some(Value::strings()), names.iter().map(|s| Value::str(s)).collect()))
}

fn list_attributes(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let r = get_attributes(it, a)?;
    let Value::Seq(s) = &r[0] else { unreachable!() };
    for v in &s.elems {
        if let Value::Str(n) = v {
            it.out.write(&format!("{n}\n"));
        }
    }
    none()
}

fn unknown_attribute(name: Sym) -> RuntimeError {
    RuntimeError::runtime(format!("Unknown attribute \"{name}\" for this object"))
}

fn has_attribute(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let v = a.args[0].clone();
    let name = Sym::new(a.str(1)?);
    if let Value::Cat(ty) = v {
        let x = it.category_attr(ty, name).ok_or_else(|| unknown_attribute(name))?;
        return Ok(vec![Value::Bool(true), x]);
    }
    match it.attr_assigned(&v, name) {
        Ok(true) => Ok(vec![Value::Bool(true), it.get_attr(&v, name)?]),
        _ => Ok(vec![Value::Bool(false), Value::Undef]),
    }
}

fn assert_attribute(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    let name = Sym::new(a.str(1)?);
    let value = a.args[2].clone();
    match &a.args[0] {
        Value::Struct(s) => {
            s.attrs.borrow_mut().insert(name, value);
        }
        Value::Obj(o) => {
            o.attrs.borrow_mut().insert(name, value);
        }
        Value::Cat(ty) => {
            if it.category_attr(*ty, name).is_none() {
                return Err(unknown_attribute(name));
            }
            // The only one so far: RngInt`CunninghamStorageLimit, a small
            // non-negative integer.
            let Value::Int(n) = &value else {
                return Err(RuntimeError::runtime(format!("Bad rhs type for attribute \"{name}\"")));
            };
            match n.to_i64().filter(|&n| (0..1 << 30).contains(&n)) {
                Some(n) => it.cunningham_storage_limit = n,
                None => return Err(super::arg_not(2, "positive")),
            }
        }
        other => return Err(RuntimeError::runtime(format!("Objects of type {} do not have attributes", it.type_name(other)))),
    }
    none()
}

fn assign_names(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vec<Value>> {
    none()
}

fn ngens(it: &mut Interp, a: &mut CallArgs) -> RResult<Vec<Value>> {
    Err(RuntimeError::runtime(format!("Objects of type {} have no generators", it.type_name(&a.args[0]))))
}

pub fn register(it: &mut Interp) {
    let ops: &[(&str, super::NativeFn)] = &[
        ("+", op_add),
        ("*", op_mul),
        ("/", op_div),
        ("div", op_intdiv),
        ("mod", op_mod),
        ("^", op_pow),
        ("cat", op_cat),
        ("join", op_join),
        ("meet", op_meet),
        ("diff", op_diff),
        ("sdiff", op_sdiff),
        ("eq", op_eq),
        ("ne", op_ne),
        ("lt", op_lt),
        ("le", op_le),
        ("gt", op_gt),
        ("ge", op_ge),
        ("cmpeq", op_cmpeq),
        ("cmpne", op_cmpne),
        ("in", op_in),
        ("notin", op_notin),
        ("subset", op_subset),
        ("notsubset", op_notsubset),
        ("and", op_and),
        ("or", op_or),
        ("xor", op_xor),
    ];
    for (name, f) in ops {
        it.def_generic(name, "x::., y::. -> .", "The operator applied to x and y.", *f);
    }
    it.def_generic("-", "x::., y::. -> .", "The difference x - y.", op_sub);
    it.def_generic("-", "x::. -> .", "The negation -x.", op_sub);
    it.def_generic("not", "x::. -> .", "The negation of x.", op_not);
    it.def_generic("#", "x::. -> .", "The cardinality of x.", op_card);
    it.def_generic("!", "S::., x::. -> .", "The coercion of x into S.", op_coerce);
    it.def_generic("@", "x::., f::. -> .", "The image of x under f.", op_image);
    it.def_generic("@@", "y::., f::. -> .", "The preimage of y under f.", op_preimage);
    it.def_generic("[]", "x::., i::., ... -> .", "Indexing.", op_index);
    it.def_generic(".", "S::., i::. -> .", "The i-th generator of S.", op_dot);

    it.def("Type", "x::. -> Cat", "The type (category) of x.", type_of);
    it.def("Category", "x::. -> Cat", "The type (category) of x.", type_of);
    it.def("ExtendedType", "x::. -> ECat", "The extended type of x.", extended_type_of);
    it.def("ExtendedCategory", "x::. -> ECat", "The extended type of x.", extended_type_of);
    for sig in ["T::Cat, U::Cat -> BoolElt", "T::Cat, U::ECat -> BoolElt", "T::ECat, U::Cat -> BoolElt", "T::ECat, U::ECat -> BoolElt"] {
        it.def("ISA", sig, "Whether objects of type T inherit from type U.", isa);
    }
    it.def("BaseType", "T::ECat -> Cat", "The base type of the extended type T.", base_type);
    it.def("BaseType", "T::Cat -> Cat", "The base type of T (T itself).", base_type);
    it.def("MakeType", "S::MonStgElt -> Cat", "The type named by the string S.", make_type);
    it.def("ElementType", "S::. -> .", "The type of the elements of the structure S.", element_type);
    it.def("CoveringStructure", "S::., T::. -> .", "A structure containing both S and T.", covering_structure);
    it.def("ExistsCoveringStructure", "S::., T::. -> BoolElt, .", "Whether a structure containing S and T exists, and such a structure.", exists_covering_structure);
    it.def("Parent", "x::. -> .", "The parent structure of x.", parent);
    it.def("IsCoercible", "S::., x::. -> BoolElt, .", "Whether x can be coerced into S, and the result of the coercion.", is_coercible);
    it.def("Integers", "-> RngInt", "The ring of integers.", integers);
    it.def("IntegerRing", "-> RngInt", "The ring of integers.", integers);
    it.def("Rationals", "-> FldRat", "The field of rational numbers.", rationals);
    it.def("RationalField", "-> FldRat", "The field of rational numbers.", rationals);
    it.def("Booleans", "-> Bool", "The Boolean structure.", booleans);
    it.def("Zero", "S::. -> .", "The zero element of S.", zero);
    it.def("One", "S::. -> .", "The identity element of S.", one_of);

    it.def("Random", "S::. -> .", "A random element of the finite structure or aggregate S.", random_elt);
    it.def("Random", "B::Bool -> BoolElt", "A random Boolean.", random_bool);
    it.def("SetSeed", "s::RngIntElt", "Reset the random number generator to seed s.", set_seed);
    it.def("SetSeed", "s::RngIntElt, c::RngIntElt", "Reset the random number generator to seed s and advance it c steps.", set_seed);
    it.def("GetSeed", "-> RngIntElt, RngIntElt", "The seed of the random number generator and the number of steps taken since seeding.", get_seed);

    it.def("IsIntrinsic", "S::MonStgElt -> BoolElt, Intrinsic", "Whether an intrinsic named S exists, and the intrinsic.", is_intrinsic);
    it.def("Error", "x::. -> Err", "An error object carrying x.", error_obj);
    it.def("NumberOfResults", "-> RngIntElt, [BoolElt]", "The number of results requested from the current function.", nresults);
    it.def("Nresults", "-> RngIntElt, [BoolElt]", "The number of results requested from the current function.", nresults);
    it.def("Hash", "x::. -> RngIntElt", "A hash value for x.", hash);
    it.def("New", "T::Cat -> .", "A new object of the user-defined type T.", new_object);
    it.def("Clone", "X::. -> .", "A copy of X with its own attributes.", clone_object);
    it.def("AddAttribute", "C::Cat, F::MonStgElt", "Make F a valid attribute name for objects of type C.", add_attribute);
    it.def("GetAttributes", "C::Cat -> [MonStgElt]", "The valid attribute names for objects of type C.", get_attributes);
    it.def("ListAttributes", "C::Cat", "List the valid attribute names for objects of type C.", list_attributes);
    it.def("HasAttribute", "S::., F::MonStgElt -> BoolElt, .", "Whether attribute F of S is assigned, and its value.", has_attribute);
    it.def("AssertAttribute", "S::., F::MonStgElt, v::.", "Set attribute F of S to v.", assert_attribute);
    it.def("AssignNames", "~S::., N::[MonStgElt]", "Assign names to the generators of S.", assign_names);
    it.def("Ngens", "S::. -> RngIntElt", "The number of generators of S.", ngens);
    let _ = t::ANY;
}
