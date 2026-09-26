//! Finite fields: creation, subfields and embeddings, the functions of the
//! fields and of their elements, polynomials over finite fields, discrete
//! logarithms and permutation polynomials. The lattice of fields and the
//! maps between them are in `rings::finite`.
//!
//! Coordinates of an element over a subfield E of F are taken in the power
//! basis of `Generator(F, E)` (`F.1` when it generates F over E), as in
//! Magma; over the ground field this is the basis of `F.1` in which
//! elements print.
//!
//! The submodules follow the sections of the handbook chapter; this module
//! has the helpers they share and the registration.

mod arithmetic;
mod creation;
mod elements;
mod lattice;
mod logs;
mod maps;
mod permutation;
mod polynomials;
mod structure;

use std::rc::Rc;

use calyx_flint::gr::{Ctx, CtxKind, Elem, Truth};
use calyx_flint::{Integer, Nmod};
use calyx_syntax::ast::BinOp;

use super::{arg_ge, arg_not, arg_prime, boolv, dlog, factseq, intv, none, one, require};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::rings::finite::{self, field_of};
use crate::rings::fp::{Coords, LinMap};
use crate::rings::{FiniteField, Ring, make_elt};
use crate::sym::Sym;
use crate::value::*;

use arithmetic::*;
use creation::*;
use elements::*;
use lattice::*;
use logs::*;
use permutation::*;
use polynomials::*;
use structure::*;

pub use maps::hom_images;

fn bad() -> RuntimeError {
    RuntimeError::runtime("Bad argument types")
}

fn ff(st: &Struct) -> (&Ring, &FiniteField) {
    field_of(st).expect("a finite field")
}

fn id(st: &Struct) -> u64 {
    ff(st).0.id
}

fn degree(st: &Struct) -> u64 {
    ff(st).1.degree
}

fn is_zero(x: &Elem) -> bool {
    x.is_zero() == Truth::True
}

fn is_zech(ctx: &Ctx) -> bool {
    matches!(ctx.kind(), CtxKind::FqZech { .. })
}

fn field_arg(a: &CallArgs, i: usize) -> RResult<Rc<Struct>> {
    finite::field_struct(&a.args[i]).cloned().ok_or_else(bad)
}

/// A finite field element argument: its field and its FLINT element.
fn felt_arg(a: &CallArgs, i: usize) -> RResult<(Rc<Struct>, Elem)> {
    let e = crate::rings::small::elt_of(&a.args[i]).ok_or_else(bad)?;
    if field_of(&e.parent).is_none() {
        return Err(bad());
    }
    Ok((e.parent.clone(), e.x.clone()))
}

fn prime_of(it: &mut Interp, st: &Struct) -> RResult<Rc<Struct>> {
    let p = ff(st).1.p.clone();
    it.default_field(&p, 1)
}

/// The ground field: the field `st` was built over, else the prime field.
fn ground_of(it: &mut Interp, st: &Struct) -> RResult<Rc<Struct>> {
    match &ff(st).1.ground {
        Some(g) => Ok(g.field.clone()),
        None => prime_of(it, st),
    }
}

/// The polynomial with coefficients `cs` (in the context of `base`,
/// constant term first) in the global polynomial ring over `base`.
fn poly_value(it: &mut Interp, base: &Rc<Struct>, cs: &[Elem]) -> RResult<Value> {
    let px = it.poly_ring(&Value::Struct(base.clone()), true)?;
    let Value::Struct(ps) = &px else { unreachable!() };
    let StructKind::Ring(pr) = &ps.kind else { unreachable!() };
    Ok(make_elt(ps, Elem::poly_from_coeffs(&pr.ctx, cs)?))
}

/// The polynomial with integer coefficients over GF(p).
fn int_poly_value(it: &mut Interp, p: &Integer, cs: &[Integer]) -> RResult<Value> {
    let fp = it.default_field(p, 1)?;
    let ctx = ff(&fp).0.ctx.clone();
    poly_value(it, &fp, &finite::int_poly_in(cs, &ctx))
}

const NOT_SUB: &str = "Argument 2 is not a subfield of the parent of argument 1";
const NOT_SUB_OF: &str = "Argument 2 is not a subfield of argument 1";

/// The image in `f` of the generator of the context of its known subfield
/// `e`, else the error `msg`.
fn sub_image(e: &Rc<Struct>, f: &Rc<Struct>, msg: &str) -> RResult<Elem> {
    finite::find_emb(e, f).ok_or_else(|| RuntimeError::runtime(msg))
}

/// `y`, an element of `f` lying in its known subfield `e`, in `e`.
fn down(y: &Elem, f: &Rc<Struct>, e: &Rc<Struct>) -> Elem {
    finite::restrict(y, f, e).flatten().expect("an element of the subfield")
}

/// Magma's order on the elements of a field: prime fields by residue,
/// others as `rings::finite::elt_order`.
fn elem_cmp(a: &Elem, b: &Elem) -> std::cmp::Ordering {
    match a.ctx().kind() {
        CtxKind::Nmod(_) | CtxKind::FmpzMod(_) => a.to_integer().unwrap_or_default().cmp(&b.to_integer().unwrap_or_default()),
        _ => finite::elt_order(a, b),
    }
}

fn sort_elems(v: &mut [Elem]) {
    v.sort_by(elem_cmp);
}

// ----- registration --------------------------------------------------------------------

pub fn register(it: &mut Interp) {
    for name in ["FiniteField", "GaloisField", "GF"] {
        it.def_params(
            name,
            "q::RngIntElt -> FldFin",
            &[("Optimize", Value::Bool(true)), ("Sparse", Value::Bool(false))],
            "The finite field with q elements.",
            finite_field_q,
        );
        it.def_params(
            name,
            "p::RngIntElt, n::RngIntElt -> FldFin",
            &[("Check", Value::Bool(true)), ("Optimize", Value::Bool(true)), ("Sparse", Value::Bool(false))],
            "The finite field with p^n elements.",
            finite_field_pn,
        );
    }
    it.def("RandomExtension", "F::FldFin, n::RngIntElt -> FldFin", "The extension of F by a random irreducible polynomial of degree n.", random_extension);
    it.def("SplittingField", "P::RngUPolElt[FldFin] -> FldFin", "The splitting field of P over its coefficient field.", splitting_field);
    it.def("SplittingField", "S::{RngUPolElt} -> FldFin", "The splitting field of the polynomials in S.", splitting_field_set);
    it.def("RootsInSplittingField", "f::RngUPolElt[FldFin] -> [Tup], FldFin", "The roots of f in its splitting field S, and S.", roots_in_splitting_field);
    for name in ["FactorizationOverSplittingField", "FactorisationOverSplittingField"] {
        it.def(
            name,
            "f::RngUPolElt[FldFin] -> [Tup], FldFin",
            "The factorization of f into linear factors over its splitting field S, and S.",
            factorization_over_splitting_field,
        );
    }
    for name in ["GroundField", "BaseField"] {
        it.def(name, "F::FldFin -> FldFin", "The field F was constructed over (the prime field if none).", ground_field);
    }
    it.def("meet", "F::FldFin, G::FldFin -> FldFin", "The intersection of F and G.", meet);
    it.def("CommonOverfield", "K::FldFin, L::FldFin -> FldFin", "The smallest field containing K and L.", common_overfield);
    it.def("Embed", "E::FldFin, F::FldFin", "Embed E in F.", embed);
    it.def("Embed", "E::FldFin, F::FldFin, x::FldFinElt", "Embed E in F, mapping the generator of E to x.", embed);
    it.def("IsIsomorphic", "E::FldFin, F::FldFin -> BoolElt, Map", "Whether E and F are isomorphic, and an isomorphism.", is_isomorphic);

    it.def("FieldOfFractions", "F::FldFin -> FldFin", "The field F itself.", |_, a| one(a.args[0].clone()));
    it.def("Degree", "F::FldFin -> RngIntElt", "The degree of F over its prime field.", degree_ff);
    it.def("Degree", "F::FldFin, E::FldFin -> RngIntElt", "The degree of F over its subfield E.", degree_over);
    it.def("IsConway", "F::FldFin -> BoolElt", "Whether F is defined by a Conway polynomial.", is_conway);
    it.def("IsDefault", "F::FldFin -> BoolElt", "Whether F is a default field.", is_default);
    it.def("DefiningPolynomial", "F::FldFin -> RngUPolElt", "The polynomial defining F over its ground field.", defining_polynomial);
    it.def("DefiningPolynomial", "F::FldFin, E::FldFin -> RngUPolElt", "The minimal polynomial of Generator(F, E) over E.", defining_polynomial_over);
    it.def("AdditiveGroup", "F::FldFin -> GrpAb, Map", "The additive group of F, and its map to F.", additive_group);
    for name in ["MultiplicativeGroup", "UnitGroup"] {
        it.def(name, "F::FldFin -> GrpAb, Map", "The multiplicative group of F, and its map to F.", multiplicative_group);
    }
    it.def(
        "RootOfUnity",
        "n::RngIntElt, K::FldFin -> FldFinElt",
        "A primitive n-th root of unity in the smallest extension of K containing one.",
        root_of_unity,
    );

    it.def("SetPowerPrinting", "F::FldFin, l::BoolElt", "Print the elements of F as powers of the primitive element (or not).", set_power_printing);
    it.def("AssertAttribute", "F::FldFin, A::MonStgElt, l::.", "Set attribute A of F (PowerPrinting: the printing of elements).", assert_attribute);
    it.def("HasAttribute", "F::FldFin, A::MonStgElt -> BoolElt, .", "Whether attribute A of F is set, and its value.", has_attribute);

    it.def("Generator", "F::FldFin -> FldFinElt", "The generator F.1 of F over its ground field.", generator);
    it.def("Generator", "F::FldFin, E::FldFin -> FldFinElt", "An element generating F over its subfield E (F.1 if it does).", generator_over);
    it.def("PrimitiveElement", "F::FldFin -> FldFinElt", "The primitive element of F (the base of Log).", primitive_element);
    it.def("SetPrimitiveElement", "F::FldFin, x::FldFinElt", "Set the primitive element of F to x.", set_primitive_element);
    it.def("Identity", "F::FldFin -> FldFinElt", "The identity 1 of F.", |_, a| {
        let f = field_arg(a, 0)?;
        one(make_elt(&f, Elem::one(&ff(&f).0.ctx)?))
    });
    it.def("Random", "F::FldFin -> FldFinElt", "A random element of F.", random);
    it.def("NormalElement", "F::FldFin -> FldFinElt", "A normal element of F over its ground field.", normal_element);
    it.def("NormalElement", "F::FldFin, E::FldFin -> FldFinElt", "A normal element of F over its subfield E.", normal_element_e);
    for name in ["SequenceToElement", "Seqelt"] {
        it.def(name, "s::[FldFinElt], F::FldFin -> FldFinElt", "The element of F with coordinates s over the field of s.", seqelt);
    }
    for name in ["ElementToSequence", "Eltseq"] {
        it.def(name, "a::FldFinElt -> [FldFinElt]", "The coordinates of a over the ground field.", eltseq);
        it.def(name, "a::FldFinElt, E::FldFin -> [FldFinElt]", "The coordinates of a over the subfield E.", eltseq_e);
    }

    it.def("IsPrimitive", "a::FldFinElt -> BoolElt", "Whether a generates the multiplicative group.", is_primitive_elt);
    it.def("IsPrimitive", "f::RngUPolElt[FldFin] -> BoolElt", "Whether x is primitive in the extension defined by f.", is_primitive_poly);
    it.def("IsRegular", "a::FldFinElt -> BoolElt", "Whether a is not a zero divisor (is non-zero).", |_, a| {
        let (_, x) = felt_arg(a, 0)?;
        boolv(!is_zero(&x))
    });
    it.def("IsNormal", "a::FldFinElt -> BoolElt", "Whether a generates a normal basis over the ground field.", is_normal);
    it.def("IsNormal", "a::FldFinElt, E::FldFin -> BoolElt", "Whether a generates a normal basis over E.", is_normal);
    it.def("IsSquare", "a::FldFinElt -> BoolElt, FldFinElt", "Whether a is a square, and a square root.", is_square);
    for name in ["SquareRoot", "Sqrt"] {
        it.def(name, "a::FldFinElt -> FldFinElt", "A square root of a.", sqrt);
    }
    it.def("Root", "a::FldFinElt, n::RngIntElt -> FldFinElt", "An n-th root of a.", root);
    it.def("IsPower", "a::FldFinElt, n::RngIntElt -> BoolElt, FldFinElt", "Whether a is an n-th power, and an n-th root.", is_power);
    it.def("AllRoots", "a::FldFinElt, n::RngIntElt -> [FldFinElt]", "All n-th roots of a in its field.", all_roots);
    it.def("MinimalPolynomial", "a::FldFinElt -> RngUPolElt", "The minimal polynomial of a over the ground field.", minimal_polynomial);
    it.def("MinimalPolynomial", "a::FldFinElt, E::FldFin -> RngUPolElt", "The minimal polynomial of a over E.", minimal_polynomial);
    it.def("CharacteristicPolynomial", "a::FldFinElt -> RngUPolElt", "The characteristic polynomial of a over the ground field.", characteristic_polynomial);
    it.def("CharacteristicPolynomial", "a::FldFinElt, E::FldFin -> RngUPolElt", "The characteristic polynomial of a over E.", characteristic_polynomial);
    it.def("Norm", "a::FldFinElt -> FldFinElt", "The norm of a to the ground field.", norm);
    it.def("Norm", "a::FldFinElt, E::FldFin -> FldFinElt", "The norm of a to E.", norm);
    it.def("Trace", "a::FldFinElt -> FldFinElt", "The trace of a to the ground field.", trace);
    it.def("Trace", "a::FldFinElt, E::FldFin -> FldFinElt", "The trace of a to E.", trace);
    for name in ["AbsoluteNorm", "NormAbs"] {
        it.def(name, "a::FldFinElt -> FldFinElt", "The norm of a to the prime field.", absolute_norm);
    }
    for name in ["AbsoluteTrace", "TraceAbs"] {
        it.def(name, "a::FldFinElt -> FldFinElt", "The trace of a to the prime field.", absolute_trace);
    }
    it.def("Frobenius", "a::FldFinElt -> FldFinElt", "a^q for q the size of the ground field.", frobenius);
    it.def("Frobenius", "a::FldFinElt, r::RngIntElt -> FldFinElt", "a^(q^r) for q the size of the ground field.", frobenius);
    it.def("Frobenius", "a::FldFinElt, E::FldFin -> FldFinElt", "a^#E.", frobenius);
    it.def("Frobenius", "a::FldFinElt, E::FldFin, r::RngIntElt -> FldFinElt", "a^((#E)^r).", frobenius);
    it.def(
        "NormEquation",
        "K::FldFin, y::FldFinElt -> BoolElt, FldFinElt",
        "Whether y is a norm from K to the field of y, and an element of K of norm y.",
        norm_equation,
    );
    it.def("Hilbert90", "a::FldFinElt, q::RngIntElt -> FldFinElt", "A solution of x^(q-1) = a, in an extension if needed.", hilbert90);
    it.def("AdditiveHilbert90", "a::FldFinElt, q::RngIntElt -> FldFinElt", "A solution of x^q - x = a, in an extension if needed.", additive_hilbert90);
    it.def("FactoredOrder", "a::FldFinElt -> RngIntEltFact", "The factored multiplicative order of a.", factored_order);

    it.def("Log", "x::FldFinElt -> RngIntElt", "The logarithm of x to the base of the primitive element.", log);
    it.def("Log", "b::FldFinElt, x::FldFinElt -> RngIntElt", "The logarithm of x to the base b (-1 if there is none).", log_b);
    it.def("ZechLog", "K::FldFin, n::RngIntElt -> RngIntElt", "The Zech logarithm of n: the logarithm of w^n + 1 for the primitive element w.", zech_log);
    it.def_params("Sieve", "K::FldFin", &[("Lanczos", Value::Bool(false))], "Prepare the logarithms of K (nothing to do here).", sieve);
    it.verbose.insert(Rc::from("FFLog"), (0, 2));

    it.def("ConwayPolynomial", "p::RngIntElt, n::RngIntElt -> RngUPolElt", "The Conway polynomial of degree n over GF(p).", conway_polynomial);
    it.def(
        "ExistsConwayPolynomial",
        "p::RngIntElt, n::RngIntElt -> BoolElt, RngUPolElt",
        "Whether the Conway polynomial of degree n over GF(p) is known, and the polynomial.",
        exists_conway_polynomial,
    );
    it.def("IrreduciblePolynomial", "F::FldFin, n::RngIntElt -> RngUPolElt", "An irreducible polynomial of degree n over F.", irreducible_polynomial);
    it.def(
        "RandomIrreduciblePolynomial",
        "F::FldFin, n::RngIntElt -> RngUPolElt",
        "A random irreducible polynomial of degree n over F.",
        random_irreducible_polynomial,
    );
    it.def("PrimitivePolynomial", "F::FldFin, m::RngIntElt -> RngUPolElt", "A primitive polynomial of degree m over F.", primitive_polynomial);
    it.def(
        "AllIrreduciblePolynomials",
        "F::FldFin, m::RngIntElt -> SetEnum",
        "The monic irreducible polynomials of degree m over F.",
        all_irreducible_polynomials,
    );
    it.def(
        "IrreducibleLowTermGF2Polynomial",
        "n::RngIntElt -> RngUPolElt",
        "The irreducible x^n + g over GF(2) with g of least degree, first in lexicographic order.",
        irreducible_low_term_gf2,
    );
    it.def(
        "IrreducibleSparseGF2Polynomial",
        "n::RngIntElt -> RngUPolElt",
        "The first irreducible trinomial x^n + x^k + 1 over GF(2), else pentanomial.",
        irreducible_sparse_gf2,
    );

    it.def_params(
        "IsProbablyPermutationPolynomial",
        "p::RngUPolElt -> BoolElt",
        &[("NumAttempts", Value::int(100))],
        "Whether p probably permutes its coefficient field.",
        is_probably_permutation_polynomial,
    );
}
