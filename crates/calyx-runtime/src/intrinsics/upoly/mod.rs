//! Univariate polynomial rings (the handbook chapter of that name):
//! creating polynomials, changing coefficient rings, the functions of
//! polynomials, greatest common divisors and content, the functions for
//! integer polynomials, factorization, resultants and Hensel lifting, small
//! roots modulo an integer (`small_roots`) and functional decomposition.
//!
//! Polynomials are `gr_poly`s. The algorithms beyond generic arithmetic run
//! on FLINT's specialised types through `calyx_flint::upoly`, over the
//! integers, the rationals, prime residue rings and finite fields, and over
//! polynomial rings over these flattened (`tower`).
//!
//! The submodules follow the sections of the handbook chapter; this module
//! has the helpers they share and the registration.

mod creation;
mod decomposition;
mod division;
mod elements;
mod factor;
mod finite_fields;
mod gcd;
mod ideals;
mod integers;
mod roots;
mod small_roots;
mod special;
mod tower;

use std::cmp::Ordering;
use std::rc::Rc;

use calyx_flint::gr::{Ctx, CtxKind, Elem, Truth};

use super::arg_not;
use crate::error::{ErrStyle, ErrorInfo, RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::rings::props::ring_props;
use crate::rings::{Elt, Ring, make_elt};
use crate::value::*;

use creation::*;
use decomposition::*;
use division::*;
use elements::*;
use factor::*;
use finite_fields::*;
use gcd::*;
use ideals::*;
use integers::*;
use roots::*;
use small_roots::*;
use special::*;

pub use division::quotrem;
pub(crate) use gcd::norm_unit;
pub(crate) use tower::{Tower, over_ground, poly_divides, poly_gcd};
pub use ideals::{enumerate_res, format_ideal, ideal_binop, ideal_constructor, ideal_member, quo_constructor};
pub use ideals::{res_div, res_is_domain, res_modulus, res_pow, res_reduce};

// ----- helpers ---------------------------------------------------------------

/// Argument `i`, which the signature makes a polynomial.
fn pol(a: &CallArgs, i: usize) -> Rc<Elt> {
    match &a.args[i] {
        Value::Elt(e) => e.clone(),
        _ => unreachable!("a polynomial argument"),
    }
}

/// Argument `i`, a univariate polynomial ring (the ring of an ideal of
/// one), or a quotient of one.
fn ring_arg(a: &CallArgs, i: usize) -> (Rc<Struct>, Rc<Ring>) {
    match &a.args[i] {
        Value::Struct(s) => match &s.kind {
            StructKind::Ring(r) => (s.clone(), r.clone()),
            StructKind::UPolIdeal(g) => (g.parent.clone(), g.ring_rc()),
            _ => unreachable!("a polynomial ring argument"),
        },
        _ => unreachable!("a polynomial ring argument"),
    }
}

/// The coefficient ring of the ring of `f`.
fn base_of(f: &Elt) -> Value {
    f.ring().base().expect("a polynomial").clone()
}

/// The FLINT context of the coefficients of `f`.
fn bctx(f: &Elt) -> Rc<Ctx> {
    f.x.ctx().base().expect("a polynomial").clone()
}

fn len(f: &Elt) -> usize {
    f.x.poly_len()
}

/// A polynomial in the ring of `f`.
fn like(f: &Elt, x: Elem) -> Value {
    make_elt(&f.parent, x)
}

/// A coefficient of `f` as a value of the coefficient ring.
fn cval(it: &Interp, f: &Elt, c: Elem) -> Value {
    it.elem_to_value(&base_of(f), c)
}

fn poly_seq(f: &Elt, xs: Vec<Elem>) -> Value {
    Value::seq(Some(f.parent_value()), xs.into_iter().map(|x| like(f, x)).collect())
}

fn coeff_seq(it: &Interp, f: &Elt, cs: Vec<Elem>) -> Value {
    let b = base_of(f);
    Value::seq(Some(b.clone()), cs.into_iter().map(|c| it.elem_to_value(&b, c)).collect())
}

fn nonzero(f: &Elt) -> RResult<()> {
    if len(f) == 0 { Err(arg_not(1, "non-zero")) } else { Ok(()) }
}

fn is_field(v: &Value) -> bool {
    ring_props(v).is_some_and(|p| p.field)
}

fn is_integers(f: &Elt) -> bool {
    matches!(bctx(f).kind(), CtxKind::Integers)
}

/// Two polynomials in one ring (the ring of the first if the second
/// coerces into it).
fn pair_of(it: &mut Interp, u: &Value, v: &Value) -> RResult<(Rc<Elt>, Elem)> {
    if let (Value::Elt(f), Value::Elt(g)) = (u, v) {
        if f.ring().id == g.ring().id {
            return Ok((f.clone(), g.x.clone()));
        }
    }
    let (pu, pv) = (it.parent_of(u)?, it.parent_of(v)?);
    if let Some(Value::Struct(st)) = it.common_ring(&pu, &pv)? {
        let x = it.to_ring_elem(&st, u, false)?;
        let y = it.to_ring_elem(&st, v, false)?;
        if let (Some(x), Some(y)) = (x, y) {
            return Ok((Rc::new(Elt { parent: st, x }), y));
        }
    }
    Err(RuntimeError::runtime(format!("Bad argument types\nArgument types given: {}, {}", it.type_name_ext(u), it.type_name_ext(v))))
}

/// The two polynomial arguments in one ring.
fn pair(it: &mut Interp, a: &CallArgs) -> RResult<(Rc<Elt>, Elem)> {
    pair_of(it, &a.args[0], &a.args[1])
}

/// A unit (constant) polynomial?
fn is_unit_poly(f: &Elem) -> bool {
    f.poly_len() == 1 && f.poly_coeff(0).is_invertible() == Truth::True
}

/// Sort values of one ring in its order.
fn sort_by_ring_order<T>(it: &mut Interp, v: &mut [(Value, T)]) {
    v.sort_by(|a, b| it.compare_ord(&a.0, &b.0).ok().flatten().unwrap_or(Ordering::Equal));
}

/// Errors of Magma's package intrinsics, reported without a position.
fn package_error(msg: &str) -> RuntimeError {
    ErrorInfo { style: ErrStyle::Bare, ..ErrorInfo::runtime(msg) }.into()
}

fn not_available() -> RuntimeError {
    RuntimeError::runtime("Algorithm is not available for this kind of coefficient ring")
}

// ----- registration ----------------------------------------------------------------------

pub fn register(it: &mut Interp) {
    // Creation.
    it.def("Polynomial", "Q::[RngElt] -> RngUPolElt", "The polynomial over the universe of Q with coefficients Q (constant term first).", polynomial_seq);
    it.def("Polynomial", "R::Rng, Q::[RngElt] -> RngUPolElt", "The polynomial over R with coefficients Q coerced into R.", polynomial_over);
    it.def("Polynomial", "R::Rng, f::RngUPolElt -> RngUPolElt", "The polynomial f with its coefficients coerced into R.", polynomial_over);
    it.def("Identity", "P::RngUPol -> RngUPolElt", "The identity of P.", identity);
    it.def(".", "P::RngUPol, i::RngIntElt -> RngUPolElt", "The indeterminate of P (i = 1).", indeterminate);
    it.def("Name", "P::RngUPol, i::RngIntElt -> RngUPolElt", "The indeterminate of P (i = 1).", indeterminate);
    it.def("AssignNames", "~P::RngUPol, S::[MonStgElt]", "Name the indeterminate of P (for printing).", assign_names);
    it.def(".", "Q::RngUPolRes, i::RngIntElt -> RngUPolResElt", "The image of the indeterminate in Q (i = 1).", indeterminate);
    it.def("Name", "Q::RngUPolRes, i::RngIntElt -> RngUPolResElt", "The image of the indeterminate in Q (i = 1).", indeterminate);
    it.def("AssignNames", "~Q::RngUPolRes, S::[MonStgElt]", "Name the indeterminate of Q (for printing).", assign_names);
    it.def("ChangeRing", "P::RngUPol, S::Rng -> RngUPol, Map", "The polynomial ring over S, with the map from P coercing coefficients.", change_ring);
    it.def("ChangeRing", "P::RngUPol, S::Rng, f::Map -> RngUPol, Map", "The polynomial ring over S, with the map from P applying f to the coefficients.", change_ring);

    // Predicates.
    it.def("IsMonic", "f::RngUPolElt -> BoolElt", "Whether the leading coefficient of f is 1.", is_monic);
    it.def("IsRegular", "f::RngUPolElt -> BoolElt", "Whether f is not a zero divisor.", is_regular);

    // Coefficients and terms.
    for name in ["Coefficients", "ElementToSequence", "Eltseq"] {
        it.def(name, "f::RngUPolElt -> [RngElt]", "The coefficients of f, constant term first.", coefficients);
    }
    it.def("Coefficient", "f::RngUPolElt, i::RngIntElt -> RngElt", "The coefficient of x^i in f.", coefficient);
    it.def("MonomialCoefficient", "f::RngUPolElt, m::RngUPolElt -> RngElt", "The coefficient of the monomial m in f.", monomial_coefficient);
    it.def("LeadingCoefficient", "f::RngUPolElt -> RngElt", "The coefficient of the highest power of x in f.", leading_coefficient);
    it.def("TrailingCoefficient", "f::RngUPolElt -> RngElt", "The coefficient of the lowest power of x in f.", trailing_coefficient);
    it.def("ConstantCoefficient", "f::RngUPolElt -> RngElt", "The constant term of f.", constant_coefficient);
    it.def("Terms", "f::RngUPolElt -> [RngUPolElt]", "The non-zero terms of f in ascending order.", terms);
    it.def("LeadingTerm", "f::RngUPolElt -> RngUPolElt", "The term of f of highest degree.", leading_term);
    it.def("TrailingTerm", "f::RngUPolElt -> RngUPolElt", "The term of f of lowest degree.", trailing_term);
    it.def("Monomials", "f::RngUPolElt -> [RngUPolElt]", "The powers of x up to the degree of f.", monomials);
    it.def("Support", "f::RngUPolElt -> [RngIntElt], [RngElt]", "The exponents of the non-zero terms of f, and their coefficients.", support);
    it.def("Reductum", "f::RngUPolElt -> RngUPolElt", "f without its leading term.", reductum);
    it.def("Round", "f::RngUPolElt -> RngUPolElt", "The integer polynomial with the coefficients of f rounded.", round);
    it.def("Valuation", "f::RngUPolElt -> RngIntElt", "The exponent of the largest power of x dividing f.", valuation);
    it.def("Degree", "f::RngUPolElt -> RngIntElt", "The degree of f (-1 for zero).", degree);

    // Roots.
    it.def_params("Roots", "f::RngUPolElt -> [Tup]", &[("Max", Value::Undef)], "The roots of f in its coefficient ring with their multiplicities.", roots);
    it.def_params("Roots", "f::RngUPolElt, S::Rng -> [Tup]", &[("Max", Value::Undef)], "The roots of f in S with their multiplicities.", roots_in);
    it.def("HasRoot", "f::RngUPolElt -> BoolElt, RngElt", "Whether f has a root in its coefficient ring, and a root.", has_root);
    it.def("HasRoot", "f::RngUPolElt, S::Rng -> BoolElt, RngElt", "Whether f has a root in S, and a root.", has_root_in);
    let small = [("Bits", Value::Bool(false)), ("Beta", Value::Undef), ("Exponent", Value::Undef), ("Finalshifts", Value::Undef), ("Direct", Value::Bool(false))];
    let doc = "The integers x0 with |x0| <= X and p(x0) = 0 modulo a divisor of N of at least N^Beta, by Coppersmith's method.";
    it.def_params("SmallRoots", "p::RngUPolElt, N::RngIntElt, X::RngIntElt -> [RngIntElt]", &small, doc, small_roots_fn);

    // Derivatives, evaluation and interpolation.
    it.def("Derivative", "f::RngUPolElt -> RngUPolElt", "The derivative of f.", derivative);
    it.def("Derivative", "f::RngUPolElt, n::RngIntElt -> RngUPolElt", "The n-th derivative of f.", derivative);
    it.def("Integral", "f::RngUPolElt -> RngUPolElt", "The integral of f with constant term 0.", integral);
    it.def("Evaluate", "f::RngUPolElt, r::RngElt -> RngElt", "The value of f at r.", evaluate);
    it.def("Interpolation", "I::[RngElt], V::[RngElt] -> RngUPolElt", "The polynomial of least degree taking the values V at the points I.", interpolation);

    // Decomposition.
    let doc = "The complete decompositions [f1, ..., fr] of f over a field, f = fr(...(f1)).";
    it.def_params("Decomposition", "f::RngUPolElt -> [[RngUPolElt]]", &[("All", Value::Bool(true))], doc, decomposition_fn);

    // Quotient and remainder.
    it.def("Quotrem", "f::RngUPolElt, g::RngUPolElt -> RngUPolElt, RngUPolElt", "The quotient and remainder of f by g.", quotrem_fn);
    it.def("IsDivisibleBy", "f::RngUPolElt, g::RngUPolElt -> BoolElt, RngUPolElt", "Whether g divides f, and the quotient.", is_divisible_by);
    it.def("ExactQuotient", "f::RngUPolElt, g::RngUPolElt -> RngUPolElt", "f / g for g dividing f.", exact_quotient);
    it.def("Valuation", "f::RngUPolElt, g::RngUPolElt -> RngIntElt", "The exponent of the largest power of g dividing f.", valuation_by);
    it.def("PseudoRemainder", "f::RngUPolElt, g::RngUPolElt -> RngUPolElt", "The pseudo-remainder of f by g.", pseudo_remainder);
    it.def("EuclideanNorm", "f::RngUPolElt -> RngIntElt", "The degree of f plus one (0 for zero).", euclidean_norm);

    // Modular arithmetic.
    it.def("Modexp", "f::RngUPolElt, n::RngIntElt, g::RngUPolElt -> RngUPolElt", "f^n mod g.", modexp);
    for name in ["ChineseRemainderTheorem", "CRT"] {
        it.def(name, "X::[RngUPolElt], M::[RngUPolElt] -> RngUPolElt", "The polynomial congruent to X[i] modulo M[i] for each i.", crt);
    }

    // Other operations.
    it.def("ReciprocalPolynomial", "f::RngUPolElt -> RngUPolElt", "The coefficients of f reversed.", reciprocal_polynomial);
    it.def("PowerPolynomial", "f::RngUPolElt, n::RngIntElt -> RngUPolElt", "The polynomial whose roots are the n-th powers of those of f.", power_polynomial);

    // Greatest common divisors and content.
    for name in ["GreatestCommonDivisor", "Gcd", "GCD"] {
        it.def(name, "f::RngUPolElt, g::RngUPolElt -> RngUPolElt", "The normalized greatest common divisor of f and g.", gcd);
    }
    for name in ["ExtendedGreatestCommonDivisor", "Xgcd", "XGCD"] {
        it.def(name, "f::RngUPolElt, g::RngUPolElt -> RngUPolElt, RngUPolElt, RngUPolElt", "The monic gcd d of f and g over a field, with a and b such that d = a f + b g.", xgcd);
    }
    for name in ["LeastCommonMultiple", "Lcm", "LCM"] {
        it.def(name, "f::RngUPolElt, g::RngUPolElt -> RngUPolElt", "The normalized least common multiple of f and g.", lcm);
    }
    for name in ["Normalize", "Normalise"] {
        it.def(name, "f::RngUPolElt -> RngUPolElt", "The normalized associate of f.", normalize);
    }
    it.def("Content", "f::RngUPolElt -> RngElt", "The gcd of the coefficients of f.", content);
    it.def("PrimitivePart", "f::RngUPolElt -> RngUPolElt", "f divided by its content.", primitive_part);
    for name in ["ContentAndPrimitivePart", "Contpp"] {
        it.def(name, "f::RngUPolElt -> RngElt, RngUPolElt", "The content and the primitive part of f.", content_and_primitive_part);
    }

    // Polynomials over the integers.
    it.def("Sign", "f::RngUPolElt -> RngIntElt", "The sign of the leading coefficient of f.", sign);
    for name in ["AbsoluteValue", "Abs"] {
        it.def(name, "f::RngUPolElt -> RngUPolElt", "f or -f, whichever has a non-negative leading coefficient.", abs);
    }
    it.def("MaxNorm", "f::RngUPolElt -> RngIntElt", "The largest absolute value of a coefficient of f.", max_norm);
    it.def("SumNorm", "f::RngUPolElt -> RngIntElt", "The sum of the absolute values of the coefficients of f.", sum_norm);
    it.def("DedekindTest", "f::RngUPolElt, p::RngIntElt -> BoolElt", "Whether the equation order of the monic f is maximal at the prime p.", dedekind_test);

    // Polynomials over finite fields.
    it.def("PrimePolynomials", "R::RngUPol, d::RngIntElt -> [RngUPolElt]", "The monic irreducible polynomials of degree d over the finite field of R.", prime_polynomials);
    it.def("PrimePolynomials", "R::RngUPol, d::RngIntElt, n::RngIntElt -> [RngUPolElt]", "The first n monic irreducible polynomials of degree d (and more) over the finite field of R.", prime_polynomials);
    it.def("RandomPrimePolynomial", "R::RngUPol, d::RngIntElt -> RngUPolElt", "A random monic irreducible polynomial of degree d over the finite field of R.", random_prime_polynomial);
    for t in ["RngIntElt", "FldFin", "RngUPol"] {
        it.def("NumberOfPrimePolynomials", &format!("q::{t}, d::RngIntElt -> RngIntElt"), "The number of monic irreducible polynomials of degree d over the finite field of size q.", number_of_prime_polynomials);
    }
    it.def("JacobiSymbol", "a::RngUPolElt, b::RngUPolElt -> RngIntElt", "The Jacobi symbol (a/b) of polynomials over a finite field of odd characteristic.", jacobi_symbol);

    // Factorization.
    for name in ["Factorization", "Factorisation"] {
        let al = [("Al", Value::str("Default"))];
        it.def_params(name, "f::RngUPolElt -> [Tup], RngElt", &al, "The factorization of f into normalized irreducibles, and the unit.", factorization);
    }
    it.def("IsIrreducible", "f::RngUPolElt -> BoolElt", "Whether f is irreducible.", is_irreducible);
    it.def("IsPrime", "f::RngUPolElt -> BoolElt", "Whether f is irreducible (prime).", is_irreducible);
    it.def("SquarefreeFactorization", "f::RngUPolElt -> [Tup]", "The squarefree factorization of f.", squarefree_factorization);
    let deg = [("Degree", Value::int(0))];
    it.def_params("DistinctDegreeFactorization", "f::RngUPolElt -> [Tup]", &deg, "The products of the irreducible factors of each degree of the squarefree f.", distinct_degree_factorization);
    it.def("EqualDegreeFactorization", "f::RngUPolElt, d::RngIntElt, g::RngUPolElt -> [RngUPolElt]", "The irreducible factors of f, a product of irreducibles of degree d (g = x^q mod f).", equal_degree_factorization);
    it.def("IsSeparable", "f::RngUPolElt -> BoolElt", "Whether f has no repeated roots.", is_separable);
    it.def("HasPolynomialFactorization", "R::Rng -> BoolElt", "Whether polynomials over R can be factored.", has_polynomial_factorization);
    for name in ["FactorisationToPolynomial", "Facpol"] {
        it.def(name, "Q::[Tup] -> RngElt", "The product of the factorization sequence Q of a polynomial.", facpol);
    }

    // Special families.
    for name in ["ChebyshevFirst", "ChebyshevT"] {
        it.def(name, "n::RngIntElt -> RngUPolElt", "The Chebyshev polynomial of the first kind T_n.", chebyshev_t);
    }
    for name in ["ChebyshevSecond", "ChebyshevU"] {
        it.def(name, "n::RngIntElt -> RngUPolElt", "The Chebyshev polynomial of the second kind of degree n - 1.", chebyshev_u);
    }
    it.def("LegendrePolynomial", "n::RngIntElt -> RngUPolElt", "The Legendre polynomial P_n.", legendre_polynomial);
    it.def("LaguerrePolynomial", "n::RngIntElt -> RngUPolElt", "The Laguerre polynomial L_n.", laguerre_polynomial);
    it.def("LaguerrePolynomial", "n::RngIntElt, m::RngElt -> RngUPolElt", "The generalized Laguerre polynomial L_n^m.", laguerre_polynomial);
    it.def("HermitePolynomial", "n::RngIntElt -> RngUPolElt", "The Hermite polynomial H_n.", hermite_polynomial);
    it.def("GegenbauerPolynomial", "n::RngIntElt, m::RngElt -> RngUPolElt", "The Gegenbauer polynomial C_n^m.", gegenbauer_polynomial);
    it.def("DicksonFirst", "n::RngIntElt, a::RngElt -> RngUPolElt", "The Dickson polynomial of the first kind D_n(x, a).", dickson_first);
    it.def("DicksonSecond", "n::RngIntElt, a::RngElt -> RngUPolElt", "The Dickson polynomial of the second kind E_n(x, a).", dickson_second);
    it.def("BernoulliPolynomial", "n::RngIntElt -> RngUPolElt", "The n-th Bernoulli polynomial.", bernoulli_polynomial);
    it.def("SwinnertonDyerPolynomial", "n::RngIntElt -> RngUPolElt", "The minimal polynomial of the sum of the square roots of the first n primes.", swinnerton_dyer_polynomial);

    // Ideals and quotient rings.
    it.def("Modulus", "Q::RngUPolRes -> RngUPolElt", "The polynomial f of the quotient Q = P/(f).", modulus);
    it.def("PreimageRing", "Q::RngUPolRes -> RngUPol", "The polynomial ring P of the quotient Q = P/(f).", preimage_ring);
    it.def("IsUnit", "x::RngUPolResElt -> BoolElt", "Whether x is a unit.", res_is_unit);
    it.def("IsZero", "x::RngUPolResElt -> BoolElt", "Whether x is zero.", res_is_zero);
    it.def("IsOne", "x::RngUPolResElt -> BoolElt", "Whether x is one.", res_is_one);
    it.def("IsMinusOne", "x::RngUPolResElt -> BoolElt", "Whether x is minus one.", res_is_minus_one);
    for name in ["BaseRing", "CoefficientRing"] {
        for t in ["I::RngUPol", "Q::RngUPolRes", "f::RngUPolResElt"] {
            it.def(name, &format!("{t} -> Rng"), "The coefficient ring.", coefficient_ring);
        }
    }
    it.def("Generators", "I::RngUPol -> SetEnum", "The generator of the ideal I, as a set.", ideal_generators);
    it.def("IsPrime", "I::RngUPol -> BoolElt", "Whether the ideal I is prime.", ideal_is_prime);
    it.def("IsMaximal", "I::RngUPol -> BoolElt", "Whether the ideal I is maximal.", ideal_is_maximal);
    it.def("IsPrincipal", "I::RngUPol -> BoolElt", "Whether the ideal I is principal (always).", ideal_is_principal);
    for name in ["Coefficients", "ElementToSequence", "Eltseq"] {
        it.def(name, "f::RngUPolResElt -> [RngElt]", "The coefficients of the reduced representative of f, constant term first.", coefficients);
    }
    it.def("Coefficient", "f::RngUPolResElt, i::RngIntElt -> RngElt", "The coefficient of x^i in the reduced representative of f.", coefficient);
    it.def("LeadingCoefficient", "f::RngUPolResElt -> RngElt", "The leading coefficient of the reduced representative of f.", leading_coefficient);
    it.def("TrailingCoefficient", "f::RngUPolResElt -> RngElt", "The trailing coefficient of the reduced representative of f.", trailing_coefficient);
    it.def("ConstantCoefficient", "f::RngUPolResElt -> RngElt", "The constant term of the reduced representative of f.", constant_coefficient);
    it.def("Terms", "f::RngUPolResElt -> [RngUPolResElt]", "The non-zero terms of the reduced representative of f.", terms);
    it.def("LeadingTerm", "f::RngUPolResElt -> RngUPolResElt", "The leading term of the reduced representative of f.", leading_term);
    it.def("TrailingTerm", "f::RngUPolResElt -> RngUPolResElt", "The trailing term of the reduced representative of f.", trailing_term);
    it.def("Degree", "f::RngUPolResElt -> RngIntElt", "The degree of the reduced representative of f.", degree);

    // Resultants, discriminants and Hensel lifting.
    it.def("Resultant", "f::RngUPolElt, g::RngUPolElt -> RngElt", "The resultant of f and g.", resultant);
    it.def("Discriminant", "f::RngUPolElt -> RngElt", "The discriminant of f.", discriminant);
    it.def("HenselLift", "f::RngUPolElt, s::[RngUPolElt], P::RngUPol -> [RngUPolElt]", "Lift the factors s of f modulo p to factors modulo p^k in P over Z/p^kZ.", hensel_lift);
}
