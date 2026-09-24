# sage.doctest: needs sage.rings.function_field sage.rings.padics
r"""
Frobenius and exact primitives at general Coleman endpoints

The integral-basis coordinates of a ramified or infinite point need not
determine an affine ``y`` coordinate.  Their minimal polynomials over
``QQ(x)`` do, however, specialize at the Frobenius image of ``x``.  The root
congruent to the old coordinate raised to the ``p``-th power is the desired
lift.

Primitive evaluations are expressed in the finite or infinite integral basis
as appropriate.  They return an absolute precision bound together with the
value.  Poles at the *exact* branch point are reported explicitly; the
general integration routine moves such endpoints to a nearby boundary point.

The algorithm follows [BT2017]_, using the Frobenius and cohomological
reduction framework of [T2014a]_ and [T2014b]_.
Tangential endpoint values use the normalized constant-term construction of
[BB2012]_.

REFERENCES:

.. [BT2017] Jennifer S. Balakrishnan and Jan Tuitman, *Explicit Coleman
   integration for curves*, arXiv:1710.01673.
.. [BB2012] Jennifer S. Balakrishnan and Amnon Besser, *Coleman--Gross
   height pairings and the p-adic sigma function*, arXiv:1201.6016.
.. [T2014a] Jan Tuitman, *Counting points on curves using a map to* `\mathbf
   P^1`, arXiv:1402.6758.
.. [T2014b] Jan Tuitman, *Counting points on curves using a map to* `\mathbf
   P^1`, *II*, arXiv:1412.7217.

EXAMPLES::

    sage: from sage.schemes.curves.coleman.data import coleman_data
    sage: from sage.schemes.curves.coleman.general_integration import (
    ....:     coleman_integrals_on_basis, frobenius_point)
    sage: from sage.schemes.curves.coleman.points import (point_from_basis_coordinates,
    ....:     point_from_good_affine_coordinates)
    sage: R.<x> = QQ[]; S.<y> = R[]
    sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 2, genus=1)
    sage: branch = point_from_basis_coordinates(1, [1, 0], False, data)
    sage: infinity_point = point_from_basis_coordinates(0, [1, 0], True, data)
    sage: frobenius_point(branch, data)
    Traceback (most recent call last):
    ...
    PrecisionError: the selected root is not known to the requested precision
    sage: frobenius_point(infinity_point, data).infinity
    True
    sage: good = point_from_good_affine_coordinates(0, 3, data)
    sage: I1, n1 = coleman_integrals_on_basis(branch, good, data)
    sage: I2, n2 = coleman_integrals_on_basis(infinity_point, good, data)
    sage: all((a-b).valuation() >= min(n1, n2) for a, b in zip(I1, I2))
    True

The bad-point Frobenius construction also works outside the hyperelliptic
case::

    sage: Q = y^3 + (-x^2-1)*y^2 - x^3*y + x^3 + 2*x^2 + x
    sage: data3 = coleman_data(Q, 7, 4, genus=3)
    sage: branch3 = point_from_basis_coordinates(0, [1, 0, 0], False, data3)
    sage: frobenius_point(branch3, data3).b[1].valuation() >= data3.N
    True
    sage: good3 = point_from_good_affine_coordinates(
    ....:     5, -32582624253112412, data3)
    sage: values3, precision3 = coleman_integrals_on_basis(
    ....:     good3, branch3, data3, e=15)
    sage: expected3 = vector(QQ, [197200*7, -2355398, 2318140,
    ....:     -114216*7, QQ(6600662)/7, QQ(14277898)/7])
    sage: precision3 == 1 and all((a-b).valuation() >= precision3
    ....:     for a, b in zip(values3, expected3))
    True

"""

from dataclasses import dataclass
from functools import lru_cache

from sage.matrix.constructor import identity_matrix, matrix
from sage.modules.free_module_element import vector

from sage.rings.finite_rings.integer_mod_ring import IntegerModRing
from sage.rings.function_field.constructor import FunctionField
from sage.rings.infinity import infinity
from sage.rings.integer_ring import ZZ
from sage.rings.laurent_series_ring import LaurentSeriesRing
from sage.rings.padics.factory import Qp
from sage.rings.padics.precision_error import PrecisionError
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ

from .cohomology import (
    _evaluate_matrix,
    _evaluate_rational_function,
    _substitute_inverse,
)
from .integration import (
    _common_point_field,
    _root_certificate,
    _series_terms,
    _truncate_vector,
)
from .points import (
    ColemanIntegrationPoint,
    ColemanTangentialPoint,
    affine_coordinates,
    are_in_same_residue_disk,
    is_bad_residue_disk_center,
    is_in_bad_residue_disk,
    point_from_good_affine_coordinates,
)


def _function_field_scalar(value, rational_function_field):
    """Coerce a ``QQ(x)`` element into a rational function field.

    TESTS::

        sage: from sage.schemes.curves.coleman.general_integration import _function_field_scalar
        sage: R.<x> = QQ[]; K.<x> = FunctionField(QQ)
        sage: _function_field_scalar((R.gen() + 1)/(R.gen() + 2), K)
        (x + 1)/(x + 2)
    """
    if value == 0:
        return rational_function_field.zero()
    return (rational_function_field(value.numerator())
            / rational_function_field(value.denominator()))


@lru_cache(maxsize=32)
def _basis_minimal_polynomials(Q, basis_entries):
    """Return minimal polynomials of integral-basis functions over ``QQ(x)``.

    TESTS::

        sage: from sage.schemes.curves.coleman.general_integration import _basis_minimal_polynomials
        sage: R.<x> = QQ[]; S.<y> = R[]; K.<x> = FunctionField(QQ)
        sage: polynomials = _basis_minimal_polynomials(
        ....:     y^2 - R.gen(), tuple(identity_matrix(K, 2).list()))
        sage: tuple(f.degree() for f in polynomials)
        (1, 2)
    """
    degree = Q.degree()
    K = FunctionField(QQ, Q.base_ring().variable_name())
    Ky = PolynomialRing(K, 'Y')
    defining = Ky([K(coefficient) for coefficient in Q.list()])
    curve_field = K.extension(defining, 'a')
    y = curve_field.gen()
    powers = [curve_field.one()]
    for _ in range(1, degree):
        powers.append(powers[-1] * y)
    result = []
    for i in range(degree):
        basis_element = sum(
            (_function_field_scalar(basis_entries[i * degree + j], K)
             * powers[j] for j in range(degree)), curve_field.zero()
        )
        result.append(basis_element.minimal_polynomial())
    return tuple(result)


def _at_infinity(function, t):
    """Evaluate a rational function at ``x=1/t``, including ``t=0``.

    TESTS::

        sage: from sage.schemes.curves.coleman.general_integration import _at_infinity
        sage: K.<x> = FunctionField(QQ)
        sage: _at_infinity((x + 1)/x, QQ(0)), _at_infinity((x + 1)/x, QQ(2))
        (1, 3)
    """
    # Substitution in QQ(t) cancels common powers before specialization at 0.
    t_ring = PolynomialRing(QQ, 't')
    rational_t = t_ring.fraction_field()
    substituted = _substitute_inverse(function, rational_t)
    return _evaluate_rational_function(substituted, t)


def _specialized_minimal_polynomial(poly, x_value, infinity):
    """Specialize a minimal polynomial's coefficients in the point field.

    TESTS::

        sage: from sage.schemes.curves.coleman.general_integration import _specialized_minimal_polynomial
        sage: K.<x> = FunctionField(QQ); R.<B> = K[]; F = Qp(5, 6)
        sage: polynomial = _specialized_minimal_polynomial(B^2 - x, F(1), False)
        sage: polynomial(F(1)).valuation()
        6
    """
    field = x_value.parent()
    ring = PolynomialRing(field, 'B')
    if infinity:
        coefficients = [field(_at_infinity(coefficient, x_value))
                        for coefficient in poly.list()]
    else:
        coefficients = [field(_evaluate_rational_function(coefficient, x_value))
                        for coefficient in poly.list()]
    return ring(coefficients)


def _selected_root(polynomial, target, needed_precision):
    """Choose the root in the target residue disk and certify its precision.

    Candidates come from Sage's precision-tracking root finder.  The
    selected candidate is certified by
    :func:`~sage.schemes.curves.coleman.integration._root_certificate`
    instead of trusting the precision reported by the root finder, and it
    is returned with exactly its certified precision.

    TESTS::

        sage: from sage.schemes.curves.coleman.general_integration import _selected_root
        sage: K = Qp(5, 6); R.<z> = K[]
        sage: root = _selected_root(z^2 - 1, K(1), 5)
        sage: root == K(1)
        True

    A small residual does not certify an unresolved multiple root::

        sage: _selected_root(z^2 - 5^4, K(0, 5), 5)
        Traceback (most recent call last):
        ...
        ArithmeticError: Frobenius root is not uniquely determined in this disk

    Nor is a root certified to full precision when another root agrees with
    it modulo `5^2`; only four digits survive::

        sage: _selected_root((z - 1)*(z - 26), K(1), 5)
        Traceback (most recent call last):
        ...
        PrecisionError: the selected root is not known to the requested precision
        sage: _selected_root((z - 1)*(z - 26), K(1), 4)
        1 + O(5^4)
    """
    e = ZZ(target.parent()(target.parent().prime()).valuation())
    required = ZZ(needed_precision) * e
    if target.precision_absolute() < required:
        raise PrecisionError(
            'the target coordinate is not known to the requested precision'
        )
    roots = [root for root, _ in polynomial.roots(algorithm='sage')]
    if not roots:
        raise PrecisionError(
            'the specialized integral-basis root cannot be separated at '
            'the available precision'
        )
    distances = [(root - target).valuation() for root in roots]
    best = max(distances)
    if best <= 0 or sum(distance == best for distance in distances) != 1:
        raise ArithmeticError('Frobenius root is not uniquely determined in this disk')
    chosen = roots[distances.index(best)]
    center, digits, _ = _root_certificate(polynomial, chosen)
    # A non-unique certificate bounds every root in the residue disk, which
    # includes the Frobenius image, so it is sufficient here as well.
    if digits is None or digits < required:
        raise PrecisionError(
            'the selected root is not known to the requested precision'
        )
    return center if digits == infinity else center.add_bigoh(digits)


def frobenius_point(P, data):
    r"""Return Frobenius on a finite good, finite bad, or infinite point.

    For a bad point the integral-basis coordinates are lifted independently
    through their minimal polynomials.  The selected roots are required to be
    unique in the residue disk of ``b_i(P)^p``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.general_integration import frobenius_point
        sage: from sage.schemes.curves.coleman.points import point_from_basis_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 2, genus=1)
        sage: P = point_from_basis_coordinates(1, [1, 0], False, data)
        sage: frobenius_point(P, data)
        Traceback (most recent call last):
        ...
        PrecisionError: the selected root is not known to the requested precision
    """
    if not is_in_bad_residue_disk(P, data):
        from .integration import frobenius_point as good_frobenius
        return good_frobenius(P, data)

    basis_matrix = data.Winf if P.infinity else data.W0
    polynomials = _basis_minimal_polynomials(data.Q, tuple(basis_matrix.list()))
    x_image = P.x**data.p
    coordinates = []
    for polynomial, basis_value in zip(polynomials, P.b):
        specialized = _specialized_minimal_polynomial(
            polynomial, x_image, P.infinity
        )
        coordinates.append(_selected_root(
            specialized, basis_value**data.p, data.N
        ))
    return ColemanIntegrationPoint(
        x=x_image, b=tuple(coordinates), infinity=P.infinity
    )


def _value_and_precision(terms, field, N, source_precision=None):
    """Sum terms using an absolute coefficient-precision bound.

    TESTS::

        sage: from sage.schemes.curves.coleman.general_integration import _value_and_precision
        sage: K = Qp(5, 6)
        sage: _value_and_precision([(QQ(1), K(2)), (QQ(1)/5, K(5))], K, 6)
        (3 + O(5^6), 6)
    """
    total = field.zero()
    ramification = ZZ(field(field.prime()).valuation())
    precision = ZZ(N) * ramification
    source_precision = ZZ(N if source_precision is None else source_precision)
    p = field.prime()
    for coefficient, multiplier in terms:
        term = field(coefficient) * multiplier
        total += term
        if coefficient and multiplier:
            precision = min(precision,
                            source_precision * ramification
                            + min(ZZ.zero(),
                                  ZZ(QQ(coefficient).valuation(p))) * ramification
                            + ZZ(multiplier.valuation()))
        precision = min(precision, term.precision_absolute())
    precision = min(precision, total.precision_absolute())
    if precision <= 0:
        raise PrecisionError(
            'primitive evaluation has no reliable p-adic digits; '
            'move the endpoint to a near-boundary point'
        )
    return total, ZZ(precision // ramification)


def _laurent_as_rational(entry, x):
    """Interpret a finite Laurent series as a rational function in ``x``.

    TESTS::

        sage: from sage.schemes.curves.coleman.general_integration import _laurent_as_rational
        sage: L.<z> = LaurentSeriesRing(QQ); K.<x> = FunctionField(QQ)
        sage: _laurent_as_rational(2*z^-1 + 3*z, x)
        (3*x^2 + 2)/x
    """
    field = x.parent()
    return sum((field(coefficient) * x**exponent
                for exponent, coefficient in (_series_terms(entry) or [])),
               field.zero())


def _finite_primitive_functions(f0, data):
    """Write the finite primitive vector over ``QQ(x)`` exactly.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.general_integration import _finite_primitive_functions
        sage: R.<x> = QQ[]; K.<x> = FunctionField(QQ)
        sage: L.<z> = LaurentSeriesRing(R)
        sage: data = SimpleNamespace(W0=identity_matrix(K, 2), r=R.gen() + 1)
        sage: _finite_primitive_functions(vector(L, [0, 0]), data)
        (0, 0)
    """
    field = data.W0.base_ring()
    z = field(data.r) / field(data.r.leading_coefficient())
    return vector(field, [
        sum((field(polynomial) * z**exponent
             for exponent, polynomial in (_series_terms(entry) or [])),
            field.zero())
        for entry in f0
    ])


def _evaluate_vector_in_basis(functions, P, data, *, finite_basis=True):
    """Evaluate rational functions after cancellation at a special point.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.general_integration import _evaluate_vector_in_basis
        sage: from sage.schemes.curves.coleman.points import ColemanIntegrationPoint
        sage: K.<x> = FunctionField(QQ); F = Qp(5, 4)
        sage: data = SimpleNamespace(N=4, W0=identity_matrix(K, 2),
        ....:                        Winf=identity_matrix(K, 2))
        sage: P = ColemanIntegrationPoint(F(1), (F(1), F(2)))
        sage: _evaluate_vector_in_basis(vector(K, [1, x]), P, data)
        (3 + O(5^4), 0)
    """
    field = P.x.parent()
    if not any(functions):
        return field.zero(), ZZ(data.N)
    function_field = data.W0.base_ring()
    if P.infinity:
        if finite_basis:
            functions = functions * (data.W0 * data.Winf.inverse())
        scalars = [_at_infinity(function_field(function), P.x)
                   for function in functions]
    else:
        if not finite_basis:
            functions = functions * (data.Winf * data.W0.inverse())
        scalars = [_evaluate_rational_function(function_field(function), P.x)
                   for function in functions]
    value = sum((field(scalar) * basis_value
                 for scalar, basis_value in zip(scalars, P.b)), field.zero())
    # A basis change with a pole may have cancelled before specialization.
    # Its input-coefficient error cannot be bounded termwise at that point.
    return value, ZZ.zero()


def _basis_values(P, data, *, finite_basis):
    """Return finite or infinite integral-basis values at a noncentral point.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.general_integration import _basis_values
        sage: from sage.schemes.curves.coleman.points import ColemanIntegrationPoint
        sage: K.<x> = FunctionField(QQ); F = Qp(5, 4)
        sage: data = SimpleNamespace(W0=identity_matrix(K, 2),
        ....:                        Winf=identity_matrix(K, 2))
        sage: P = ColemanIntegrationPoint(F(1), (F(1), F(2)))
        sage: _basis_values(P, data, finite_basis=True)
        (1 + O(5^4), 2 + O(5^4))
    """
    field = P.x.parent()
    if finite_basis == (not P.infinity):
        return tuple(P.b)
    transform = (data.W0 * data.Winf.inverse() if finite_basis
                 else data.Winf * data.W0.inverse())
    x_value = 1 / P.x if P.infinity else P.x
    transformed = _evaluate_matrix(transform, x_value, field)
    return tuple(transformed * vector(field, P.b))


def evaluate_finite_primitive(f0, P, data):
    r"""Evaluate ``f0`` at a finite good/bad or infinite point.

    At an exact branch point a genuine pole is undefined.  Cancellation
    within a rational coefficient is performed before specialization.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.general_integration import evaluate_finite_primitive
        sage: from sage.schemes.curves.coleman.points import point_from_basis_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 2, genus=1)
        sage: P = point_from_basis_coordinates(1, [1, 0], False, data)
        sage: zero = vector(data.f0_list[0].base_ring(), [0, 0])
        sage: evaluate_finite_primitive(zero, P, data)
        (0, 2)
    """
    if not is_in_bad_residue_disk(P, data):
        from .integration import evaluate_finite_primitive as good_evaluation
        return good_evaluation(f0, P, data)
    try:
        if P.infinity and not P.x:
            return _evaluate_vector_in_basis(
                _finite_primitive_functions(f0, data), P, data
            )
        x_value = 1 / P.x if P.infinity else P.x
        z_value = _evaluate_rational_function(data.r, x_value) / data.r.leading_coefficient()
        if not z_value:
            return _evaluate_vector_in_basis(
                _finite_primitive_functions(f0, data), P, data
            )
        field = P.x.parent()
        basis_values = _basis_values(P, data, finite_basis=True)
        terms = []
        for index, entry in enumerate(f0):
            for radix_exponent, polynomial in (_series_terms(entry) or []):
                radix_power = z_value**radix_exponent
                for exponent, coefficient in enumerate(polynomial.list()):
                    if coefficient:
                        terms.append((coefficient,
                                      x_value**exponent * radix_power
                                      * basis_values[index]))
        return _value_and_precision(terms, field, data.N, data.Nmax)
    except ZeroDivisionError as error:
        raise ZeroDivisionError('finite primitive has a pole at this endpoint') from error


def _evaluate_finite_primitives(f0_list, P, data):
    r"""Evaluate several finite primitives with shared endpoint arithmetic.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.general_integration import _evaluate_finite_primitives
        sage: from sage.schemes.curves.coleman.points import ColemanIntegrationPoint
        sage: R.<x> = QQ[]; K = Qp(5, 3)
        sage: P = ColemanIntegrationPoint(K(1), (K(1), K(1)))
        sage: _evaluate_finite_primitives([], P, SimpleNamespace(r=R.one()))
        []
    """
    f0_list = tuple(f0_list)
    if (not is_in_bad_residue_disk(P, data)
            or (P.infinity and not P.x)):
        return [evaluate_finite_primitive(f0, P, data) for f0 in f0_list]

    x_value = 1 / P.x if P.infinity else P.x
    z_value = (_evaluate_rational_function(data.r, x_value)
               / data.r.leading_coefficient())
    if not z_value:
        return [evaluate_finite_primitive(f0, P, data) for f0 in f0_list]

    field = P.x.parent()
    basis_values = _basis_values(P, data, finite_basis=True)
    ramification = ZZ(field(field.prime()).valuation())
    x_valuation = x_value.valuation()
    z_valuation = z_value.valuation()
    polynomial_cache = {}
    power_cache = {ZZ.zero(): field.one(), ZZ.one(): z_value}

    def polynomial_value(polynomial):
        try:
            return polynomial_cache[polynomial]
        except KeyError:
            value = polynomial(x_value)
            polynomial_cache[polynomial] = value
            return value

    def z_power(exponent):
        exponent = ZZ(exponent)
        if exponent not in power_cache:
            power_cache[exponent] = z_value**exponent
        return power_cache[exponent]

    output = []
    for f0 in f0_list:
        total = field.zero()
        precision = ZZ(data.N) * ramification
        for index, entry in enumerate(f0):
            terms = list(_series_terms(entry) or [])
            if not terms:
                continue
            current_exponent, polynomial = terms[-1]
            entry_value = polynomial_value(polynomial)
            for radix_exponent, polynomial in reversed(terms[:-1]):
                entry_value = (
                    entry_value * z_power(current_exponent - radix_exponent)
                    + polynomial_value(polynomial)
                )
                current_exponent = radix_exponent
            entry_value *= z_power(current_exponent)
            total += entry_value * basis_values[index]

            basis_valuation = basis_values[index].valuation()
            for radix_exponent, polynomial in terms:
                for exponent, coefficient in enumerate(polynomial.list()):
                    if coefficient:
                        precision = min(
                            precision,
                            ZZ(data.Nmax) * ramification
                            + min(ZZ.zero(), ZZ(QQ(coefficient).valuation(
                                field.prime()))) * ramification
                            + ZZ(exponent) * x_valuation
                            + ZZ(radix_exponent) * z_valuation
                            + basis_valuation,
                        )
        precision = min(precision, total.precision_absolute())
        if precision <= 0:
            raise PrecisionError(
                'primitive evaluation has no reliable p-adic digits; '
                'move the endpoint to a near-boundary point'
            )
        output.append((total, ZZ(precision // ramification)))
    return output


def evaluate_infinite_primitive(finf, P, data):
    r"""Evaluate ``finf`` using the infinite integral basis.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.general_integration import evaluate_infinite_primitive
        sage: from sage.schemes.curves.coleman.points import point_from_basis_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 2, genus=1)
        sage: P = point_from_basis_coordinates(1, [1, 0], False, data)
        sage: zero = vector(data.finf_list[0].base_ring(), [0, 0])
        sage: evaluate_infinite_primitive(zero, P, data)
        (0, 2)
    """
    if not is_in_bad_residue_disk(P, data):
        from .integration import evaluate_infinite_primitive as good_evaluation
        return good_evaluation(finf, P, data)
    try:
        if P.infinity and not P.x:
            if all(exponent <= 0
                   for entry in finf
                   for exponent, _ in (_series_terms(entry) or [])):
                return _value_and_precision(
                    ((coefficient, P.b[i])
                     for i, entry in enumerate(finf)
                     for exponent, coefficient in (_series_terms(entry) or [])
                     if exponent == 0), P.x.parent(), data.N, data.Nmax
                )
            function_field = data.Winf.base_ring()
            x = function_field.gen()
            functions = vector(function_field,
                               [_laurent_as_rational(entry, x)
                                for entry in finf])
            return _evaluate_vector_in_basis(
                functions, P, data, finite_basis=False
            )
        field = P.x.parent()
        x_value = 1 / P.x if P.infinity else P.x
        basis_values = _basis_values(P, data, finite_basis=False)
        return _value_and_precision(
            ((coefficient, x_value**exponent * basis_values[i])
             for i, entry in enumerate(finf)
             for exponent, coefficient in (_series_terms(entry) or [])),
            field, data.N, data.Nmax
        )
    except ZeroDivisionError as error:
        raise ZeroDivisionError('infinite primitive has a pole at this endpoint') from error


def evaluate_terminal_primitive(fend, P, data):
    r"""Evaluate the final polynomial primitive in the finite basis.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.general_integration import evaluate_terminal_primitive
        sage: from sage.schemes.curves.coleman.points import point_from_basis_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 2, genus=1)
        sage: P = point_from_basis_coordinates(1, [1, 0], False, data)
        sage: evaluate_terminal_primitive(vector(R, [0, 0]), P, data)
        (0, 2)
    """
    if not is_in_bad_residue_disk(P, data):
        from .integration import evaluate_terminal_primitive as good_evaluation
        return good_evaluation(fend, P, data)
    try:
        if P.infinity and not P.x:
            function_field = data.W0.base_ring()
            functions = vector(function_field,
                               [function_field(entry) for entry in fend])
            return _evaluate_vector_in_basis(functions, P, data)
        field = P.x.parent()
        x_value = 1 / P.x if P.infinity else P.x
        basis_values = _basis_values(P, data, finite_basis=True)
        return _value_and_precision(
            ((coefficient, x_value**exponent * basis_values[i])
             for i, entry in enumerate(fend)
             for exponent, coefficient in enumerate(entry.list())
             if coefficient), field, data.N, data.Nmax
        )
    except ZeroDivisionError as error:
        raise ZeroDivisionError('terminal primitive has a pole at this endpoint') from error


def is_hyperelliptic(data):
    r"""Return whether the model has the involution `(x,y)\mapsto(x,-y)`.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.general_integration import is_hyperelliptic
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: is_hyperelliptic(SimpleNamespace(Q=y^2-x^3+x))
        True
        sage: is_hyperelliptic(SimpleNamespace(Q=y^3-x^4+x))
        False
    """
    return (data.Q.degree() == 2 and data.Q[1] == 0
            and data.Q[2] == data.Q.base_ring().one())


def _fixed_by_hyperelliptic_involution(P, data):
    """Test whether a branch or odd-degree infinity point is fixed.

    TESTS::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.general_integration import _fixed_by_hyperelliptic_involution
        sage: from sage.schemes.curves.coleman.points import point_from_basis_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 2, genus=1)
        sage: P = point_from_basis_coordinates(1, [1, 0], False, data)
        sage: _fixed_by_hyperelliptic_involution(P, data)
        True
    """
    if (not is_hyperelliptic(data)
            or not is_bad_residue_disk_center(P, data)):
        return False
    from .ramified import local_data
    if local_data(P, data)[0] != 2:
        return False
    if P.infinity:
        return True
    if data.W0 == identity_matrix(data.W0.base_ring(), 2):
        return P.b[1].valuation() >= data.N
    try:
        return affine_coordinates(P, data)[1].valuation() >= data.N
    except (ZeroDivisionError, PrecisionError):
        return False


def _local_parameter_value(P, center, index, field):
    """Return the parameter value relative to a central bad point.

    TESTS::

        sage: from sage.schemes.curves.coleman.general_integration import _local_parameter_value
        sage: from sage.schemes.curves.coleman.points import ColemanIntegrationPoint
        sage: K = Qp(5, 4)
        sage: P = ColemanIntegrationPoint(K(1), (K(1), K(2)))
        sage: Q = ColemanIntegrationPoint(K(1), (K(1), K(7)))
        sage: _local_parameter_value(Q, P, 2, K)
        5 + O(5^4)
    """
    if index:
        return field(P.b[index - 1]) - field(center.b[index - 1])
    return field(P.x) - field(center.x)


def _evaluate_rational_functions_at_series(functions, value):
    r"""Evaluate rational functions using one shared table of series powers.

    Polynomial evaluation by repeated Horner substitution repeats nearly the
    same power-series multiplications for every coefficient of a differential
    basis.  At a finite local parameter, precomputing the required powers of
    ``value`` makes the number of series-by-series products depend on the
    maximum degree, rather than the sum of all degrees.

    TESTS::

        sage: from sage.schemes.curves.coleman.general_integration import _evaluate_rational_functions_at_series
        sage: R.<x> = QQ[]; T.<t> = PowerSeriesRing(QQ, default_prec=8)
        sage: functions = ((x^3 + 2*x + 1)/3, (x^2 - 1)/(x + 2))
        sage: value = t + t^2 + O(t^8)
        sage: fast = _evaluate_rational_functions_at_series(functions, value)
        sage: from sage.schemes.curves.coleman.cohomology import _evaluate_rational_function
        sage: slow = tuple(_evaluate_rational_function(f, value) for f in functions)
        sage: all((a-b).is_zero() for a, b in zip(fast, slow))
        True
    """
    functions = tuple(functions)
    if not functions:
        return ()
    if value.valuation() < 0:
        return tuple(_evaluate_rational_function(f, value) for f in functions)

    parent = value.parent()
    decomposed = []
    polynomial_coefficients = {}
    maximum_degree = 0

    def coefficients(polynomial):
        nonlocal maximum_degree
        if not callable(polynomial):
            return None
        try:
            cached = polynomial_coefficients.get(polynomial)
        except TypeError:
            cached = None
        if cached is not None:
            return cached
        try:
            cached = tuple(polynomial.list())
        except AttributeError:
            return None
        maximum_degree = max(maximum_degree, len(cached) - 1)
        try:
            polynomial_coefficients[polynomial] = cached
        except TypeError:
            pass
        return cached

    for function in functions:
        if not function:
            decomposed.append(None)
            continue
        try:
            numerator = function.numerator()
            denominator = function.denominator()
        except AttributeError:
            numerator = function
            denominator = 1
        numerator_coefficients = coefficients(numerator)
        denominator_coefficients = coefficients(denominator)
        if callable(numerator) and numerator_coefficients is None:
            return tuple(_evaluate_rational_function(f, value)
                         for f in functions)
        if callable(denominator) and denominator_coefficients is None:
            return tuple(_evaluate_rational_function(f, value)
                         for f in functions)
        decomposed.append((numerator, numerator_coefficients,
                           denominator, denominator_coefficients))

    powers = [parent.one()]
    for _ in range(maximum_degree):
        powers.append(powers[-1] * value)

    evaluated_polynomials = {}

    def evaluate(polynomial, coefficient_list):
        if coefficient_list is None:
            return parent(polynomial)
        try:
            cached = evaluated_polynomials.get(polynomial)
        except TypeError:
            cached = None
        if cached is not None:
            return cached
        result = sum(
            (parent(coefficient) * powers[exponent]
             for exponent, coefficient in enumerate(coefficient_list)
             if coefficient),
            parent.zero(),
        )
        try:
            evaluated_polynomials[polynomial] = result
        except TypeError:
            pass
        return result

    output = []
    for entry in decomposed:
        if entry is None:
            output.append(parent.zero())
            continue
        numerator, numerator_coefficients, denominator, denominator_coefficients = entry
        output.append(
            evaluate(numerator, numerator_coefficients)
            / evaluate(denominator, denominator_coefficients)
        )
    return tuple(output)


def _local_differentials_in_ring(center, data, basis, ring, coordinate,
                                 stored_basis):
    r"""Expand ``basis`` in a supplied Laurent-series coefficient ring.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.general_integration import _local_differentials_in_ring
        sage: R.<x> = QQ[]; S.<y> = R[]; L.<t> = LaurentSeriesRing(QQ)
        sage: center = SimpleNamespace(infinity=False)
        sage: data = SimpleNamespace(Q=y^2-x, r=x+1)
        sage: forms = _local_differentials_in_ring(
        ....:     center, data, [vector(R, [1, 0])], L, 1+t,
        ....:     vector(L, [1, 1+t]))
        sage: len(forms), forms[0][0]
        (1, 1/2)
    """
    change_entries = []
    if center.infinity:
        x_series = coordinate**(-1)
        change = data.W0 * data.Winf.inverse()
        change_entries = list(change.list())
    else:
        x_series = coordinate
    coefficient_entries = [coefficient for row in basis for coefficient in row]
    evaluated = iter(_evaluate_rational_functions_at_series(
        [data.r] + change_entries + coefficient_entries, x_series
    ))
    r_series = next(evaluated)
    if center.infinity:
        change_values = matrix(
            ring, change.nrows(), change.ncols(),
            [next(evaluated) for _ in change_entries],
        )
        finite_basis = vector(ring, [
            sum((change_values[i, j] * stored_basis[j]
                 for j in range(data.Q.degree())),
                ring.zero()) for i in range(data.Q.degree())
        ])
    else:
        finite_basis = stored_basis
    scale = (ring(data.r.leading_coefficient()) * x_series.derivative()
             / r_series)
    return [
        sum((next(evaluated) * finite_basis[i]
             for i in range(len(row))),
            ring.zero()) * scale for row in basis
    ]


def _modular_local_differentials(center, data, prec, basis, xt, bt):
    r"""Use packed arithmetic modulo ``p^N`` when all inputs are integral.

    A capped-relative p-adic power series stores a separate p-adic object for
    every coefficient.  The local differential computation needs only fixed
    absolute coefficient precision, so arithmetic over ``ZZ/p^N ZZ`` gives
    the same result while using compiled dense polynomial kernels.  ``None``
    signals that the inputs require the general p-adic path.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.general_integration import _modular_local_differentials
        sage: from sage.schemes.curves.coleman.points import ColemanIntegrationPoint
        sage: R.<x> = QQ[]; S.<y> = R[]; K = Qp(5, 4)
        sage: T.<t> = PowerSeriesRing(K, default_prec=5)
        sage: P = ColemanIntegrationPoint(K(1), (K(1), K(1)))
        sage: data = SimpleNamespace(Q=y^2-x, r=x+1)
        sage: forms = _modular_local_differentials(
        ....:     P, data, 5, [vector(R, [1, 0])], 1+t, (T(1), 1+t))
        sage: len(forms), forms[0][0]
        (1, 3 + 2*5 + 2*5^2 + 2*5^3 + O(5^4))
    """
    field = center.x.parent()
    try:
        if field.degree() != 1 or field(field.prime()).valuation() != 1:
            return None
        prime = ZZ(field.prime())
        coefficient_precision = ZZ(field.precision_cap())
    except (AttributeError, TypeError, ValueError):
        return None

    coefficients = [field(coefficient)
                    for series in (xt,) + tuple(bt)
                    for coefficient in series.list()]
    if any(coefficient and coefficient.valuation() < 0
           for coefficient in coefficients):
        return None
    finite_precisions = [
        coefficient.precision_absolute() for coefficient in coefficients
        if coefficient.precision_absolute() != infinity
    ]
    if finite_precisions:
        coefficient_precision = min(
            coefficient_precision, *(ZZ(value) for value in finite_precisions)
        )
    if coefficient_precision <= 0:
        return None

    coefficient_ring = IntegerModRing(prime**coefficient_precision)
    modular_ring = LaurentSeriesRing(
        coefficient_ring, 't', default_prec=prec
    )

    def to_modular(series):
        values = [
            coefficient_ring(ZZ(field(coefficient).lift()))
            for coefficient in series.list()
        ]
        return modular_ring(values).add_bigoh(series.precision_absolute())

    try:
        coordinate = to_modular(xt)
        stored_basis = vector(
            modular_ring, [to_modular(value) for value in bt]
        )
        modular = _local_differentials_in_ring(
            center, data, basis, modular_ring, coordinate, stored_basis
        )
    except (TypeError, ValueError, ZeroDivisionError):
        return None

    padic_ring = LaurentSeriesRing(field, 't', default_prec=prec)

    def to_padic(series):
        if not series:
            return padic_ring.zero().add_bigoh(series.precision_absolute())
        values = [
            field(ZZ(coefficient.lift())).add_bigoh(coefficient_precision)
            for coefficient in series.list()
        ]
        return (padic_ring(values).shift(ZZ(series.valuation()))
                .add_bigoh(series.precision_absolute()))

    return [to_padic(series) for series in modular]


def _local_differentials(center, data, prec, indices=None):
    """Expand each de Rham differential at a bad or infinite center.

    TESTS::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.general_integration import _local_differentials
        sage: from sage.schemes.curves.coleman.points import point_from_basis_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 8, genus=1)
        sage: P = point_from_basis_coordinates(1, [1, 0], False, data)
        sage: index, differentials = _local_differentials(P, data, 12)
        sage: index, len(differentials), [f[-1] for f in differentials]
        (2, 2, [0, 0])
    """
    from .ramified import local_coordinates

    xt, bt, index = local_coordinates(center, prec, data)
    basis = (data.basis if indices is None
             else [data.basis[i] for i in indices])
    differentials = _modular_local_differentials(
        center, data, prec, basis, xt, bt
    )
    if differentials is None:
        ring = LaurentSeriesRing(center.x.parent(), 't', default_prec=prec)
        differentials = _local_differentials_in_ring(
            center, data, basis, ring, ring(xt),
            vector(ring, [ring(value) for value in bt]),
        )
    return index, differentials


@dataclass(frozen=True)
class LocalLogarithmicPrimitive:
    r"""A local primitive ``regular + residue * log(t)``.

    The regular part is a Laurent series with zero constant term.  Keeping
    the logarithmic coefficient separate avoids symbolic-ring arithmetic in
    the numerical integration kernel.
    """

    regular: object
    residue: object


def _laurent_primitive(differential, data):
    """Integrate a local Laurent differential, retaining its logarithm.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.general_integration import _laurent_primitive
        sage: K = Qp(5, 6); L.<t> = LaurentSeriesRing(K, default_prec=8)
        sage: differential = t^-2 + 1 + O(t^5)
        sage: primitive = _laurent_primitive(differential, SimpleNamespace(N=6))
        sage: recovered = (primitive.regular.derivative()
        ....:              + primitive.residue*t^-1)
        sage: (recovered - differential).is_zero()
        True

    The residue is kept as the coefficient of the formal ``log(t)`` term::

        sage: primitive = _laurent_primitive(t^-1 + 2 + O(t^5),
        ....:                                SimpleNamespace(N=6))
        sage: primitive.residue, primitive.regular.derivative()[0]
        (1 + O(5^6), 2 + O(5^6))
    """
    ring = differential.parent()
    if not differential:
        return LocalLogarithmicPrimitive(
            ring.zero(), ring.base_ring().zero()
        )
    t = ring.gen()
    residue = differential[-1]
    if residue:
        differential = differential - residue * t**(-1)
    # LaurentSeries.integral() constructs the coefficient array once.  The
    # former term-by-term ``+=`` loop rebuilt a length-n series n times and
    # made the e=100 boundary calculation effectively quadratic.
    return LocalLogarithmicPrimitive(differential.integral(), residue)


def _laurent_at(primitive, parameter, field):
    """Evaluate a Laurent primitive, rejecting a pole at parameter zero.

    TESTS::

        sage: from sage.schemes.curves.coleman.general_integration import _laurent_at
        sage: K = Qp(5, 6); L.<t> = LaurentSeriesRing(K)
        sage: (_laurent_at(t + t^2, K(5), K) - 30).valuation() >= 6
        True
    """
    if not primitive:
        return field.zero()
    valuation = ZZ(primitive.valuation())
    if not parameter and valuation < 0:
        raise ZeroDivisionError('the differential has a pole at the endpoint')
    # Horner evaluation avoids one extension exponentiation for every term.
    value = field.zero()
    for coefficient in reversed(primitive.list()):
        value = value * parameter + field(coefficient)
    return value * parameter**valuation


def _endpoint_log_argument(parameter, endpoint, field):
    r"""Return the local parameter or tangent scale used by the logarithm.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.general_integration import _endpoint_log_argument
        sage: from sage.schemes.curves.coleman.points import (ColemanIntegrationPoint,
        ....:     tangential_point)
        sage: K = Qp(5, 4); P = ColemanIntegrationPoint(K(0), (K(1), K(0)))
        sage: _endpoint_log_argument(K(5), P, K)
        5 + O(5^5)
        sage: _endpoint_log_argument(K(0), tangential_point(P, 1+5), K)
        1 + 5 + O(5^4)
    """
    if parameter:
        return field(parameter)
    if isinstance(endpoint, ColemanTangentialPoint):
        return field(endpoint.tangent_scale)
    raise ValueError(
        'an endpoint at a logarithmic pole must be a tangential point'
    )


def _endpoint_logarithm(parameter, endpoint, field):
    r"""Return the standard-branch logarithm at a local endpoint.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.general_integration import _endpoint_logarithm
        sage: from sage.schemes.curves.coleman.points import ColemanIntegrationPoint
        sage: K = Qp(5, 5); P = ColemanIntegrationPoint(K(0), (K(1), K(0)))
        sage: _endpoint_logarithm(K(1+5), P, K) == K(1+5).log()
        True
    """
    return _endpoint_log_argument(parameter, endpoint, field).log(
        p_branch=field.zero()
    )


def _local_primitive_at(primitive, parameter, endpoint, field, data, *,
                        logarithm=None):
    r"""Evaluate a local logarithmic primitive at a point or tangent.

    At a nonzero parameter this evaluates ``regular(t) + r*log(t)``.  At
    zero, a nonzero residue requires a
    :class:`~sage.schemes.curves.coleman.points.ColemanTangentialPoint`; for
    the tangent ``c*d/dt`` the normalized value is ``r*log(c)``.  The
    standard Coleman branch ``log(p) = 0`` is used throughout.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.general_integration import (
        ....:     LocalLogarithmicPrimitive, _local_primitive_at)
        sage: from sage.schemes.curves.coleman.points import (
        ....:     ColemanIntegrationPoint, tangential_point)
        sage: K = Qp(5, 8); L.<t> = LaurentSeriesRing(K)
        sage: primitive = LocalLogarithmicPrimitive(t + t^2, K(3))
        sage: P = ColemanIntegrationPoint(K(0), (K(1), K(0)))
        sage: T = tangential_point(P, K(1) + 5)
        sage: (_local_primitive_at(primitive, K(0), T, K,
        ....:                      SimpleNamespace(N=8))
        ....:  - 3*(K(1) + 5).log()).valuation() >= 8
        True
    """
    regular = (field.zero() if not parameter
               else _laurent_at(primitive.regular, parameter, field))
    residue = primitive.residue
    if not residue or residue.valuation() >= data.N:
        return regular
    if logarithm is None:
        logarithm = _endpoint_logarithm(parameter, endpoint, field)
    return regular + field(residue) * logarithm


def _tiny_integrals_local(center, start, end, data, prec, indices=None,
                          local_expansion=None):
    """Integrate between two points of the selected bad residue disk.

    TESTS::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.general_integration import _tiny_integrals_local
        sage: from sage.schemes.curves.coleman.points import point_from_basis_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 8, genus=1)
        sage: P = point_from_basis_coordinates(1, [1, 0], False, data)
        sage: _tiny_integrals_local(P, P, P, data, 12)
        ((0, 0), 8)

    With the canonical tangent and the standard branch ``log(p) = 0``, a
    boundary parameter that is a root of ``p`` has zero logarithm.  The
    result therefore agrees with the former residue-deleted regular part::

        sage: from sage.schemes.curves.coleman.general_integration import (
        ....:     _boundary_extension, _boundary_point, _laurent_at,
        ....:     _laurent_primitive, _lift_center, _local_differentials,
        ....:     _local_parameter_value)
        sage: from sage.schemes.curves.coleman.points import tangential_point
        sage: open_data = coleman_data(
        ....:     y^2 - (x^3 - 10*x + 9), 5, 4,
        ....:     genus=1, use_open_curve=True)
        sage: W = point_from_basis_coordinates(1, [1, 0], False, open_data)
        sage: E, _ = _boundary_extension(
        ....:     open_data, (W, W), (W, W), e=11)
        sage: center = _lift_center(W, open_data, E.base_ring())
        sage: boundary = _boundary_point(center, open_data, E, 30)
        sage: selected = (2, 3, 4)
        sage: values, _ = _tiny_integrals_local(
        ....:     center, tangential_point(W), boundary, open_data, 30,
        ....:     indices=selected)
        sage: index, differentials = _local_differentials(
        ....:     center, open_data, 30, indices=selected)
        sage: parameter = _local_parameter_value(
        ....:     boundary, center, index, E)
        sage: regular = [
        ....:     _laurent_at(_laurent_primitive(f, open_data).regular,
        ....:                 parameter, E) for f in differentials]
        sage: all((a - b).valuation() >= 25
        ....:     for a, b in zip(values, regular))
        True
    """
    indices = (tuple(range(len(data.basis))) if indices is None
               else tuple(ZZ(i) for i in indices))
    if not indices:
        return vector(start.x.parent(), []), ZZ(data.N)
    if len(set(indices)) != len(indices) or any(
            i < 0 or i >= len(data.basis) for i in indices):
        raise ValueError('basis indices are out of range or repeated')
    field = (end.x.parent() if end.x.parent().ramification_index() > 1
             else start.x.parent())
    e = ZZ(field(data.p).valuation())
    if local_expansion is None:
        index, differentials = _local_differentials(
            center, data, prec, indices=indices
        )
    else:
        index, differentials = local_expansion
        if len(differentials) != len(indices):
            raise ValueError('local differential expansion has the wrong size')
    t_start = _local_parameter_value(start, center, index, field)
    t_end = _local_parameter_value(end, center, index, field)
    start_scale = (field(start.tangent_scale)
                   if not t_start
                   and isinstance(start, ColemanTangentialPoint) else None)
    end_scale = (field(end.tangent_scale)
                 if not t_end
                 and isinstance(end, ColemanTangentialPoint) else None)
    logarithmic = any(
        differential[-1]
        and differential[-1].valuation() < data.N
        for differential in differentials
    )
    if logarithmic and ((not t_start and start_scale is None)
                        or (not t_end and end_scale is None)):
        raise ValueError(
            'an endpoint at a logarithmic pole must be a tangential point'
        )
    if t_start == t_end and start_scale == end_scale:
        return vector(field, len(indices)), ZZ(data.N)
    positive = [t.valuation() for t in (t_start, t_end) if t]
    if positive and min(positive) <= 0:
        raise ValueError('local endpoints do not lie in the selected residue disk')
    parameter_valuation = min(positive) if positive else None
    values = []
    available_precision = ZZ(data.N) * e
    # Every basis differential uses the same local parameter.  Compute the
    # logarithm of the endpoint ratio once, rather than one logarithm per
    # basis coordinate (or even one per endpoint and coordinate).
    if logarithmic:
        start_argument = _endpoint_log_argument(t_start, start, field)
        end_argument = _endpoint_log_argument(t_end, end, field)
        log_difference = (end_argument / start_argument).log(
            p_branch=field.zero()
        )
    else:
        log_difference = field.zero()
    for differential in differentials:
        primitive = _laurent_primitive(differential, data)
        start_regular = (field.zero() if not t_start else _laurent_at(
            primitive.regular, t_start, field
        ))
        end_regular = (field.zero() if not t_end else _laurent_at(
            primitive.regular, t_end, field
        ))
        residue = primitive.residue
        logarithmic_term = (field.zero()
                            if not residue or residue.valuation() >= data.N
                            else field(residue) * log_difference)
        value = end_regular - start_regular + logarithmic_term
        values.append(value)
        available_precision = min(
            available_precision, value.precision_absolute()
        )

    if parameter_valuation is None:
        precision = min(QQ(data.N), QQ(available_precision) / e)
        if precision <= 0:
            raise PrecisionError('local tiny integral has no reliable p-adic digits')
        return vector(field, values), precision

    # Keep the bound as a rational number of p-adic digits; Ceiling is applied
    # only after the final result has descended from the ramified extension.
    from .local import tiny_integral_precision

    max_pole_order = -min(ZZ(f.valuation()) for f in differentials)
    max_degree = max(ZZ(f.degree()) for f in differentials)
    min_degree = min(ZZ(f.degree()) for f in differentials)
    formula_precision = tiny_integral_precision(
        prec, e, max_pole_order, max_degree, min_degree,
        parameter_valuation, data
    )
    precision = min(QQ(available_precision) / e, formula_precision)
    if precision <= 0:
        raise PrecisionError('local tiny integral has no reliable p-adic digits')
    return vector(field, values), precision


def tiny_integrals_on_basis_to_parameter(P, data, *, prec=None, indices=None):
    r"""Return bad-disk tiny integrals as series in a local parameter.

    This is the ramified/infinite counterpart of
    :func:`sage.schemes.curves.coleman.local.tiny_integrals_on_basis_to_parameter`.
    If ``P`` is not the central normalized point of its bad disk, the
    constant term is the tiny integral from ``P`` to that center.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.general_integration import tiny_integrals_on_basis_to_parameter
        sage: from sage.schemes.curves.coleman.points import point_from_basis_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 8, genus=1)
        sage: P = point_from_basis_coordinates(1, [1, 0], False, data)
        sage: integrals, _, _, precision = tiny_integrals_on_basis_to_parameter(
        ....:     P, data, prec=12)
        sage: len(integrals), precision
        (2, 8)

    A caller can request only the regular block of an open-curve basis,
    without being obstructed by logarithmic forms in unused coordinates::

        sage: open_data = coleman_data(
        ....:     y^2 - (x^3 - 10*x + 9), 5, 4,
        ....:     genus=1, use_open_curve=True)
        sage: W = point_from_basis_coordinates(1, [1, 0], False, open_data)
        sage: regular, _, _, _ = tiny_integrals_on_basis_to_parameter(
        ....:     W, open_data, prec=30, indices=range(open_data.genus))
        sage: len(regular), regular[0][0]
        (1, 0)
    """
    from .local import t_adic_precision
    from .ramified import find_bad_point_in_disk, local_coordinates

    indices = (tuple(range(len(data.basis))) if indices is None
               else tuple(ZZ(i) for i in indices))
    if len(set(indices)) != len(indices) or any(
            i < 0 or i >= len(data.basis) for i in indices):
        raise ValueError('basis indices are out of range or repeated')

    if not is_in_bad_residue_disk(P, data):
        from .local import tiny_integrals_on_basis_to_parameter as good_series
        return good_series(P, data, prec=prec, indices=indices)

    center = (P if is_bad_residue_disk_center(P, data)
              else find_bad_point_in_disk(P, data))
    prec = (max(ZZ(100), t_adic_precision(data, 1)) if prec is None
            else ZZ(prec))
    if prec < 2:
        raise ValueError('t-adic precision must be at least two')

    if center is P:
        initial = vector(P.x.parent(), len(indices))
        initial_precision = QQ(data.N)
    else:
        initial, initial_precision = _tiny_integrals_local(
            center, P, center, data, prec, indices=indices
        )

    xt, bt, _ = local_coordinates(center, prec, data)
    _, differentials = _local_differentials(
        center, data, prec, indices=indices
    )
    primitives = [_laurent_primitive(differential, data)
                  for differential in differentials]
    if any(primitive.residue
           and primitive.residue.valuation() < data.N
           for primitive in primitives):
        raise NotImplementedError(
            'a logarithmic primitive is not a Laurent series; evaluate it '
            'between points or tangential points instead'
        )
    ring = primitives[0].regular.parent() if primitives else xt.parent()
    integrals = vector(ring, [
        primitive.regular + ring(initial[i])
        for i, primitive in enumerate(primitives)
    ])
    return integrals, xt, vector(xt.parent(), bt), ZZ(
        QQ(initial_precision).ceil()
    )


def _boundary_extension(data, endpoints, centers, e=None):
    """Choose a totally ramified field for all bad near-boundary points.

    The local ramification condition only gives a strict lower bound for
    ``e``.  It does not account for the poles in the exact primitives, so the
    parameter remains caller-configurable.  The default is ``e = 100``;
    callers may override it.

    TESTS::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.general_integration import _boundary_extension
        sage: from sage.schemes.curves.coleman.points import point_from_basis_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 8, genus=1)
        sage: P = point_from_basis_coordinates(1, [1, 0], False, data)
        sage: field, degree = _boundary_extension(
        ....:     data, (P, P), (P, P), e=11)
        sage: field.ramification_index(), degree
        (11, 11)
        sage: field.base_ring().precision_cap() >= 2 * data.N
        True
    """
    from .ramified import local_data

    fields = {P.x.parent() for P in endpoints}
    if len(fields) != 1:
        raise TypeError('both endpoints must be over the same p-adic field')
    original_field = fields.pop()
    if original_field.ramification_index() != 1:
        raise NotImplementedError(
            'automatic boundary construction currently starts over Qp'
        )
    local_ramification = [
        ZZ(local_data(center, data)[0])
        for center in centers if center is not None
    ]
    minimum = max(ZZ(data.p) * local_degree + 1
                  for local_degree in local_ramification)
    e = max(ZZ(100), minimum) if e is None else ZZ(e)
    if e < minimum:
        raise ValueError(
            f'boundary ramification degree must be at least {minimum}'
        )
    # Reconstructing a center above a point of local ramification ``d`` can
    # divide the available root precision by ``d``.  Allocate enough source
    # digits that every resulting coordinate still has the requested ``N``
    # digits before it is evaluated in the boundary extension.
    base_precision = max(
        ZZ(data.Nmax) + 6,
        ZZ(data.N) + 6,
        max(local_ramification) * ZZ(data.N),
    )
    base = Qp(data.p, prec=base_precision)
    ring = PolynomialRing(base, 'u')
    E = base.extension(ring.gen()**e - data.p, names='pi')
    return E, ZZ(e)


def _lift_center(center, data, field):
    """Reconstruct a bad center at the boundary field's precision.

    TESTS::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.general_integration import (_boundary_extension,
        ....:     _lift_center)
        sage: from sage.schemes.curves.coleman.points import point_from_basis_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 8, genus=1)
        sage: P = point_from_basis_coordinates(1, [1, 0], False, data)
        sage: field, _ = _boundary_extension(data, (P, P), (P, P), e=11)
        sage: lifted = _lift_center(P, data, field.base_ring())
        sage: (lifted.x - 1).valuation() >= data.N and not lifted.b[1]
        True
    """
    from .ramified import find_bad_point_in_disk

    def residue_lift(value):
        if value.valuation() < 0:
            raise ValueError('bad center has a nonintegral coordinate')
        return field(ZZ(value.residue()))

    seed = ColemanIntegrationPoint(
        x=field.zero() if center.infinity else residue_lift(center.x),
        b=tuple(residue_lift(value) for value in center.b),
        infinity=center.infinity,
    )
    return find_bad_point_in_disk(seed, data)


def _boundary_point(center, data, field, prec):
    """Evaluate a bad local parametrization at the extension uniformizer.

    TESTS::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.general_integration import (_boundary_extension,
        ....:     _boundary_point, _lift_center)
        sage: from sage.schemes.curves.coleman.points import point_from_basis_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 8, genus=1)
        sage: P = point_from_basis_coordinates(1, [1, 0], False, data)
        sage: field, _ = _boundary_extension(data, (P, P), (P, P), e=11)
        sage: center = _lift_center(P, data, field.base_ring())
        sage: boundary = _boundary_point(center, data, field, 12)
        sage: boundary.infinity, (boundary.x - center.x).valuation()
        (False, 2)
    """
    from .ramified import local_coordinates

    xt, bt, _ = local_coordinates(center, prec, data)
    parameter = field.gen()
    return ColemanIntegrationPoint(
        x=xt(parameter),
        b=tuple(series(parameter) for series in bt),
        infinity=center.infinity,
    )


def descend_to_base_field(values):
    r"""Project a vector over a totally ramified extension back to `\QQ_p`.

    OUTPUT: the vector of constant coefficients and the minimum precision, in
    base-field digits, to which all discarded nonconstant coefficients vanish.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.general_integration import descend_to_base_field
        sage: K = Qp(5, 8); R.<u> = K[]
        sage: E.<pi> = K.extension(u^3-5)
        sage: rounded, precision = descend_to_base_field(
        ....:     vector(E, [K(2)+pi^7, K(3)]))
        sage: rounded == vector(K, [2, 3]) and precision == 7/3
        True
    """
    entries = list(values)
    if not entries:
        return vector(QQ, []), infinity
    extension = entries[0].parent()
    if any(entry.parent() is not extension for entry in entries):
        entries = [extension(entry) for entry in entries]
    degree = ZZ(extension.degree())
    if degree <= 0:
        raise ValueError("coefficient field has invalid degree")
    base = extension.base_ring()
    precision = ZZ(extension.precision_cap())
    constants = []
    for entry in entries:
        constant = base(entry.polynomial()[0])
        constants.append(constant)
        residual = entry - extension(constant)
        if residual:
            precision = min(precision, ZZ(residual.valuation()))
    return vector(base, constants), QQ(precision) / degree


def _descent_output_precision(theoretical_precision, rounding_precision):
    r"""Return the integral precision certified by base-field descent.

    Let ``y`` be the computed extension-field value, ``a`` its constant
    projection, and ``x`` the exact integral in `\QQ_p`.  The theoretical
    bound controls ``y-x``, while ``rounding_precision`` controls ``y-a``.
    Hence ``x-a`` is known to their minimum.  Both ``x`` and ``a`` lie in
    `\QQ_p`, so this lower bound rounds up to an integral valuation.

    TESTS::

        sage: from sage.schemes.curves.coleman.general_integration import _descent_output_precision
        sage: _descent_output_precision(15/2, 657/100)
        7
        sage: _descent_output_precision(15/2, 399/50)
        8
        sage: _descent_output_precision(13/2, Infinity)
        7
    """
    effective_precision = QQ(theoretical_precision)
    if rounding_precision != infinity:
        effective_precision = min(
            effective_precision, QQ(rounding_precision)
        )
    return ZZ(effective_precision.ceil())


def _general_integrals(P1, P2, data, *, e=None, indices=None):
    """Normalize bad endpoints, split tiny paths, then solve Frobenius.

    TESTS:

    A non-hyperelliptic branch endpoint exercises the general path::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.general_integration import _general_integrals
        sage: from sage.schemes.curves.coleman.points import (point_from_basis_coordinates,
        ....:     point_from_good_affine_coordinates)
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: Q = y^3 + (-x^2 - 1)*y^2 - x^3*y + x^3 + 2*x^2 + x
        sage: data = coleman_data(Q, 7, 4, genus=3)
        sage: branch = point_from_basis_coordinates(0, [1, 0, 0], False, data)
        sage: good = point_from_good_affine_coordinates(
        ....:     5, -32582624253112412, data)
        sage: values, precision = _general_integrals(  # indirect doctest
        ....:     good, branch, data, e=15)
        sage: len(values), precision
        (6, 1)
    """
    from .local import tiny_integrals_on_basis as good_tiny
    from .ramified import find_bad_point_in_disk

    indices = (tuple(range(len(data.basis))) if indices is None
               else tuple(ZZ(i) for i in indices))
    if not indices:
        return vector(P1.x.parent(), []), ZZ(data.N)
    if len(set(indices)) != len(indices) or any(
            i < 0 or i >= len(data.basis) for i in indices):
        raise ValueError('basis indices are out of range or repeated')

    complement = tuple(i for i in range(len(data.basis)) if i not in indices)
    if any(data.frobenius_matrix[i, j] or data.frobenius_matrix[j, i]
           for i in indices for j in complement):
        raise ValueError('the selected basis coordinates are not a Frobenius block')

    endpoints = (P1, P2)
    bad = tuple(is_in_bad_residue_disk(P, data) for P in endpoints)
    centers = tuple(
        (P if is_bad_residue_disk_center(P, data)
         else find_bad_point_in_disk(P, data))
        if bad[i] else None for i, P in enumerate(endpoints)
    )
    extension, e = _boundary_extension(data, endpoints, centers, e=e)
    centers = tuple(_lift_center(center, data, extension.base_ring())
                    if center is not None else None for center in centers)
    from .local import t_adic_precision
    prec = max(ZZ(100), t_adic_precision(data, e))
    boundary = tuple(
        _boundary_point(centers[i], data, extension, prec) if bad[i]
        else endpoints[i] for i in range(2)
    )
    images = tuple(frobenius_point(P, data) for P in boundary)
    zero = vector(extension, len(indices))
    endpoint_tiny = []
    frobenius_tiny = []
    precision = ZZ(data.N)
    for i in range(2):
        if bad[i]:
            local_expansion = _local_differentials(
                centers[i], data, prec, indices=indices
            )
            first, first_precision = _tiny_integrals_local(
                centers[i], endpoints[i], boundary[i], data, prec,
                indices=indices, local_expansion=local_expansion
            )
            second, second_precision = _tiny_integrals_local(
                centers[i], boundary[i], images[i], data, prec,
                indices=indices, local_expansion=local_expansion
            )
        else:
            first, first_precision = zero, ZZ(data.N)
            full_second, second_precision = good_tiny(
                endpoints[i], images[i], data
            )
            second = vector(extension, [full_second[j] for j in indices])
        endpoint_tiny.append(vector(extension, first))
        frobenius_tiny.append(vector(extension, second))
        precision = min(precision, first_precision, second_precision)

    finite_values = [
        _evaluate_finite_primitives(
            (data.f0_list[i] for i in indices), endpoint, data
        )
        for endpoint in boundary
    ]
    rhs = []
    for position, i in enumerate(indices):
        values = []
        for endpoint_index, endpoint in enumerate(boundary):
            finite_term, finite_precision = finite_values[
                endpoint_index
            ][position]
            infinite_term, infinite_precision = evaluate_infinite_primitive(
                data.finf_list[i], endpoint, data
            )
            terminal_term, terminal_precision = evaluate_terminal_primitive(
                data.fend_list[i], endpoint, data
            )
            precision = min(
                precision, finite_precision, infinite_precision,
                terminal_precision,
            )
            terms = [extension(finite_term), extension(infinite_term),
                     extension(terminal_term)]
            values.append(sum(terms, extension.zero()))
        rhs.append(values[0] - values[1] - frobenius_tiny[0][position]
                   + frobenius_tiny[1][position])

    full_system = data.frobenius_matrix - identity_matrix(
        QQ, len(data.basis)
    )
    system = full_system.matrix_from_rows_and_columns(indices, indices)
    if not system.is_invertible():
        raise ArithmeticError('Frobenius minus identity is singular')
    inverse = system.inverse()
    rhs_vector = vector(extension, rhs)
    determinant_loss = ZZ(system.det().valuation(data.p))
    precision = min(
        QQ(precision) - determinant_loss,
        ZZ(data.N) - 2 * determinant_loss - ZZ(data.delta),
    )
    global_integral = (
        rhs_vector * inverse.transpose().change_ring(extension)
    )
    result = global_integral + endpoint_tiny[0] - endpoint_tiny[1]
    if precision <= 0:
        raise PrecisionError('integral has no reliable p-adic digits')

    projected, rounding_precision = descend_to_base_field(result)
    output_precision = _descent_output_precision(
        precision, rounding_precision
    )
    if output_precision <= 0:
        raise PrecisionError(
            'boundary computation does not certify descent to the base field'
        )
    values = vector(P1.x.parent(), projected)
    return _truncate_vector(values, output_precision), output_precision


def coleman_integrals_on_basis(P1, P2, data, *, e=None):
    r"""Integrate the basis, including fixed hyperelliptic branch endpoints.

    The good-good computation uses the Frobenius linear system.  A branch
    point fixed by the hyperelliptic involution satisfies
    ``integral(W,Q) = integral(iota(Q),Q)/2`` on the anti-invariant de Rham
    basis.  The same identity applies to the unique point at infinity of an
    odd-degree model.  Other bad endpoints are normalized, moved to a
    ramified near-boundary point, and integrated by local Laurent series.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.general_integration import (
        ....:     _local_differentials, coleman_integrals_on_basis)
        sage: from sage.schemes.curves.coleman.points import (point_from_basis_coordinates,
        ....:     point_from_good_affine_coordinates)
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 2, genus=1)
        sage: branch = point_from_basis_coordinates(1, [1, 0], False, data)
        sage: good = point_from_good_affine_coordinates(0, 3, data)
        sage: len(coleman_integrals_on_basis(branch, good, data)[0])
        2

        sage: K = Qp(5, 3); L = Qp(5, 5)
        sage: branch_K = point_from_basis_coordinates(
        ....:     K(1), [K(1), K(0)], False, data)
        sage: good_L = point_from_good_affine_coordinates(L(0), L(3), data)
        sage: len(coleman_integrals_on_basis(branch_K, good_L, data)[0])
        2

    The hyperelliptic fixed-point shortcut is applied only to the
    anti-invariant block.  An ordinary endpoint at a logarithmic pole is
    rejected, while an explicit tangent supplies its normalized value::

        sage: open_data = coleman_data(
        ....:     y^2 - (x^3 - 10*x + 9), 5, 4,
        ....:     use_open_curve=True, genus=1)
        sage: open_branch = point_from_basis_coordinates(
        ....:     1, [1, 0], False, open_data)
        sage: open_good = point_from_good_affine_coordinates(0, 3, open_data)
        sage: coleman_integrals_on_basis(open_branch, open_good, open_data)
        Traceback (most recent call last):
        ...
        ValueError: an endpoint at a logarithmic pole must be a tangential point
        sage: from sage.schemes.curves.coleman.points import tangential_point
        sage: tangent = tangential_point(open_branch)
        sage: forward, n1 = coleman_integrals_on_basis(
        ....:     tangent, open_good, open_data)
        sage: reverse, n2 = coleman_integrals_on_basis(
        ....:     open_good, tangent, open_data)
        sage: min(n1, n2) >= 2
        True
        sage: all((a + b).valuation() >= min(n1, n2)
        ....:     for a, b in zip(forward, reverse))
        True

    Tangent rescaling has the expected residue-logarithm correction, and
    path additivity is retained::

        sage: scaled = tangential_point(open_branch, 1 + open_data.p)
        sage: scaled_values, n3 = coleman_integrals_on_basis(
        ....:     scaled, open_good, open_data)
        sage: _, local_forms = _local_differentials(open_branch, open_data, 20)
        sage: residues = [form[-1] for form in local_forms]
        sage: log_scale = open_branch.x.parent()(1 + open_data.p).log()
        sage: bound = min(n1, n3)
        sage: all((scaled_values[i] - forward[i]
        ....:          + residues[i]*log_scale).valuation() >= bound
        ....:     for i in range(len(forward)))
        True
        sage: other = point_from_good_affine_coordinates(8, 21, open_data)
        sage: tail, n4 = coleman_integrals_on_basis(open_good, other, open_data)
        sage: total, n5 = coleman_integrals_on_basis(tangent, other, open_data)
        sage: bound = min(n1, n4, n5)
        sage: all((forward[i] + tail[i] - total[i]).valuation() >= bound
        ....:     for i in range(len(forward)))
        True

    Two fixed tangential endpoints retain exact zeroes on the fast
    anti-invariant block while the logarithmic block uses the general path::

        sage: open_infinity = tangential_point(point_from_basis_coordinates(
        ....:     0, [1, 0], True, open_data))
        sage: fixed_values, fixed_precision = coleman_integrals_on_basis(
        ....:     tangent, open_infinity, open_data)
        sage: all(fixed_values[i].valuation() >= fixed_precision
        ....:     for i in (0, 1))
        True

    TESTS:

    A branch point may have an irrational `x`-coordinate, here `\sqrt{2}`
    in `\QQ_7` on the non-hyperelliptic curve `y^3 = (x^2 - 2)(x - 1)`.  The
    automorphism `y \mapsto \zeta y` fixes every branch point and scales
    both basis differentials by nontrivial cube roots of unity.  Hence the
    integral between two branch points vanishes, and the integrals from the
    branch points over `\sqrt{2}` and over `1` agree.  The positive valuation
    of the ramified root derivative consumes one digit of root precision::

        sage: f = (x^2 - 2)*(x - 1)
        sage: data3 = coleman_data(y^3 - f, 7, 5)
        sage: data3.W0.is_one(), [tuple(w) for w in data3.basis]
        (True, [(0, 1, 0), (0, 0, -3*x + 1)])
        sage: K = Qp(7, 5); Z.<z> = K[]
        sage: y5 = [r for r, _ in (z^3 - f(5)).roots() if r.residue() == 1][0]
        sage: good3 = point_from_good_affine_coordinates(K(5), y5, data3)
        sage: irrational = point_from_basis_coordinates(
        ....:     K(2).sqrt(), [1, 0, 0], False, data3)
        sage: rational = point_from_basis_coordinates(
        ....:     1, [1, 0, 0], False, data3)
        sage: I1, n1 = coleman_integrals_on_basis(irrational, good3, data3)
        sage: I2, n2 = coleman_integrals_on_basis(rational, good3, data3)
        sage: n1, n2, all((a - b).valuation() >= min(n1, n2)
        ....:                for a, b in zip(I1, I2))
        (4, 4, True)
    """
    from .integration import coleman_integrals_on_basis as good_integrals

    P1, P2 = _common_point_field(P1, P2, data.p)

    bad1 = is_in_bad_residue_disk(P1, data)
    bad2 = is_in_bad_residue_disk(P2, data)
    if not bad1 and not bad2:
        return good_integrals(P1, P2, data)
    if bad1 and bad2 and are_in_same_residue_disk(P1, P2, data):
        from .ramified import find_bad_point_in_disk
        center = (P1 if is_bad_residue_disk_center(P1, data)
                  else find_bad_point_in_disk(P1, data))
        prec = max(ZZ(100), ZZ(data.N) + ZZ(data.Nmax) + 3)
        value, precision = _tiny_integrals_local(
            center, P1, P2, data, prec
        )
        precision = ZZ(precision.ceil())
        return _truncate_vector(value, precision), precision
    fixed1 = (_fixed_by_hyperelliptic_involution(P1, data)
              if bad1 else False)
    fixed2 = (_fixed_by_hyperelliptic_involution(P2, data)
              if bad2 else False)
    shortcut = (fixed1 and fixed2) or (fixed1 and not bad2) or (
        fixed2 and not bad1
    )
    if not shortcut:
        return _general_integrals(P1, P2, data, e=e)

    anti_indices = tuple(i for i, differential in enumerate(data.basis)
                         if not differential[0])
    remaining_indices = tuple(i for i in range(len(data.basis))
                              if i not in anti_indices)
    if any(data.frobenius_matrix[i, j] or data.frobenius_matrix[j, i]
           for i in anti_indices for j in remaining_indices):
        return _general_integrals(P1, P2, data, e=e)

    field = P1.x.parent()
    output = [field.zero() for _ in data.basis]
    precision = ZZ(data.N)
    if remaining_indices:
        remaining, remaining_precision = _general_integrals(
            P1, P2, data, e=e, indices=remaining_indices
        )
        for i, value in zip(remaining_indices, remaining):
            output[i] = field(value)
        precision = min(precision, remaining_precision)

    if fixed1 and fixed2:
        return _truncate_vector(vector(field, output), precision), precision
    if fixed1 and not bad2:
        x, y = affine_coordinates(P2, data)
        conjugate = point_from_good_affine_coordinates(x, -y, data)
        value, precision = good_integrals(conjugate, P2, data)
        precision -= ZZ(data.p == 2)
        value /= 2
        for i in anti_indices:
            output[i] = field(value[i])
        if remaining_indices:
            precision = min(precision, remaining_precision)
        return _truncate_vector(vector(field, output), precision), precision
    if fixed2 and not bad1:
        x, y = affine_coordinates(P1, data)
        conjugate = point_from_good_affine_coordinates(x, -y, data)
        value, precision = good_integrals(conjugate, P1, data)
        precision -= ZZ(data.p == 2)
        value = -value / 2
        for i in anti_indices:
            output[i] = field(value[i])
        if remaining_indices:
            precision = min(precision, remaining_precision)
        return _truncate_vector(vector(field, output), precision), precision
    raise AssertionError('unreachable hyperelliptic shortcut state')
