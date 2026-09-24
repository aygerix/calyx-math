# sage.doctest: needs sage.rings.function_field sage.rings.padics sage.libs.singular
r"""
Point enumeration for Coleman integration on plane curves

The reduction points are degree-one places of the function field.  This is
important for singular plane models: distinct branches above one affine
coordinate pair remain distinct points on the normalization.

``padic_points`` lifts good affine residue disks by fixing an integral lift of
``x`` and applying Hensel's lemma to ``Q(x,y)``.  Bad, ramified, and infinite
disks are lifted through their normalized integral-basis coordinates.  A
supplied point can select any remaining disk; ``skip_unsupported=True`` omits
a normalized residue place that is not representable over `\QQ_p`.

EXAMPLES::

    sage: from types import SimpleNamespace
    sage: from sage.schemes.curves.coleman.auxiliary import (auxiliary_polynomials,
    ....:     integral_basis_matrices)
    sage: from sage.schemes.curves.coleman.applications import (padic_points,
    ....:     reduction_points)
    sage: from sage.schemes.curves.coleman.points import (affine_coordinates,
    ....:     is_in_bad_residue_disk)
    sage: R.<x> = QQ[]
    sage: S.<y> = R[]
    sage: Q = y^2 - (x^3 - 10*x + 9)
    sage: W0, Winf = integral_basis_matrices(Q)
    sage: data = SimpleNamespace(Q=Q, p=5, N=8, W0=W0, Winf=Winf,
    ....:                        r=auxiliary_polynomials(Q)[0])
    sage: reduction = reduction_points(data)
    sage: len(reduction) == 6   # elliptic curve over GF(5)
    True
    sage: lifts, _ = padic_points(data, skip_unsupported=True)
    sage: len(lifts) == len(reduction) == 6
    True
    sage: all(sum(c(P.x)*affine_coordinates(P, data)[1]^i
    ....:         for i, c in enumerate(Q.list())).valuation() >= data.N
    ....:         for P in lifts if not is_in_bad_residue_disk(P, data))
    True
    sage: all_lifts, _ = padic_points(data)
    sage: len(all_lifts), sum(is_in_bad_residue_disk(P, data)
    ....:                     for P in all_lifts)
    (6, 2)

The genus-three Bruin--Poonen--Stoll model has nontrivial infinite basis::

    sage: Q = y^3 + (-x^2 - 1)*y^2 - x^3*y + x^3 + 2*x^2 + x
    sage: W0, Winf = integral_basis_matrices(Q)
    sage: data = SimpleNamespace(Q=Q, p=7, N=8, W0=W0, Winf=Winf,
    ....:                        r=auxiliary_polynomials(Q)[0])
    sage: reduction = reduction_points(data)
    sage: lifts, _ = padic_points(data)
    sage: len(reduction), len(lifts), sum(P.infinity for P in lifts)
    (9, 9, 3)
    sage: all(sum(c(P.x)*affine_coordinates(P, data)[1]^i
    ....:         for i, c in enumerate(Q.list())).valuation() >= data.N
    ....:         for P in lifts if not is_in_bad_residue_disk(P, data))
    True

"""

from typing import NamedTuple

from sage.rings.finite_rings.finite_field_constructor import GF
from sage.rings.integer_ring import ZZ
from sage.rings.padics.factory import Qp
from sage.rings.padics.precision_error import PrecisionError
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ
from sage.schemes.affine.affine_space import AffineSpace

from .auxiliary import (
    _function_field_model,
    _reduce_model_mod_prime,
    _validate_prime,
)
from .integration import _newton_root
from .points import (
    ColemanIntegrationPoint,
    is_in_bad_residue_disk,
    point_from_basis_coordinates,
    point_from_good_affine_coordinates,
)


class ColemanReductionPoint(NamedTuple):
    r"""A degree-one place, expressed in one of the two integral bases.

    ``x`` is the value of ``x`` for a finite place and of ``1/x`` at
    infinity.  ``index=0`` means this coordinate is a uniformizer;
    otherwise ``b[index-1]`` is one.  Positive indices are one-based.
    """

    x: object
    b: tuple
    infinity: bool
    index: int


def _reduce_function(f, K):
    r"""Reduce a rational function in ``QQ(x)`` into ``GF(p)(x)``.

    TESTS::

        sage: from sage.schemes.curves.coleman.applications import _reduce_function
        sage: R.<x> = QQ[]; K.<x> = FunctionField(GF(5))
        sage: _reduce_function((x^2-1)/(x-1), K)
        x + 1
    """
    k = K.constant_base_field()
    polynomial_ring = PolynomialRing(k, names=K.variable_name())
    try:
        numerator = polynomial_ring([k(c) for c in f.numerator().list()])
        denominator = polynomial_ring([k(c) for c in f.denominator().list()])
    except (TypeError, ValueError, ZeroDivisionError) as exc:
        raise ValueError("integral basis has coefficients not defined modulo p") from exc
    if not denominator:
        raise ValueError("integral basis has a denominator vanishing modulo p")
    return K(numerator) / K(denominator)


def _basis_functions(W, L, K):
    r"""Express reduced integral-basis rows as function-field elements.

    TESTS::

        sage: from sage.schemes.curves.coleman.applications import _basis_functions
        sage: R.<x> = QQ[]; k = GF(5); K.<x> = FunctionField(k)
        sage: T.<Y> = K[]; L.<y> = K.extension(Y^2-x)
        sage: _basis_functions(identity_matrix(R.fraction_field(), 2), L, K)
        (1, y)
    """
    y = L.gen()
    return tuple(sum((L(_reduce_function(W[i, j], K)) * y**j
                      for j in range(W.ncols())), L.zero())
                 for i in range(W.nrows()))


def _exact_basis_functions(W, L):
    r"""Express integral-basis rows in an exact function field.

    TESTS::

        sage: from sage.schemes.curves.coleman.applications import _exact_basis_functions
        sage: R.<x> = QQ[]; K.<x> = FunctionField(QQ)
        sage: T.<Y> = K[]; L.<y> = K.extension(Y^2-x)
        sage: _exact_basis_functions(identity_matrix(R.fraction_field(), 2), L)
        (1, y)
    """
    y = L.gen()
    K = L.base_field()
    return tuple(sum((L(K(W[i, j])) * y**j for j in range(W.ncols())),
                     L.zero())
                 for i in range(W.nrows()))


def _maximal_order_with_known_basis(function_field, basis):
    r"""Build decomposition data from a certified integral basis.

    TESTS::

        sage: from sage.schemes.curves.coleman.applications import _maximal_order_with_known_basis
        sage: K.<x> = FunctionField(QQ); T.<Y> = K[]
        sage: L.<y> = K.extension(Y^2-x)
        sage: _maximal_order_with_known_basis(L, [L.one(), y]).basis()
        (1, y)
    """
    from sage.rings.function_field.order_polymod import (
        FunctionFieldMaximalOrder_polymod,
    )

    order = FunctionFieldMaximalOrder_polymod(
        function_field, _basis=basis, _basis_is_maximal=True
    )
    return order


def reduction_points(data):
    r"""Return every rational place of the smooth reduction of ``data.Q``.

    Both finite and infinite places are returned, including branches over
    singular points of the supplied plane model.  Each result is an
    :class:`ColemanReductionPoint` with values in ``GF(data.p)``.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.applications import reduction_points
        sage: from sage.schemes.curves.coleman.auxiliary import integral_basis_matrices
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: Q = y^2-(x^3-10*x+9); W0, Winf = integral_basis_matrices(Q)
        sage: data = SimpleNamespace(Q=Q, p=5, W0=W0, Winf=Winf)
        sage: len(reduction_points(data))
        6
    """
    p = _validate_prime(data.p)
    K, q = _reduce_model_mod_prime(data.Q, p)
    if not q.is_irreducible():
        raise ValueError("bad prime: Q is reducible modulo p")
    L = K.extension(q, names=q.parent().variable_name())
    k = GF(p)
    x = L(K.gen())
    finite_basis = _basis_functions(data.W0, L, K)
    infinite_basis = _basis_functions(data.Winf, L, K)
    points = []
    for place in L.places(1):
        at_infinity = x.valuation(place) < 0
        coordinate = 1 / x if at_infinity else x
        coordinate_value = k(coordinate.evaluate(place))
        basis = infinite_basis if at_infinity else finite_basis
        values = tuple(k(f.evaluate(place)) for f in basis)
        if (coordinate - L(coordinate_value)).valuation(place) == 1:
            index = 0
        else:
            index = next((i for i, (f, value) in enumerate(zip(basis, values), 1)
                          if (f - L(value)).valuation(place) == 1), None)
            if index is None:
                raise ArithmeticError("no stored basis element is a local coordinate")
        points.append(ColemanReductionPoint(
            coordinate_value, values, at_infinity, index
        ))
    return points


def _residue(value, k):
    r"""Reduce an integral p-adic coordinate to the prime residue field.

    TESTS::

        sage: from sage.schemes.curves.coleman.applications import _residue
        sage: _residue(Qp(5, 4)(7), GF(5))
        2
    """
    value = Qp(k.characteristic(), prec=2)(value) if not hasattr(value, "residue") else value
    if value.valuation() < 0:
        raise ValueError("a supplied point has a nonintegral stored coordinate")
    return k(value.residue(1))


def _same_reduction(P, residue_point, k):
    r"""Test whether an integration point belongs to a residue disk.

    TESTS::

        sage: from sage.schemes.curves.coleman.applications import (ColemanReductionPoint,
        ....:     _same_reduction)
        sage: from sage.schemes.curves.coleman.points import ColemanIntegrationPoint
        sage: K = Qp(5, 4); k = GF(5)
        sage: P = ColemanIntegrationPoint(K(5), (K(1), K(5)))
        sage: Q = ColemanReductionPoint(k(0), (k(1), k(0)), False, 0)
        sage: _same_reduction(P, Q, k)
        True
    """
    return (P.infinity == residue_point.infinity
            and _residue(P.x, k) == residue_point.x
            and len(P.b) == len(residue_point.b)
            and all(_residue(b, k) == v for b, v in zip(P.b, residue_point.b)))


def _evaluate_function_mod_p(f, k, x):
    r"""Evaluate a rational function at a residue coordinate when regular.

    TESTS::

        sage: from sage.schemes.curves.coleman.applications import _evaluate_function_mod_p
        sage: R.<x> = QQ[]; k = GF(5)
        sage: _evaluate_function_mod_p((x+1)/(x+2), k, k(0))
        3
    """
    try:
        numerator = f.numerator().change_ring(k)(x)
        denominator = f.denominator().change_ring(k)(x)
    except (TypeError, ValueError, ZeroDivisionError) as exc:
        raise ValueError("integral basis cannot be reduced modulo p") from exc
    if denominator == 0:
        raise NotImplementedError("integral basis has a pole at this residue coordinate")
    return numerator / denominator


def _lift_good_affine(residue_point, data, k):
    r"""Hensel lift one smooth affine residue disk.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.applications import (ColemanReductionPoint,
        ....:     _lift_good_affine)
        sage: R.<x> = QQ[]; S.<y> = R[]; k = GF(5)
        sage: Q = y^2-(x^3-10*x+9)
        sage: data = SimpleNamespace(Q=Q, p=5, N=6,
        ....:     W0=identity_matrix(R.fraction_field(), 2), r=R.one())
        sage: Pbar = ColemanReductionPoint(k(0), (k(1), k(3)), False, 0)
        sage: P = _lift_good_affine(Pbar, data, k)
        sage: P.x == 0, (P.b[1]-3).valuation() >= 1
        (True, True)
    """
    p = _validate_prime(data.p)
    N = ZZ(data.N)
    work_precision = max(N + 2, (3 * N + 1) // 2)
    field = Qp(p, prec=work_precision)
    x0 = field(ZZ(residue_point.x))
    reduced_polynomial = PolynomialRing(k, names=data.Q.parent().variable_name())([
        coefficient.change_ring(k)(residue_point.x)
        for coefficient in data.Q.list()
    ])
    matching_roots = []
    degree = data.Q.degree()
    for y0, multiplicity in reduced_polynomial.roots():
        if multiplicity != 1:
            continue
        values = tuple(sum((_evaluate_function_mod_p(data.W0[i, j], k,
                                                     residue_point.x) * y0**j
                            for j in range(degree)), k.zero())
                       for i in range(degree))
        if values == residue_point.b:
            matching_roots.append(y0)
    if len(matching_roots) != 1:
        raise ArithmeticError("the residue basis does not identify one simple y-root")
    polynomial_ring = PolynomialRing(field, names=data.Q.parent().variable_name())
    specialized = polynomial_ring([field(coefficient(x0))
                                   for coefficient in data.Q.list()])
    y = _newton_root(specialized, field(ZZ(matching_roots[0])), precision=N)
    point = point_from_good_affine_coordinates(x0, y, data)
    if not _same_reduction(point, residue_point, k):
        raise ArithmeticError("Hensel lift changed the selected residue disk")
    return point


def _lift_normalized_residue(residue_point, data, k):
    r"""Lift a bad, ramified, or infinite normalized residue place.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.applications import (ColemanReductionPoint,
        ....:     _lift_normalized_residue)
        sage: from sage.schemes.curves.coleman.auxiliary import (auxiliary_polynomials,
        ....:     integral_basis_matrices)
        sage: R.<x> = QQ[]; S.<y> = R[]; k = GF(5)
        sage: Q = y^2-(x^3-10*x+9); W0, Winf = integral_basis_matrices(Q)
        sage: data = SimpleNamespace(Q=Q, p=5, N=6, W0=W0, Winf=Winf,
        ....:     r=auxiliary_polynomials(Q)[0])
        sage: Pbar = ColemanReductionPoint(k(1), (k(1), k(0)), False, 2)
        sage: _lift_normalized_residue(Pbar, data, k).x
        1 + O(5^6)
    """
    from .ramified import find_bad_point_in_disk

    requested_precision = ZZ(data.N)
    precision_error = None
    for multiplier in (2, 3, 4, 6, 8):
        work_precision = max(requested_precision + 2,
                             multiplier * requested_precision)
        work_field = Qp(data.p, prec=work_precision)
        point = point_from_basis_coordinates(
            work_field(ZZ(residue_point.x)),
            [work_field(ZZ(value)) for value in residue_point.b],
            residue_point.infinity,
            data,
        )
        if not is_in_bad_residue_disk(point, data):
            raise ArithmeticError(
                "normalized residue place was not detected as bad"
            )
        try:
            point = find_bad_point_in_disk(point, data)
        except PrecisionError as error:
            precision_error = error
            continue
        if not _same_reduction(point, residue_point, k):
            raise ArithmeticError(
                "normalized lift changed the selected residue disk"
            )
        break
    else:
        raise precision_error
    field = Qp(data.p, prec=data.N)
    return ColemanIntegrationPoint(
        field(point.x), tuple(field(value) for value in point.b),
        point.infinity,
    )


def padic_points(data, points=(), *, skip_unsupported=False):
    r"""Lift the rational residue disks to points over ``Qp(data.p)``.

    Supplied
    :class:`~sage.schemes.curves.coleman.points.ColemanIntegrationPoint`
    objects are reused when they match a disk.  Good affine disks are lifted
    by scalar Hensel iteration; bad, ramified, and infinite places are lifted
    through their normalized integral-basis coordinates.  Set
    ``skip_unsupported=True`` to omit a disk if its normalized lift cannot be
    represented over ``Qp(data.p)``.

    OUTPUT: a pair ``(list_of_points, data)``.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.applications import padic_points
        sage: from sage.schemes.curves.coleman.auxiliary import (auxiliary_polynomials,
        ....:     integral_basis_matrices)
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: Q = y^2-(x^3-10*x+9); W0, Winf = integral_basis_matrices(Q)
        sage: data = SimpleNamespace(Q=Q, p=5, N=6, W0=W0, Winf=Winf,
        ....:     r=auxiliary_polynomials(Q)[0])
        sage: points, _ = padic_points(data)
        sage: len(points)
        6

    A normalized coordinate that has two distinct lifts in one residue
    class is refused instead of being combined with coordinates from a
    different point::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: Q = (y^3 + (3*x^2 + x - 2)*y^2
        ....:      + (-3*x^3 - 3*x^2 + 2*x + 2)*y + x^4 + x^3)
        sage: ambiguous = coleman_data(Q, 7, 2, genus=3)
        sage: padic_points(ambiguous)
        Traceback (most recent call last):
        ...
        ValueError: the selected disk has no unique Qp-rational lift
    """
    p = _validate_prime(data.p)
    k = GF(p)
    supplied = tuple(points)
    if any(not isinstance(point, ColemanIntegrationPoint)
           for point in supplied):
        raise TypeError(
            "supplied points must be ColemanIntegrationPoint objects"
        )
    reduction = reduction_points(data)
    r_mod_p = data.r.change_ring(k)
    lifted = []
    for residue_point in reduction:
        matches = [point for point in supplied
                   if _same_reduction(point, residue_point, k)]
        if len(matches) > 1:
            raise ValueError("multiple supplied points lie in one residue disk")
        if matches:
            lifted.append(matches[0])
        elif (not residue_point.infinity and residue_point.index == 0
              and r_mod_p(residue_point.x) != 0):
            lifted.append(_lift_good_affine(residue_point, data, k))
        else:
            try:
                lifted.append(_lift_normalized_residue(residue_point, data, k))
            except (ArithmeticError, NotImplementedError, TypeError,
                    ValueError, ZeroDivisionError):
                if not skip_unsupported:
                    raise
    return lifted, data


def _affine_rational_x_values(Q, bound):
    r"""Return distinct x-coordinates found by an affine point search.

    TESTS::

        sage: from sage.schemes.curves.coleman.applications import _affine_rational_x_values
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: 0 in _affine_rational_x_values(y^2-x, 2)
        True
    """
    affine_space = AffineSpace(QQ, 2, names=("x", "y"))
    x, y = affine_space.gens()
    equation = sum((QQ(coefficient) * x**j * y**i
                    for i, polynomial in enumerate(Q.list())
                    for j, coefficient in enumerate(polynomial.list())),
                   affine_space.coordinate_ring().zero())
    curve = affine_space.subscheme([equation])
    x_values = []
    for point in curve.rational_points(bound=bound):
        value = QQ(point[0])
        if value not in x_values:
            x_values.append(value)
    return x_values


def rational_points(data, bound):
    r"""Search for rational points and retain their normalized branches.

    An affine height search is used only to find candidate `x`-coordinates.
    The places above each candidate are then decomposed in the exact function
    field, so two branches at a singular point of the plane model are not
    conflated.  Every rational place above infinity is included as well.  As
    with the underlying affine point search, the finite part is not guaranteed
    to be complete.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.auxiliary import (auxiliary_polynomials,
        ....:     integral_basis_matrices)
        sage: from sage.schemes.curves.coleman.applications import rational_points
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: Q = y^2 - (x^3 - 10*x + 9)
        sage: W0, Winf = integral_basis_matrices(Q)
        sage: data = SimpleNamespace(Q=Q, p=5, N=8, W0=W0, Winf=Winf,
        ....:                        r=auxiliary_polynomials(Q)[0])
        sage: points = rational_points(data, 10)
        sage: len(points), sum(point.infinity for point in points)
        (4, 1)

    Point search on a singular plane model retains both normalized branches::

        sage: Q = y^2 - x^2*(x+1)
        sage: W0, Winf = integral_basis_matrices(Q)
        sage: data = SimpleNamespace(Q=Q, p=5, N=8, W0=W0, Winf=Winf,
        ....:                        r=auxiliary_polynomials(Q)[0])
        sage: node = [P for P in rational_points(data, 3)
        ....:         if not P.infinity and not P.x]
        sage: len(node), {ZZ(P.b[1].residue()) for P in node}
        (2, {1, 4})
    """
    bound = ZZ(bound)
    if bound <= 0:
        raise ValueError("bound must be positive")
    p = _validate_prime(data.p)
    K, L = _function_field_model(data.Q)
    x = K.gen()
    finite_basis = _exact_basis_functions(data.W0, L)
    infinite_basis = _exact_basis_functions(data.Winf, L)
    base_order = K.maximal_order()
    finite_order = _maximal_order_with_known_basis(L, finite_basis)

    points = []
    for value in _affine_rational_x_values(data.Q, bound):
        decomposition = finite_order.decomposition(base_order.ideal(x - value))
        places = [ideal.place() for ideal, degree, _ in decomposition
                  if degree == 1]
        at_infinity = value.valuation(p) < 0
        stored_x = 1 / value if at_infinity else value
        basis = infinite_basis if at_infinity else finite_basis
        for place in places:
            values = [QQ(function.evaluate(place)) for function in basis]
            points.append(point_from_basis_coordinates(
                stored_x, values, at_infinity, data
            ))

    inverse_field, _, to_inverse = L._inversion_isomorphism()
    inverse_basis = tuple(to_inverse(function) for function in infinite_basis)
    inverse_order = _maximal_order_with_known_basis(inverse_field, inverse_basis)
    inverse_x = inverse_field.base_field().gen()
    inverse_base_order = inverse_field.base_field().maximal_order()
    decomposition = inverse_order.decomposition(
        inverse_base_order.ideal(inverse_x)
    )
    for ideal, degree, _ in decomposition:
        if degree != 1:
            continue
        place = ideal.place()
        values = [QQ(to_inverse(function).evaluate(place))
                  for function in infinite_basis]
        points.append(point_from_basis_coordinates(0, values, True, data))
    return points
