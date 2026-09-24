# sage.doctest: needs sage.rings.padics
r"""
Coleman integration on general plane curves

This module contains the Frobenius linear-system step and evaluations of the
three exact primitives produced by cohomological reduction.  The fast core
handles finite good points directly; the public entry points dispatch bad,
ramified, and infinite endpoints to the general local-parameter layer.

"""

from sage.matrix.constructor import identity_matrix
from sage.modules.free_module_element import vector

from sage.rings.infinity import infinity
from sage.rings.integer_ring import ZZ
from sage.rings.padics.factory import Qp
from sage.rings.rational_field import QQ

from .cohomology import _evaluate_rational_function
from .points import (
    ColemanIntegrationPoint,
    ColemanTangentialPoint,
    affine_coordinates,
    are_in_same_residue_disk,
    is_in_bad_residue_disk,
    point_from_affine_coordinates,
    point_from_good_affine_coordinates,
)


def _truncate_vector(values, precision):
    """Return ``values`` with every entry capped at absolute ``precision``.

    TESTS::

        sage: from sage.schemes.curves.coleman.integration import _truncate_vector
        sage: K = Qp(5, 8)
        sage: [x.precision_absolute() for x in _truncate_vector(vector(K, [1, 2]), 3)]
        [3, 3]
    """
    precision = max(ZZ.zero(), ZZ(precision))
    return vector(values.base_ring(), [
        value.add_bigoh(precision) for value in values
    ])


def _truncate_scalar(value, precision):
    """Return ``value`` capped at absolute ``precision``.

    TESTS::

        sage: from sage.schemes.curves.coleman.integration import _truncate_scalar
        sage: _truncate_scalar(Qp(5, 8)(1), 3).precision_absolute()
        3
    """
    return value.add_bigoh(max(ZZ.zero(), ZZ(precision)))


def _evaluate_model_at_x(Q, x_value):
    """Specialize the coefficients in ``x`` of ``Q`` at ``x_value``.

    TESTS::

        sage: from sage.schemes.curves.coleman.integration import _evaluate_model_at_x
        sage: R.<x> = QQ[]; S.<y> = R[]; K = Qp(5, 6)
        sage: _evaluate_model_at_x(y^2 - x, K(1))(K(1))
        O(5^6)
    """
    field = x_value.parent()
    polynomial_ring = Q.parent().change_ring(field)
    return polynomial_ring([
        field(coefficient(x_value)) for coefficient in Q.list()
    ])


def _newton_root(polynomial, initial, precision=None):
    """Lift a simple p-adic root by Newton iteration.

    TESTS::

        sage: from sage.schemes.curves.coleman.integration import _newton_root
        sage: K = Qp(5, 6); R.<z> = K[]
        sage: root = _newton_root(z^2 - 6, K(1))
        sage: (root^2 - 6).valuation()
        6
    """
    root = polynomial.base_ring()(initial)
    derivative = polynomial.derivative()
    target = (precision if precision is not None
              else polynomial.base_ring().precision_cap())
    previous_valuation = -1
    for _ in range(max(8, 2 * ZZ(target).nbits() + 4)):
        value = polynomial(root)
        if not value:
            return root
        derivative_value = derivative(root)
        if not derivative_value:
            raise ValueError("the selected root is not simple")
        valuation = value.valuation()
        if valuation >= target:
            return root
        if valuation <= previous_valuation and previous_valuation >= 0:
            raise ArithmeticError("p-adic Newton iteration did not improve")
        previous_valuation = valuation
        root -= value / derivative_value
    if polynomial(root).valuation() < target:
        raise ArithmeticError("p-adic Newton iteration did not converge")
    return root


def _root_certificate(polynomial, root, *, coefficient_precision=None):
    r"""
    Certify how closely ``root`` approximates a root of ``polynomial``.

    The coefficients of ``polynomial`` may be inexact.  The bound holds for
    every polynomial whose coefficients agree with them to their stated
    absolute precision.  It is read off the Newton polygon of
    ``polynomial(center + X)``, where ``center`` is ``root`` lifted to full
    precision, so the precision that a root finder attached to ``root`` is
    never trusted.  Valuations are normalized so that a uniformizer of the
    coefficient ring has valuation one.

    OUTPUT:

    A triple ``(center, digits, unique)``.  If ``unique`` is ``True``,
    Hensel's lemma applies: exactly one root is strictly closer to ``center``
    than all the others, and it agrees with ``center`` to at least ``digits``.
    Otherwise ``digits`` bounds the distance from ``center`` to every root
    in its residue disk, or is ``None`` when that disk contains no root.  The
    bound ``digits`` is rational, or ``+Infinity`` for an exact root.

    EXAMPLES:

    Two roots that agree modulo `5^3` each keep only seven certified digits,
    whatever precision a root finder reports::

        sage: from sage.schemes.curves.coleman.integration import _root_certificate
        sage: R.<z> = Zp(5, 10)[]
        sage: f = (z - 1)*(z - 126)
        sage: _root_certificate(f, 1)[1:], _root_certificate(f, 126)[1:]
        ((7, True), (7, True))

    A cluster of roots is bounded through every root in its residue disk::

        sage: _root_certificate((z - 1)^2, 1)[1:]
        (5, False)
        sage: _root_certificate(z^2, 0, coefficient_precision=3)[1:]
        (3/2, False)

    A point whose residue disk contains no root is rejected::

        sage: _root_certificate(f, 2)[1:]
        (None, False)

    Over a ramified extension the bound is measured in powers of the
    uniformizer::

        sage: K = Qp(5, 8); U.<u> = K[]; E.<pi> = K.extension(u^3 - 5)
        sage: W.<w> = E[]
        sage: _root_certificate((w - pi)*(w - pi - pi^4), pi)[1:]
        (22, True)
    """
    center = polynomial.base_ring()(root).lift_to_precision()
    shifted = polynomial(polynomial.parent().gen() + center)
    coefficients = shifted.list()
    lower = [coefficient.valuation() for coefficient in coefficients]
    known = [bool(coefficient) for coefficient in coefficients]
    if coefficient_precision is not None:
        coefficient_precision = ZZ(coefficient_precision)
        if coefficient_precision <= 0:
            raise ValueError("coefficient_precision must be positive")
        lower = [value if flag else coefficient_precision
                 for value, flag in zip(lower, known)]
    degree = len(coefficients) - 1

    # Hensel: the segment from the constant term to a known linear term is
    # steeper than every later segment, so it isolates exactly one root.
    if degree >= 1 and known[1]:
        derivative_valuation = ZZ(lower[1])
        if lower[0] == infinity:
            return center, infinity, True
        distance = ZZ(lower[0]) - derivative_valuation
        separations = [QQ(derivative_valuation - lower[k]) / (k - 1)
                       for k in range(2, degree + 1) if lower[k] != infinity]
        if not separations or distance > max(separations):
            return center, distance, True

    # Otherwise bound all roots of positive valuation after the shift.  The
    # content is only certain when no inexact coefficient could lower it.
    known_valuations = [lower[k] for k in range(degree + 1) if known[k]]
    if not known_valuations:
        return center, ZZ.zero(), False
    content = min(known_valuations)
    if any(value < content for value in lower):
        return center, ZZ.zero(), False
    cluster = min(k for k in range(degree + 1)
                  if known[k] and lower[k] == content)
    if not cluster:
        return center, None, False
    bounds = [QQ(lower[k] - content) / (cluster - k)
              for k in range(cluster) if lower[k] != infinity]
    return center, (min(bounds) if bounds else infinity), False


def frobenius_point(P, data):
    r"""Return the Frobenius image of a finite good affine point ``P``.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.integration import frobenius_point
        sage: from sage.schemes.curves.coleman.points import point_from_good_affine_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: Q = y^2 - (x^3 - 10*x + 9)
        sage: data = SimpleNamespace(Q=Q, p=5, N=6,
        ....:     W0=identity_matrix(QQ, 2), r=4*x^3 - 40*x + 36)
        sage: P = point_from_good_affine_coordinates(0, 3, data)
        sage: FP = frobenius_point(P, data)
        sage: FP.x, (FP.b[1]^2 - (FP.x^3 - 10*FP.x + 9)).valuation()
        (0, 6)
    """
    if P.infinity or is_in_bad_residue_disk(P, data):
        raise NotImplementedError(
            "Frobenius at bad or infinite points needs ramified local data"
        )
    x0, y0 = affine_coordinates(P, data)
    x_frobenius = x0**data.p
    specialized = _evaluate_model_at_x(data.Q, x_frobenius)
    y_frobenius = _newton_root(
        specialized, y0**data.p, precision=data.N
    )
    return point_from_good_affine_coordinates(
        x_frobenius, y_frobenius, data
    )


def teichmuller_point(P, data, precision=None):
    r"""Return the Frobenius-fixed lift in the residue disk of a good point.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.integration import teichmuller_point
        sage: from sage.schemes.curves.coleman.points import point_from_good_affine_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: Q = y^2 - (x^3 - 10*x + 9)
        sage: data = SimpleNamespace(Q=Q, p=5, N=6,
        ....:     W0=identity_matrix(QQ, 2), r=4*x^3 - 40*x + 36)
        sage: P = point_from_good_affine_coordinates(0, 3, data)
        sage: T = teichmuller_point(P, data)
        sage: T.x, (T.b[1]^2 - (T.x^3 - 10*T.x + 9)).valuation()
        (0, 6)
    """
    if P.infinity or is_in_bad_residue_disk(P, data):
        raise ValueError("the point must be finite and good")
    precision = data.N if precision is None else ZZ(precision)
    field = P.x.parent()
    x_teichmuller = field.teichmuller(P.x)
    _, y0 = affine_coordinates(P, data)
    specialized = _evaluate_model_at_x(data.Q, x_teichmuller)
    y_teichmuller = _newton_root(
        specialized, y0, precision=precision
    )
    return point_from_good_affine_coordinates(
        x_teichmuller, y_teichmuller, data
    )


def _series_terms(f):
    """Iterate through represented terms of a finite Laurent series.

    TESTS::

        sage: from sage.schemes.curves.coleman.integration import _series_terms
        sage: L.<u> = LaurentSeriesRing(QQ)
        sage: list(_series_terms(u^-2 + 3*u))
        [(-2, 1), (1, 3)]
    """
    if not f:
        return
    valuation = ZZ(f.valuation())
    for offset, coefficient in enumerate(f.list()):
        if coefficient:
            yield valuation + offset, coefficient


def _coefficient_precision(values, p, default):
    """Return conservative absolute precision after coefficient loss.

    TESTS::

        sage: from sage.schemes.curves.coleman.integration import _coefficient_precision
        sage: _coefficient_precision([QQ(1)/25, QQ(3)], 5, 8)
        6
    """
    valuations = [QQ(value).valuation(p) for value in values if value]
    return ZZ(default + (min(valuations) if valuations else 0))


def evaluate_finite_primitive(f0, P, data):
    r"""Evaluate a finite-reduction primitive at a finite good point.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.integration import evaluate_finite_primitive
        sage: from sage.schemes.curves.coleman.points import point_from_good_affine_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = SimpleNamespace(Q=y^2 - (x^3 - 10*x + 9), p=5, N=6,
        ....:     W0=identity_matrix(QQ, 2), r=4*x^3 - 40*x + 36)
        sage: P = point_from_good_affine_coordinates(0, 3, data)
        sage: L.<u> = LaurentSeriesRing(R)
        sage: evaluate_finite_primitive(vector(L, [x + 1, 0]), P, data)
        (1 + O(5^6), 6)
    """
    if P.infinity or is_in_bad_residue_disk(P, data):
        raise NotImplementedError("finite primitive evaluation currently needs a good affine point")
    field = P.x.parent()
    z0 = field(data.r(P.x) / data.r.leading_coefficient())
    result = field.zero()
    rational_coefficients = []
    for basis_value, entry in zip(P.b, f0):
        for exponent, polynomial in (_series_terms(entry) or []):
            rational_coefficients.extend(polynomial.list())
            result += field(polynomial(P.x)) * z0**exponent * basis_value
    return result, _coefficient_precision(rational_coefficients, data.p, data.N)


def evaluate_infinite_primitive(finf, P, data):
    r"""Evaluate an infinity-reduction primitive at a finite good point.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.integration import evaluate_infinite_primitive
        sage: from sage.schemes.curves.coleman.points import point_from_good_affine_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]; K.<u> = FunctionField(QQ)
        sage: data = SimpleNamespace(Q=y^2 - (x^3 - 10*x + 9), p=5, N=6,
        ....:     W0=identity_matrix(K, 2), Winf=identity_matrix(K, 2),
        ....:     r=4*R.gen()^3 - 40*R.gen() + 36)
        sage: P = point_from_good_affine_coordinates(0, 3, data)
        sage: L.<u> = LaurentSeriesRing(QQ)
        sage: evaluate_infinite_primitive(vector(L, [1 + u, 0]), P, data)
        (1 + O(5^6), 6)
    """
    if P.infinity or is_in_bad_residue_disk(P, data):
        raise NotImplementedError("infinite primitive evaluation currently needs a good affine point")
    field = P.x.parent()
    function_field = data.W0.base_ring()
    x = function_field.gen()
    coefficients_as_functions = []
    rational_coefficients = []
    for entry in finf:
        value = function_field.zero()
        for exponent, coefficient in (_series_terms(entry) or []):
            rational_coefficients.append(coefficient)
            value += function_field(coefficient) * x**exponent
        coefficients_as_functions.append(value)
    coefficients_in_finite_basis = (
        vector(function_field, coefficients_as_functions)
        * (data.Winf * data.W0.inverse())
    )
    evaluated = vector(field, [
        _evaluate_rational_function(entry, P.x)
        for entry in coefficients_in_finite_basis
    ])
    result = evaluated * vector(field, P.b)
    return result, _coefficient_precision(rational_coefficients, data.p, data.N)


def evaluate_terminal_primitive(fend, P, data):
    r"""Evaluate a polynomial primitive in the finite integral basis.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.integration import evaluate_terminal_primitive
        sage: from sage.schemes.curves.coleman.points import point_from_good_affine_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = SimpleNamespace(Q=y^2 - (x^3 - 10*x + 9), p=5, N=6,
        ....:     W0=identity_matrix(QQ, 2), r=4*x^3 - 40*x + 36)
        sage: P = point_from_good_affine_coordinates(0, 3, data)
        sage: evaluate_terminal_primitive(vector(R, [x + 1, 2*x]), P, data)
        (1 + O(5^6), 6)
    """
    if P.infinity:
        raise NotImplementedError("terminal primitive evaluation at infinity is not implemented")
    field = P.x.parent()
    result = field.zero()
    rational_coefficients = []
    for basis_value, polynomial in zip(P.b, fend):
        rational_coefficients.extend(polynomial.list())
        result += field(polynomial(P.x)) * basis_value
    return result, _coefficient_precision(rational_coefficients, data.p, data.N)


def _zero_tiny(P, data):
    """Return a zero tiny-integral vector over the point's p-adic field.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.integration import _zero_tiny
        sage: from sage.schemes.curves.coleman.points import ColemanIntegrationPoint
        sage: K = Qp(5, 6); P = ColemanIntegrationPoint(K(0), (K(1), K(1)))
        sage: _zero_tiny(P, SimpleNamespace(basis=[1, 2]))
        (0, 0)
    """
    return vector(P.x.parent(), len(data.basis))


def _common_point_field(P1, P2, p):
    """Coerce Qp-rational points to a shared precision parent if necessary.

    TESTS::

        sage: from sage.schemes.curves.coleman.integration import _common_point_field
        sage: from sage.schemes.curves.coleman.points import ColemanIntegrationPoint
        sage: K4 = Qp(5, 4); K6 = Qp(5, 6)
        sage: P = ColemanIntegrationPoint(K4(0), (K4(1), K4(1)))
        sage: Q = ColemanIntegrationPoint(K6(0), (K6(1), K6(1)))
        sage: P, Q = _common_point_field(P, Q, 5)
        sage: P.x.parent().precision_cap(), Q.x.parent().precision_cap()
        (6, 6)

    Tangential metadata is preserved during coercion::

        sage: from sage.schemes.curves.coleman.points import (
        ....:     ColemanTangentialPoint, tangential_point)
        sage: P4 = ColemanIntegrationPoint(K4(0), (K4(1), K4(1)))
        sage: T, Q = _common_point_field(tangential_point(P4, 1 + 5), Q, 5)
        sage: isinstance(T, ColemanTangentialPoint), T.tangent_scale.parent() is Q.x.parent()
        (True, True)
    """
    if P1.x.parent() == P2.x.parent():
        return P1, P2
    parents = (P1.x.parent(), P2.x.parent())
    if any(not hasattr(parent, "prime") or parent.prime() != p
           for parent in parents):
        raise TypeError("the endpoints must have compatible p-adic fields")
    field = Qp(p, prec=max(parent.precision_cap() for parent in parents))

    def coerce(point):
        point_class = (ColemanTangentialPoint
                       if isinstance(point, ColemanTangentialPoint)
                       else ColemanIntegrationPoint)
        keywords = {}
        if isinstance(point, ColemanTangentialPoint):
            keywords['tangent_scale'] = field(point.tangent_scale)
        return point_class(
            x=field(point.x),
            b=tuple(field(value) for value in point.b),
            infinity=point.infinity,
            **keywords,
        )

    return coerce(P1), coerce(P2)


def coleman_integrals_on_basis(P1, P2, data, *, e=None):
    r"""Compute Coleman integrals between represented curve points.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.integration import coleman_integrals_on_basis
        sage: from sage.schemes.curves.coleman.points import point_from_good_affine_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 3, genus=1)
        sage: P = point_from_good_affine_coordinates(0, 3, data)
        sage: coleman_integrals_on_basis(P, P, data)
        ((O(5^3), O(5^3)), 3)

    At an anomalous prime, both the reported precision and the displayed
    entries include the loss from inverting Frobenius minus identity::

        sage: anomalous = coleman_data(y^2-(x^5-x+1), 7, 6, genus=2)
        sage: A = point_from_good_affine_coordinates(-1, 1, anomalous)
        sage: B = point_from_good_affine_coordinates(0, 1, anomalous)
        sage: values, precision = coleman_integrals_on_basis(A, B, anomalous)
        sage: precision, [value.precision_absolute() for value in values]
        (4, [4, 4, 4, 4])
        sage: K = Qp(7, 10); Kx.<x> = K[]
        sage: H = HyperellipticCurve(x^5 - x + 1)
        sage: reference = H.coleman_integrals_on_basis(
        ....:     H(K(-1), K(1)), H(K(0), K(1)))
        sage: all((K(values[i]) - 2*reference[i]).valuation() >= precision
        ....:     for i in range(4))
        True

    A point close to an irrational branch point retains enough starting
    precision for the ramified endpoint lift::

        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: bolza = coleman_data(y^2 - (x^5 - x), 13, 5, genus=2)
        sage: K = Qp(13, 8); T.<z> = K[]
        sage: i = next(root for root, _ in (z^2 + 1).roots()
        ....:          if root.residue() == 5)
        sage: x0 = i + 13^2
        sage: y0 = next(root for root, _ in (z^2 - (x0^5 - x0)).roots()
        ....:           if (root/13).residue() == 2)
        sage: near_branch = point_from_good_affine_coordinates(
        ....:     x0, y0, bolza)
        sage: y1 = next(root for root, _ in (z^2 - 30).roots()
        ....:           if root.residue() == 2)
        sage: ordinary = point_from_good_affine_coordinates(2, y1, bolza)
        sage: values, precision = coleman_integrals_on_basis(
        ....:     near_branch, ordinary, bolza)
        sage: precision >= 4, [ZZ(value.lift()) % 13^4 for value in values]
        (True, [5278, 26741, 9361, 7798])
    """
    P1, P2 = _common_point_field(P1, P2, data.p)
    if (is_in_bad_residue_disk(P1, data)
            or is_in_bad_residue_disk(P2, data)):
        from .general_integration import coleman_integrals_on_basis as general
        return general(P1, P2, data, e=e)

    from .local import tiny_integrals_on_basis

    field = P1.x.parent()
    if are_in_same_residue_disk(P1, P2, data):
        values, precision = tiny_integrals_on_basis(P1, P2, data)
        return _truncate_vector(values, precision), precision

    FP1 = frobenius_point(P1, data)
    FP2 = frobenius_point(P2, data)
    tiny1, precision1 = tiny_integrals_on_basis(P1, FP1, data)
    tiny2, precision2 = tiny_integrals_on_basis(P2, FP2, data)

    rhs = []
    precision = min(precision1, precision2)
    for i in range(len(data.basis)):
        f0_P1, n0_P1 = evaluate_finite_primitive(data.f0_list[i], P1, data)
        f0_P2, n0_P2 = evaluate_finite_primitive(data.f0_list[i], P2, data)
        finf_P1, ni_P1 = evaluate_infinite_primitive(data.finf_list[i], P1, data)
        finf_P2, ni_P2 = evaluate_infinite_primitive(data.finf_list[i], P2, data)
        fend_P1, ne_P1 = evaluate_terminal_primitive(data.fend_list[i], P1, data)
        fend_P2, ne_P2 = evaluate_terminal_primitive(data.fend_list[i], P2, data)
        precision = min(precision, n0_P1, n0_P2, ni_P1, ni_P2,
                        ne_P1, ne_P2)
        rhs.append(f0_P1 - f0_P2 + finf_P1 - finf_P2
                   + fend_P1 - fend_P2 - tiny1[i] + tiny2[i])

    system = data.frobenius_matrix - identity_matrix(QQ, len(data.basis))
    if not system.is_invertible():
        raise ArithmeticError("Frobenius minus identity is singular")
    inverse_transpose = system.inverse().transpose().change_ring(field)
    integrals = vector(field, rhs) * inverse_transpose
    determinant_loss = ZZ(system.det().valuation(data.p))
    precision = max(ZZ.zero(), min(
        ZZ(precision) - determinant_loss,
        ZZ(data.N) - 2 * determinant_loss - ZZ(data.delta),
    ))
    return _truncate_vector(integrals, precision), precision


def coleman_integrals_on_basis_divisors(D, E, data, *, e=None):
    r"""Integrate the cohomology basis between two ordered zero cycles.

    ``D`` and ``E`` are equally sized iterables of affine ``(x, y)`` pairs.
    The returned vector is the sum of the basis integrals; precision remains
    encoded in its p-adic entries.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.integration import coleman_integrals_on_basis_divisors
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 3, genus=1)
        sage: coleman_integrals_on_basis_divisors([(0, 3)], [(0, 3)], data)
        (O(5^3), O(5^3))
    """
    D = list(D)
    E = list(E)
    if len(D) != len(E):
        raise ValueError("D and E must have the same number of points")
    if not D:
        return vector(Qp(data.p, prec=data.N), len(data.basis))

    total = None
    for first, second in zip(D, E):
        value, _ = coleman_integrals_on_basis(
            point_from_affine_coordinates(first, data),
            point_from_affine_coordinates(second, data),
            data,
            e=e,
        )
        total = value if total is None else total + value
    return total


def coleman_integral(P1, P2, differential, data, *, basis_integrals=None,
                     basis_precision=None, e=None):
    r"""Integrate an arbitrary represented differential between points.

    ``differential`` uses the same radix-vector representation as
    :func:`~sage.schemes.curves.coleman.reductions.reduce_with_functions`.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.integration import coleman_integral
        sage: from sage.schemes.curves.coleman.points import point_from_good_affine_coordinates
        sage: from sage.schemes.curves.coleman.reductions import polynomial_vector_to_laurent_series
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 3, genus=1)
        sage: P = point_from_good_affine_coordinates(0, 3, data)
        sage: zero = polynomial_vector_to_laurent_series(vector(R, [0, 0]), data)
        sage: coleman_integral(P, P, zero, data)
        (O(5^3), 3)

    A differential with a third-kind component cannot be projected silently
    onto the proper-curve cohomology basis::

        sage: Q = point_from_good_affine_coordinates(8, 21, data)
        sage: third_kind = polynomial_vector_to_laurent_series(
        ....:     vector(R, [x^2+x-9, 0]), data)
        sage: coleman_integral(P, Q, third_kind, data)
        Traceback (most recent call last):
        ...
        ValueError: the differential has components outside the selected cohomology basis; use an open-curve basis

    With the open-curve basis, the same third-kind integral agrees with the
    p-adic logarithm::

        sage: open_data = coleman_data(
        ....:     y^2 - (x^3 - 10*x + 9), 5, 6,
        ....:     use_open_curve=True, genus=1)
        sage: open_P = point_from_good_affine_coordinates(0, 3, open_data)
        sage: open_Q = point_from_good_affine_coordinates(8, 21, open_data)
        sage: open_form = polynomial_vector_to_laurent_series(
        ....:     vector(R, [x^2+x-9, 0]), open_data)
        sage: value, precision = coleman_integral(
        ....:     open_P, open_Q, open_form, open_data)
        sage: precision, (value - Qp(5, 6)(7).log()).valuation()
        (6, 6)
    """
    from .reductions import reduce_with_functions

    coefficients, f0, finf, fend = reduce_with_functions(
        differential, data.Q, data.p, data.N, data.Nmax, data.r,
        data.W0, data.Winf, data.G0, data.Ginf,
        data.finite_reduction_matrices, data.infinite_reduction_matrices,
        data.basis, data.integrals, data.quotient_map
    )
    if basis_integrals is None:
        basis_integrals, basis_precision = coleman_integrals_on_basis(
            P1, P2, data, e=e
        )
    elif basis_precision is None:
        basis_precision = data.N

    if (is_in_bad_residue_disk(P1, data)
            or is_in_bad_residue_disk(P2, data)):
        from .general_integration import (
            evaluate_finite_primitive as finite_evaluation,
        )
        from .general_integration import (
            evaluate_infinite_primitive as infinite_evaluation,
        )
        from .general_integration import (
            evaluate_terminal_primitive as terminal_evaluation,
        )
    else:
        finite_evaluation = evaluate_finite_primitive
        infinite_evaluation = evaluate_infinite_primitive
        terminal_evaluation = evaluate_terminal_primitive
    f0_P1, n0_P1 = finite_evaluation(f0, P1, data)
    f0_P2, n0_P2 = finite_evaluation(f0, P2, data)
    finf_P1, ni_P1 = infinite_evaluation(finf, P1, data)
    finf_P2, ni_P2 = infinite_evaluation(finf, P2, data)
    fend_P1, ne_P1 = terminal_evaluation(fend, P1, data)
    fend_P2, ne_P2 = terminal_evaluation(fend, P2, data)
    value = (f0_P2 - f0_P1 + finf_P2 - finf_P1
             + fend_P2 - fend_P1)
    precision = min(basis_precision, n0_P1, n0_P2, ni_P1, ni_P2,
                    ne_P1, ne_P2)
    for coefficient, integral in zip(coefficients, basis_integrals):
        value += coefficient * integral
        if coefficient:
            precision = min(
                precision,
                basis_precision + ZZ(QQ(coefficient).valuation(data.p))
            )
    precision = max(ZZ.zero(), ZZ(precision))
    return _truncate_scalar(value, precision), precision
