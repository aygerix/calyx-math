# sage.doctest: needs sage.rings.padics
r"""
Chabauty--Coleman linear algebra for general plane curves

This module provides finite-precision kernels, annihilating differentials,
and disk-wise zero finding using local power-series integration.

"""

from sage.matrix.constructor import matrix

from sage.rings.infinity import infinity
from sage.rings.integer_ring import ZZ
from sage.rings.padics.factory import Qp, Zp
from sage.rings.padics.precision_error import PrecisionError
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ

from .applications import padic_points
from .applications import rational_points as _rational_points
from .integration import _root_certificate, coleman_integrals_on_basis
from .local import tiny_integrals_on_basis_to_parameter
from .points import (
    ColemanIntegrationPoint,
    are_in_same_residue_disk,
    is_bad_residue_disk_center,
    is_in_bad_residue_disk,
    tangential_point,
)


def roots_in_padic_integers(f, *, coefficient_precision=None):
    r"""Find roots of a nonzero polynomial over a finite-precision p-adic ring.

    Candidates come from Sage's precision-tracking root finder, which keeps
    a root cluster that the available precision cannot separate.  Each
    candidate is then certified by
    :func:`~sage.schemes.curves.coleman.integration._root_certificate`, so
    the certified digits hold for every polynomial that agrees with ``f`` to
    the precision of its coefficients.  Each output is a pair
    ``(root, certified_digits)``, and ``root`` carries exactly
    ``certified_digits`` digits of absolute precision.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.chabauty import roots_in_padic_integers
        sage: R.<z> = Zp(5, 5)[]
        sage: roots = roots_in_padic_integers((z-1)*(z-2))
        sage: sorted(ZZ(root.residue()) for root, _ in roots)
        [1, 2]

    Roots in one residue class are both retained.  They agree modulo `5^3`,
    so each is certified to only seven of the ten available digits::

        sage: R.<z> = Zp(5, 10)[]
        sage: roots = roots_in_padic_integers((z-1)*(z-126))
        sage: sorted((ZZ(root.lift()), digits) for root, digits in roots)
        [(1, 7), (126, 7)]
        sage: all(max((root - 1).valuation(), (root - 126).valuation()) >= digits
        ....:     for root, digits in roots)
        True

    Imprecise coefficients limit the certified digits, and an unresolved
    double root is certified only to half the precision::

        sage: S.<w> = Zp(5, 10)[]
        sage: low_precision = w^2 - 3*w
        sage: sorted(digits for _, digits in roots_in_padic_integers(
        ....:     low_precision, coefficient_precision=3))
        [3, 3]
        sage: roots_in_padic_integers(w^2, coefficient_precision=3)
        [(O(5^2), 2)]
    """
    if not f:
        raise ValueError("f must be nonzero")
    polynomial_ring = f.parent()
    base_ring = polynomial_ring.base_ring()
    p = base_ring.prime()
    coefficient_valuations = [
        ZZ(coefficient.valuation()) for coefficient in f.list()
        if coefficient.valuation() != infinity
    ]
    content_valuation = min(coefficient_valuations)
    f = polynomial_ring([coefficient / p**content_valuation
                         for coefficient in f.list()])
    coefficient_precisions = []
    for coefficient in f.list():
        entry_precision = coefficient.precision_absolute()
        if entry_precision != infinity:
            coefficient_precisions.append(ZZ(entry_precision))
    working_precision = min(
        [ZZ(base_ring.precision_cap())] + coefficient_precisions
    )
    if coefficient_precision is not None:
        coefficient_precision = ZZ(coefficient_precision) - content_valuation
        working_precision = min(working_precision, coefficient_precision)
    if working_precision <= 0:
        raise PrecisionError(
            "the polynomial has no coefficient precision after normalization"
        )

    # Sage's Newton polygon rejects an inexact leading coefficient.  Terms
    # beyond the last nonzero coefficient vanish modulo the working
    # precision on the disk, so they are omitted when finding candidates but
    # kept when certifying them.
    coefficients = f.list()
    known = [degree for degree, coefficient in enumerate(coefficients)
             if coefficient]
    if not known:
        raise PrecisionError(
            "the polynomial has no nonzero coefficient at the available precision"
        )
    candidates = polynomial_ring(coefficients[:known[-1] + 1])

    output = []
    for root, _ in candidates.roots(algorithm="sage"):
        center, digits, unique = _root_certificate(
            f, root, coefficient_precision=coefficient_precision
        )
        # A candidate is discarded only when the certificate proves that its
        # residue disk contains no root.
        if digits is None or (unique and digits <= 0):
            continue
        if digits == infinity:
            digits = working_precision
        digits = ZZ(QQ(digits).ceil())
        output.append((center.add_bigoh(digits), digits))
    return output


def basis_kernel(A):
    r"""Return a row basis for the finite-precision left kernel of ``A``.

    The rows of ``A`` index differentials, so the required annihilators are
    vectors ``v`` satisfying ``v*A = 0``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.chabauty import basis_kernel
        sage: K = Qp(5, 6); A = matrix(K, [[1, 2], [2, 4]])
        sage: kernel = basis_kernel(A)
        sage: len(kernel), kernel[0] * A
        (1, (O(5^6), O(5^6)))
    """
    if A.nrows() == 0:
        return []
    if A.ncols() == 0:
        return list((A.base_ring()**A.nrows()).basis())
    nonzero = [entry for entry in A.list() if entry]
    minimum = min([ZZ.zero()] + [ZZ(entry.valuation()) for entry in nonzero])
    scaled = A.base_ring().prime()**(-minimum) * A
    return list(scaled.left_kernel().basis())


def vanishing_differentials(points, data, *, e=None):
    r"""Compute regular forms annihilating supplied point differences.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.chabauty import vanishing_differentials
        sage: from sage.schemes.curves.coleman.points import ColemanIntegrationPoint
        sage: K = Qp(5, 6); P = ColemanIntegrationPoint(K(0), (K(1), K(0)))
        sage: forms, integrals, precisions = vanishing_differentials(
        ....:     [P], SimpleNamespace(genus=2))
        sage: len(forms), integrals, precisions
        (2, [], [])
    """
    if not points:
        raise ValueError("at least one point is required")
    genus = ZZ(data.genus)
    if genus <= 0:
        return [], [], []

    integrals = []
    precisions = []
    for point in points[1:]:
        values, precision = coleman_integrals_on_basis(
            points[0], point, data, e=e
        )
        integrals.append(values)
        precisions.append(ZZ(precision))
    if not integrals:
        field = points[0].x.parent()
        empty = matrix(field, genus, 0)
        return basis_kernel(empty), integrals, precisions

    working_precision = min(precisions)
    if working_precision <= 0:
        raise ArithmeticError("the Coleman integrals have no certified precision")
    field = Qp(data.p, prec=working_precision)
    integral_matrix = matrix(
        field, genus, len(integrals),
        lambda i, j: field(integrals[j][i])
    )
    return basis_kernel(integral_matrix), integrals, precisions


def _series_linear_combination(coefficients, base_integrals, local_integrals):
    r"""Form one Chabauty function in the local parameter.

    TESTS::

        sage: from sage.schemes.curves.coleman.chabauty import _series_linear_combination
        sage: T.<t> = Qp(5, 6)[[]]
        sage: _series_linear_combination([1, 2], [3, 4], vector(T, [t, t^2]))
        1 + 2*5 + O(5^6) + (1 + O(5^6))*t + (2 + O(5^6))*t^2
    """
    ring = local_integrals.base_ring()
    output = ring.zero()
    for coefficient, base, local in zip(coefficients, base_integrals,
                                        local_integrals):
        output += ring(coefficient) * (ring(base) + local)
    return output


def _integral_polynomial_in_scaled_parameter(
        series, p, precision, *, return_precision=False):
    r"""Return an integral polynomial representing ``series(p*z)``.

    The series is known to absolute ``precision`` on the disk, so every
    coefficient in ``z`` is capped at that precision, shifted by the scaling
    that makes the polynomial integral.

    TESTS::

        sage: from sage.schemes.curves.coleman.chabauty import _integral_polynomial_in_scaled_parameter
        sage: T.<t> = Qp(5, 6)[[]]
        sage: _integral_polynomial_in_scaled_parameter(1+t, 5, 6)
        (5 + O(5^6))*z + 1 + O(5^6)
        sage: h, coefficient_precision = _integral_polynomial_in_scaled_parameter(
        ....:     t/5 + t^2, 5, 6, return_precision=True)
        sage: h, coefficient_precision
        ((5^3 + O(5^7))*z^2 + (5 + O(5^7))*z, 7)
    """
    coefficients = series.list()
    nonzero = [coefficient for coefficient in coefficients if coefficient]
    minimum = min([ZZ.zero()] + [ZZ(c.valuation()) for c in nonzero])
    scale = p**(-minimum)
    certified = ZZ(precision) - minimum
    integers = Zp(p, prec=precision)
    polynomial_ring = PolynomialRing(integers, names="z")
    polynomial = polynomial_ring([
        integers(scale * coefficient * p**exponent).add_bigoh(certified)
        for exponent, coefficient in enumerate(coefficients)
    ])
    return (polynomial, certified) if return_precision else polynomial


def _annihilator_precision(annihilators, cap):
    r"""Return the finite absolute precision shared by ``annihilators``.

    Exact zero entries have infinite absolute precision and therefore do not
    lower the bound::

        sage: from sage.schemes.curves.coleman.chabauty import _annihilator_precision
        sage: K = Qp(5, 6)
        sage: rows = list((K^2).basis())
        sage: _annihilator_precision(rows, 6)
        6
    """
    finite = [
        ZZ(value.precision_absolute())
        for row in annihilators for value in row
        if value and value.precision_absolute() != infinity
    ]
    return min([ZZ(cap)] + finite)


def zeros_on_disk(P1, P2, annihilators, data, *, prec=None,
                  integral=None, e=None):
    r"""Find common zeros of Chabauty integrals in a good residue disk.

    TESTS::

        sage: from sage.schemes.curves.coleman.chabauty import (vanishing_differentials,
        ....:     zeros_on_disk)
        sage: zeros_on_disk(None, None, [], None)
        Traceback (most recent call last):
        ...
        ValueError: at least one annihilating differential is required

    Exact zero entries in a genus-two annihilator basis have infinite
    precision and are ignored when determining the finite working precision::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.points import point_from_good_affine_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^5 - x + 1), 7, 3, genus=2)
        sage: P = point_from_good_affine_coordinates(0, 1, data)
        sage: annihilators, _, _ = vanishing_differentials([P], data)
        sage: zeros_on_disk(P, P, annihilators, data)
        Traceback (most recent call last):
        ...
        ArithmeticError: all annihilating integrals vanish at the available precision
    """
    if not annihilators:
        raise ValueError("at least one annihilating differential is required")
    if integral is None:
        # The open-curve cohomology basis can contain logarithmic forms even
        # though Chabauty uses only its initial regular block.  Give any
        # central bad endpoint the canonical tangent while solving the full
        # Frobenius system, then discard the unused coordinates below.  The
        # selected regular integrals have zero residue and hence do not
        # depend on this auxiliary normalization.
        base_start = (tangential_point(P1)
                      if is_bad_residue_disk_center(P1, data) else P1)
        base_end = (tangential_point(P2)
                    if is_bad_residue_disk_center(P2, data) else P2)
        base_integrals, base_precision = coleman_integrals_on_basis(
            base_start, base_end, data, e=e
        )
    else:
        base_integrals, base_precision = integral
    local_integrals, xt, bt, local_precision = (
        tiny_integrals_on_basis_to_parameter(
            P2, data, prec=prec, indices=range(len(annihilators[0]))
        )
    )
    annihilator_precision = _annihilator_precision(annihilators, data.N)
    working_precision = min(ZZ(base_precision), ZZ(local_precision),
                            annihilator_precision)
    if working_precision <= 0:
        raise ArithmeticError("insufficient precision for disk zero finding")

    root_sets = []
    for row in annihilators:
        series = _series_linear_combination(
            row, base_integrals[:len(row)], local_integrals[:len(row)]
        )
        polynomial, coefficient_precision = (
            _integral_polynomial_in_scaled_parameter(
                series, data.p, working_precision, return_precision=True
            )
        )
        if (not polynomial or all(
                coefficient.valuation() >= working_precision
                for coefficient in polynomial.list())):
            continue
        root_sets.append(roots_in_padic_integers(
            polynomial, coefficient_precision=coefficient_precision
        ))

    if not root_sets:
        raise ArithmeticError(
            "all annihilating integrals vanish at the available precision"
        )

    common = []
    for root, digits in root_sets[0]:
        if all(any((root - candidate).valuation() >= min(digits, candidate_digits)
                   for candidate, candidate_digits in roots)
               for roots in root_sets[1:]):
            common.append((root, digits))

    field = P2.x.parent()
    points = []
    for root, _ in common:
        parameter = field(data.p * root)
        points.append(ColemanIntegrationPoint(
            x=xt(parameter),
            b=tuple(value(parameter) for value in bt),
            infinity=P2.infinity,
        ))
    return points


def effective_chabauty(data, *, rational_points=None, bound=0, rank=None,
                       skip_unsupported=False, e=None):
    r"""Run effective Chabauty over the rational residue disks.

    When the Mordell--Weil ``rank`` is supplied, it must be strictly less
    than the genus, and the divisor differences represented by
    ``rational_points`` must certify an annihilator of dimension
    ``genus - rank``.  If ``rank`` is omitted, the available point
    differences determine the annihilator without a rank certificate.

    Supply either known ``rational_points`` or a positive affine search
    ``bound``.  Rational point search and ramified/infinite disks are supplied
    by the corresponding applications and local-parameter layers.  Passing
    ``skip_unsupported=True`` restricts the computation to good affine disks.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.chabauty import effective_chabauty
        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.points import point_from_good_affine_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2-(x^3-10*x+9), 5, 3, genus=1)
        sage: P = point_from_good_affine_coordinates(0, 3, data)
        sage: points, forms = effective_chabauty(
        ....:     data, rational_points=[P], rank=0, skip_unsupported=True)
        sage: len(points), len(forms)
        (4, 1)
        sage: all_points, _ = effective_chabauty(
        ....:     data, rational_points=[P], rank=0)
        sage: len(all_points)
        6
        sage: inferred, inferred_forms = effective_chabauty(
        ....:     data, rational_points=[P], skip_unsupported=True)
        sage: len(inferred), len(inferred_forms)
        (4, 1)
        sage: effective_chabauty(data, rational_points=[P], rank=1)
        Traceback (most recent call last):
        ...
        ValueError: rank must satisfy 0 <= rank < genus

    On an open curve, logarithmic coordinates outside the regular block do
    not obstruct the Chabauty computation, including at bad residue disks::

        sage: open_data = coleman_data(
        ....:     y^2-(x^3-10*x+9), 5, 4,
        ....:     genus=1, use_open_curve=True)
        sage: open_P = point_from_good_affine_coordinates(0, 3, open_data)
        sage: open_points, open_forms = effective_chabauty(
        ....:     open_data, rational_points=[open_P], rank=0)
        sage: len(open_points), len(open_forms)
        (4, 1)
    """
    genus = ZZ(data.genus)
    certified_rank = None if rank is None else ZZ(rank)
    if (certified_rank is not None
            and (certified_rank < 0 or certified_rank >= genus)):
        raise ValueError("rank must satisfy 0 <= rank < genus")

    rational_points = list(rational_points or ())
    if not rational_points and bound:
        rational_points = _rational_points(data, bound)
    if not rational_points:
        raise ValueError("supply rational_points or a positive search bound")
    if certified_rank == 0:
        field = rational_points[0].x.parent()
        annihilators = list((field**data.genus).basis())
        base_integrals = []
        base_precisions = []
    else:
        annihilators, base_integrals, base_precisions = (
            vanishing_differentials(rational_points, data, e=e)
        )
    if (certified_rank is not None
            and len(annihilators) != genus - certified_rank):
        raise ValueError(
            "the supplied point differences do not certify the stated rank"
        )
    representatives, _ = padic_points(
        data, points=rational_points,
        skip_unsupported=skip_unsupported
    )
    if skip_unsupported:
        representatives = [
            point for point in representatives
            if not is_in_bad_residue_disk(point, data)
        ]
    output = []
    for representative in representatives:
        known_index = next((i for i, point in enumerate(rational_points)
                            if are_in_same_residue_disk(
                                point, representative, data
                            )),
                           None)
        integral = None
        if known_index is not None and known_index > 0 and base_integrals:
            integral = (base_integrals[known_index - 1],
                        base_precisions[known_index - 1])
        output.extend(zeros_on_disk(
            rational_points[0], representative, annihilators, data,
            integral=integral, e=e
        ))
    return output, annihilators


def torsion_packet(P, data, *, rational_points=None, bound=0,
                   skip_unsupported=False, e=None):
    r"""Find the common Coleman zeros of all regular forms based at ``P``.

    These are the points whose divisor class difference from ``P`` is
    torsion, subject to the available p-adic precision.  A positive ``bound``
    optionally supplies known rational representatives to
    :func:`~sage.schemes.curves.coleman.applications.padic_points` before the
    residue-disk search.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.chabauty import torsion_packet
        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.points import point_from_good_affine_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2-(x^3-10*x+9), 5, 3, genus=1)
        sage: P = point_from_good_affine_coordinates(0, 3, data)
        sage: len(torsion_packet(
        ....:     P, data, rational_points=[P], skip_unsupported=True))
        4
    """
    field = P.x.parent()
    annihilators = list((field**data.genus).basis())
    supplied = list(rational_points or ())
    if not supplied and bound:
        supplied = _rational_points(data, bound)
    representatives, _ = padic_points(
        data, points=supplied,
        skip_unsupported=skip_unsupported
    )
    if skip_unsupported:
        representatives = [
            point for point in representatives
            if not is_in_bad_residue_disk(point, data)
        ]
    output = []
    for representative in representatives:
        output.extend(zeros_on_disk(
            P, representative, annihilators, data, e=e
        ))
    return output
