# sage.doctest: needs sage.rings.padics
r"""
Point representations for Coleman integration on general plane curves

Points store the value of ``x`` and the values of the finite integral basis
``b_i^0``.  This remains meaningful at ramified points where ``y`` itself is
not a convenient local coordinate.

"""

from dataclasses import dataclass, field

from sage.matrix.constructor import identity_matrix, matrix
from sage.modules.free_module_element import vector

from sage.rings.integer_ring import ZZ
from sage.rings.padics.factory import Qp
from sage.rings.rational_field import QQ

from .cohomology import _evaluate_matrix, _evaluate_rational_function


@dataclass
class ColemanIntegrationPoint:
    r"""A finite-precision point represented in an integral function basis.

    Local-expansion caches are implementation details and do not affect point
    equality::

        sage: from sage.schemes.curves.coleman.points import ColemanIntegrationPoint
        sage: K = Qp(5, 4)
        sage: P = ColemanIntegrationPoint(K(0), (K(1), K(0)))
        sage: Q = ColemanIntegrationPoint(K(0), (K(1), K(0)))
        sage: P.xt = K(2)
        sage: P == Q
        True
    """

    x: object
    b: tuple
    infinity: bool = False
    xt: object = field(default=None, compare=False, repr=False)
    bt: object = field(default=None, compare=False, repr=False)
    index: object = field(default=None, compare=False, repr=False)
    _cache_data: object = field(default=None, compare=False, repr=False)


@dataclass
class ColemanTangentialPoint(ColemanIntegrationPoint):
    r"""A nonzero tangent vector based at a Coleman integration point.

    ``tangent_scale`` expresses the vector relative to the local parameter
    selected by the normalized residue-disk computation.  Thus scale ``1``
    is the canonical tangent for that parameter.  Coleman logarithms use the
    standard branch ``log(p) = 0``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.points import (
        ....:     ColemanIntegrationPoint, ColemanTangentialPoint,
        ....:     tangential_point)
        sage: K = Qp(5, 5)
        sage: P = ColemanIntegrationPoint(K(1), (K(1), K(0)))
        sage: T = tangential_point(P, K(1) + 5)
        sage: isinstance(T, ColemanTangentialPoint), T.tangent_scale
        (True, 1 + 5 + O(5^5))
        sage: tangential_point(P, 0)
        Traceback (most recent call last):
        ...
        ValueError: a tangent vector must have nonzero scale
    """

    tangent_scale: object = 1

    def __post_init__(self):
        self.tangent_scale = self.x.parent()(self.tangent_scale)
        if not self.tangent_scale:
            raise ValueError("a tangent vector must have nonzero scale")


def tangential_point(point, scale=1):
    r"""Return the tangent ``scale * d/dt`` based at ``point``.

    Here ``t`` is the normalized local parameter computed for the residue
    disk.  Changing ``scale`` from `1` to `c` changes the value of a
    logarithmic primitive of residue `r` by `r\log(c)`.

    INPUT:

    - ``point`` -- a :class:`ColemanIntegrationPoint`
    - ``scale`` -- a nonzero element of the point's coefficient field

    The point's local-coordinate cache is retained, so constructing a tangent
    does not repeat residue-disk normalization.
    """
    if not isinstance(point, ColemanIntegrationPoint):
        raise TypeError("the tangent must be based at a Coleman integration point")
    if isinstance(point, ColemanTangentialPoint):
        point = ColemanIntegrationPoint(
            x=point.x, b=point.b, infinity=point.infinity,
            xt=point.xt, bt=point.bt, index=point.index,
            _cache_data=point._cache_data,
        )
    return ColemanTangentialPoint(
        x=point.x, b=point.b, infinity=point.infinity,
        xt=point.xt, bt=point.bt, index=point.index,
        _cache_data=point._cache_data, tangent_scale=scale,
    )


def _point_field(value, p, N):
    r"""Choose the supplied p-adic parent, or create ``Qp(p, N)``.

    TESTS::

        sage: from sage.schemes.curves.coleman.points import _point_field
        sage: _point_field(QQ(1), 5, 7) is Qp(5, 7)
        True
        sage: K = Qp(7, 4)
        sage: _point_field(K(1), 7, 2) is K
        True
    """
    try:
        parent = value.parent()
    except AttributeError:
        parent = None
    if parent is QQ or parent is ZZ or parent is None:
        return Qp(p, prec=N)
    return parent


def point_from_good_affine_coordinates(x0, y0, data):
    r"""Construct a point from good affine coordinates ``(x0, y0)``.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.points import point_from_good_affine_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = SimpleNamespace(Q=y^2-x^3, p=5, N=6,
        ....:     W0=identity_matrix(QQ, 2), r=R.one())
        sage: P = point_from_good_affine_coordinates(1, 1, data)
        sage: P.x, P.b
        (1 + O(5^6), (1 + O(5^6), 1 + O(5^6)))
    """
    field = _point_field(x0, data.p, data.N)
    x0 = field(x0)
    y0 = field(y0)
    if x0.valuation() < 0:
        raise ValueError("x0 must have nonnegative p-adic valuation")

    degree = data.Q.degree()
    identity = identity_matrix(data.W0.base_ring(), degree)
    if (data.W0 != identity
            and _evaluate_rational_function(data.r, x0).valuation() > 0):
        raise ValueError("W0 is nontrivial and r(x0) vanishes modulo p")

    powers = vector(field, [y0**i for i in range(degree)])
    W0_at_x = _evaluate_matrix(data.W0, x0, field)
    basis_values = powers * W0_at_x.transpose()
    return ColemanIntegrationPoint(
        x=x0, b=tuple(basis_values), infinity=False
    )


def point_from_basis_coordinates(x, basis_values, at_infinity, data):
    r"""Construct a point directly from its integral-basis coordinates.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.points import point_from_basis_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = SimpleNamespace(Q=y^2-x, p=5, N=4)
        sage: P = point_from_basis_coordinates(0, [1, 0], True, data)
        sage: P.infinity, P.b
        (True, (1 + O(5^4), 0))
    """
    degree = data.Q.degree()
    if len(basis_values) != degree:
        raise ValueError(
            "basis_values must contain one value for each basis element"
        )
    field = _point_field(x, data.p, data.N)
    return ColemanIntegrationPoint(
        x=field(x),
        b=tuple(field(value) for value in basis_values),
        infinity=bool(at_infinity),
    )


def affine_coordinates(P, data):
    r"""Recover affine ``(x, y)`` coordinates from a represented point.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.points import (affine_coordinates,
        ....:     point_from_basis_coordinates)
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = SimpleNamespace(Q=y^2-x, p=5, N=4,
        ....:     W0=identity_matrix(QQ, 2))
        sage: P = point_from_basis_coordinates(1, [1, 1], False, data)
        sage: affine_coordinates(P, data)
        (1 + O(5^4), 1 + O(5^4))
    """
    if P.infinity:
        raise ValueError("the point is not affine")
    field = P.x.parent()
    W0_inverse_at_x = _evaluate_matrix(data.W0.inverse(), P.x, field)
    powers = W0_inverse_at_x * matrix(field, len(P.b), 1, list(P.b))
    if len(P.b) < 2:
        raise ValueError("a degree-one model has no stored y coordinate")
    return P.x, powers[1, 0]


def is_in_bad_residue_disk(P, data):
    r"""Return whether ``P`` lies in a bad or infinite residue disk.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.points import (is_in_bad_residue_disk,
        ....:     point_from_basis_coordinates)
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = SimpleNamespace(Q=y^2-x, p=5, N=4, r=x)
        sage: P = point_from_basis_coordinates(0, [1, 0], False, data)
        sage: is_in_bad_residue_disk(P, data)
        True
    """
    if P.infinity:
        return True
    return _evaluate_rational_function(data.r, P.x).valuation() > 0


def is_bad_residue_disk_center(P, data):
    r"""Return whether ``P`` represents the center of a bad residue disk.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.points import (is_bad_residue_disk_center,
        ....:     point_from_basis_coordinates)
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = SimpleNamespace(Q=y^2-x, p=5, N=4, r=x)
        sage: P = point_from_basis_coordinates(0, [1, 0], False, data)
        sage: is_bad_residue_disk_center(P, data)
        True
    """
    if P.infinity:
        return P.x.valuation() >= data.N
    return _evaluate_rational_function(data.r, P.x).valuation() >= data.N


def are_in_same_residue_disk(P1, P2, data):
    r"""Return whether two represented points have the same reduction.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.points import (are_in_same_residue_disk,
        ....:     point_from_basis_coordinates)
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = SimpleNamespace(Q=y^2-x, p=5, N=4)
        sage: P = point_from_basis_coordinates(0, [1, 0], False, data)
        sage: Q = point_from_basis_coordinates(5, [1, 5], False, data)
        sage: are_in_same_residue_disk(P, Q, data)
        True
    """
    if P1.infinity != P2.infinity or (P1.x - P2.x).valuation() < 1:
        return False
    return all((a - b).valuation() >= 1 for a, b in zip(P1.b, P2.b))


def point_from_affine_coordinates(coordinates, data):
    r"""Construct the appropriate point representation from affine coordinates.

    Finite good points use integral affine coordinates; finite branch points
    and points in infinity disks retain the values of the relevant integral
    basis.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.points import point_from_affine_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = SimpleNamespace(Q=y^2-x, p=5, N=4, r=x+1,
        ....:     W0=identity_matrix(QQ, 2), Winf=identity_matrix(QQ, 2))
        sage: point_from_affine_coordinates((1, 1), data).b
        (1 + O(5^4), 1 + O(5^4))
    """
    if len(coordinates) != 2:
        raise ValueError("coordinates must be a pair (x,y)")
    x0, y0 = coordinates
    field = _point_field(x0, data.p, data.N)
    x0 = field(x0)
    y0 = field(y0)
    degree = data.Q.degree()
    powers = vector(field, [y0**i for i in range(degree)])
    if x0.valuation() >= 0:
        if _evaluate_rational_function(data.r, x0).valuation() == 0:
            return point_from_good_affine_coordinates(x0, y0, data)
        basis_matrix = _evaluate_matrix(data.W0, x0, field)
        values = basis_matrix * powers
        return ColemanIntegrationPoint(
            x=x0, b=tuple(values), infinity=False
        )

    basis_matrix = _evaluate_matrix(data.Winf, x0, field)
    values = basis_matrix * powers
    return ColemanIntegrationPoint(
        x=1 / x0, b=tuple(values), infinity=True
    )
