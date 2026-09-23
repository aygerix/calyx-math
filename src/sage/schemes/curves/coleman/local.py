# sage.doctest: needs sage.rings.padics sage.rings.function_field
r"""
Local coordinates and tiny Coleman integrals at good affine points

At a good point the projection to the `x` line is unramified.  Thus
`t=x-x(P)` is a parameter, and the equation of the curve has a unique
solution `y(t)` with the prescribed value at `P`.  This module computes that
solution over a finite-precision p-adic power-series ring and integrates the
cohomology basis term by term.

EXAMPLES::

    sage: from sage.schemes.curves.coleman.data import coleman_data
    sage: from sage.schemes.curves.coleman.local import (local_coordinates,
    ....:     tiny_integrals_on_basis, tiny_integrals_on_basis_to_parameter)
    sage: from sage.schemes.curves.coleman.points import point_from_good_affine_coordinates
    sage: R.<x> = QQ[]
    sage: S.<y> = R[]
    sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 8, genus=1)
    sage: P = point_from_good_affine_coordinates(0, 3, data)
    sage: xt, bt, index = local_coordinates(P, 12, data)
    sage: index == 0 and xt[0] == P.x and xt[1] == 1
    True
    sage: (bt[1]^2 - (xt^3 - 10*xt + 9)).is_zero()
    True
    sage: I, xt, bt, n = tiny_integrals_on_basis_to_parameter(P, data, prec=12)
    sage: len(I) == 2 and all(f[0] == 0 for f in I) and n > 0
    True

The same construction works in a non-hyperelliptic model::

    sage: Q = y^3 + (-x^2 - 1)*y^2 - x^3*y + x^3 + 2*x^2 + x
    sage: data = coleman_data(Q, 7, 8, genus=3)
    sage: P = point_from_good_affine_coordinates(
    ....:     5, -32582624253112412, data)
    sage: xt, bt, index = local_coordinates(P, 12, data)
    sage: index == 0 and len(bt) == 3 and len(data.basis) == 6
    True
    sage: I, xt, bt, n = tiny_integrals_on_basis_to_parameter(P, data, prec=12)
    sage: len(I) == 6 and all(f[0] == 0 for f in I) and n > 0
    True
    sage: P2 = point_from_good_affine_coordinates(
    ....:     12, 25123732258943588, data)
    sage: tiny, n = tiny_integrals_on_basis(P, P2, data)
    sage: len(tiny) == 6 and n >= 8
    True
    sage: all((tiny[i] - I[i](P2.x - P.x)).valuation() >= 8 for i in range(6))
    True

"""

from sage.modules.free_module_element import vector

from sage.rings.infinity import infinity
from sage.rings.integer_ring import ZZ
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.rational_field import QQ

from .cohomology import _evaluate_rational_function
from .points import (
    affine_coordinates,
    are_in_same_residue_disk,
    is_in_bad_residue_disk,
)


def _series_value(f, argument, series_ring):
    """Evaluate a polynomial or rational function of ``x`` in a series.

    TESTS::

        sage: from sage.schemes.curves.coleman.local import _series_value
        sage: R.<x> = QQ[]; K = Qp(5, 6)
        sage: T.<t> = PowerSeriesRing(K, default_prec=5)
        sage: value = _series_value((x + 1)/(x + 2), K(1) + t, T)
        sage: ((K(1) + t + 2)*value - (K(1) + t + 1)).is_zero()
        True
    """
    if hasattr(f, "denominator"):
        numerator = f.numerator()
        denominator = f.denominator()
        numerator = numerator(argument) if callable(numerator) else numerator
        denominator = (denominator(argument) if callable(denominator)
                       else denominator)
        if not series_ring(denominator)[0]:
            raise ZeroDivisionError("a rational function has a pole in this disk")
        return series_ring(numerator) / series_ring(denominator)
    return series_ring(f(argument))


def _model_series(Q, xt, series_ring):
    """Specialize the `x` coefficients of ``Q`` at ``xt``.

    TESTS::

        sage: from sage.schemes.curves.coleman.local import _model_series
        sage: R.<x> = QQ[]; S.<y> = R[]; K = Qp(5, 6)
        sage: T.<t> = PowerSeriesRing(K, default_prec=5)
        sage: coefficients = _model_series(y^2 - x, K(1) + t, T)
        sage: len(coefficients), all(
        ....:     not c for c in (coefficients[0] + K(1) + t).list())
        (3, True)
    """
    return [_series_value(coefficient, xt, series_ring)
            for coefficient in Q.list()]


def _horner(coefficients, value):
    """Evaluate a polynomial supplied in ascending coefficient order.

    TESTS::

        sage: from sage.schemes.curves.coleman.local import _horner
        sage: R.<x> = QQ[]
        sage: _horner([1, 2, 3], x)
        3*x^2 + 2*x + 1
    """
    answer = value.parent().zero()
    for coefficient in reversed(coefficients):
        answer = answer * value + coefficient
    return answer


def hensel_lift_power_series(coefficients, root, prec=None):
    r"""
    Lift a simple root of a polynomial over a p-adic power-series ring.

    ``coefficients`` are in ascending order, and ``root`` is the chosen
    constant term.  The derivative must be a p-adic unit.  Newton iteration
    doubles the known `t` precision at each step.  Since the constant root
    itself has finite p-adic precision, its residual is tested modulo the
    precision of its coefficient field rather than for exact zero.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.local import hensel_lift_power_series
        sage: K = Qp(5, 8); T.<t> = PowerSeriesRing(K, default_prec=6)
        sage: root = hensel_lift_power_series([-(1 + t), 0, 1], T(1))
        sage: (root^2 - (1 + t)).is_zero(), root[0]
        (True, 1 + O(5^8))

    The convergence test respects lower-precision input data::

        sage: K = Qp(5, 20); T.<t> = PowerSeriesRing(K, default_prec=6)
        sage: one = K(1).add_bigoh(6)
        sage: root = hensel_lift_power_series([-(one + t), 0, 1], T(one))
        sage: all(c.valuation() >= 6
        ....:     for c in (root^2 - (one + t)).list())
        True
    """
    ring = root.parent() if hasattr(root, "parent") else None
    if ring is None or not hasattr(ring, "default_prec"):
        raise TypeError("root must belong to a power-series ring")
    prec = ZZ(ring.default_prec() if prec is None else prec)
    if prec < 2:
        raise ValueError("power-series precision must be at least two")
    root = ring(root).add_bigoh(prec)
    coefficients = [ring(coefficient).add_bigoh(prec)
                    for coefficient in coefficients]
    input_precisions = []
    for series in [root] + coefficients:
        for coefficient in series.list():
            coefficient_precision = coefficient.precision_absolute()
            if coefficient_precision != infinity:
                input_precisions.append(ZZ(coefficient_precision))
    target_precision = min(
        [ZZ(root.base_ring().precision_cap())] + input_precisions
    )
    derivative = [(i + 1) * coefficients[i + 1]
                  for i in range(len(coefficients) - 1)]
    if not derivative:
        raise ValueError("the polynomial has no simple root")
    derivative_at_zero = _horner(derivative, root)[0]
    if not derivative_at_zero or derivative_at_zero.valuation() != 0:
        raise ValueError("the selected root is not simple modulo p")

    # Every step doubles formal accuracy; a few extra steps absorb the
    # finite p-adic error in the supplied constant root.
    for _ in range(2 * prec.nbits() + 4):
        residual = _horner(coefficients, root)
        correction = (residual / _horner(derivative, root)).add_bigoh(prec)
        updated = (root - correction).add_bigoh(prec)
        if updated == root:
            root = updated
            break
        root = updated

    residual = _horner(coefficients, root)
    if any(coefficient.valuation() < target_precision
           for coefficient in residual.list()):
        raise ArithmeticError("power-series Newton lift did not converge")
    return root


def local_data(P, data):
    r"""Return ``(1, 0)`` for an unramified good affine point.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.local import local_data
        sage: from sage.schemes.curves.coleman.points import point_from_good_affine_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: Q = y^2 - (x^3 - 10*x + 9)
        sage: data = SimpleNamespace(Q=Q, p=5, N=6,
        ....:     W0=identity_matrix(QQ, 2), r=4*x^3 - 40*x + 36)
        sage: local_data(point_from_good_affine_coordinates(0, 3, data), data)
        (1, 0)
    """
    if P.infinity or is_in_bad_residue_disk(P, data):
        raise NotImplementedError("this local slice supports good affine points")
    if _evaluate_rational_function(data.r, P.x).valuation() != 0:
        raise ValueError("the x projection is ramified at this point")
    return ZZ.one(), ZZ.zero()


def local_coordinates(P, prec, data):
    r"""
    Return ``(x(t), (b_i^0(t)), 0)`` with ``t = x - x(P)``.

    The stored point's ``b`` coordinates are the values of the finite
    integral basis; this routine recovers ``y(P)`` and lifts it using the
    defining equation.  Results are cached on the point by precision.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.local import local_coordinates
        sage: from sage.schemes.curves.coleman.points import point_from_good_affine_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: Q = y^2 - (x^3 - 10*x + 9)
        sage: data = SimpleNamespace(Q=Q, p=5, N=6,
        ....:     W0=identity_matrix(QQ, 2), r=4*x^3 - 40*x + 36)
        sage: P = point_from_good_affine_coordinates(0, 3, data)
        sage: xt, bt, index = local_coordinates(P, 6, data)
        sage: index, xt[1], (bt[1]^2 - (xt^3 - 10*xt + 9)).is_zero()
        (0, 1 + O(5^6), True)
        sage: P._cache_data is data
        True
    """
    local_data(P, data)
    prec = ZZ(prec)
    if prec < 2:
        raise ValueError("power-series precision must be at least two")
    if (P._cache_data is data and P.xt is not None and P.bt is not None
            and P.xt.parent().default_prec() >= prec
            and P.xt.precision_absolute() >= prec):
        return P.xt.add_bigoh(prec), tuple(b.add_bigoh(prec) for b in P.bt), 0

    field = P.x.parent()
    ring = PowerSeriesRing(field, names='t', default_prec=prec)
    t = ring.gen()
    xt = (ring(P.x) + t).add_bigoh(prec)
    _, y0 = affine_coordinates(P, data)
    coefficients = _model_series(data.Q, xt, ring)
    residual_at_point = _horner(coefficients, ring(y0))[0]
    if residual_at_point.valuation() < min(data.N, field.precision_cap()):
        raise ValueError("the supplied coordinates do not lie on the curve")
    yt = hensel_lift_power_series(coefficients, ring(y0), prec)
    powers = [ring.one()]
    for _ in range(1, data.Q.degree()):
        powers.append((powers[-1] * yt).add_bigoh(prec))
    bt = tuple(
        sum((_series_value(data.W0[i, j], xt, ring) * powers[j]
             for j in range(data.Q.degree())), ring.zero()).add_bigoh(prec)
        for i in range(data.Q.degree())
    )
    P.xt, P.bt, P.index, P._cache_data = xt, bt, 0, data
    return xt, bt, 0


def t_adic_precision(data, e=1, N=None):
    r"""
    Choose enough terms for tiny integration to precision ``N``.

    For points in one p-adic residue disk, the parameter has valuation at
    least ``1/e``.  Dividing a `t^n` term by ``n`` can lose
    ``floor(log_p(n))`` digits.  The returned cutoff makes every omitted
    integral term have valuation at least ``N`` when the differential has
    integral local coefficients.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.local import t_adic_precision
        sage: t_adic_precision(SimpleNamespace(p=5, N=8))
        100
    """
    e = ZZ(e)
    N = ZZ(data.N if N is None else N)
    if e <= 0 or N <= 0:
        raise ValueError("e and N must be positive")
    p = ZZ(data.p)
    prec = ZZ.one()
    while _ramified_tail_bound(prec + 1, e, p) < N:
        prec += 1
    return max(prec, ZZ(100))


def _series_integral(f):
    """Integrate a regular power series with zero constant term.

    TESTS::

        sage: from sage.schemes.curves.coleman.local import _series_integral
        sage: R.<t> = PowerSeriesRing(QQ, default_prec=5)
        sage: _series_integral(1 + t + O(t^4))
        t + 1/2*t^2 + O(t^5)
    """
    return f.integral()


def _floor_log(n, p):
    """Return ``floor(log_p(n))`` using integer arithmetic.

    TESTS::

        sage: from sage.schemes.curves.coleman.local import _floor_log
        sage: [_floor_log(n, 5) for n in (1, 5, 24, 25)]
        [0, 1, 1, 2]
    """
    n = ZZ(n)
    p = ZZ(p)
    exponent = ZZ.zero()
    while n >= p:
        n //= p
        exponent += 1
    return exponent


def _ramified_tail_bound(first_exponent, e, p):
    r"""Bound ``k/e - v_p(k)`` for every ``k >= first_exponent``.

    The lower bound ``v_p(k) <= floor(log_p(k))`` is sharp at powers of
    ``p``.  Between consecutive powers the resulting bound increases, so it
    is enough to inspect the first exponent and subsequent powers of ``p``.

    TESTS::

        sage: from sage.schemes.curves.coleman.local import _ramified_tail_bound
        sage: _ramified_tail_bound(201, 20, 5)
        141/20
        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.local import t_adic_precision
        sage: cutoff = t_adic_precision(SimpleNamespace(p=5, N=8), e=20)
        sage: _ramified_tail_bound(cutoff + 1, 20, 5) >= 8
        True
    """
    first_exponent = ZZ(first_exponent)
    e = ZZ(e)
    p = ZZ(p)
    if first_exponent <= 0 or e <= 0 or p <= 1:
        raise ValueError("first_exponent, e, and p must be positive")

    exponent = _floor_log(first_exponent, p)
    bound = QQ(first_exponent) / e - exponent
    exponent += 1
    while True:
        power = p**exponent
        candidate = QQ(power) / e - exponent
        bound = min(bound, candidate)
        next_difference_positive = power * (p - 1) >= e
        if next_difference_positive and candidate >= bound:
            return bound
        exponent += 1


def _coefficient_valuation_bound(f, x0, p):
    r"""
    Bound below the valuations of all coefficients of ``f(x0+t)``.

    The denominator must have p-integral Taylor coefficients after its
    constant term is scaled to a unit.  This holds on the good affine disks
    of the models supported here, and makes the bound valid for the entire
    infinite Taylor expansion, including terms past the computed cutoff.

    TESTS::

        sage: from sage.schemes.curves.coleman.local import _coefficient_valuation_bound
        sage: R.<x> = QQ[]; K = Qp(5, 6)
        sage: _coefficient_valuation_bound((x + 1)/(x + 2), K(0), 5)
        0
    """
    if not f:
        return None
    numerator = f.numerator() if hasattr(f, "numerator") else f
    denominator = f.denominator() if hasattr(f, "denominator") else 1
    numerator_coefficients = (numerator.list() if hasattr(numerator, "list")
                              else [numerator])
    denominator_coefficients = (denominator.list() if hasattr(denominator, "list")
                                else [denominator])
    numerator_bound = min(ZZ(c.valuation(p)) for c in numerator_coefficients
                          if c)
    denominator_value = (denominator(x0) if callable(denominator)
                         else x0.parent()(denominator))
    denominator_valuation = ZZ(denominator_value.valuation())
    denominator_bound = min(ZZ(c.valuation(p))
                            for c in denominator_coefficients if c)
    if denominator_bound < denominator_valuation:
        raise ValueError(
            "the local denominator has nonintegral Taylor coefficients"
        )
    return numerator_bound - denominator_valuation


def _integrand_valuation_bound(P, data):
    """Give a lower bound for all local differential coefficients.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.local import _integrand_valuation_bound
        sage: from sage.schemes.curves.coleman.points import point_from_good_affine_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: Q = y^2 - (x^3 - 10*x + 9)
        sage: data = SimpleNamespace(Q=Q, p=5, N=6,
        ....:     W0=identity_matrix(QQ, 2), r=4*x^3 - 40*x + 36,
        ....:     basis=[vector(R, [1, 0]), vector(R, [0, 1])])
        sage: P = point_from_good_affine_coordinates(0, 3, data)
        sage: _integrand_valuation_bound(P, data)
        0
    """
    _, y0 = affine_coordinates(P, data)
    if P.x.valuation() < 0 or y0.valuation() < 0:
        raise ValueError("good affine coordinates must be p-integral")
    p = data.p
    if any(_coefficient_valuation_bound(c, P.x, p) < 0
           for c in data.Q.list() if c):
        raise ValueError("the plane equation must have p-integral coefficients")

    basis_bounds = []
    for i in range(data.Q.degree()):
        bounds = [_coefficient_valuation_bound(data.W0[i, j], P.x, p)
                  for j in range(data.Q.degree())]
        basis_bounds.append(min(c for c in bounds if c is not None))
    differential_bounds = []
    for differential in data.basis:
        bounds = [(_coefficient_valuation_bound(coefficient, P.x, p)
                   + basis_bounds[i])
                  for i, coefficient in enumerate(differential) if coefficient]
        differential_bounds.append(min(bounds))
    if not differential_bounds:
        return ZZ.zero()
    return (ZZ(data.r.leading_coefficient().valuation(p))
            - ZZ(_evaluate_rational_function(data.r, P.x).valuation())
            + min(differential_bounds))


def _differentials(P, data, prec):
    """Expand each cohomology differential in the good local parameter.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.local import _differentials
        sage: from sage.schemes.curves.coleman.points import point_from_good_affine_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: Q = y^2 - (x^3 - 10*x + 9)
        sage: data = SimpleNamespace(Q=Q, p=5, N=6,
        ....:     W0=identity_matrix(QQ, 2), r=4*x^3 - 40*x + 36,
        ....:     basis=[vector(R, [1, 0]), vector(R, [0, 1])])
        sage: P = point_from_good_affine_coordinates(0, 3, data)
        sage: xt, bt, differentials = _differentials(P, data, 6)
        sage: len(bt), len(differentials), xt[1]
        (2, 2, 1 + O(5^6))
    """
    xt, bt, _ = local_coordinates(P, prec, data)
    ring = xt.parent()
    denominator = _series_value(data.r, xt, ring)
    if not denominator[0] or denominator[0].valuation() != 0:
        raise ValueError("r(x(P)) must be a p-adic unit")
    scale = ring(data.r.leading_coefficient()) / denominator
    differentials = []
    for basis_element in data.basis:
        if len(basis_element) != len(bt):
            raise ValueError("cohomology differential has wrong basis length")
        differential = sum(
            (_series_value(coefficient, xt, ring) * basis_value
             for coefficient, basis_value in zip(basis_element, bt)),
            ring.zero()
        ) * scale
        differentials.append(differential.add_bigoh(prec))
    return xt, bt, differentials


def _tail_precision(prec, val, p, coefficient_bound=0):
    """Lower bound on all omitted integral terms.

    TESTS::

        sage: from sage.schemes.curves.coleman.local import _tail_precision
        sage: _tail_precision(10, 1, 5, -1)
        9
    """
    return ZZ(coefficient_bound + (prec + 1) * val
              - _floor_log(prec + 1, p))


def tiny_integral_precision(prec, e, maxpoleorder, maxdegree, mindegree, val,
                            data, *, N=0):
    r"""Return the certified precision of a ramified tiny integral.

    The ``prec`` argument validates the requested series precision.  The
    result is a rational number of base-field p-adic digits; callers round
    only after descent from a ramified extension.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.local import tiny_integral_precision
        sage: data = SimpleNamespace(p=ZZ(7), N=ZZ(10))
        sage: tiny_integral_precision(100, 3, 0, 8, 0, 1, data)
        2/3
    """
    ZZ(prec)
    e = ZZ(e)
    maxpoleorder = ZZ(maxpoleorder)
    maxdegree = ZZ(maxdegree)
    mindegree = ZZ(mindegree)
    val = ZZ(val)
    N = ZZ(data.N if not N else N)
    p = ZZ(data.p)
    if e <= 0:
        raise ValueError("ramification degree must be positive")

    positive_loss = N * e - val
    for i in range(1, maxdegree + 1):
        positive_loss = min(
            positive_loss, N * e + i - e * _floor_log(i + 1, p)
        )

    first_omitted = mindegree + 2
    omitted_loss = e * _ramified_tail_bound(first_omitted, e, p)

    pole_loss = N * e - val
    if maxpoleorder >= 2:
        pole_loss = (N * e - val - maxpoleorder * val
                     - e * _floor_log(maxpoleorder - 1, p))
    return QQ(min(positive_loss, omitted_loss, pole_loss)) / e


def tiny_integrals_on_basis(P1, P2, data, *, prec=None):
    r"""Integrate the cohomology basis between two good points in one disk.

    OUTPUT: a vector of p-adic integrals and a conservative absolute
    precision.  The default `t` cutoff comes from :func:`t_adic_precision`.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.local import tiny_integrals_on_basis
        sage: from sage.schemes.curves.coleman.points import point_from_good_affine_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 4, genus=1)
        sage: P = point_from_good_affine_coordinates(0, 3, data)
        sage: K = P.x.parent(); T.<z> = K[]
        sage: y2 = [root for root, _ in (z^2 - K(84)).roots()
        ....:       if root.residue() == 3][0]
        sage: Q = point_from_good_affine_coordinates(K(5), y2, data)
        sage: values, precision = tiny_integrals_on_basis(P, Q, data, prec=8)
        sage: len(values), precision >= 4
        (2, True)
    """
    local_data(P1, data)
    local_data(P2, data)
    if not are_in_same_residue_disk(P1, P2, data):
        raise ValueError("the points do not lie in the same residue disk")
    if P1.x.parent() != P2.x.parent():
        raise TypeError("the points must have the same p-adic coefficient field")
    field = P1.x.parent()
    if field(data.p).valuation() != 1:
        raise NotImplementedError("ramified coefficient fields need a base-point lift")
    if P1.x == P2.x:
        if all((a - b).valuation() >= data.N
               for a, b in zip(P1.b, P2.b)):
            return vector(field, len(data.basis)), ZZ(data.N)
        raise ValueError("points with the same x have inconsistent basis values")

    delta = P2.x - P1.x
    val = delta.valuation()
    if val < 1:
        raise ValueError("the local parameter must have positive valuation")
    coefficient_bound = _integrand_valuation_bound(P1, data)
    automatic_precision = prec is None
    prec = t_adic_precision(data) if automatic_precision else ZZ(prec)
    if prec < 2:
        raise ValueError("t-adic precision must be at least two")
    if automatic_precision:
        while _tail_precision(prec, val, data.p, coefficient_bound) < data.N:
            prec += 1
    _, _, differentials = _differentials(P1, data, prec)
    values = [_series_integral(f)(delta) for f in differentials]
    available = min([ZZ(data.N)] + [ZZ(value.precision_absolute())
                                    for value in values])
    tail = _tail_precision(prec, val, data.p, coefficient_bound)
    return vector(field, values), max(ZZ.zero(), min(available, tail))


def tiny_integrals_on_basis_to_parameter(P, data, *, prec=None, indices=None):
    r"""
    Return tiny integrals from ``P`` as series in ``t=x-x(P)``.

    OUTPUT: ``(integral_series, x_series, basis_series, precision)``.
    All integral series have zero constant term.  The precision is the
    guaranteed p-adic precision on evaluating at another point in the same
    residue disk, under the usual integral-coefficient hypothesis.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.local import tiny_integrals_on_basis_to_parameter
        sage: from sage.schemes.curves.coleman.points import point_from_good_affine_coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 4, genus=1)
        sage: P = point_from_good_affine_coordinates(0, 3, data)
        sage: values, _, _, precision = tiny_integrals_on_basis_to_parameter(
        ....:     P, data, prec=8)
        sage: len(values), all(f[0] == 0 for f in values), precision >= 4
        (2, True, True)
    """
    indices = (tuple(range(len(data.basis))) if indices is None
               else tuple(ZZ(i) for i in indices))
    if len(set(indices)) != len(indices) or any(
            i < 0 or i >= len(data.basis) for i in indices):
        raise ValueError("basis indices are out of range or repeated")
    if is_in_bad_residue_disk(P, data):
        from .general_integration import (
            tiny_integrals_on_basis_to_parameter as general_series,
        )
        return general_series(P, data, prec=prec, indices=indices)
    local_data(P, data)
    if P.x.parent()(data.p).valuation() != 1:
        raise NotImplementedError("ramified coefficient fields need a base-point lift")
    automatic_precision = prec is None
    prec = t_adic_precision(data) if automatic_precision else ZZ(prec)
    coefficient_bound = _integrand_valuation_bound(P, data)
    if automatic_precision:
        while _tail_precision(prec, 1, data.p, coefficient_bound) < data.N:
            prec += 1
    xt, bt, differentials = _differentials(P, data, prec)
    integrals = vector(xt.parent(), [_series_integral(differentials[i])
                                     for i in indices])
    precision = max(ZZ.zero(), min(ZZ(data.N), _tail_precision(
        prec, 1, data.p, coefficient_bound
    )))
    return integrals, xt, vector(xt.parent(), bt), precision
