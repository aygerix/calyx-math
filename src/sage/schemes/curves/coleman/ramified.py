# sage.doctest: needs sage.rings.function_field sage.rings.padics
r"""Local coordinates on normalized bad and infinite Coleman disks.

The residue disk is selected on the normalization of the reduction, using
values of the finite or infinite integral basis.  At a ramified place an
integral basis element of valuation one is the parameter.  Relations over
``QQ`` then lift the other coordinates as p-adic power series.

An elliptic branch point has `t=y`; the same curve has `t=y/x^2` at
infinity::

    sage: from types import SimpleNamespace
    sage: from sage.schemes.curves.coleman.auxiliary import auxiliary_polynomials, integral_basis_matrices
    sage: from sage.schemes.curves.coleman.points import point_from_affine_coordinates
    sage: from sage.schemes.curves.coleman.ramified import (find_bad_point_in_disk,
    ....:     local_coordinates, local_data)
    sage: R.<x> = QQ[]
    sage: S.<y> = R[]
    sage: Q = y^2 - (x^3 - 10*x + 9)
    sage: r, _, _ = auxiliary_polynomials(Q)
    sage: W0, Winf = integral_basis_matrices(Q)
    sage: data = SimpleNamespace(Q=Q, p=ZZ(5), N=ZZ(10), r=r, W0=W0, Winf=Winf)
    sage: P = point_from_affine_coordinates((1, 0), data)
    sage: local_data(P, data)[:2]
    (2, 2)
    sage: B = find_bad_point_in_disk(P, data)
    sage: xt, bt, index = local_coordinates(B, 12, data)
    sage: index == 2 and (bt[1]^2 - (xt^3 - 10*xt + 9)).add_bigoh(12).is_zero()
    True
    sage: K = Qp(5, 10)
    sage: xx = K(1) / 25
    sage: yy = (xx^3 - 10*xx + 9).sqrt()
    sage: Pinf = point_from_affine_coordinates((xx, yy), data)
    sage: local_data(Pinf, data)[:2]
    (2, 2)
    sage: Binf = find_bad_point_in_disk(Pinf, data)
    sage: ti, bi, index = local_coordinates(Binf, 12, data)
    sage: index == 2 and ti.valuation() == 2 and bi[1].valuation() == 1
    True

A degree-three genus-three model exercises a non-hyperelliptic branch::

    sage: Q = y^3 - (x^4 - x)
    sage: r, _, _ = auxiliary_polynomials(Q)
    sage: W0, Winf = integral_basis_matrices(Q)
    sage: data = SimpleNamespace(Q=Q, p=ZZ(7), N=ZZ(10), r=r, W0=W0, Winf=Winf)
    sage: B = find_bad_point_in_disk(
    ....:     point_from_affine_coordinates((0, 0), data), data)
    sage: xt, bt, index = local_coordinates(B, 14, data)
    sage: index == 2 and xt.valuation() == 3 and (bt[1]^3 - (xt^4 - xt)).add_bigoh(14).is_zero()
    True

The normalization distinguishes the two branches of a singular plane
point through the value of `y/x`::

    sage: from sage.schemes.curves.coleman.points import ColemanIntegrationPoint
    sage: Q = y^2 - x^2*(x+1)
    sage: r, _, _ = auxiliary_polynomials(Q)
    sage: W0, Winf = integral_basis_matrices(Q)
    sage: data = SimpleNamespace(Q=Q, p=ZZ(5), N=ZZ(9), r=r, W0=W0, Winf=Winf)
    sage: K = Qp(5, 9)
    sage: P = ColemanIntegrationPoint(K.zero(), (K.one(), K.one()))
    sage: local_data(P, data)[:2]
    (1, 0)
    sage: B = find_bad_point_in_disk(P, data)
    sage: xt, bt, index = local_coordinates(B, 12, data)
    sage: index == 0 and (bt[1]^2 - (xt+1)).add_bigoh(12).is_zero()
    True
"""

from sage.matrix.constructor import matrix
from sage.modules.free_module_element import vector

from sage.rings.finite_rings.finite_field_constructor import GF
from sage.rings.finite_rings.integer_mod_ring import IntegerModRing
from sage.rings.function_field.constructor import FunctionField
from sage.rings.infinity import infinity
from sage.rings.integer_ring import ZZ
from sage.rings.padics.factory import Qp
from sage.rings.padics.precision_error import PrecisionError
from sage.rings.polynomial.polynomial_ring import (
    PolynomialRing_dense_padic_field_capped_relative,
)
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.rational_field import QQ

from .auxiliary import _function_field_model
from .local import local_coordinates as _good_local_coordinates
from .points import (
    ColemanIntegrationPoint,
    is_bad_residue_disk_center,
    is_in_bad_residue_disk,
)


def _coordinates(L, W):
    """Return an integral basis as elements of ``L`` (rows of ``W``).

    TESTS::

        sage: from sage.schemes.curves.coleman.ramified import _coordinates
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: K.<x> = FunctionField(QQ); T.<y> = K[]
        sage: L.<y> = K.extension(y^2 - x)
        sage: _coordinates(L, identity_matrix(K, 2))
        (1, y)
    """
    z = L.gen()
    return tuple(sum((L(W[i, j]) * z**j for j in range(W.ncols())), L.zero())
                 for i in range(W.nrows()))


def _reduce_rational_function(f, K):
    """Reduce a rational function in ``x`` coefficientwise modulo ``p``.

    TESTS::

        sage: from sage.schemes.curves.coleman.ramified import _reduce_rational_function
        sage: R.<x> = QQ[]; K.<x> = FunctionField(GF(5))
        sage: _reduce_rational_function((R.gen() + 1)/(R.gen() + 2), K)
        (x + 1)/(x + 2)
    """
    k = K.constant_base_field()
    x = K.gen()

    def reduce_polynomial(poly):
        return sum((k(c) * x**i for i, c in enumerate(poly.list())), K.zero())

    numerator = f.numerator() if hasattr(f, 'numerator') else f
    denominator = f.denominator() if hasattr(f, 'denominator') else 1
    if not hasattr(numerator, 'list'):
        numerator = PolynomialRing(QQ, names=K.variable_name())(numerator)
    if not hasattr(denominator, 'list'):
        denominator = PolynomialRing(QQ, names=K.variable_name())(denominator)
    den = reduce_polynomial(denominator)
    if not den:
        raise ValueError("integral-basis denominator vanishes identically modulo p")
    return reduce_polynomial(numerator) / den


def _reduced_model(data):
    """Return the reduced rational function field and curve function field.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.ramified import _reduced_model
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: K, L = _reduced_model(SimpleNamespace(Q=y^2 - x, p=5))
        sage: K.characteristic(), L.degree()
        (5, 2)
    """
    k = GF(data.p)
    K = FunctionField(k, names=data.Q.base_ring().variable_name())
    R = PolynomialRing(K, names=data.Q.parent().variable_name())
    try:
        q = R([_reduce_rational_function(c, K) for c in data.Q.list()])
    except (TypeError, ZeroDivisionError) as exc:
        raise ValueError("model is not p-integral") from exc
    if not q.is_irreducible():
        raise ValueError("the reduction is not geometrically represented by an irreducible model")
    return K, K.extension(q, names=data.Q.parent().variable_name())


def _residue(value, place):
    """Return the residue of an integral function at a degree-one place.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.auxiliary import (auxiliary_polynomials,
        ....:     integral_basis_matrices)
        sage: from sage.schemes.curves.coleman.points import point_from_affine_coordinates
        sage: from sage.schemes.curves.coleman.ramified import _residue, local_data
        sage: R.<x> = QQ[]; S.<y> = R[]; Q = y^2 - (x^3 - 10*x + 9)
        sage: r, _, _ = auxiliary_polynomials(Q)
        sage: W0, Winf = integral_basis_matrices(Q)
        sage: data = SimpleNamespace(Q=Q, p=5, N=8, r=r, W0=W0, Winf=Winf)
        sage: P = point_from_affine_coordinates((1, 0), data)
        sage: _, _, place, basis = local_data(P, data)
        sage: _residue(basis[1], place)
        0
    """
    _, _, to_residue = place.residue_field()
    return to_residue(value)


def _padic_residue(value, k):
    """Return the residue of an integral p-adic value in ``k``.

    TESTS::

        sage: from sage.schemes.curves.coleman.ramified import _padic_residue
        sage: _padic_residue(Qp(5, 6)(6), GF(5))
        1
    """
    if value.valuation() < 0:
        raise ValueError("point has a nonintegral basis coordinate")
    return k(value.residue())


def local_data(P, data):
    r"""Return ramification index, parameter index, place and reduced basis.

    ``index=0`` means ``x-x(P)`` (or ``1/x``) is a parameter.  Positive
    indices are one-based.  Only rational residue places can match a point
    represented over ``Qp``.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.auxiliary import (auxiliary_polynomials,
        ....:     integral_basis_matrices)
        sage: from sage.schemes.curves.coleman.points import point_from_affine_coordinates
        sage: from sage.schemes.curves.coleman.ramified import local_data
        sage: R.<x> = QQ[]; S.<y> = R[]; Q = y^2 - (x^3 - 10*x + 9)
        sage: r, _, _ = auxiliary_polynomials(Q)
        sage: W0, Winf = integral_basis_matrices(Q)
        sage: data = SimpleNamespace(Q=Q, p=5, N=8, r=r, W0=W0, Winf=Winf)
        sage: local_data(point_from_affine_coordinates((1, 0), data), data)[:2]
        (2, 2)
    """
    if not is_in_bad_residue_disk(P, data):
        return ZZ.one(), 0
    K, L = _reduced_model(data)
    k = K.constant_base_field()
    W = data.Winf if P.infinity else data.W0
    bmod = tuple(sum((_reduce_rational_function(W[i, j], K) * L.gen()**j
                      for j in range(data.Q.degree())), L.zero())
                 for i in range(data.Q.degree()))
    if P.infinity:
        places = L.places_infinite(degree=1)
        base_function = L(1 / K.gen())
    else:
        a = _padic_residue(P.x, k)
        below = K.maximal_order().ideal(K.gen() - a).place()
        places = [q for q in L.places_above(below) if q.degree() == 1]
        base_function = L(K.gen() - a)
    point_values = tuple(_padic_residue(b, k) for b in P.b)
    matches = []
    for place in places:
        try:
            if all(_residue(b, place) == v for b, v in zip(bmod, point_values)):
                matches.append(place)
        except (ValueError, ZeroDivisionError):
            continue
    if len(matches) != 1:
        raise ValueError("basis coordinates do not select a unique rational place on the normalization")
    place = matches[0]
    e = ZZ(base_function.valuation(place))
    if e < 1:
        raise ArithmeticError("selected place does not lie over the requested base point")
    index = 0
    if e > 1:
        for i, b in enumerate(bmod, 1):
            if (b - L(point_values[i - 1])).valuation(place) == 1:
                index = i
                break
        if not index:
            raise ArithmeticError("the integral basis contains no local uniformizer at this place")
    return e, index, place, bmod


def _one_left_kernel_relation(integral_matrix):
    r"""Return one rational relation among the rows, or ``None``.

    A modular rank profile rejects full-row-rank matrices before any exact
    linear algebra.  When relations exist, one dependent row is recovered
    from a square nonsingular minor and then checked against every column.
    This avoids constructing a basis for a kernel when the caller needs only
    one relation.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.ramified import _one_left_kernel_relation
        sage: A = matrix(ZZ, [[1, 0], [2, 0]])
        sage: relation = _one_left_kernel_relation(A)
        sage: relation * A
        (0, 0)
        sage: _one_left_kernel_relation(identity_matrix(ZZ, 3)) is None
        True
    """
    profiles = []
    for prime in (65521, 65519):
        modular = integral_matrix.change_ring(GF(prime))
        row_pivots = tuple(modular.transpose().pivots())
        if len(row_pivots) == integral_matrix.nrows():
            return None
        profiles.append((len(row_pivots), modular, row_pivots))

    for _, modular, row_pivots in sorted(profiles, reverse=True,
                                         key=lambda item: item[0]):
        pivot_set = set(row_pivots)
        column_pivots = tuple(
            modular.matrix_from_rows(row_pivots).pivots()
        )
        square = integral_matrix.matrix_from_rows_and_columns(
            row_pivots, column_pivots
        ).change_ring(QQ)
        for dependent in range(integral_matrix.nrows()):
            if dependent in pivot_set:
                continue
            right = -vector(
                QQ, [integral_matrix[dependent, column]
                     for column in column_pivots]
            )
            solution = square.solve_left(right)
            relation = vector(QQ, integral_matrix.nrows())
            relation[dependent] = 1
            for row, coefficient in zip(row_pivots, solution):
                relation[row] = coefficient
            if not relation * integral_matrix:
                return relation

    kernel = (
        integral_matrix.transpose().__pari__().matker()
        .mattranspose().sage()
    )
    return None if not kernel.nrows() else kernel.row(0)


def minimal_polynomial(f1, f2, *, max_bound=30):
    r"""Return a polynomial relation for ``f2`` over ``QQ(f1)``.

    Coefficients are polynomials in a new variable ``u``.  A rational
    linear-dependence computation avoids assuming that ``f1`` is the
    original ``x`` coordinate.  The vanishing irreducible factor is chosen.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.ramified import minimal_polynomial
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: from sage.schemes.curves.coleman.auxiliary import _function_field_model
        sage: _, L = _function_field_model(y^2 - x)
        sage: minimal_polynomial(L(L.base_field().gen()), L.gen())
        z^2 - u
        sage: minimal_polynomial(L(1/L.base_field().gen()), L.gen())
        u*z^2 - 1
    """
    if f1.parent() is not f2.parent():
        raise TypeError("f1 and f2 must belong to the same function field")
    L = f1.parent()
    _, _, to_vector = L.vector_space()
    Rx = PolynomialRing(QQ, names='u')
    Rz = PolynomialRing(Rx, names='z')
    try:
        constant = QQ(f2)
    except (TypeError, ValueError):
        pass
    else:
        return Rz.gen() - constant
    if f2 == f1:
        return Rz.gen() - Rx.gen()

    base_generator = L(L.base_field().gen())
    if f1 == base_generator or f1 * base_generator == 1:
        fraction_field = Rx.fraction_field()
        u = fraction_field(Rx.gen())
        argument = u if f1 == base_generator else 1 / u
        coefficients = []
        for coefficient in f2.minimal_polynomial().list():
            numerator = coefficient.numerator()
            denominator = coefficient.denominator()
            numerator_value = sum(
                (QQ(value) * argument**i
                 for i, value in enumerate(numerator.list())),
                fraction_field.zero()
            )
            denominator_value = sum(
                (QQ(value) * argument**i
                 for i, value in enumerate(denominator.list())),
                fraction_field.zero()
            )
            coefficients.append(numerator_value / denominator_value)
        denominator = Rx.one()
        for coefficient in coefficients:
            denominator = denominator.lcm(coefficient.denominator())
        integral = [Rx(denominator * coefficient)
                    for coefficient in coefficients]
        content = next((coefficient for coefficient in integral
                        if coefficient), Rx.one())
        for coefficient in integral:
            if coefficient:
                content = content.gcd(coefficient)
        if content.degree() > 0:
            integral = [coefficient // content for coefficient in integral]
        return Rz(integral)

    max_bound = ZZ(max_bound)
    if max_bound < 5:
        raise ValueError("max_bound must be at least 5")
    bounds = list(range(5, max_bound + 1, 3))
    if bounds[-1] != max_bound:
        bounds.append(max_bound)
    for bound in bounds:
        f1_powers = [L.one()]
        f2_powers = [L.one()]
        for _ in range(bound):
            f1_powers.append(f1_powers[-1] * f1)
            f2_powers.append(f2_powers[-1] * f2)
        terms = [f1_powers[j] * f2_powers[i] for i in range(bound + 1)
                 for j in range(bound + 1)]
        coords = [to_vector(term) for term in terms]
        denominator = coords[0][0].denominator().parent().one()
        for row in coords:
            for c in row:
                denominator = denominator.lcm(c.denominator())
        polynomials = [[(denominator * c).numerator() for c in row]
                       for row in coords]
        degree = max((h.degree() for row in polynomials for h in row if h),
                     default=0)
        columns = [[QQ(h[k]) for h in row for k in range(degree + 1)]
                   for row in polynomials]
        relation_matrix = matrix(QQ, columns)
        matrix_denominator = ZZ.one()
        for entry in relation_matrix.list():
            matrix_denominator = matrix_denominator.lcm(entry.denominator())
        integral_matrix = matrix(
            ZZ, relation_matrix.nrows(), relation_matrix.ncols(),
            [ZZ(matrix_denominator * entry)
             for entry in relation_matrix.list()],
        )
        relation = _one_left_kernel_relation(integral_matrix)
        if relation is None:
            continue
        candidate = Rz([sum((Rx(relation[i * (bound + 1) + j]) * Rx.gen()**j
                             for j in range(bound + 1)), Rx.zero())
                        for i in range(bound + 1)])
        if candidate.degree() < 1:
            continue
        for factor, _ in candidate.factor():
            if factor.degree() < 1:
                continue
            value = sum((L(c(f1)) * f2**i for i, c in enumerate(factor.list())),
                        L.zero())
            if not value:
                denominator = ZZ.one()
                for coefficient in factor.list():
                    for scalar in coefficient.list():
                        denominator = denominator.lcm(QQ(scalar).denominator())
                integral = Rz(denominator * factor)
                content = ZZ.zero()
                for coefficient in integral.list():
                    for scalar in coefficient.list():
                        content = content.gcd(ZZ(scalar))
                return Rz(integral / content)
    raise ArithmeticError("could not determine a polynomial relation within max_bound")


def mod_p_expansion(f, place, parameter, prec):
    """Expand an integral function in the selected normalized parameter.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.auxiliary import (auxiliary_polynomials,
        ....:     integral_basis_matrices)
        sage: from sage.schemes.curves.coleman.points import point_from_affine_coordinates
        sage: from sage.schemes.curves.coleman.ramified import local_data, mod_p_expansion
        sage: R.<x> = QQ[]; S.<y> = R[]; Q = y^2 - (x^3 - 10*x + 9)
        sage: r, _, _ = auxiliary_polynomials(Q)
        sage: W0, Winf = integral_basis_matrices(Q)
        sage: data = SimpleNamespace(Q=Q, p=5, N=8, r=r, W0=W0, Winf=Winf)
        sage: P = point_from_affine_coordinates((1, 0), data)
        sage: _, _, place, basis = local_data(P, data)
        sage: mod_p_expansion(basis[1], place, basis[1], 4)
        t
    """
    if parameter.valuation(place) != 1:
        raise ValueError("the selected element is not a local uniformizer")
    k, from_k, to_k = place.residue_field()
    series = PowerSeriesRing(k, names='t', default_prec=prec)
    coefficients = []
    for _ in range(prec):
        c = to_k(f)
        coefficients.append(c)
        f = (f - from_k(c)) / parameter
    return series(coefficients)


def _specialize_relation(poly, parameter, series_ring):
    """Specialize ``u`` in a relation to a p-adic series.

    TESTS::

        sage: from sage.schemes.curves.coleman.ramified import _specialize_relation
        sage: R.<u> = QQ[]; S.<z> = R[]
        sage: K = Qp(5, 6); T.<t> = PowerSeriesRing(K, default_prec=5)
        sage: coefficients = _specialize_relation(z^2 - (u + 1), t, T)
        sage: all(not c for c in (coefficients[0] + t + 1).list()), coefficients[2]
        (True, 1 + O(5^6))
    """
    def evaluate(c):
        return sum((series_ring(c[i]) * parameter**i
                    for i in range(c.degree() + 1)), series_ring.zero())
    return [evaluate(c) for c in poly.list()]


def _horner(coefficients, value):
    """Evaluate a coefficient sequence at ``value`` by Horner's rule.

    TESTS::

        sage: from sage.schemes.curves.coleman.ramified import _horner
        sage: R.<x> = QQ[]
        sage: _horner([1, 2, 3], x)
        3*x^2 + 2*x + 1
    """
    result = value.parent().zero()
    for c in reversed(coefficients):
        result = result * value + c
    return result


def _mod_p_valuation(series, prec):
    """Return the first exponent with a nonzero coefficient modulo ``p``.

    TESTS::

        sage: from sage.schemes.curves.coleman.ramified import _mod_p_valuation
        sage: K = Qp(5, 6); T.<t> = PowerSeriesRing(K, default_prec=6)
        sage: _mod_p_valuation(5 + t^3, 6)
        3
    """
    for i in range(prec):
        c = series[i]
        if c and c.valuation() <= 0:
            return ZZ(i)
    return ZZ(prec)


def mod_p_prec(coefficients, approximate, prec):
    r"""Test the power-series Hensel criterion modulo ``p``.

    Return the first truncation where the selected root is separated.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.ramified import mod_p_prec
        sage: K = Qp(5, 6); T.<t> = PowerSeriesRing(K, default_prec=6)
        sage: mod_p_prec([-t^2*(1 + t), 0, 1], t, 6)
        3
    """
    derivative = [(i + 1) * coefficients[i + 1]
                  for i in range(len(coefficients) - 1)]
    v2 = _mod_p_valuation(_horner(derivative, approximate), prec)
    v1 = _mod_p_valuation(_horner(coefficients, approximate), prec)
    if v1 <= 2 * v2:
        raise ValueError("t-adic precision does not yet separate the selected root")
    return max(ZZ.one(), 2 * v2 + 1)


def _coefficient_solutions(equation, residue_coefficient, field,
                           residue_field):
    r"""Lift the permitted coefficients of one residue-series term.

    A coefficient equation can be known only as zero at the available
    p-adic precision.  In that case it imposes no condition beyond the
    already selected residue expansion, so its canonical residue lift is a
    valid seed for the subsequent Hensel step.

    TESTS::

        sage: from sage.schemes.curves.coleman.ramified import _coefficient_solutions
        sage: K = Qp(7, 6); R.<z> = K[]; k = GF(7)
        sage: _coefficient_solutions(K(0, absprec=6)*z, k(3), K, k)
        [3 + O(7^6)]
        sage: _coefficient_solutions((z-1)*(z-2), k(2), K, k)
        [2 + O(7^6)]
    """
    if not equation or all(not coefficient for coefficient in equation.list()):
        return [field(residue_coefficient.lift())]
    return [
        solution for solution in equation.roots(multiplicities=False)
        if (solution.valuation() >= 0
            and residue_field(solution.residue()) == residue_coefficient)
    ]


def approximate_root(coefficients, constant, expansion, prec):
    r"""Construct a coefficient-by-coefficient p-adic root seed.

    At degree ``n`` the coefficient of ``t`` with least exponent in
    ``F(root + z*t^n)`` is a polynomial in ``z`` over the p-adic base
    field.  Its linear roots are filtered by the selected residue expansion.
    This is stronger than lifting the residue coefficient as an integer: the
    chosen coefficient is already known to full p-adic precision before the
    subsequent Newton doubling.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.ramified import approximate_root
        sage: K = Qp(5, 8); T.<t> = PowerSeriesRing(K, default_prec=8)
        sage: coefficients = [-t^2*(1 + t), T.zero(), T.one()]
        sage: F = GF(5); U.<u> = PowerSeriesRing(F, default_prec=8)
        sage: expansion = u*(1 + u).sqrt()
        sage: root = approximate_root(coefficients, K(0), expansion, 4)
        sage: (root^2 - t^2*(1 + t)).valuation() >= 5
        True
    """
    ring = coefficients[0].parent()
    if expansion.precision_absolute() < prec:
        raise ValueError("residue expansion has insufficient precision")
    field = ring.base_ring()
    # Only the initial Hensel inequality through ``prec`` is decided here.
    # Building these coefficient equations in the final 1,200-term parent
    # makes a degree-13 relation needlessly huge.
    # A doubled guard precision detects every leading equation relevant to
    # the seed; ``hensel_lift`` subsequently expands to the full target by
    # Newton doubling.
    work_precision = min(ZZ(ring.default_prec()), 2 * ZZ(prec) + 2)
    polynomial_ring = PolynomialRing(field, names='z')
    z = polynomial_ring.gen()
    nested_ring = PowerSeriesRing(
        polynomial_ring, names=ring.variable_name(),
        default_prec=work_precision
    )
    t = nested_ring.gen()

    def nested(series):
        return nested_ring([
            polynomial_ring(c) for c in list(series)[:work_precision]
        ]).add_bigoh(work_precision)

    nested_coefficients = [nested(c) for c in coefficients]
    candidates = [ring(field(constant)).add_bigoh(work_precision)]
    residue_field = expansion.base_ring()
    for degree in range(1, ZZ(prec)):
        next_candidates = []
        for candidate in candidates:
            trial = nested(candidate) + z * t**degree
            value = _horner(nested_coefficients, trial)
            if not value:
                solutions = [field(expansion[degree].lift())]
            else:
                equation = polynomial_ring.zero()
                for exponent in range(ZZ(value.valuation()), work_precision):
                    candidate_equation = polynomial_ring(value[exponent])
                    if any(candidate_equation.list()):
                        equation = candidate_equation
                        break
                solutions = _coefficient_solutions(
                    equation, expansion[degree], field, residue_field
                )
            for solution in solutions:
                next_candidates.append(
                    (candidate + ring(solution) * ring.gen()**degree)
                    .add_bigoh(work_precision)
                )
        candidates = next_candidates
        if not candidates:
            raise ValueError(
                "no p-adic coefficient matches the selected residue root"
            )
    if len(candidates) != 1:
        raise ValueError("the selected residue root is not unique")
    candidate = candidates[0]
    mod_p_prec(coefficients, candidate, prec)
    return candidate


def hensel_lift(coefficients, root, prec=None):
    r"""Hensel lift a selected series root, including a ramified branch.

    A unit derivative uses the fast Newton lift from
    :mod:`sage.schemes.curves.coleman.local`.  A
    derivative divisible by ``t`` is handled in the Laurent-series field;
    coefficient precision must already satisfy the Hensel inequality.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.ramified import hensel_lift
        sage: K = Qp(5, 12)
        sage: T.<t> = PowerSeriesRing(K, default_prec=12)
        sage: z = hensel_lift([-t^2*(1+t), T.zero(), T.one()], t, 12)
        sage: (z^2 - t^2*(1+t)).add_bigoh(12).is_zero()
        True

    The constant term of the root may be irrational, as at a branch point
    whose `x`-coordinate is `\sqrt{2} \in \QQ_7`.  It is then known only to
    the working precision, and a residual that vanishes to that precision
    is treated as zero::

        sage: K = Qp(7, 10); T.<t> = PowerSeriesRing(K, default_prec=12)
        sage: z = hensel_lift([-2 - t, T.zero(), T.one()], T(K(2).sqrt()), 12)
        sage: (z^2 - 2 - t).add_bigoh(12).is_zero()
        True
        sage: z[0] == K(2).sqrt(), z[1] == 1/(2*K(2).sqrt())
        (True, True)

    The lift carries no digits beyond the working absolute precision, even
    when a coefficient has positive valuation.  Here the constant term is the
    root of `X^2 + X - 9` in `3^2\ZZ_3`, as at the Weierstrass point over it
    on `y^2 = x^3 - 10x + 9`::

        sage: K = Qp(3, 10); T.<t> = PowerSeriesRing(K, default_prec=12)
        sage: R.<X> = K[]
        sage: c0 = [r for r, _ in (X^2 + X - 9).roots() if r.valuation() > 0][0]
        sage: z = hensel_lift([-9 - t, T.one(), T.one()], T(c0), 12)
        sage: z[0].precision_absolute(), (z^2 + z - 9 - t).add_bigoh(12).is_zero()
        (10, True)

    An input root may have less precision than its ambient field after a
    multiple-root lift.  Newton arithmetic respects that actual precision
    instead of reviving arbitrary digits from its rational representative::

        sage: K = Qp(7, 12); T.<t> = PowerSeriesRing(K, default_prec=8)
        sage: root = T(K(2).sqrt().add_bigoh(6))
        sage: z = hensel_lift([-2 - t, T.zero(), T.one()], root, 8)
        sage: z[0].precision_absolute(), (z^2 - 2 - t).add_bigoh(8).is_zero()
        (6, True)

    Nonintegral coefficients use the rational-series fallback::

        sage: K = Qp(5, 8); T.<t> = PowerSeriesRing(K, default_prec=8)
        sage: z = hensel_lift([-t/5, T.one()], t/5, 8)
        sage: (z - t/5).add_bigoh(8).is_zero()
        True
    """
    ring = root.parent()
    prec = ZZ(ring.default_prec() if prec is None else prec)
    coefficients = [ring(c).add_bigoh(prec) for c in coefficients]
    derivative = [(i + 1) * coefficients[i + 1]
                  for i in range(len(coefficients) - 1)]
    if not derivative:
        raise ValueError("relation has no simple root")

    def change_precision(series, target, parent):
        r"""Truncate or zero-extend a series to exactly ``target`` terms.

        TESTS:

        This helper is exercised by an integral-coefficient lift::

            sage: from sage.schemes.curves.coleman.ramified import hensel_lift
            sage: K = Qp(5, 6); T.<t> = PowerSeriesRing(K, default_prec=6)
            sage: lifted = hensel_lift(  # indirect doctest
            ....:     [-t, T.one()], t, 6)
            sage: (lifted - t).add_bigoh(6).is_zero()
            True
        """
        return parent(list(series)[:target]).add_bigoh(target)

    # Sage's p-adic elements cap relative precision only, so the reduction
    # also cuts every coefficient at the field's absolute precision.  A
    # residual that vanishes to the available precision then becomes zero in
    # QQ[[t]].  This matters when the root has an irrational constant term.
    field = ring.base_ring()
    finite_precisions = [
        ZZ(coefficient.precision_absolute())
        for series in coefficients + [root]
        for coefficient in series.list()
        if coefficient.precision_absolute() != infinity
    ]
    absolute_precision = min(
        [ZZ(field.precision_cap())] + finite_precisions
    )

    # Integral Qp coefficients can be represented by one dense series over
    # ZZ/p^N ZZ.  Its compiled polynomial arithmetic avoids constructing a
    # separate p-adic object for every coefficient at every Newton step.
    # The rational path below remains necessary for negative valuations and
    # coefficient fields other than Qp.
    try:
        use_modular = (
            absolute_precision > 0
            and field.degree() == 1
            and field(field.prime()).valuation() == 1
            and all(
                not coefficient or coefficient.valuation() >= 0
                for series in coefficients + [root]
                for coefficient in series.list()
            )
        )
    except (AttributeError, TypeError, ValueError):
        use_modular = False

    if use_modular:
        prime = ZZ(field.prime())
        coefficient_ring = IntegerModRing(prime**absolute_precision)
        modular_ring = PowerSeriesRing(
            coefficient_ring, names=ring.variable_name(), default_prec=prec
        )

        def to_modular(series, target):
            return modular_ring([
                coefficient_ring(ZZ(field(coefficient).lift()))
                for coefficient in list(series)[:target]
            ]).add_bigoh(target)

        modular_coefficients = [
            to_modular(series, prec) for series in coefficients
        ]
        modular_derivative = [
            (i + 1) * modular_coefficients[i + 1]
            for i in range(len(modular_coefficients) - 1)
        ]
        current = to_modular(root, prec)
        residual = _horner(modular_coefficients, current)
        derivative_value = _horner(modular_derivative, current)
        if not derivative_value:
            raise ArithmeticError(
                "derivative vanished during local Hensel lift"
            )
        derivative_order = ZZ(derivative_value.valuation())
        if not derivative_value[derivative_order].is_unit():
            raise ValueError(
                "leading derivative coefficient is divisible by p"
            )
        residual_order = ZZ(residual.valuation())
        if residual_order <= 2 * derivative_order:
            raise ValueError(
                "power-series Hensel condition is not satisfied"
            )

        schedule = []
        target = prec
        while target > residual_order:
            schedule.append(target)
            target = (target + 1) // 2 + derivative_order
        schedule.reverse()

        for target in schedule:
            current = change_precision(current, target, modular_ring)
            numerator = _horner(
                [coefficient.add_bigoh(target)
                 for coefficient in modular_coefficients],
                current,
            )
            denominator = _horner(
                [coefficient.add_bigoh(target)
                 for coefficient in modular_derivative],
                current,
            )
            if not denominator:
                raise ArithmeticError(
                    "derivative vanished during local Hensel lift"
                )
            order = ZZ(denominator.valuation())
            unit = denominator.shift(-order)
            if not unit[0].is_unit():
                raise ValueError(
                    "leading derivative coefficient is divisible by p"
                )
            correction = (
                numerator.shift(-order) * unit.inverse_of_unit()
            )
            current = change_precision(
                current - correction, target, modular_ring
            )

        if _horner(modular_coefficients, current).valuation() < prec:
            raise ArithmeticError("local Hensel lift did not converge")
        return ring([
            field(ZZ(coefficient.lift())).add_bigoh(absolute_precision)
            for coefficient in list(current)[:prec]
        ]).add_bigoh(prec)

    # Perform Newton arithmetic over QQ[[t]], with a round trip through the
    # p-adic series ring between steps to reduce every coefficient to the
    # available precision.  This path also supports nonintegral coefficients.
    rational_ring = PowerSeriesRing(
        QQ, names=ring.variable_name(), default_prec=prec
    )
    rational_coefficients = [rational_ring(c).add_bigoh(prec)
                             for c in coefficients]
    rational_derivative = [(i + 1) * rational_coefficients[i + 1]
                           for i in range(len(rational_coefficients) - 1)]

    def reduce_coefficients(series, target):
        r"""Apply p-adic coefficient reduction, then lift back to `\QQ[[t]]`.

        TESTS:

        This helper is exercised by a nonintegral lift::

            sage: from sage.schemes.curves.coleman.ramified import hensel_lift
            sage: K = Qp(5, 6); T.<t> = PowerSeriesRing(K, default_prec=6)
            sage: lifted = hensel_lift(  # indirect doctest
            ....:     [-t/5, T.one()], t/5, 6)
            sage: (lifted - t/5).add_bigoh(6).is_zero()
            True
        """
        padic = ring([field(coefficient).add_bigoh(absolute_precision)
                      for coefficient in list(series)[:target]]).add_bigoh(target)
        return change_precision(padic, target, rational_ring)

    current = change_precision(root, prec, ring)
    current_rational = change_precision(current, prec, rational_ring)
    residual = reduce_coefficients(
        _horner(rational_coefficients, current_rational), prec
    )
    derivative_value = reduce_coefficients(
        _horner(rational_derivative, current_rational), prec
    )
    if not derivative_value:
        raise ArithmeticError("derivative vanished during local Hensel lift")
    derivative_order = ZZ(derivative_value.valuation())
    leading = QQ(derivative_value[derivative_order])
    if leading.valuation(ring.base_ring().prime()) != 0:
        raise ValueError(
            "leading derivative coefficient is divisible by p"
        )
    residual_order = ZZ(residual.valuation())
    if residual_order <= 2 * derivative_order:
        raise ValueError("power-series Hensel condition is not satisfied")

    schedule = []
    target = prec
    while target > residual_order:
        schedule.append(target)
        target = (target + 1) // 2 + derivative_order
    schedule.reverse()

    for target in schedule:
        current_rational = change_precision(current, target, rational_ring)
        numerator = reduce_coefficients(
            _horner(rational_coefficients, current_rational), target
        )
        denominator = reduce_coefficients(
            _horner(rational_derivative, current_rational), target
        )
        if not denominator:
            raise ArithmeticError("derivative vanished during local Hensel lift")
        updated = current_rational - numerator / denominator
        current = change_precision(updated, target, ring)

    # The lift is only correct to the absolute precision used above.  Without
    # this cap a coefficient of positive valuation would report spurious
    # digits beyond it, which later divisions could amplify.
    return ring([field(coefficient).add_bigoh(absolute_precision)
                 for coefficient in list(current)[:prec]]).add_bigoh(prec)


def _rational_bases(data):
    """Return the curve function field and its two integral bases.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.auxiliary import integral_basis_matrices
        sage: from sage.schemes.curves.coleman.ramified import _rational_bases
        sage: R.<x> = QQ[]; S.<y> = R[]; Q = y^2 - x
        sage: W0, Winf = integral_basis_matrices(Q)
        sage: L, finite, infinite = _rational_bases(
        ....:     SimpleNamespace(Q=Q, W0=W0, Winf=Winf))
        sage: L.degree(), len(finite), len(infinite)
        (2, 2, 2)
    """
    cached = getattr(data, "_ramified_rational_bases", None)
    if cached is not None:
        return cached
    K, L = _function_field_model(data.Q)
    cached = (L, _coordinates(L, data.W0), _coordinates(L, data.Winf))
    data._ramified_rational_bases = cached
    return cached


def _cached_minpoly(data, key, first, second):
    """Return and cache the selected function-field relation.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.auxiliary import integral_basis_matrices
        sage: from sage.schemes.curves.coleman.ramified import (_cached_minpoly,
        ....:     _rational_bases)
        sage: R.<x> = QQ[]; S.<y> = R[]; Q = y^2 - x
        sage: W0, Winf = integral_basis_matrices(Q)
        sage: data = SimpleNamespace(Q=Q, W0=W0, Winf=Winf)
        sage: L, finite, _ = _rational_bases(data)
        sage: _cached_minpoly(
        ....:     data, (False, 0, "b", 0), L(L.base_field().gen()), finite[0])
        z - 1
        sage: len(data._ramified_minpolys)
        1
    """
    cache = getattr(data, "_ramified_minpolys", None)
    if cache is None:
        cache = {}
        data._ramified_minpolys = cache
    if key not in cache:
        cache[key] = minimal_polynomial(first, second)
    return cache[key]


def update_minimal_polynomials(data, at_infinity, index):
    r"""Precompute the relations used by a normalized residue disk.

    The value ``index=0`` uses `x` (or `1/x` at infinity) as parameter.  A
    positive one-based ``index`` uses that integral-basis element as
    parameter.  The data object is returned for convenient setup pipelines.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.auxiliary import integral_basis_matrices
        sage: from sage.schemes.curves.coleman.ramified import update_minimal_polynomials
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: Q = y^2 - (x^3 - 10*x + 9)
        sage: W0, Winf = integral_basis_matrices(Q)
        sage: data = SimpleNamespace(Q=Q, W0=W0, Winf=Winf)
        sage: update_minimal_polynomials(data, False, 0) is data
        True
        sage: len(data._ramified_minpolys) == Q.degree()
        True
    """
    index = ZZ(index)
    degree = ZZ(data.Q.degree())
    if index < 0 or index > degree:
        raise ValueError("basis index is out of range")
    L, bfinite, binfinite = _rational_bases(data)
    bfun = binfinite if at_infinity else bfinite
    xfun = (L(1 / L.base_field().gen()) if at_infinity
            else L(L.base_field().gen()))
    location = bool(at_infinity)
    if index == 0:
        for i, function in enumerate(bfun):
            _cached_minpoly(
                data, (location, 0, "b", i), xfun, function
            )
    else:
        parameter = bfun[index - 1]
        _cached_minpoly(
            data, (location, index, "x"), parameter, xfun
        )
        for i, function in enumerate(bfun):
            _cached_minpoly(
                data, (location, index, "b", i), parameter, function
            )
    return data


def _relation_series(f1, f2, parameter, root_constant, place, residue_target,
                     prec, ring, *, relation=None):
    """Lift a selected algebraic relation to a local power series.

    TESTS:

    This helper is exercised by the bad-point coordinate constructor::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.auxiliary import (auxiliary_polynomials,
        ....:     integral_basis_matrices)
        sage: from sage.schemes.curves.coleman.points import point_from_affine_coordinates
        sage: from sage.schemes.curves.coleman.ramified import (find_bad_point_in_disk,
        ....:     local_coordinates)
        sage: R.<x> = QQ[]; S.<y> = R[]; Q = y^2 - (x^3 - 10*x + 9)
        sage: r, _, _ = auxiliary_polynomials(Q)
        sage: W0, Winf = integral_basis_matrices(Q)
        sage: data = SimpleNamespace(Q=Q, p=5, N=8, r=r, W0=W0, Winf=Winf)
        sage: P = find_bad_point_in_disk(
        ....:     point_from_affine_coordinates((1, 0), data), data)
        sage: local_coordinates(P, 12, data)[2]  # indirect doctest
        2
    """
    poly = minimal_polynomial(f1, f2) if relation is None else relation
    coefficients = _specialize_relation(poly, parameter, ring)
    if residue_target is None:
        initial = ring(root_constant)
    else:
        # Compute only enough residue coefficients to separate the chosen root
        # and satisfy v(f) > 2*v(f').  Asking for the full (often 1,200-term)
        # residue expansion defeats the subsequent Newton doubling and spends
        # almost all runtime in place evaluation.
        seed_precision = min(ZZ(2), ZZ(prec))
        while True:
            expansion = mod_p_expansion(
                residue_target[0], place, residue_target[1], seed_precision
            )
            try:
                initial = approximate_root(
                    coefficients, root_constant, expansion, seed_precision
                )
            except ValueError as error:
                if seed_precision >= prec:
                    raise ArithmeticError(
                        "t-adic precision does not separate the selected root"
                    ) from error
                seed_precision = min(ZZ(prec), 2 * seed_precision)
                continue
            return hensel_lift(coefficients, initial, prec)
    return hensel_lift(coefficients, initial, prec)


def local_coordinates(P, prec, data):
    r"""Return ``(x(t), b(t), index)`` at a finite bad or infinite point.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.auxiliary import (auxiliary_polynomials,
        ....:     integral_basis_matrices)
        sage: from sage.schemes.curves.coleman.points import point_from_affine_coordinates
        sage: from sage.schemes.curves.coleman.ramified import (find_bad_point_in_disk,
        ....:     local_coordinates)
        sage: R.<x> = QQ[]; S.<y> = R[]; Q = y^2 - (x^3 - 10*x + 9)
        sage: r, _, _ = auxiliary_polynomials(Q)
        sage: W0, Winf = integral_basis_matrices(Q)
        sage: data = SimpleNamespace(Q=Q, p=5, N=8, r=r, W0=W0, Winf=Winf)
        sage: P = find_bad_point_in_disk(
        ....:     point_from_affine_coordinates((1, 0), data), data)
        sage: xt, bt, index = local_coordinates(P, 12, data)
        sage: index, (bt[1]^2 - (xt^3 - 10*xt + 9)).add_bigoh(12).is_zero()
        (2, True)
    """
    if not is_in_bad_residue_disk(P, data):
        return _good_local_coordinates(P, prec, data)
    prec = ZZ(prec)
    if prec < 2:
        raise ValueError("power-series precision must be at least two")
    if (P._cache_data is data and P.xt is not None and P.bt is not None
            and P.xt.precision_absolute() >= prec
            and all(b.precision_absolute() >= prec for b in P.bt)):
        return P.xt.add_bigoh(prec), tuple(b.add_bigoh(prec) for b in P.bt), P.index
    if not is_bad_residue_disk_center(P, data):
        raise ValueError("first lift the disk to its point above a root of r or infinity")
    workprec = prec
    for _ in range(4):
        xt, bt, index = _local_coord_at_precision(P, workprec, data)
        if (xt.precision_absolute() >= prec
                and all(b.precision_absolute() >= prec for b in bt)):
            P.xt, P.bt, P.index, P._cache_data = xt, bt, index, data
            return xt.add_bigoh(prec), tuple(b.add_bigoh(prec) for b in bt), index
        workprec *= 2
    raise ArithmeticError("local coordinate lost too much t-adic precision")


def _local_coord_at_precision(P, prec, data):
    """Compute local expansions at an internal working precision.

    TESTS::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.auxiliary import (auxiliary_polynomials,
        ....:     integral_basis_matrices)
        sage: from sage.schemes.curves.coleman.points import point_from_affine_coordinates
        sage: from sage.schemes.curves.coleman.ramified import (_local_coord_at_precision,
        ....:     find_bad_point_in_disk)
        sage: R.<x> = QQ[]; S.<y> = R[]; Q = y^2 - (x^3 - 10*x + 9)
        sage: r, _, _ = auxiliary_polynomials(Q)
        sage: W0, Winf = integral_basis_matrices(Q)
        sage: data = SimpleNamespace(Q=Q, p=5, N=8, r=r, W0=W0, Winf=Winf)
        sage: P = find_bad_point_in_disk(
        ....:     point_from_affine_coordinates((1, 0), data), data)
        sage: xt, bt, index = _local_coord_at_precision(P, 12, data)
        sage: index, (bt[1]^2 - (xt^3 - 10*xt + 9)).add_bigoh(12).is_zero()
        (2, True)
    """
    _, index, place, bmod = local_data(P, data)
    L, bfinite, binfinite = _rational_bases(data)
    bfun = binfinite if P.infinity else bfinite
    xfun = L(1 / L.base_field().gen()) if P.infinity else L(L.base_field().gen())
    residue_xfun = bmod[0].parent()(1 / bmod[0].parent().base_field().gen()) if P.infinity else bmod[0].parent()(bmod[0].parent().base_field().gen())
    field = P.x.parent()
    ring = PowerSeriesRing(field, names='t', default_prec=prec)
    t = ring.gen()
    if index == 0:
        xt = (ring(P.x) + t).add_bigoh(prec)
        residue_parameter = (residue_xfun - residue_xfun.parent()(P.x.residue()))
        bt = tuple(_relation_series(
                       xfun, f, xt, P.b[i], place,
                       (bmod[i], residue_parameter), prec, ring,
                       relation=_cached_minpoly(
                           data, (P.infinity, 0, "b", i), xfun, f
                       )
                   )
                   for i, f in enumerate(bfun))
    else:
        j = index - 1
        parameter = (ring(P.b[j]) + t).add_bigoh(prec)
        residue_parameter = bmod[j] - bmod[j].parent()(P.b[j].residue())
        xt = _relation_series(
            bfun[j], xfun, parameter, P.x, place,
            (residue_xfun, residue_parameter), prec, ring,
            relation=_cached_minpoly(
                data, (P.infinity, index, "x"), bfun[j], xfun
            )
        )
        bt = []
        for i, f in enumerate(bfun):
            if i == j:
                bt.append(parameter)
            else:
                bt.append(_relation_series(
                    bfun[j], f, parameter, P.b[i], place,
                    (bmod[i], residue_parameter), prec, ring,
                    relation=_cached_minpoly(
                        data, (P.infinity, index, "b", i), bfun[j], f
                    )
                ))
        bt = tuple(bt)
    return xt, bt, index


def _digit_lifted_padic_root(poly, approximate, target):
    """Lift one integral residue class by enumerating successive digits.

    Return ``None`` if the available precision does not isolate one branch.

    TESTS::

        sage: from sage.schemes.curves.coleman.ramified import _digit_lifted_padic_root
        sage: K = Qp(5, 8); R.<z> = K[]
        sage: _digit_lifted_padic_root(z^2 - 1, K(1), 8)
        1 + O(5^8)
        sage: _digit_lifted_padic_root((z - 5)*(z + 5), K(0), 8) is None
        True
    """
    if approximate.valuation() < 0:
        return None
    field = approximate.parent()
    p = ZZ(field.prime())
    target = ZZ(target)
    candidates = [ZZ(approximate.residue())]
    modulus = p
    for precision in range(1, target):
        next_modulus = modulus * p
        candidates = [
            candidate + digit * modulus
            for candidate in candidates
            for digit in range(p)
            if poly(field(candidate + digit * modulus)).valuation()
            >= precision + 1
        ]
        if not candidates or len(candidates) > 10000:
            return None
        modulus = next_modulus

    derivative = poly.derivative()
    branches = {}
    for candidate in candidates:
        value = field(candidate)
        derivative_value = derivative(value)
        if not derivative_value:
            return None
        precision = max(
            ZZ.one(),
            target - max(ZZ.zero(), ZZ(derivative_value.valuation()))
        )
        representative = candidate % p**precision
        branches[(precision, representative)] = value
    if len(branches) != 1:
        return None
    (precision, representative), _ = branches.popitem()
    root = field(representative).add_bigoh(precision)
    if poly(root).valuation() < target:
        return None
    return root


def _multiple_root_center(poly, approximate, target):
    r"""Lift the common center of a residue-multiple root cluster.

    The derivative of order one less than the residual multiplicity has a
    simple root at the common center.  A center is returned only when it also
    satisfies the original relation to ``target`` digits.

    TESTS::

        sage: from sage.schemes.curves.coleman.ramified import _multiple_root_center
        sage: K = Qp(5, 8); R.<z> = K[]
        sage: root = K(1 + 5 + 2*5^2)
        sage: lifted = _multiple_root_center((z-root)^2, K(1), 8)
        sage: lifted.precision_absolute(), ((lifted-root)^2).valuation() >= 8
        (4, True)
        sage: _multiple_root_center(z^2 + K(0, 8), K(10, 2), 8)
        O(5^4)
        sage: _multiple_root_center((z-5)*(z+5), K(0), 8) is None
        True
    """
    if approximate.valuation() < 0:
        return None
    field = approximate.parent()
    p = ZZ(field.prime())
    nonzero_valuations = [coefficient.valuation()
                          for coefficient in poly if coefficient]
    if not nonzero_valuations:
        return None
    scale_valuation = min(nonzero_valuations)
    scale = field(p)**scale_valuation
    residue_field = GF(p)
    residue_ring = PolynomialRing(
        residue_field, names=poly.parent().variable_name()
    )
    residue_poly = residue_ring([
        residue_field((coefficient / scale).residue())
        if coefficient else residue_field.zero()
        for coefficient in poly
    ])
    residue_root = residue_field(approximate.residue())
    divisor = residue_ring.gen() - residue_root
    multiplicity = ZZ.zero()
    while residue_poly and residue_poly(residue_root) == 0:
        residue_poly, remainder = residue_poly.quo_rem(divisor)
        if remainder:
            break
        multiplicity += 1
    if multiplicity < 2:
        return None

    deflated = poly
    for _ in range(multiplicity - 1):
        deflated = deflated.derivative()
    derivative = deflated.derivative()
    root = field(approximate).lift_to_precision()
    for _ in range(max(8, 2 * ZZ(target).nbits() + 4)):
        value = deflated(root)
        if value.valuation() >= target:
            break
        derivative_value = derivative(root)
        if (not derivative_value
                or value.valuation() <= 2 * derivative_value.valuation()):
            return None
        root -= value / derivative_value
    if (deflated(root).valuation() < target
            or poly(root).valuation() < target):
        return None
    root_precision = root.precision_absolute()
    relation_precision = (ZZ(target) + multiplicity - 1) // multiplicity
    precision = (relation_precision if root_precision == infinity
                 else min(ZZ(root_precision), relation_precision))
    return root.add_bigoh(precision)


def _selected_padic_root(poly, approximate):
    """Choose the unique rational p-adic root in the same residue class.

    TESTS::

        sage: from sage.schemes.curves.coleman.ramified import _selected_padic_root
        sage: K = Qp(5, 8); R.<z> = K[]
        sage: _selected_padic_root(z^2 - 1, K(1))
        1 + O(5^8)

    A simple root can still be lifted when cancellation leaves an inexact
    zero coefficient::

        sage: uncertain = K(5^3).add_bigoh(5)
        sage: lifted = _selected_padic_root(z + uncertain, K(0))
        sage: lifted.precision_absolute(), (lifted + uncertain).valuation() >= 5
        (5, True)

    An exact multiple root can be represented by its common center::

        sage: exact_enough = _selected_padic_root((z - K(1))^2, K(1))
        sage: exact_enough, ((exact_enough - 1)^2).valuation() >= 8
        (1 + O(5^4), True)

    Distinct roots in one residue class are ambiguous and are refused::

        sage: _selected_padic_root(z^2 - 25, K(5 + 5^4))
        Traceback (most recent call last):
        ...
        ValueError: the selected disk has no unique Qp-rational lift
    """
    field = approximate.parent()
    coefficient_precisions = [
        ZZ(coefficient.precision_absolute())
        for coefficient in poly
        if coefficient.precision_absolute() != infinity
    ]
    target = min([ZZ(field.precision_cap())] + coefficient_precisions)
    root = field(approximate)
    derivative = poly.derivative()

    def root_precision(candidate):
        derivative_value = derivative(candidate)
        if not derivative_value:
            return target
        return max(ZZ.zero(),
                   target - max(ZZ.zero(), ZZ(derivative_value.valuation())))

    value = poly(root)
    derivative_value = derivative(root)
    if (value.valuation() >= target and derivative_value
            and derivative_value.valuation() == 0):
        return root.add_bigoh(root_precision(root))
    multiple_root = _multiple_root_center(poly, approximate, target)
    if multiple_root is not None:
        return multiple_root
    factorization_error = None
    try:
        factor_field = Qp(field.prime(), prec=target)
        factor_ring = PolynomialRing_dense_padic_field_capped_relative(
            factor_field, name=poly.parent().variable_name()
        )
        factor_poly = factor_ring(
            [factor_field(coefficient) for coefficient in poly]
        )
        factors = factor_poly.factor()
    except NotImplementedError:
        factors = ()
    except PrecisionError as error:
        factorization_error = error
        factors = ()
    candidates = []
    for factor, _ in factors:
        if factor.degree() != 1:
            continue
        candidate = field(-factor[0] / factor[1])
        if ((candidate - approximate).valuation() > 0
                and poly(candidate).valuation() >= target):
            precision = min(
                ZZ(candidate.precision_absolute()),
                root_precision(candidate),
            )
            candidates.append(candidate.add_bigoh(precision))
    if len(candidates) == 1:
        return candidates[0]
    if len(candidates) > 1:
        raise ValueError(
            "the selected disk has no unique Qp-rational lift"
        )
    lifted = _digit_lifted_padic_root(poly, approximate, target)
    if lifted is not None:
        return lifted
    if factorization_error is not None:
        raise factorization_error
    raise ValueError("the selected disk has no unique Qp-rational lift")


def _at_padic_value(poly, value, field):
    """Specialize the coefficient variable of ``poly`` at ``value``.

    TESTS::

        sage: from sage.schemes.curves.coleman.ramified import _at_padic_value
        sage: R.<u> = QQ[]; S.<z> = R[]; K = Qp(5, 8)
        sage: _at_padic_value(z + u + 1, K(2), K)
        (1 + O(5^8))*z + 3 + O(5^8)
    """
    try:
        exact_rational = value.parent() is QQ
    except AttributeError:
        exact_rational = False
    if exact_rational:
        return PolynomialRing(field, names='z')(
            [field(coefficient(value)) for coefficient in poly.list()]
        )
    return PolynomialRing(field, names='z')(
        [sum((field(c[i]) * value**i for i in range(c.degree() + 1)),
             field.zero()) for c in poly.list()]
    )


def find_bad_point_in_disk(P, data):
    r"""Lift a bad residue disk to its point above ``r=0`` or infinity.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.auxiliary import (auxiliary_polynomials,
        ....:     integral_basis_matrices)
        sage: from sage.schemes.curves.coleman.points import point_from_affine_coordinates
        sage: from sage.schemes.curves.coleman.ramified import find_bad_point_in_disk
        sage: R.<x> = QQ[]; S.<y> = R[]; Q = y^2 - (x^3 - 10*x + 9)
        sage: r, _, _ = auxiliary_polynomials(Q)
        sage: W0, Winf = integral_basis_matrices(Q)
        sage: data = SimpleNamespace(Q=Q, p=5, N=8, r=r, W0=W0, Winf=Winf)
        sage: P = find_bad_point_in_disk(
        ....:     point_from_affine_coordinates((1, 0), data), data)
        sage: P.x, P.b
        (1 + O(5^8), (1 + O(5^8), O(5^4)))
    """
    if not is_in_bad_residue_disk(P, data):
        raise ValueError("residue disk does not contain a bad point")
    field = P.x.parent()
    if P.infinity:
        x0 = field.zero()
        relation_x = QQ.zero()
    else:
        rational_roots = [(a, field(a)) for a, _ in data.r.roots(QQ)
                          if (field(a) - P.x).valuation() > 0]
        if len(rational_roots) == 1:
            relation_x, x0 = rational_roots[0]
        else:
            r = PolynomialRing(field, names='x')([field(c) for c in data.r.list()])
            x0 = _selected_padic_root(r, P.x)
            relation_x = x0
    _, index, _, _ = local_data(P, data)
    L, bfinite, binfinite = _rational_bases(data)
    bfun = binfinite if P.infinity else bfinite
    xfun = L(1 / L.base_field().gen()) if P.infinity else L(L.base_field().gen())
    values = list(P.b)
    if index == 0:
        for i, b in enumerate(bfun):
            relation = _cached_minpoly(
                data, (P.infinity, 0, "b", i), xfun, b
            )
            values[i] = _selected_padic_root(
                _at_padic_value(relation, relation_x, field), values[i])
    else:
        j = index - 1
        relation = _cached_minpoly(
            data, (P.infinity, 0, "b", j), xfun, bfun[j]
        )
        values[j] = _selected_padic_root(
            _at_padic_value(relation, relation_x, field), values[j])
        for i, b in enumerate(bfun):
            if i == j:
                continue
            relation = _cached_minpoly(
                data, (P.infinity, index, "b", i), bfun[j], b
            )
            values[i] = _selected_padic_root(
                _at_padic_value(relation, values[j], field), values[i])
    return ColemanIntegrationPoint(
        x=x0, b=tuple(values), infinity=P.infinity
    )
