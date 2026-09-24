# sage.doctest: needs sage.rings.number_field sage.rings.padics
r"""
Finite-precision cohomological reductions for general plane curves

These routines reduce Frobenius pullbacks modulo exact differentials.  The
implementation keeps characteristic-zero representatives and balances every
coefficient modulo the requested power of ``p`` while keeping the small
matrix inversions exact.

"""

from sage.matrix.constructor import identity_matrix, matrix
from sage.modules.free_module_element import vector

from sage.rings.integer_ring import ZZ
from sage.rings.laurent_series_ring import LaurentSeriesRing
from sage.rings.number_field.number_field import NumberField
from sage.rings.rational_field import QQ

from .auxiliary import _model_rings, _validate_prime, positive_log
from .cohomology import order_matrix_at_infinity, order_matrix_at_zero


def _reduce_rational_sequence_mod_prime_power(values, p, N):
    r"""Reduce rational values using one common denominator.

    The common denominator makes reduction of polynomial and matrix
    coefficients a single modular inversion rather than a sequence of
    independent rational normalizations.

    TESTS::

        sage: from sage.schemes.curves.coleman.reductions import _reduce_rational_sequence_mod_prime_power
        sage: _reduce_rational_sequence_mod_prime_power(
        ....:     [QQ(13)/6, QQ(14)/15, 0], 5, 2)
        [-2, -37/5, 0]
    """
    values = [QQ(value) for value in values]
    if not values:
        return []
    denominator = ZZ.one()
    for value in values:
        denominator = denominator.lcm(value.denominator())
    denominator_valuation = ZZ(denominator.valuation(p))
    p_power = p**denominator_valuation
    modulus = p**(N + denominator_valuation)
    unit_inverse = (denominator // p_power).inverse_mod(modulus)
    reduced = []
    for value in values:
        residue = (ZZ(value * denominator) * unit_inverse) % modulus
        if 2 * residue >= modulus:
            residue -= modulus
        reduced.append(QQ(residue) / p_power)
    return reduced


def _coefficient_valuation(value, p):
    r"""Return the least ``p``-adic valuation among scalar coefficients.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.reductions import _coefficient_valuation
        sage: R.<x> = QQ[]
        sage: _coefficient_valuation((x^2 + 5*x)/25, 5)
        -2
    """
    try:
        return ZZ(QQ(value).valuation(p))
    except (TypeError, ValueError):
        valuations = [_coefficient_valuation(coefficient, p)
                      for coefficient in value.list() if coefficient]
        return min(valuations, default=ZZ.zero())


def reduce_rational_mod_prime_power(value, p, N):
    r"""Return a balanced rational representative modulo ``p^N``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.reductions import reduce_rational_mod_prime_power
        sage: reduce_rational_mod_prime_power(QQ(130)/3, 5, 2)
        10
    """
    p = _validate_prime(p)
    N = ZZ(N)
    return _reduce_rational_sequence_mod_prime_power([value], p, N)[0]


def reduce_polynomial_mod_prime_power(polynomial, p, N):
    r"""Reduce every coefficient of a rational polynomial modulo ``p^N``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.reductions import reduce_polynomial_mod_prime_power
        sage: R.<x> = QQ[]
        sage: reduce_polynomial_mod_prime_power(13*x + 14, 5, 2)
        -12*x - 11
    """
    p = _validate_prime(p)
    N = ZZ(N)
    parent = polynomial.parent()
    return parent(_reduce_rational_sequence_mod_prime_power(
        polynomial.list(), p, N
    ))


def reduce_matrix_mod_prime_power(A, p, N):
    r"""Reduce a rational matrix coefficientwise modulo ``p^N``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.reductions import reduce_matrix_mod_prime_power
        sage: reduce_matrix_mod_prime_power(matrix(QQ, [[13, 14], [1/2, 0]]), 5, 2)
        [-12 -11]
        [-12   0]
    """
    p = _validate_prime(p)
    N = ZZ(N)
    return matrix(QQ, A.nrows(), A.ncols(),
                  _reduce_rational_sequence_mod_prime_power(A.list(), p, N))


def _number_field_coefficients(value):
    """Return the power-basis coefficients of a number-field element.

    TESTS::

        sage: from sage.schemes.curves.coleman.reductions import _number_field_coefficients
        sage: R.<x> = QQ[]; K.<a> = NumberField(x^2 - 2)
        sage: _number_field_coefficients(13*a + 14)
        [14, 13]
    """
    if value.parent() is QQ:
        return [QQ(value)]
    return [QQ(coefficient) for coefficient in value.list()]


def reduce_number_field_mod_prime_power(value, p, N):
    r"""Reduce a number-field element coefficientwise modulo ``p^N``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.reductions import reduce_number_field_mod_prime_power
        sage: R.<x> = QQ[]; K.<a> = NumberField(x^2 - 2)
        sage: reduce_number_field_mod_prime_power(13*a + 14, 5, 2)
        -12*a - 11
    """
    p = _validate_prime(p)
    N = ZZ(N)
    parent = value.parent()
    if parent is QQ:
        return _reduce_rational_sequence_mod_prime_power([value], p, N)[0]
    return parent(_reduce_rational_sequence_mod_prime_power(
        _number_field_coefficients(value), p, N
    ))


def reduce_number_field_matrix_mod_prime_power(A, p, N):
    r"""Reduce a number-field matrix coefficientwise modulo ``p^N``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.reductions import reduce_number_field_matrix_mod_prime_power
        sage: R.<x> = QQ[]; K.<a> = NumberField(x^2 - 2)
        sage: reduce_number_field_matrix_mod_prime_power(
        ....:     matrix(K, [[13*a + 14]]), 5, 2)
        [-12*a - 11]
    """
    p = _validate_prime(p)
    N = ZZ(N)
    base_ring = A.base_ring()
    if base_ring is QQ:
        entries = _reduce_rational_sequence_mod_prime_power(A.list(), p, N)
    else:
        coefficient_lists = [
            _number_field_coefficients(entry) for entry in A.list()
        ]
        lengths = [len(coefficients) for coefficients in coefficient_lists]
        reduced = _reduce_rational_sequence_mod_prime_power(
            [coefficient
             for coefficients in coefficient_lists
             for coefficient in coefficients],
            p, N
        )
        entries = []
        offset = 0
        for length in lengths:
            entries.append(base_ring(reduced[offset:offset + length]))
            offset += length
    return matrix(base_ring, A.nrows(), A.ncols(), entries)


def reduce_laurent_mod_prime_power(f, p, N):
    r"""Reduce a finite Laurent series coefficientwise modulo ``p^N``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.reductions import reduce_laurent_mod_prime_power
        sage: L.<z> = LaurentSeriesRing(QQ)
        sage: reduce_laurent_mod_prime_power(13*z^-1 + 14*z, 5, 2)
        -12*z^-1 - 11*z
    """
    p = _validate_prime(p)
    N = ZZ(N)
    parent = f.parent()
    if not f:
        return parent.zero()
    variable = parent.gen()
    valuation = ZZ(f.valuation())
    coefficients = _reduce_rational_sequence_mod_prime_power(f.list(), p, N)
    return sum((coefficient
                * variable**(valuation + offset)
                for offset, coefficient in enumerate(coefficients)
                if coefficient), parent.zero())


def inverse_number_field_mod_prime_power(value, p, N):
    r"""Return a reduced representative of ``1/value`` modulo ``p^N``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.reductions import inverse_number_field_mod_prime_power
        sage: R.<x> = QQ[]; K.<a> = NumberField(x^2 - 2)
        sage: inverse_number_field_mod_prime_power(1 + a, 5, 2)
        a - 1
    """
    if not value:
        raise ZeroDivisionError("cannot invert zero")
    return reduce_number_field_mod_prime_power(value**(-1), p, N)


def push_matrix_to_field(A, field):
    r"""Coerce a rational matrix into ``field``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.reductions import push_matrix_to_field
        sage: R.<x> = QQ[]; K.<a> = NumberField(x^2 - 2)
        sage: push_matrix_to_field(matrix(QQ, [[1, 2]]), K)
        [1 2]
    """
    entries = []
    for entry in A.list():
        parent = entry.parent()
        if field is not QQ and parent is not QQ and parent is not field:
            entries.append(field(_number_field_coefficients(entry)))
        else:
            entries.append(field(entry))
    return matrix(field, A.nrows(), A.ncols(), entries)


def _field_polynomial(value, polynomial_ring):
    """Express a rational or number-field element in its power basis.

    TESTS::

        sage: from sage.schemes.curves.coleman.reductions import _field_polynomial
        sage: R.<x> = QQ[]; K.<a> = NumberField(x^2 - 2)
        sage: _field_polynomial(1 + 2*a, R)
        2*x + 1
    """
    if value.parent() is QQ:
        return polynomial_ring(value)
    return polynomial_ring(value.list())


def _crt_idempotents(r, factors):
    """Return the standard polynomial CRT idempotents for squarefree ``r``.

    TESTS::

        sage: from sage.schemes.curves.coleman.reductions import _crt_idempotents
        sage: R.<x> = QQ[]; r = (x - 1)*(x + 1)
        sage: values = _crt_idempotents(r, [x - 1, x + 1])
        sage: [(e^2 - e) % r for e in values], sum(values) % r
        ([0, 0], 1)
    """
    output = []
    for factor in factors:
        quotient = r.quo_rem(factor)[0]
        inverse = quotient.inverse_mod(factor)
        output.append((quotient * inverse) % r)
    return output


def reduction_matrices(Q, p, N, r, W0, Winf, e0, einf,
                       J0, Jinf, T0, Tinf, T0inv, Tinfinv):
    r"""Precompute finite and infinite cohomological reduction matrices.

    TESTS:

    The data constructor exercises this routine::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(  # indirect doctest
        ....:     y^2 - (x^3 - 10*x + 9), 5, 3, genus=1)
        sage: len(data.finite_reduction_matrices), len(data.infinite_reduction_matrices)
        (25, 7)
    """
    p = _validate_prime(p)
    N = ZZ(N)
    polynomial_ring, _ = _model_rings(Q, require_monic=True)
    degree = Q.degree()
    r = polynomial_ring(r)
    r = polynomial_ring(r / r.leading_coefficient())
    factors = [factor.monic() for factor, _ in r.factor()]

    N0 = ZZ(positive_log(p, p * e0 * (N - 1)).floor())
    working_precision_finite = N + N0
    count_finite = p * (N - 1)
    per_factor = []
    reduced_factors = []
    for index, factor in enumerate(factors):
        reduced_factor = reduce_polynomial_mod_prime_power(
            factor, p, working_precision_finite
        )
        reduced_factors.append(reduced_factor)
        field_factor = (
            reduced_factor
            if reduced_factor.degree() == 1 or reduced_factor.is_irreducible()
            else factor
        )
        if field_factor.degree() == 1:
            field = QQ
            root = -field_factor[0]
        else:
            field = NumberField(field_factor, name="a")
            root = field.gen()
        D = push_matrix_to_field(J0[index], field)
        P = reduce_number_field_matrix_mod_prime_power(
            push_matrix_to_field(T0[index], field),
            p, working_precision_finite
        )
        P_inverse = reduce_number_field_matrix_mod_prime_power(
            push_matrix_to_field(T0inv[index], field),
            p, working_precision_finite
        )
        denominator_inverse = reduce_number_field_mod_prime_power(
            field(r.derivative()(root))**(-1), p, working_precision_finite
        )
        matrices = []
        identity = identity_matrix(field, degree)
        for _ in range(count_finite):
            D -= identity
            reduction = P_inverse * D.inverse() * P
            reduction *= denominator_inverse
            matrices.append(reduce_number_field_matrix_mod_prime_power(
                reduction, p, working_precision_finite
            ))
        per_factor.append(matrices)

    r_reduced = reduce_polynomial_mod_prime_power(
        r, p, working_precision_finite
    )
    crt_modulus = polynomial_ring.one()
    for factor in reduced_factors:
        crt_modulus *= factor
    idempotents = _crt_idempotents(crt_modulus, reduced_factors)
    finite = []
    for step in range(count_finite):
        entries = []
        for row in range(degree):
            for column in range(degree):
                entry = polynomial_ring.zero()
                for index in range(len(factors)):
                    local = _field_polynomial(
                        per_factor[index][step][row, column], polynomial_ring
                    )
                    entry += (local * idempotents[index]) % r_reduced
                entries.append(reduce_polynomial_mod_prime_power(
                    entry % r_reduced, p, working_precision_finite
                ))
        finite.append(matrix(polynomial_ring, degree, degree, entries))

    W = Winf * W0.inverse()
    Ninf = ZZ(positive_log(
        p, -(order_matrix_at_infinity(W.inverse()) + 1) * einf
    ).floor())
    working_precision_infinite = N + N0 + Ninf
    count_infinite = ZZ(
        -p * (order_matrix_at_zero(W)
              + order_matrix_at_infinity(W) + 1)
        - order_matrix_at_infinity(W.inverse())
    )
    infinite = []
    for step in range(1, count_infinite + 1):
        shifted = Jinf - step * identity_matrix(QQ, degree)
        reduction = Tinfinv * shifted.inverse() * Tinf
        infinite.append(reduce_matrix_mod_prime_power(
            reduction, p, working_precision_infinite
        ))
    return finite, infinite


def modular_to_rational_laurent_vector(w, Q):
    r"""Lift a modular radix vector to Laurent series over ``QQ[x]``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.frobenius import frobenius_rings
        sage: from sage.schemes.curves.coleman.reductions import modular_to_rational_laurent_vector
        sage: _, R5, L5, _ = frobenius_rings(5, 3)
        sage: z = L5.gen(); R.<x> = QQ[]; S.<y> = R[]
        sage: w = vector(L5, [L5(R5([1, 2]))*z^-1, 0])
        sage: modular_to_rational_laurent_vector(w, y^2 - x)
        ((2*x + 1)*z^-1, 0)
    """
    polynomial_ring, _ = _model_rings(Q, require_monic=True)
    laurent_ring = LaurentSeriesRing(polynomial_ring, names="z")
    z = laurent_ring.gen()
    output = []
    for entry in w:
        if not entry:
            output.append(laurent_ring.zero())
            continue
        valuation = ZZ(entry.valuation())
        lifted = laurent_ring.zero()
        for offset, coefficient in enumerate(entry.list()):
            if coefficient:
                polynomial = polynomial_ring([
                    ZZ(scalar.lift()) if hasattr(scalar, "lift") else ZZ(scalar)
                    for scalar in coefficient.list()
                ])
                lifted += polynomial * z**(valuation + offset)
        output.append(lifted)
    return vector(laurent_ring, output)


def polynomial_vector_to_laurent_series(w, data):
    r"""Convert an ordinary polynomial vector to the radix Laurent format.

    First reduce the coefficients modulo ``p^N`` in the nested Frobenius
    rings, then lift balanced representatives back to Laurent series over
    ``QQ[x]``.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.reductions import polynomial_vector_to_laurent_series
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = SimpleNamespace(p=5, N=3, Q=y^2 - x)
        sage: polynomial_vector_to_laurent_series(vector(R, [1 + x, 0]), data)
        ((x + 1), 0)
    """
    from .frobenius import frobenius_rings

    _, polynomial_ring, laurent_ring, _ = frobenius_rings(data.p, data.N)
    if len(w) != data.Q.degree():
        raise ValueError("w must have one entry for each power of y")
    modular = []
    for entry in w:
        coefficients = entry.list() if hasattr(entry, "list") else [entry]
        modular.append(laurent_ring(polynomial_ring(coefficients)))
    return modular_to_rational_laurent_vector(
        vector(laurent_ring, modular), data.Q
    )


def vector_laurent_valuation(v):
    r"""Return the minimum valuation among the nonzero entries of ``v``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.reductions import vector_laurent_valuation
        sage: L.<z> = LaurentSeriesRing(QQ)
        sage: vector_laurent_valuation(vector(L, [z^-2 + 1, z]))
        -2
    """
    valuations = [ZZ(entry.valuation()) for entry in v if entry]
    return min(valuations) if valuations else ZZ.zero()


def reduce_finite(w, Q, p, N, r, G0, finite_matrices):
    r"""Reduce finite poles in a differential represented in the ``b^0`` basis.

    EXAMPLES::

        sage: from types import SimpleNamespace
        sage: from sage.schemes.curves.coleman.reductions import (polynomial_vector_to_laurent_series,
        ....:     reduce_finite)
        sage: R.<x> = QQ[]; S.<y> = R[]; Q = y^2 - x
        sage: data = SimpleNamespace(p=5, N=3, Q=Q)
        sage: w = polynomial_vector_to_laurent_series(vector(R, [0, 0]), data)
        sage: reduce_finite(w, Q, 5, 3, x + 1, identity_matrix(QQ, 2), [])
        ((0, 0), (0, 0))
    """
    p = _validate_prime(p)
    N = ZZ(N)
    polynomial_ring, _ = _model_rings(Q, require_monic=True)
    degree = Q.degree()
    laurent_ring = w.base_ring()
    z = laurent_ring.gen()
    r_input = polynomial_ring(r)
    r_monic = polynomial_ring(r_input / r_input.leading_coefficient())
    f0 = vector(laurent_ring, degree)
    if not any(w):
        return w, f0

    pole_order = -vector_laurent_valuation(w)
    if pole_order <= 0:
        return w, f0
    if pole_order > len(finite_matrices):
        raise ValueError("finite reduction list is too short")

    coefficients = []
    for entry in w:
        data = {}
        if entry:
            valuation = ZZ(entry.valuation())
            for offset, coefficient in enumerate(entry.list()):
                if coefficient:
                    data[valuation + offset] = polynomial_ring(coefficient)
        coefficients.append(data)

    M = matrix(polynomial_ring, degree, degree,
               [polynomial_ring(r_monic * entry) for entry in G0.list()])
    derivative_r = r_monic.derivative()
    for pole in range(pole_order, 0, -1):
        w_vector = vector(polynomial_ring,
                          [data.get(-pole, polynomial_ring.zero())
                           for data in coefficients])
        reduction_matrix = finite_matrices[pole - 1]
        v_vector = w_vector * reduction_matrix
        v_vector = vector(polynomial_ring,
                          [reduce_polynomial_mod_prime_power(entry % r_monic, p, N)
                           for entry in v_vector])
        for i in range(degree):
            f0[i] += laurent_ring(v_vector[i]) * z**(-pole)

        differential_matrix = matrix(polynomial_ring, M)
        for i in range(degree):
            differential_matrix[i, i] -= pole * derivative_r
        remainder = w_vector - v_vector * differential_matrix
        next_coefficient = []
        for i in range(degree):
            # The precomputed inverse is only known modulo p^N, so the
            # omitted remainder is p^N-divisible.  Only the polynomial
            # quotient contributes at the available precision.
            quotient = remainder[i].quo_rem(r_monic)[0]
            value = quotient - v_vector[i].derivative()
            next_coefficient.append(reduce_polynomial_mod_prime_power(value, p, N))
            coefficients[i].pop(-pole, None)
            coefficients[i][-pole + 1] = (
                coefficients[i].get(-pole + 1, polynomial_ring.zero())
                + next_coefficient[i]
            )

    reduced = []
    for data in coefficients:
        reduced.append(sum((laurent_ring(polynomial) * z**exponent
                            for exponent, polynomial in data.items()
                            if polynomial), laurent_ring.zero()))
    return vector(laurent_ring, reduced), f0


def evaluate_polynomial_mod_prime_power(f, g, p, N):
    r"""Evaluate a nonnegative Laurent polynomial at ``g`` modulo ``p^N``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.reductions import evaluate_polynomial_mod_prime_power
        sage: R.<x> = QQ[]; L.<z> = LaurentSeriesRing(QQ)
        sage: evaluate_polynomial_mod_prime_power(z^2 + 2*z + 3, x + 1, 5, 2)
        x^2 + 4*x + 6
    """
    p = _validate_prime(p)
    N = ZZ(N)
    polynomial_ring = g.parent()
    if not f:
        return polynomial_ring.zero()
    valuation = ZZ(f.valuation())
    if valuation < 0:
        raise ValueError("f must have no negative powers")
    degree = ZZ(f.degree())
    f_valuations = [_coefficient_valuation(coefficient, p)
                    for coefficient in f if coefficient]
    f_valuation = min(f_valuations, default=ZZ.zero())
    g_valuations = [_coefficient_valuation(coefficient, p)
                    for coefficient in g if coefficient]
    g_valuation = min(g_valuations, default=ZZ.zero())
    working_precision = (
        N - min(f_valuation, ZZ.zero())
        - degree * min(g_valuation, ZZ.zero())
    )
    block_count = (degree + 4) // 4
    blocks = []
    for block in range(block_count):
        top = 4 * block + 3
        value = polynomial_ring(f[top])
        for exponent in range(top - 1, top - 4, -1):
            value = value * g + polynomial_ring(f[exponent])
        blocks.append(value)

    g_power = reduce_polynomial_mod_prime_power(g**4, p, working_precision)
    while len(blocks) > 1:
        if len(blocks) % 2:
            blocks.append(polynomial_ring.zero())
        blocks = [
            reduce_polynomial_mod_prime_power(
                blocks[index] + blocks[index + 1] * g_power,
                p, working_precision
            )
            for index in range(0, len(blocks), 2)
        ]
        if len(blocks) > 1:
            g_power = reduce_polynomial_mod_prime_power(
                g_power**2, p, working_precision
            )
    return reduce_polynomial_mod_prime_power(blocks[0], p, N)


def _inverse_polynomial_to_laurent(polynomial, laurent_ring):
    """Substitute ``x=1/t`` in a polynomial, producing a Laurent series.

    TESTS::

        sage: from sage.schemes.curves.coleman.reductions import _inverse_polynomial_to_laurent
        sage: R.<x> = QQ[]; L.<t> = LaurentSeriesRing(QQ)
        sage: _inverse_polynomial_to_laurent(1 + 2*x + 3*x^2, L)
        3*t^-2 + 2*t^-1 + 1
    """
    t = laurent_ring.gen()
    return sum((QQ(coefficient) * t**(-exponent)
                for exponent, coefficient in enumerate(polynomial.list())
                if coefficient), laurent_ring.zero())


def _inverse_rational_to_laurent(f, laurent_ring):
    """Substitute ``x=1/t`` in a rational function as a Laurent series.

    TESTS::

        sage: from sage.schemes.curves.coleman.reductions import _inverse_rational_to_laurent
        sage: R.<x> = QQ[]; L.<t> = LaurentSeriesRing(QQ, default_prec=5)
        sage: _inverse_rational_to_laurent((x + 1)/(x + 2), L)
        1 - t + 2*t^2 - 4*t^3 + 8*t^4 + O(t^5)
    """
    if not f:
        return laurent_ring.zero()
    numerator = _inverse_polynomial_to_laurent(f.numerator(), laurent_ring)
    denominator = _inverse_polynomial_to_laurent(f.denominator(), laurent_ring)
    return numerator / denominator


def _inverse_matrix_to_laurent(A, laurent_ring):
    """Substitute ``x=1/t`` entrywise in a rational-function matrix.

    TESTS::

        sage: from sage.schemes.curves.coleman.reductions import _inverse_matrix_to_laurent
        sage: R.<x> = QQ[]; K = R.fraction_field()
        sage: L.<t> = LaurentSeriesRing(QQ, default_prec=4)
        sage: _inverse_matrix_to_laurent(matrix(K, [[x, 1/x]]), L)
        [t^-1    t]
    """
    return matrix(laurent_ring, A.nrows(), A.ncols(),
                  [_inverse_rational_to_laurent(entry, laurent_ring)
                   for entry in A.list()])


def _finite_laurent_degree(f):
    """Return the largest represented exponent of a finite Laurent series.

    TESTS::

        sage: from sage.schemes.curves.coleman.reductions import _finite_laurent_degree
        sage: L.<t> = LaurentSeriesRing(QQ)
        sage: _finite_laurent_degree(t^-2 + 1 + 3*t^4)
        4
    """
    if not f:
        return -ZZ.one()
    return ZZ(f.valuation()) + len(f.list()) - 1


def change_basis_finite_to_infinity(w, p, N, r, W0, Winf):
    r"""Change differential coefficients from ``b^0`` to ``b^infinity``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.reductions import change_basis_finite_to_infinity
        sage: R.<x> = QQ[]; K.<x> = FunctionField(QQ)
        sage: L.<z> = LaurentSeriesRing(QQ); W = identity_matrix(K, 2)
        sage: change_basis_finite_to_infinity(
        ....:     vector(L, [1 + z, 2]), 5, 2, R.gen() + 1, W, W)
        (t^-1 + 2, 2)
    """
    p = _validate_prime(p)
    N = ZZ(N)
    polynomial_ring = r.parent()
    r = polynomial_ring(r / r.leading_coefficient())
    evaluated = [evaluate_polynomial_mod_prime_power(entry, r, p, N)
                 for entry in w]
    maximum_degree = max([polynomial.degree() for polynomial in evaluated
                          if polynomial] + [0])
    precision = max(20, maximum_degree + 4 * r.degree() + 4 * p * N + 10)
    laurent_ring = LaurentSeriesRing(QQ, names="t", default_prec=precision)
    transformed = vector(laurent_ring, [
        _inverse_polynomial_to_laurent(polynomial, laurent_ring)
        for polynomial in evaluated
    ])
    W_inverse = (Winf * W0.inverse()).inverse()
    return transformed * _inverse_matrix_to_laurent(W_inverse, laurent_ring)


def _laurent_coefficients(f):
    """Return a dictionary of represented Laurent coefficients.

    TESTS::

        sage: from sage.schemes.curves.coleman.reductions import _laurent_coefficients
        sage: L.<z> = LaurentSeriesRing(QQ)
        sage: _laurent_coefficients(z^-2 + 3*z)
        {-2: 1, 1: 3}
    """
    if not f:
        return {}
    valuation = ZZ(f.valuation())
    return {valuation + offset: QQ(coefficient)
            for offset, coefficient in enumerate(f.list()) if coefficient}


def reduce_infinite(w, Q, p, N, r, W0, Winf, Ginf, infinite_matrices):
    r"""Lower the pole order at infinity in the ``b^infinity`` basis.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.reductions import reduce_infinite
        sage: R.<x> = QQ[]; S.<y> = R[]; K.<x> = FunctionField(QQ)
        sage: L.<t> = LaurentSeriesRing(QQ); W = identity_matrix(K, 2)
        sage: w = vector(L, [0, 0])
        sage: reduce_infinite(
        ....:     w, y^2 - R.gen(), 5, 3, R.gen() + 1, W, W, W, [])
        ((0, 0), (0, 0))
    """
    p = _validate_prime(p)
    N = ZZ(N)
    polynomial_ring, _ = _model_rings(Q, require_monic=True)
    degree = Q.degree()
    degree_r = r.degree()
    laurent_ring = w.base_ring()
    t = laurent_ring.gen()
    primitive_ring = LaurentSeriesRing(QQ, names="x",
                                       default_prec=laurent_ring.default_prec())
    x_series = primitive_ring.gen()
    finf = vector(primitive_ring, degree)
    if not any(w):
        return w, finf

    W = Winf * W0.inverse()
    lower_limit = -(order_matrix_at_zero(W) + 1)
    r_input = polynomial_ring(r)
    r_monic = polynomial_ring(r_input / r_input.leading_coefficient())
    M_infinity = matrix(Ginf.base_ring(), r_monic * Ginf)
    M_at_inverse = _inverse_matrix_to_laurent(M_infinity, laurent_ring)
    r_at_inverse = _inverse_polynomial_to_laurent(r_monic, laurent_ring)

    coefficients = [_laurent_coefficients(entry) for entry in w]
    valuation_w = min(min(data) for data in coefficients if data)
    m = ZZ(-valuation_w - degree_r + 1)
    if m > len(infinite_matrices):
        raise ValueError("infinite reduction list is too short")

    while m > lower_limit:
        exponent = -m - degree_r + 1
        w_vector = vector(QQ, [-data.get(exponent, QQ.zero())
                               for data in coefficients])
        v_vector = w_vector * infinite_matrices[m - 1]
        v_vector = vector(QQ, [reduce_rational_mod_prime_power(value, p, N)
                               for value in v_vector])
        for i in range(degree):
            finf[i] += primitive_ring(v_vector[i]) * x_series**m

        v_laurent = vector(laurent_ring, v_vector)
        differential = (
            t**(-m) * v_laurent * M_at_inverse
            + r_at_inverse * m * t**(1 - m) * v_laurent
        )
        for i in range(degree):
            differential_i = reduce_laurent_mod_prime_power(differential[i], p, N)
            for power, coefficient in _laurent_coefficients(differential_i).items():
                coefficients[i][power] = (
                    coefficients[i].get(power, QQ.zero()) - coefficient
                )
            coefficients[i][exponent] = QQ.zero()
        m -= 1

    reduced = []
    for data in coefficients:
        reduced.append(sum((reduce_rational_mod_prime_power(coefficient, p, N)
                            * t**power
                            for power, coefficient in data.items()
                            if coefficient), laurent_ring.zero()))
    return vector(laurent_ring, reduced), finf


def _invert_laurent_exponents(f, laurent_ring):
    """Apply ``t -> 1/t`` to a represented finite Laurent series.

    TESTS::

        sage: from sage.schemes.curves.coleman.reductions import _invert_laurent_exponents
        sage: L.<t> = LaurentSeriesRing(QQ)
        sage: _invert_laurent_exponents(t^-2 + 3*t, L)
        3*t^-1 + t^2
    """
    t = laurent_ring.gen()
    return sum((QQ(coefficient) * t**(-power)
                for power, coefficient in _laurent_coefficients(f).items()),
               laurent_ring.zero())


def change_basis_infinity_to_finite(w, W0, Winf):
    r"""Change reduced coefficients from ``b^infinity`` back to ``b^0``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.reductions import change_basis_infinity_to_finite
        sage: K.<x> = FunctionField(QQ); L.<t> = LaurentSeriesRing(QQ)
        sage: W = identity_matrix(K, 2)
        sage: change_basis_infinity_to_finite(vector(L, [1 + t^-1, 0]), W, W)
        (x + 1, 0)
    """
    laurent_ring = w.base_ring()
    W = Winf * W0.inverse()
    transformed = w * _inverse_matrix_to_laurent(W, laurent_ring)
    transformed = vector(laurent_ring,
                         [_invert_laurent_exponents(entry, laurent_ring)
                          for entry in transformed])
    polynomial_ring = W0.base_ring().gen().numerator().parent()
    x = polynomial_ring.gen()
    output = []
    for entry in transformed:
        polynomial = polynomial_ring.zero()
        for exponent, coefficient in _laurent_coefficients(entry).items():
            if exponent >= 0:
                polynomial += coefficient * x**exponent
        output.append(polynomial)
    return vector(polynomial_ring, output)


def reduce_with_functions(differential, Q, p, N, Nmax, r, W0, Winf,
                          G0, Ginf, finite_matrices, infinite_matrices,
                          basis, integrals, quotient_map):
    r"""Reduce a differential and return its class and exact primitives.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: from sage.schemes.curves.coleman.reductions import (polynomial_vector_to_laurent_series,
        ....:     reduce_with_functions)
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 3, genus=1)
        sage: zero = polynomial_vector_to_laurent_series(vector(R, [0, 0]), data)
        sage: output = reduce_with_functions(
        ....:     zero, data.Q, data.p, data.N, data.Nmax, data.r,
        ....:     data.W0, data.Winf, data.G0, data.Ginf,
        ....:     data.finite_reduction_matrices,
        ....:     data.infinite_reduction_matrices, data.basis,
        ....:     data.integrals, data.quotient_map)
        sage: all(not any(part) for part in output)
        True
    """
    polynomial_ring, _ = _model_rings(Q, require_monic=True)
    degree = Q.degree()
    degree_r = r.degree()
    differential, f0 = reduce_finite(
        differential, Q, p, Nmax, r, G0, finite_matrices
    )
    differential = change_basis_finite_to_infinity(
        differential, p, Nmax, polynomial_ring(r), W0, Winf
    )
    differential, finf = reduce_infinite(
        differential, Q, p, Nmax, r, W0, Winf, Ginf, infinite_matrices
    )
    differential = change_basis_infinity_to_finite(differential, W0, Winf)

    W = Winf * W0.inverse()
    degree_bound = ZZ(
        degree_r - order_matrix_at_zero(W)
        - order_matrix_at_infinity(W) - 2
    )
    flattened = []
    for i in range(degree):
        flattened.extend(differential[i][j]
                         for j in range(degree_bound + 1))
    coordinates = vector(QQ, flattened) * quotient_map
    offset = quotient_map.ncols() - len(integrals)
    discarded = [
        reduce_rational_mod_prime_power(coordinates[j], p, N)
        for j in range(len(basis), offset)
    ]
    if any(discarded):
        raise ValueError(
            "the differential has components outside the selected "
            "cohomology basis; use an open-curve basis"
        )
    cohomology = vector(QQ, [
        reduce_rational_mod_prime_power(coordinates[j], p, N)
        for j in range(len(basis))
    ])

    if integrals:
        fend = vector(polynomial_ring, degree)
        for j, primitive in enumerate(integrals):
            scalar = reduce_rational_mod_prime_power(coordinates[offset + j], p, Nmax)
            fend += scalar * primitive
    else:
        fend = vector(polynomial_ring, degree)
    return cohomology, f0, finf, fend
