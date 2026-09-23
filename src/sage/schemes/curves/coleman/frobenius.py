# sage.doctest: needs sage.rings.function_field sage.rings.padics
r"""
Frobenius lifts for Coleman integration on general plane curves

The implementation follows Tuitman's radix representation.  An element of
``Z/(p^N)[x,y,1/r]/(Q)`` is stored as a polynomial in ``y`` whose
coefficients are Laurent series in a formal variable ``z``.  Radix
reduction enforces ``z = r(x)`` and keeps every coefficient in ``x`` below
``degree(r)``.  All operations used here remain finite Laurent polynomials;
the Laurent-series parent is used because Sage's Laurent-polynomial ring
requires a domain as coefficient ring, while ``Z/(p^N)`` is not a domain.

Matrices act on row vectors, consistently with
:mod:`sage.schemes.curves.coleman.cohomology`.

"""

from sage.matrix.constructor import matrix
from sage.modules.free_module_element import vector

from sage.rings.finite_rings.integer_mod_ring import Integers
from sage.rings.integer_ring import ZZ
from sage.rings.laurent_series_ring import LaurentSeriesRing
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ

from .auxiliary import _model_rings, _validate_prime
from .cohomology import order_at_polynomial


def frobenius_rings(p, N, x_name="x", z_name="z", y_name="y"):
    r"""Construct the nested rings used by the finite-precision lift.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.frobenius import frobenius_rings
        sage: A, X, L, E = frobenius_rings(5, 3)
        sage: (A.cardinality(), L.base_ring() is X, E.base_ring() is L)
        (125, True, True)
    """
    p = _validate_prime(p)
    N = ZZ(N)
    if N <= 0:
        raise ValueError("N must be positive")
    coefficient_ring = Integers(p**N)
    polynomial_ring = PolynomialRing(coefficient_ring, names=x_name)
    laurent_ring = LaurentSeriesRing(polynomial_ring, names=z_name)
    extension_ring = PolynomialRing(laurent_ring, names=y_name)
    return coefficient_ring, polynomial_ring, laurent_ring, extension_ring


def _finite_laurent_terms(f):
    """Iterate through the nonzero terms of an exact finite Laurent series.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.frobenius import frobenius_rings, _finite_laurent_terms
        sage: _, X, L, _ = frobenius_rings(5, 3)
        sage: x, z = X.gen(), L.gen()
        sage: list(_finite_laurent_terms(L(x)*z^(-2) + 3*z))
        [(-2, x), (1, 3)]
    """
    if not f:
        return
    valuation = ZZ(f.valuation())
    for offset, coefficient in enumerate(f.list()):
        if coefficient:
            yield valuation + offset, coefficient


def radix_reduce(f, r):
    r"""Reduce every coefficient in ``x`` using ``x^deg(r) = z - ...``.

    The input is a polynomial in ``y`` over a Laurent-series ring in ``z``.
    The polynomial ``r`` must be monic and belong to the coefficient
    polynomial ring in ``x``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.frobenius import frobenius_rings, radix_reduce
        sage: _, X, L, E = frobenius_rings(5, 3)
        sage: x, z = X.gen(), L.gen()
        sage: radix_reduce(E(x^2 + 1), x^2 + 1) == E(z)
        True
    """
    extension_ring = f.parent()
    laurent_ring = extension_ring.base_ring()
    polynomial_ring = laurent_ring.base_ring()
    r = polynomial_ring(r)
    if not r.is_monic():
        raise ValueError("r must be monic")

    z = laurent_ring.gen()
    output_coefficients = []
    for coefficient in f.list():
        terms = dict(_finite_laurent_terms(coefficient) or [])
        if terms:
            exponent = min(terms)
            final_exponent = max(terms)
            while exponent <= final_exponent:
                polynomial = terms.get(exponent, polynomial_ring.zero())
                if polynomial and polynomial.degree() >= r.degree():
                    quotient, remainder = polynomial.quo_rem(r)
                    terms[exponent] = remainder
                    terms[exponent + 1] = (
                        terms.get(exponent + 1, polynomial_ring.zero())
                        + quotient
                    )
                    final_exponent = max(final_exponent, exponent + 1)
                exponent += 1
            reduced = sum((laurent_ring(polynomial) * z**exponent
                           for exponent, polynomial in terms.items()
                           if polynomial), laurent_ring.zero())
        else:
            reduced = laurent_ring.zero()
        output_coefficients.append(reduced)
    return extension_ring(output_coefficients)


def reduce_mod_model(f, Q, r):
    r"""Reduce an element first in the ``x`` radix and then modulo ``Q``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.frobenius import frobenius_rings, reduce_mod_model
        sage: _, X, _, E = frobenius_rings(5, 3)
        sage: x, y = X.gen(), E.gen()
        sage: Q = y^2 - E(x + 1)
        sage: reduce_mod_model(y^3, Q, x^2 + 1) == E(x + 1)*y
        True
    """
    extension_ring = f.parent()
    y = extension_ring.gen()
    f = radix_reduce(f, r)
    Q = radix_reduce(extension_ring(Q), r)
    if not Q.is_monic():
        raise ValueError("Q must be monic in y")
    while f and f.degree() >= Q.degree():
        f -= f.leading_coefficient() * y**(f.degree() - Q.degree()) * Q
        f = radix_reduce(f, r)
    return f


def substitute_xp(f, xp, r):
    r"""Substitute the represented element ``xp`` for ``x`` in ``f``.

    The input ``f`` may involve ``y`` but must not involve the radix variable
    ``z``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.frobenius import frobenius_rings, substitute_xp
        sage: _, X, L, E = frobenius_rings(5, 3)
        sage: x, z, y = X.gen(), L.gen(), E.gen()
        sage: substitute_xp(E(x^2)*y + E(x), E(x + 1), x^2 + 1) == E((2*x + z)*y + x + 1)
        True
    """
    extension_ring = f.parent()
    polynomial_ring = extension_ring.base_ring().base_ring()
    x_degree = -1
    coefficients = []
    for coefficient in f.list():
        if not coefficient:
            coefficients.append(polynomial_ring.zero())
            continue
        terms = list(_finite_laurent_terms(coefficient))
        if any(exponent != 0 for exponent, _ in terms):
            raise ValueError("the input to substitute_xp must not involve z")
        polynomial = (terms[0][1] if terms else polynomial_ring.zero())
        coefficients.append(polynomial)
        x_degree = max(x_degree, polynomial.degree())

    powers = [extension_ring.one()]
    for _ in range(x_degree):
        powers.append(radix_reduce(powers[-1] * xp, r))

    y = extension_ring.gen()
    output = extension_ring.zero()
    for y_exponent, polynomial in enumerate(coefficients):
        for x_exponent, scalar in enumerate(polynomial.list()):
            if scalar:
                output += scalar * powers[x_exponent] * y**y_exponent
    return radix_reduce(output, r)


def power_mod_model(f, exponent, Q, r):
    r"""Compute ``f^exponent`` using binary powering and reduction modulo ``Q``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.frobenius import frobenius_rings, power_mod_model
        sage: _, X, L, E = frobenius_rings(5, 3)
        sage: x, z, y = X.gen(), L.gen(), E.gen()
        sage: Q = y^2 - E(x + 1)
        sage: power_mod_model(y, 4, Q, x^2 + 1) == E(2*x + z)
        True
    """
    exponent = ZZ(exponent)
    if exponent < 0:
        raise ValueError("exponent must be nonnegative")
    result = f.parent().one()
    base = reduce_mod_model(f, Q, r)
    while exponent:
        if exponent & 1:
            result = reduce_mod_model(result * base, Q, r)
        exponent >>= 1
        if exponent:
            base = reduce_mod_model(base * base, Q, r)
    return result


def _coerce_polynomial(polynomial, target_ring):
    """Coerce a characteristic-zero polynomial coefficient by coefficient.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.frobenius import frobenius_rings, _coerce_polynomial
        sage: R.<x> = QQ[]
        sage: _, X, _, _ = frobenius_rings(5, 3)
        sage: _coerce_polynomial(x^2 + 2, X) == X.gen()^2 + 2
        True
    """
    return target_ring([target_ring.base_ring()(coefficient)
                        for coefficient in polynomial.list()])


def _coerce_model(Q, extension_ring):
    """Coerce a polynomial in ``QQ[x][y]`` into a Frobenius extension ring.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.frobenius import frobenius_rings, _coerce_model
        sage: R.<x> = QQ[]
        sage: S.<y> = R[]
        sage: _, X, _, E = frobenius_rings(5, 3)
        sage: _coerce_model(y^2 - (x + 1), E) == E.gen()^2 - E(X.gen() + 1)
        True
    """
    polynomial_ring = extension_ring.base_ring().base_ring()
    return extension_ring([
        extension_ring.base_ring()(_coerce_polynomial(coefficient,
                                                      polynomial_ring))
        for coefficient in Q.list()
    ])


def _precision_schedule(N):
    """Return the Newton precisions from the first nontrivial lift through ``N``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.frobenius import _precision_schedule
        sage: _precision_schedule(9)
        [2, 3, 5, 9]
    """
    values = []
    current = ZZ(N)
    while current > 1:
        values.append(current)
        current = (current + 1) // 2
    return list(reversed(values))


def _division_power(numerator, denominator):
    """Find a power of ``numerator`` divisible by ``denominator`` over QQ.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.frobenius import _division_power
        sage: R.<x> = QQ[]
        sage: _division_power(x - 1, (x - 1)^2)
        (2, 1)
    """
    power = numerator.parent().one()
    exponent = ZZ.zero()
    while True:
        quotient, remainder = power.quo_rem(denominator)
        if not remainder:
            return exponent, quotient
        exponent += 1
        power *= numerator
        if exponent > denominator.degree() + 1:
            raise ValueError("Delta is not supported on the zero locus of r")


def _localization_exponent(f, r):
    """Return the least ``e`` for which ``r^e*f`` is a polynomial.

    For a direct check, a double pole needs two powers of ``r``::

        sage: from sage.schemes.curves.coleman.frobenius import _localization_exponent
        sage: R.<x> = QQ[]
        sage: K = R.fraction_field()
        sage: _localization_exponent(K((x + 1)/(x - 1)^2), K(x - 1))
        2

    This also runs inside a full lift with the nontrivial integral basis
    ``(1, y/x)`` (indirect doctest)::

        sage: from sage.schemes.curves.coleman.auxiliary import auxiliary_polynomials
        sage: from sage.schemes.curves.coleman.frobenius import frobenius_lift
        sage: S.<y> = R[]
        sage: Q = y^2 - x^3
        sage: r, Delta, s = auxiliary_polynomials(Q)
        sage: W0 = matrix(K, [[1, 0], [0, 1/x]])
        sage: F = frobenius_lift(Q, 5, 3, r, Delta, s, W0)
        sage: F[1, 1] == F.base_ring().gen()^(-2)
        True
    """
    if not f:
        return ZZ.zero()
    order = order_at_polynomial(f, r)
    return max(ZZ.zero(), -ZZ(order))


def _localized_polynomial(f, r, exponent):
    """Return the polynomial ``r^exponent*f`` and verify exactness.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.frobenius import _localized_polynomial
        sage: R.<x> = QQ[]
        sage: K = R.fraction_field()
        sage: _localized_polynomial(K((x + 1)/(x - 1)^2), K(x - 1), 2)
        x + 1

    In a full lift, this clears the denominator of the basis element
    ``y/x`` before radix conversion (indirect doctest)::

        sage: from sage.schemes.curves.coleman.auxiliary import auxiliary_polynomials
        sage: from sage.schemes.curves.coleman.frobenius import frobenius_lift
        sage: S.<y> = R[]
        sage: Q = y^2 - x^3
        sage: r, Delta, s = auxiliary_polynomials(Q)
        sage: W0 = matrix(K, [[1, 0], [0, 1/x]])
        sage: F = frobenius_lift(Q, 5, 3, r, Delta, s, W0)
        sage: F[1, 1] == F.base_ring().gen()^(-2)
        True
    """
    value = f * r**exponent
    denominator = value.denominator()
    if hasattr(denominator, "degree") and denominator.degree() > 0:
        raise ValueError("matrix entry has poles away from r")
    numerator = value.numerator()
    scalar = QQ(denominator)
    return numerator / scalar


def frobenius_lift(Q, p, N, r, Delta, s, W0, *, return_maps=False):
    r"""Compute the Frobenius matrix in the basis ``b_i^0/r``.

    If ``return_maps`` is true, also return the represented images of
    ``1/r``, ``y``, and ``x``.  This is useful for certification tests.

    The images satisfy both the defining equation and the inverse relation
    for ``r(x)`` modulo ``p^N``::

        sage: from sage.schemes.curves.coleman.auxiliary import auxiliary_polynomials
        sage: from sage.schemes.curves.coleman.frobenius import (frobenius_lift, radix_reduce, reduce_mod_model, substitute_xp)
        sage: R.<x> = QQ[]
        sage: S.<y> = R[]
        sage: Q = y^2 - (x^3 - x)
        sage: r, Delta, s = auxiliary_polynomials(Q)
        sage: W0 = identity_matrix(R.fraction_field(), 2)
        sage: F, alpha, beta, xp, q, rr = frobenius_lift(Q, 5, 3, r, Delta, s, W0, return_maps=True)
        sage: F.nrows() == F.ncols() == 2
        True
        sage: reduce_mod_model(beta^2 - substitute_xp(q.parent()(-q[0]), xp, rr), q, rr) == 0
        True
        sage: radix_reduce(alpha*substitute_xp(q.parent()(rr), xp, rr) - 1, rr) == 0
        True
    """
    p = _validate_prime(p)
    N = ZZ(N)
    if N <= 0:
        raise ValueError("N must be positive")
    Rx, _ = _model_rings(Q, require_monic=True)
    r_original = Rx(r)
    Delta_original = Rx(Delta)
    s_original = Q.parent()(s)
    leading_coefficient = r_original.leading_coefficient()
    scale = QQ.one() / QQ(leading_coefficient)
    r_monic = Rx(scale * r_original)
    Delta_normalized = Rx(scale * Delta_original)
    s_normalized = Q.parent()([
        Rx(scale * coefficient) for coefficient in s_original.list()
    ])
    power_Delta, g = _division_power(r_monic, Delta_normalized)

    _, Ox, S, R = frobenius_rings(
        p, N, Rx.variable_name(), "z", Q.parent().variable_name()
    )
    x = Ox.gen()
    z = S.gen()
    y = R.gen()
    q = _coerce_model(Q, R)
    r_mod = _coerce_polynomial(r_monic, Ox)
    s_mod = _coerce_model(s_normalized, R)
    g_mod = _coerce_polynomial(g, Ox)
    degree = Q.degree()

    alpha = R(z**(-p))
    beta = power_mod_model(y, p, q, r_mod)
    xp = power_mod_model(R(x), p, q, r_mod)

    for precision in _precision_schedule(N):
        _, Oxi, Si, Ri = frobenius_rings(
            p, precision, Rx.variable_name(), "z", Q.parent().variable_name()
        )
        qi = Ri(q)
        ri = Oxi(r_mod)
        si = Ri(s_mod)
        gi = Oxi(g_mod)
        xpi = Ri(xp)
        alpha = Ri(alpha)
        beta = Ri(beta)

        r_xp = substitute_xp(Ri(ri), xpi, ri)
        alpha = radix_reduce(alpha * radix_reduce(2 - alpha * r_xp, ri), ri)

        alpha_power = Ri.one()
        for _ in range(power_Delta):
            alpha_power = radix_reduce(alpha_power * alpha, ri)
        alpha_Delta = radix_reduce(
            substitute_xp(Ri(gi), xpi, ri) * alpha_power, ri
        )

        powers = [Ri.one()]
        for _ in range(degree):
            powers.append(reduce_mod_model(beta * powers[-1], qi, ri))

        Q_xp = substitute_xp(qi, xpi, ri)
        s_xp = substitute_xp(si, xpi, ri)
        evaluated_Q = radix_reduce(sum(
            (Q_xp[j] * powers[j] for j in range(degree + 1)),
            Ri.zero()), ri)
        evaluated_s = radix_reduce(sum(
            (s_xp[j] * powers[j] for j in range(s_xp.degree() + 1)),
            Ri.zero()), ri)
        correction = reduce_mod_model(
            radix_reduce(evaluated_Q * evaluated_s, ri), qi, ri
        )
        beta = radix_reduce(beta - correction * alpha_Delta, ri)

    alpha = R(alpha)
    beta = R(beta)
    xp = R(xp)

    power_matrix = matrix(S, degree, degree, 0)
    image = radix_reduce(R(z) * alpha, r_mod)
    for i in range(degree):
        power_matrix[0, i] = image[i]
    for row in range(1, degree):
        image = reduce_mod_model(beta * image, q, r_mod)
        for column in range(degree):
            power_matrix[row, column] = image[column]

    Kx = Rx.fraction_field()
    r_in_Kx = Kx(r_monic)
    W0 = W0.change_ring(Kx)
    W0_inverse = W0.inverse()

    inverse_over_S = matrix(S, degree, degree, 0)
    for i in range(degree):
        for j in range(degree):
            entry = W0_inverse[i, j]
            exponent = _localization_exponent(entry, r_monic)
            polynomial = _localized_polynomial(entry, r_in_Kx, exponent)
            polynomial_mod = _coerce_polynomial(Rx(polynomial), Ox)
            inverse_over_S[i, j] = S(polynomial_mod) * z**(-exponent)

    matrix_b0 = power_matrix * inverse_over_S
    matrix_b0 = matrix(S, degree, degree,
                       [radix_reduce(R(entry), r_mod)[0]
                        for entry in matrix_b0.list()])

    frobenius_W0 = matrix(S, degree, degree, 0)
    for i in range(degree):
        for j in range(degree):
            entry = W0[i, j]
            exponent = _localization_exponent(entry, r_monic)
            polynomial = _localized_polynomial(entry, r_in_Kx, exponent)
            polynomial_mod = _coerce_polynomial(Rx(polynomial), Ox)
            lifted_polynomial = substitute_xp(R(polynomial_mod), xp, r_mod)
            inverse_r = power_mod_model(alpha, exponent, q, r_mod)
            frobenius_W0[i, j] = radix_reduce(
                inverse_r * lifted_polynomial, r_mod
            )[0]

    result = frobenius_W0 * matrix_b0
    result = matrix(S, degree, degree,
                    [radix_reduce(R(entry), r_mod)[0]
                     for entry in result.list()])
    if return_maps:
        return result, alpha, beta, xp, q, r_mod
    return result


def frobenius_pullback(w, Q, p, N, r, frobenius_matrix):
    r"""Pull back ``sum(w_i*b_i^0*dx/r)`` modulo ``p^N``.

    On an elliptic model, the pullback of ``dx/r`` is a nonzero vector and
    its coefficients have the expected factor of ``p``::

        sage: from sage.schemes.curves.coleman.auxiliary import auxiliary_polynomials
        sage: from sage.schemes.curves.coleman.frobenius import (frobenius_lift, frobenius_pullback, _finite_laurent_terms)
        sage: R.<x> = QQ[]
        sage: S.<y> = R[]
        sage: Q = y^2 - (x^3 - x)
        sage: r, Delta, s = auxiliary_polynomials(Q)
        sage: F = frobenius_lift(Q, 5, 3, r, Delta, s, identity_matrix(R.fraction_field(), 2))
        sage: v = frobenius_pullback(vector(R, [1, 0]), Q, 5, 4, r, F)
        sage: len(v) == 2 and bool(v[0]) and v[1] == 0
        True
        sage: all(ZZ(c.lift()) % 5 == 0 for a in v for _, h in _finite_laurent_terms(a) for c in h.list())
        True
    """
    p = _validate_prime(p)
    N = ZZ(N)
    if N <= 1:
        raise ValueError("N must be at least 2")
    Rx, _ = _model_rings(Q, require_monic=True)
    r_input = Rx(r)
    r = Rx(r_input / r_input.leading_coefficient())
    degree = Q.degree()

    _, Ox, S, R = frobenius_rings(
        p, N - 1, Rx.variable_name(), "z", Q.parent().variable_name()
    )
    q = _coerce_model(Q, R)
    r_mod = _coerce_polynomial(r, Ox)
    x = Ox.gen()
    xp_minus_one = power_mod_model(R(x), p - 1, q, r_mod)
    xp = radix_reduce(xp_minus_one * R(x), r_mod)
    matrix_low = matrix(S, degree, degree,
                        [S(entry) for entry in frobenius_matrix.list()])

    output = vector(S, degree)
    for i in range(degree):
        coefficient = _coerce_polynomial(Rx(w[i]), Ox)
        substituted = substitute_xp(R(coefficient), xp, r_mod)
        temp = radix_reduce(xp_minus_one * substituted, r_mod)
        for j in range(degree):
            output[j] += radix_reduce(
                R(matrix_low[i, j]) * temp, r_mod
            )[0]

    _, _, S_high, _ = frobenius_rings(
        p, N, Rx.variable_name(), "z", Q.parent().variable_name()
    )
    return p * vector(S_high, [S_high(entry) for entry in output])
