# sage.doctest: needs sage.rings.function_field sage.libs.singular
r"""
Auxiliary routines for Coleman integration on general plane curves

This module contains the exact-arithmetic setup used by the general-curve
Coleman integration code.  A curve model is represented by a polynomial
``Q`` in ``y`` with coefficients in `\QQ[x]`; it is assumed to be monic in
``y`` whenever a function field is constructed.

The functions :func:`finite_integral_basis_matrix` and
:func:`infinite_integral_basis_matrix` express integral bases in the power
basis `1,y,\ldots,y^{d-1}`.  Thus their rows have the same convention as the
``W0`` and ``Winf`` matrices in Tuitman's algorithms.

"""

from sage.matrix.constructor import matrix
from sage.rings.real_mpfr import RealField

from sage.rings.finite_rings.finite_field_constructor import GF
from sage.rings.function_field.constructor import FunctionField
from sage.rings.integer_ring import ZZ
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ


def _validate_prime(p):
    r"""Return ``p`` as a Sage integer after checking that it is prime.

    TESTS::

        sage: from sage.schemes.curves.coleman.auxiliary import _validate_prime
        sage: _validate_prime(5).parent() is ZZ
        True
        sage: _validate_prime(6)
        Traceback (most recent call last):
        ...
        ValueError: p must be prime
    """
    p = ZZ(p)
    if not p.is_prime():
        raise ValueError("p must be prime")
    return p


def _model_rings(Q, require_monic=False):
    r"""Validate a `\QQ[x][y]` model and return its polynomial rings.

    TESTS::

        sage: from sage.schemes.curves.coleman.auxiliary import _model_rings
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: Rx, Sy = _model_rings(y^2-x, require_monic=True)
        sage: (Rx.variable_name(), Sy.variable_name())
        ('x', 'y')
    """
    try:
        Sy = Q.parent()
        Rx = Sy.base_ring()
        constant_ring = Rx.base_ring()
        Rx.gen()
        Sy.gen()
    except (AttributeError, TypeError, ValueError):
        raise TypeError("Q must be a univariate polynomial over QQ[x]")

    if constant_ring is not QQ or Rx.ngens() != 1 or Sy.ngens() != 1:
        raise TypeError("Q must be a univariate polynomial over QQ[x]")
    if Q.degree() <= 0:
        raise ValueError("Q must have positive degree in y")
    if require_monic and not Q.is_monic():
        raise ValueError("Q must be monic in y")
    return Rx, Sy


def auxiliary_polynomials(Q):
    r"""
    Compute the auxiliary polynomials ``r``, ``Delta``, and ``s``.

    For a separable polynomial `Q(x,y)` this returns polynomials satisfying

    .. MATH::

        s Q_y - \Delta \in (Q),

    with common polynomial factors removed from `s` and `\Delta`.  The
    polynomial ``r`` is the squarefree part of the original discriminant of
    ``Q`` with respect to ``y``.  Constant factors are deliberately retained,
    matching the normalization used by the Coleman precision formulas.

    INPUT:

    - ``Q`` -- a polynomial in ``y`` over `\QQ[x]`

    OUTPUT:

    A triple ``(r, Delta, s)`` with ``r`` and ``Delta`` in `\QQ[x]` and
    ``s`` in `\QQ[x][y]`.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.auxiliary import auxiliary_polynomials
        sage: R.<x> = QQ[]
        sage: S.<y> = R[]
        sage: r, Delta, s = auxiliary_polynomials(y^3 - x)
        sage: (r, Delta, s)
        (-27*x, -27*x, -9*y)
        sage: (s * (y^3 - x).derivative() - Delta) % (y^3 - x)
        0

    A non-separable input does not define the required Bezout relation::

        sage: auxiliary_polynomials((y - x)^2)
        Traceback (most recent call last):
        ...
        ValueError: Q must be separable in y
    """
    Rx, Sy = _model_rings(Q)

    discriminant = Rx(Q.discriminant())
    if discriminant.is_zero():
        raise ValueError("Q must be separable in y")

    repeated_part = discriminant.gcd(discriminant.derivative())
    r = discriminant.quo_rem(repeated_part)[0]

    Kx = Rx.fraction_field()
    Ky = PolynomialRing(Kx, names=Sy.variable_name())
    q = Ky(Q)
    q_derivative = q.derivative()
    gcd_q, _, bezout_derivative = q.xgcd(q_derivative)
    if gcd_q.degree() != 0:
        raise ValueError("Q must be separable in y")

    # q*xgcd(q')[2] + q*xgcd(q')[1] is the unit gcd.  Multiplication by
    # the discriminant gives the adjugate/Sylvester Bezout relation over
    # QQ[x], before removing the common polynomial content.
    scale = Kx(discriminant) / gcd_q[0]
    s_over_Kx = scale * bezout_derivative

    s_coefficients = []
    for coefficient in s_over_Kx.list():
        try:
            s_coefficients.append(Rx(coefficient))
        except TypeError:
            raise ArithmeticError(
                "the discriminant Bezout relation did not clear denominators"
            )

    common_factor = discriminant
    for coefficient in s_coefficients:
        common_factor = common_factor.gcd(coefficient)

    Delta = discriminant.quo_rem(common_factor)[0]
    s = Sy([coefficient.quo_rem(common_factor)[0]
            for coefficient in s_coefficients])

    if (s * Q.derivative() - Delta) % Q:
        raise ArithmeticError("failed to construct the discriminant Bezout relation")
    return r, Delta, s


def _reduce_model_mod_prime(Q, p):
    r"""Return the defining polynomial over ``GF(p)(x)``.

    TESTS::

        sage: from sage.schemes.curves.coleman.auxiliary import _reduce_model_mod_prime
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: K, q = _reduce_model_mod_prime(y^2-x, 5)
        sage: q.degree(), K.constant_base_field()
        (2, Finite Field of size 5)
    """
    Rx, Sy = _model_rings(Q, require_monic=True)
    p = _validate_prime(p)
    k = GF(p)
    Kx = FunctionField(k, names=Rx.variable_name())
    Ky = PolynomialRing(Kx, names=Sy.variable_name())
    try:
        q = Ky([Kx(Rx(coefficient).change_ring(k)) for coefficient in Q.list()])
    except (TypeError, ValueError, ZeroDivisionError):
        raise ValueError("Q has coefficients that cannot be reduced modulo p")
    return Kx, q


def curve_genus(Q, p):
    r"""
    Return the genus of the smooth projective curve defined by ``Q`` modulo ``p``.

    The computation uses the function field of the reduction, so it computes
    the genus of the normalization even when the supplied affine plane model
    is singular.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.auxiliary import curve_genus
        sage: R.<x> = QQ[]
        sage: S.<y> = R[]
        sage: curve_genus(y^2 - (x^3 - x), 5)
        1
        sage: curve_genus(y^3 - x, 5)
        0

    Reducible reduction signals a bad prime::

        sage: curve_genus(y^2 - x^2, 5)
        Traceback (most recent call last):
        ...
        ValueError: bad prime: Q is reducible modulo p
    """
    Kx, q = _irreducible_reduction(Q, p)
    function_field = Kx.extension(q, names=q.parent().variable_name())
    return function_field.genus()


def _irreducible_reduction(Q, p):
    r"""Return the reduction of ``Q`` modulo ``p``, which must be irreducible.

    TESTS::

        sage: from sage.schemes.curves.coleman.auxiliary import _irreducible_reduction
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: _irreducible_reduction(y^2 - x, 5)[1]
        y^2 + 4*x
        sage: _irreducible_reduction(y^2 - x^2, 5)
        Traceback (most recent call last):
        ...
        ValueError: bad prime: Q is reducible modulo p
    """
    Kx, q = _reduce_model_mod_prime(Q, p)
    if not q.is_irreducible():
        raise ValueError("bad prime: Q is reducible modulo p")
    return Kx, q


def _has_smooth_affine_point(Q, p):
    r"""Return whether ``Q = 0`` has a point over `\GF{p}` off the branch locus.

    The point `(a, b)` must satisfy `Q(a, b) \equiv 0` and
    `\partial Q/\partial y (a, b) \not\equiv 0 \pmod{p}`, so it is a smooth
    point of the reduction that is unramified over the `x`-line.

    TESTS::

        sage: from sage.schemes.curves.coleman.auxiliary import _has_smooth_affine_point
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: _has_smooth_affine_point(y^2 - (x^3 - x), 5)
        True

    The curve `y^3 = 3x^3` is three lines, conjugate over `\QQ(\sqrt[3]{3})`.
    Modulo `7`, where `3` is not a cube, its only affine point is singular::

        sage: _has_smooth_affine_point(y^3 - 3*x^3, 7)
        False
    """
    k = GF(p)
    Ry = PolynomialRing(k, names='y')
    coefficients = [c.change_ring(k) for c in Q.list()]
    return any(multiplicity == 1
               for a in k
               for _, multiplicity in Ry([c(a) for c in coefficients]).roots())


def good_reduction_genus(Q, p, W0, Winf):
    r"""
    Return the genus of the curve `Q = 0`, which has good reduction at ``p``.

    The integral bases ``W0`` and ``Winf`` give the genus quickly by
    :func:`genus_from_integral_bases`, provided the curve is geometrically
    irreducible.  At a prime of good reduction, the constant field of the
    reduction contains the residue fields of the constant field of the
    curve over `\QQ`.  A point over `\GF{p}` found by
    :func:`_has_smooth_affine_point` has degree one, so it proves that the
    constant field is `\QQ`.  Without such a point, the genus of the
    reduction is computed by :func:`curve_genus`, as for a curve that is not
    geometrically irreducible.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.auxiliary import (
        ....:     good_reduction_genus, integral_basis_matrices)
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: Q = y^4 + x^4 - 1
        sage: good_reduction_genus(Q, 13, *integral_basis_matrices(Q))
        3

    The model `y^3 = 3x^3` is three lines, conjugate over `\QQ(\sqrt[3]{3})`,
    so it is not geometrically irreducible, and the integral bases alone
    would give a negative genus::

        sage: Q = y^3 - 3*x^3
        sage: good_reduction_genus(Q, 7, *integral_basis_matrices(Q))
        0
    """
    if _has_smooth_affine_point(Q, p):
        return genus_from_integral_bases(Q, W0, Winf)
    return ZZ(curve_genus(Q, p))


def genus_from_integral_bases(Q, W0, Winf):
    r"""
    Return the genus of the curve `Q = 0` from its integral bases.

    ``Q`` is monic in `y` of degree `d`.  The rows of ``W0`` and ``Winf``
    express bases of the maximal orders over `\QQ[x]` and over `\QQ[1/x]` in
    the power basis of `y`, as returned by :func:`integral_basis_matrices`.
    Such a basis has discriminant `\det(W)^2 \operatorname{disc}_y(Q)`.  The
    discriminant divisor of the degree-`d` map `x` to the projective line
    has degree `\delta`: the degree of the finite discriminant plus the
    order of the discriminant at infinity.  The Riemann--Hurwitz formula
    gives `2g - 2 = -2d + \delta`.

    This is the genus of the normalization, so singular plane models are
    handled as well.  Under the good-reduction conditions checked by
    :func:`~sage.schemes.curves.coleman.data.coleman_data`, it is also the
    genus of the reduction modulo `p`, which :func:`curve_genus` computes
    much more slowly.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.auxiliary import (
        ....:     genus_from_integral_bases, integral_basis_matrices)
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: [genus_from_integral_bases(Q, *integral_basis_matrices(Q))
        ....:  for Q in [y^2 - (x^3 - x), y^2 - (x^6 + 1), y^3 - x,
        ....:            y^4 + x^4 - 1, y^3 + x^3*y + x]]
        [1, 2, 0, 3, 3]

    A singular plane model of a curve of genus `2`::

        sage: Q = y^3 + 2*x^4 - 6*x^3 + 3*x^2 - 4*x + 12
        sage: genus_from_integral_bases(Q, *integral_basis_matrices(Q))
        2
    """
    field = W0.base_ring()
    discriminant = field(Q.discriminant())
    finite = W0.determinant()**2 * discriminant
    infinite = Winf.determinant()**2 * discriminant
    delta = (finite.numerator().degree() - finite.denominator().degree()
             + infinite.denominator().degree() - infinite.numerator().degree())
    genus, odd = ZZ(delta - 2 * Q.degree() + 2).quo_rem(2)
    if odd or genus < 0:
        raise ArithmeticError("the integral bases are not those of a curve")
    return genus


def is_smooth_mod_p(f, p):
    r"""
    Return whether ``f`` keeps its degree and is separable modulo ``p``.

    Despite the historical name ``smooth``, this is a univariate
    separability test used for the branch polynomial ``r``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.auxiliary import is_smooth_mod_p
        sage: R.<x> = QQ[]
        sage: is_smooth_mod_p(x^2 + x + 1, 2)
        True
        sage: is_smooth_mod_p(x^2 + 1, 2)
        False
        sage: is_smooth_mod_p(2*x^2 + x + 1, 2)
        False
    """
    p = _validate_prime(p)
    try:
        degree = f.degree()
        fp = f.change_ring(GF(p))
    except (AttributeError, TypeError, ValueError, ZeroDivisionError):
        raise TypeError("f must be a univariate polynomial over QQ")
    return fp.degree() == degree and fp.is_squarefree()


def positive_log(p, x):
    r"""
    Return the base-``p`` logarithm of ``x``, truncated to zero for ``x <= 0``.

    A 100-bit real field is used because downstream code applies ``floor`` or
    ``ceil`` to this value when deriving precision bounds.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.auxiliary import positive_log
        sage: positive_log(5, 25)
        2.0000000000000000000000000000
        sage: positive_log(5, 0)
        0
        sage: positive_log(89, 89^3).floor()
        3
        sage: positive_log(11, 11^7).floor()
        7
    """
    p = _validate_prime(p)
    if x <= 0:
        return ZZ.zero()
    R = RealField(100)
    try:
        rational = QQ(x)
        exponent = ZZ(rational.valuation(p))
        if rational == QQ(p)**exponent:
            return R(exponent)
    except (TypeError, ValueError):
        pass
    return R(x).log() / R(p).log()


def is_p_integral(A, p):
    r"""
    Return whether a rational-function matrix is coefficientwise ``p``-integral.

    A common polynomial denominator is cleared first.  Integrality is then
    tested on every rational coefficient of every numerator, matching the
    test needed for the finite and infinite integral-basis matrices.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.auxiliary import is_p_integral
        sage: K.<x> = FunctionField(QQ)
        sage: A = matrix(K, [[1/(x + 1), 1/3], [x, 1]])
        sage: is_p_integral(A, 5)
        True
        sage: is_p_integral(A, 3)
        False
    """
    p = _validate_prime(p)
    try:
        cleared = A * A.denominator()
    except (AttributeError, TypeError):
        raise TypeError("A must be a matrix with exact rational-function entries")

    for entry in cleared.list():
        numerator = entry.numerator() if hasattr(entry, "numerator") else entry
        coefficients = (numerator.list()
                        if hasattr(numerator, "list") else [numerator])
        for coefficient in coefficients:
            if coefficient and QQ(coefficient).valuation(p) < 0:
                return False
    return True


def _function_field_model(Q):
    r"""Construct the function field of a monic `\QQ[x][y]` model.

    TESTS::

        sage: from sage.schemes.curves.coleman.auxiliary import _function_field_model
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: K, L = _function_field_model(y^2-x)
        sage: K.degree(), L.degree()
        (1, 2)
    """
    Rx, Sy = _model_rings(Q, require_monic=True)
    Kx = FunctionField(QQ, names=Rx.variable_name())
    Ky = PolynomialRing(Kx, names=Sy.variable_name())
    q = Ky([Kx(coefficient) for coefficient in Q.list()])
    if not q.is_irreducible():
        raise ValueError("Q must be irreducible over QQ(x)")
    function_field = Kx.extension(q, names=Sy.variable_name())
    return Kx, function_field


def _basis_matrix(function_field, basis):
    r"""Express ``basis`` in the power basis of ``function_field``.

    TESTS::

        sage: from sage.schemes.curves.coleman.auxiliary import (_basis_matrix,
        ....:     _function_field_model)
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: K, L = _function_field_model(y^2-x)
        sage: _basis_matrix(L, [L.one(), L.gen()])
        [1 0]
        [0 1]
    """
    Kx = function_field.base_field()
    _, _, to_vector = function_field.vector_space()
    return matrix(Kx, [to_vector(element) for element in basis])


def finite_integral_basis_matrix(Q):
    r"""
    Return the finite integral-basis matrix ``W0`` for ``Q``.

    The rows express a basis of the integral closure of `\QQ[x]` in
    `\QQ(x)[y]/(Q)` in the power basis of ``y``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.auxiliary import finite_integral_basis_matrix
        sage: R.<x> = QQ[]
        sage: S.<y> = R[]
        sage: finite_integral_basis_matrix(y^2 - x^3)
        [  1   0]
        [  0 1/x]
    """
    _, function_field = _function_field_model(Q)
    return _basis_matrix(
        function_field, function_field._maximal_order_basis()
    )


def infinite_integral_basis_matrix(Q):
    r"""
    Return the infinite integral-basis matrix ``Winf`` for ``Q``.

    The rows express a basis integral above the infinite place of
    `\QQ(x)` in the original power basis of ``y``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.auxiliary import infinite_integral_basis_matrix
        sage: R.<x> = QQ[]
        sage: S.<y> = R[]
        sage: infinite_integral_basis_matrix(y^2 - (x^3 - x))
        [    1     0]
        [    0 1/x^2]
    """
    _, function_field = _function_field_model(Q)
    from sage.rings.function_field.maximal_order_round_two import (
        round_two_maximal_order_infinite_basis,
    )
    return _basis_matrix(
        function_field,
        round_two_maximal_order_infinite_basis(function_field),
    )


def integral_basis_matrices(Q):
    r"""
    Return both finite and infinite integral-basis matrices for ``Q``.

    This combined entry point constructs the function field only once and is
    preferable when both matrices are needed during Coleman setup.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.auxiliary import integral_basis_matrices
        sage: R.<x> = QQ[]
        sage: S.<y> = R[]
        sage: W0, Winf = integral_basis_matrices(y^2 - x^3)
        sage: W0
        [  1   0]
        [  0 1/x]
        sage: Winf
        [    1     0]
        [    0 1/x^2]
    """
    _, function_field = _function_field_model(Q)
    from sage.rings.function_field.maximal_order_round_two import (
        _canonical_module_basis,
    )
    W0 = _basis_matrix(
        function_field, function_field._maximal_order_basis()
    )
    # The infinite basis spans the maximal order of the inverted field over
    # `\QQ[1/x]`.  Singular's normalization computes that order much faster
    # than Round--2; the canonical Hermite basis is the one Round--2 returns.
    inverted, from_inverted, _ = function_field._inversion_isomorphism()
    infinite_basis = _canonical_module_basis(
        inverted, inverted._maximal_order_basis()
    )
    Winf = _basis_matrix(
        function_field, [from_inverted(b) for b in infinite_basis]
    )
    return W0, Winf
