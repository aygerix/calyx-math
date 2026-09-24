# sage.doctest: needs sage.rings.function_field sage.rings.number_field
r"""
Connections, residues, and de Rham cohomology for general plane curves

The curve is represented by a monic polynomial ``Q`` in ``y`` over
`\QQ[x]`.  Matrices act on row vectors, following Tuitman's conventions.
This convention is significant for kernels and Jordan transformations, so
row kernels are represented by Sage left kernels.

"""

from sage.matrix.constructor import identity_matrix, matrix
from sage.modules.free_module_element import vector

from sage.misc.verbose import verbose
from sage.modules.free_module import VectorSpace
from sage.rings.function_field.constructor import FunctionField
from sage.rings.infinity import infinity
from sage.rings.integer_ring import ZZ
from sage.rings.number_field.number_field import NumberField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.power_series_ring import PowerSeriesRing
from sage.rings.rational_field import QQ

from .auxiliary import _model_rings, _validate_prime


def _exact_left_kernel(A):
    r"""Return the left kernel of a rational matrix using PARI.

    Clearing denominators preserves the rational kernel.  Computing the
    integer nullspace directly avoids the slower generic rational-matrix
    backend while retaining exact arithmetic.

    TESTS::

        sage: from sage.schemes.curves.coleman.cohomology import _exact_left_kernel
        sage: A = matrix(QQ, [[1/2, 1], [1, 2], [0, 0]])
        sage: K = _exact_left_kernel(A)
        sage: K == A.left_kernel()
        True
        sage: all(v * A == 0 for v in K.basis())
        True
    """
    if A.base_ring() is not QQ:
        raise TypeError("the matrix must be over QQ")
    if not A.nrows():
        return A.left_kernel()
    timing = verbose(
        f"computing exact left kernel of {A.nrows()} by {A.ncols()} matrix",
        level=1,
    )
    denominator = ZZ.one()
    for entry in A.list():
        denominator = denominator.lcm(QQ(entry).denominator())
    integral = matrix(
        ZZ, A.nrows(), A.ncols(),
        [ZZ(denominator * entry) for entry in A.list()],
    )
    basis = integral.transpose().__pari__().matker().mattranspose().sage()
    # PARI returns an independent exact kernel basis.  Preserve that certified
    # user basis instead of immediately repeating the row reduction over QQ.
    ambient = VectorSpace(QQ, A.nrows())
    kernel = ambient.span_of_basis(basis.change_ring(QQ).rows(), check=False)
    verbose("finished exact left kernel", level=1, t=timing)
    return kernel


def _exact_intersection(left, right):
    r"""Intersect rational subspaces using the exact FLINT kernel backend.

    TESTS::

        sage: from sage.schemes.curves.coleman.cohomology import _exact_intersection
        sage: V = VectorSpace(QQ, 3)
        sage: U = V.subspace([(1, 0, 1), (0, 1, 0)])
        sage: W = V.subspace([(1, 0, 1), (1, 0, 0)])
        sage: _exact_intersection(U, W) == U.intersection(W)
        True
    """
    if left.degree() != right.degree():
        raise ValueError("the subspaces must have the same ambient degree")
    ambient = VectorSpace(QQ, left.degree())
    if not left.dimension() or not right.dimension():
        return ambient.subspace([])
    left_basis = left.basis_matrix()
    relations = _exact_left_kernel(
        left_basis.stack(-right.basis_matrix())
    ).basis_matrix()
    coefficients = relations.matrix_from_columns(range(left.dimension()))
    # Projection to the left coordinates is injective on the relation
    # kernel because both input matrices have independent rows.  Preserve
    # the resulting independent basis without another row reduction.
    return ambient.span_of_basis(
        (coefficients * left_basis).rows(), check=False
    )


def differentiate_polynomial(f):
    r"""Differentiate the coefficients of a polynomial in ``y`` by ``x``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.cohomology import differentiate_polynomial
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: differentiate_polynomial((x^2 + 1)*y + x)
        2*x*y + 1
    """
    return f.parent()([coefficient.derivative() for coefficient in f.list()])


def differentiate_matrix(A):
    r"""Differentiate a rational-function matrix entry by entry.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.cohomology import differentiate_matrix
        sage: R.<x> = QQ[]; K = R.fraction_field()
        sage: differentiate_matrix(matrix(K, [[x^2, 1/x], [0, x]]))
        [   2*x -1/x^2]
        [     0      1]
    """
    return A.apply_map(lambda entry: entry.derivative())


def differentiate_vector(v):
    r"""Differentiate a rational-function vector entry by entry.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.cohomology import differentiate_vector
        sage: R.<x> = QQ[]; K = R.fraction_field()
        sage: differentiate_vector(vector(K, [x^2, 1/x]))
        (2*x, -1/x^2)
    """
    return vector(v.base_ring(), [entry.derivative() for entry in v])


def reduce_mod_model_exact(f, Q):
    r"""Reduce a polynomial in ``y`` exactly modulo the monic polynomial ``Q``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.cohomology import reduce_mod_model_exact
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: reduce_mod_model_exact(y^3 + y, y^2 - x)
        (x + 1)*y
    """
    if not Q.is_monic():
        raise ValueError("Q must be monic")
    return f.quo_rem(Q)[1]


def polynomials_to_vector(polynomials, degree_x):
    r"""Flatten polynomial coefficients through degree ``degree_x``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.cohomology import polynomials_to_vector
        sage: R.<x> = QQ[]
        sage: polynomials_to_vector([1 + x, x^2], 2)
        (1, 1, 0, 0, 0, 1)
    """
    entries = []
    for polynomial in polynomials:
        entries.extend(_coefficient(polynomial, j) for j in range(degree_x + 1))
    return vector(QQ, entries)


def _coefficient(polynomial, exponent):
    """Return a polynomial coefficient, treating negative exponents as zero.

    TESTS::

        sage: from sage.schemes.curves.coleman.cohomology import _coefficient
        sage: R.<x> = QQ[]
        sage: _coefficient(x^2 + 3, -1), _coefficient(x^2 + 3, 2)
        (0, 1)
    """
    if exponent < 0:
        return polynomial.base_ring().zero()
    return polynomial[exponent]


def _function_field_model(Q):
    """Coerce a ``QQ[x][y]`` model to ``QQ(x)[y]``.

    TESTS::

        sage: from sage.schemes.curves.coleman.cohomology import _function_field_model
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: _, K, _, q = _function_field_model(y^2 - x)
        sage: K, q
        (Rational function field in x over Rational Field, y^2 - x)
    """
    Rx, Sy = _model_rings(Q, require_monic=True)
    Kx = FunctionField(QQ, names=Rx.variable_name())
    Ky = PolynomialRing(Kx, names=Sy.variable_name())
    return Rx, Kx, Ky, Ky([Kx(c) for c in Q.list()])


def connection_matrix(Q, Delta, s):
    r"""
    Return the connection matrix in the power basis of ``Q``.

    The result ``G`` is characterized by

    .. MATH::

        \frac{d}{dx}(1,y,\ldots,y^{d-1}) = (1,y,\ldots,y^{d-1})G.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.auxiliary import auxiliary_polynomials
        sage: from sage.schemes.curves.coleman.cohomology import connection_matrix
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: r, Delta, s = auxiliary_polynomials(y^2 - x^3)
        sage: connection_matrix(y^2 - x^3, Delta, s)
        [    0     0]
        [    0 3/2/x]
    """
    _, Kx, Ky, q = _function_field_model(Q)
    Delta = Kx(Delta)
    s = Ky(s)
    d = q.degree()
    y = Ky.gen()
    q_x = differentiate_polynomial(q)

    rows = [Ky.zero()]
    for i in range(1, d):
        rows.append(reduce_mod_model_exact(
            -i * y**(i - 1) * (s / Delta) * q_x, q
        ))
    return matrix(Kx, d, d,
                  lambda i, j: rows[i][j] if j <= rows[i].degree() else 0)


def gauge_connection_matrix(G, W):
    r"""Change the connection matrix from the power basis to the row basis ``W``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.cohomology import gauge_connection_matrix
        sage: R.<x> = QQ[]; K = R.fraction_field()
        sage: G = matrix(K, [[x, 1], [0, 1/x]])
        sage: gauge_connection_matrix(G, identity_matrix(K, 2)) == G
        True
    """
    W_inverse = W.inverse()
    return W * G * W_inverse + differentiate_matrix(W) * W_inverse


def _evaluate_rational_function(f, value):
    """Evaluate a polynomial or rational function at ``value``.

    TESTS::

        sage: from sage.schemes.curves.coleman.cohomology import _evaluate_rational_function
        sage: R.<x> = QQ[]
        sage: _evaluate_rational_function((x + 1)/(x + 2), QQ(1))
        2/3
    """
    if f == 0:
        return value.parent().zero() if hasattr(value, "parent") else QQ.zero()
    try:
        numerator = f.numerator()
        denominator = f.denominator()
    except AttributeError:
        return f(value)
    parent = value.parent() if hasattr(value, "parent") else QQ
    numerator_value = (numerator(value) if callable(numerator)
                       else parent(numerator))
    denominator_value = (denominator(value) if callable(denominator)
                         else parent(denominator))
    return numerator_value / denominator_value


def _evaluate_vector(v, value):
    """Evaluate every entry of ``v`` at ``value``.

    TESTS::

        sage: from sage.schemes.curves.coleman.cohomology import _evaluate_vector
        sage: R.<x> = QQ[]; K = R.fraction_field()
        sage: _evaluate_vector(vector(K, [(x + 1)/(x + 2), x^2]), QQ(1))
        [2/3, 1]
    """
    return [_evaluate_rational_function(entry, value) for entry in v]


def _evaluate_matrix(A, value, base_ring=None):
    """Evaluate every entry of ``A`` at ``value``.

    TESTS::

        sage: from sage.schemes.curves.coleman.cohomology import _evaluate_matrix
        sage: R.<x> = QQ[]; K = R.fraction_field()
        sage: _evaluate_matrix(matrix(K, [[x, 1/x], [0, x^2]]), QQ(1))
        [1 1]
        [0 1]
    """
    if base_ring is None:
        base_ring = value.parent() if hasattr(value, "parent") else QQ
    return matrix(base_ring, A.nrows(), A.ncols(),
                  [_evaluate_rational_function(entry, value) for entry in A.list()])


def _substitute_inverse(f, target_field):
    """Substitute ``x = 1/t`` into ``f`` as an exact rational function.

    TESTS::

        sage: from sage.schemes.curves.coleman.cohomology import _substitute_inverse
        sage: R.<x> = QQ[]; K.<t> = FunctionField(QQ)
        sage: _substitute_inverse((x + 1)/(x + 2), K) == (1 + t)/(1 + 2*t)
        True
    """
    t = target_field.gen()
    if f == 0:
        return target_field.zero()
    numerator = f.numerator()
    denominator = f.denominator()
    numerator_value = (numerator(1 / t) if callable(numerator)
                       else target_field(numerator))
    denominator_value = (denominator(1 / t) if callable(denominator)
                         else target_field(denominator))
    return target_field(numerator_value) / target_field(denominator_value)


def _substitute_inverse_matrix(A, target_field):
    """Substitute ``x = 1/t`` in a matrix.

    TESTS::

        sage: from sage.schemes.curves.coleman.cohomology import _substitute_inverse_matrix
        sage: R.<x> = QQ[]; Kx = R.fraction_field()
        sage: Kt.<t> = FunctionField(QQ)
        sage: A = _substitute_inverse_matrix(matrix(Kx, [[x, 1/x]]), Kt)
        sage: A == matrix(Kt, [[1/t, t]])
        True
    """
    return matrix(target_field, A.nrows(), A.ncols(),
                  [_substitute_inverse(entry, target_field) for entry in A.list()])


def _jordan_row_convention(A):
    r"""Return ``(J,T,Tinv)`` with ``J = T*A*Tinv`` for row vectors.

    TESTS::

        sage: from sage.schemes.curves.coleman.cohomology import _jordan_row_convention
        sage: A = matrix(QQ, [[2, 1], [0, 2]])
        sage: J, T, Tinv = _jordan_row_convention(A)
        sage: J == T*A*Tinv and T*Tinv == identity_matrix(QQ, 2)
        True

    For a non-diagonal zero-eigenvalue block, residues are coordinates in the
    cokernel, represented dually by the right kernel::

        sage: N = matrix(QQ, [[0, 1], [0, 0]])
        sage: row = vector(QQ, [2, 3])
        sage: [row.dot_product(v) for v in N.right_kernel().basis()]
        [2]
    """
    J, P = A.jordan_form(transformation=True)
    # Sage uses J = P^-1*A*P.  T=P^-1 converts this to the convention used
    # by the row-vector algorithms below.
    return J, P.inverse(), P


def jordan_at_infinity(Ginf):
    r"""Return the Jordan data of the residue of ``Ginf`` at infinity.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.cohomology import jordan_at_infinity
        sage: R.<x> = QQ[]; K = R.fraction_field()
        sage: J, T, Tinv = jordan_at_infinity(
        ....:     matrix(K, [[1/x, 0], [0, 2/x]]))
        sage: J.diagonal(), T*Tinv == identity_matrix(QQ, 2)
        ([-1, -2], True)
    """
    Kt = FunctionField(QQ, names="t")
    t = Kt.gen()
    transformed = _substitute_inverse_matrix(Ginf, Kt) / t
    residue = -_evaluate_matrix(transformed, QQ.zero(), QQ)
    return _jordan_row_convention(residue)


def jordan_at_finite_places(r, G0):
    r"""Return Jordan data for residues above irreducible factors of ``r``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.cohomology import jordan_at_finite_places
        sage: R.<x> = QQ[]; K = R.fraction_field()
        sage: G = matrix(K, [[1/x, 0], [0, 2/x]])
        sage: forms, transformations, inverses = jordan_at_finite_places(
        ....:     x*(x - 1), G)
        sage: len(forms), all(T*U == 1 for T, U in zip(transformations, inverses))
        (2, True)
    """
    polynomial_ring = r.parent()
    r = polynomial_ring(r)
    scalar = G0 * G0.base_ring()(r) / G0.base_ring()(r.derivative())
    jordan_forms = []
    transformations = []
    inverse_transformations = []

    for factor_raw, _ in r.factor():
        factor = factor_raw.monic()
        if factor.degree() == 1:
            field = QQ
            root = -factor[0]
        else:
            field = NumberField(factor, name="a")
            root = field.gen()
        residue = _evaluate_matrix(scalar, root, field)
        J, T, T_inverse = _jordan_row_convention(residue)
        jordan_forms.append(J)
        transformations.append(T)
        inverse_transformations.append(T_inverse)
    return jordan_forms, transformations, inverse_transformations


def ramification_bounds(J0, Jinf):
    r"""Return the largest finite and infinite residue denominators.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.cohomology import ramification_bounds
        sage: J0 = [matrix(QQ, [[1/2]])]
        sage: Jinf = matrix(QQ, [[1/3]])
        sage: ramification_bounds(J0, Jinf)
        (2, 3)
    """
    finite = [QQ(J[i, i]).denominator()
              for J in J0 for i in range(J.nrows())]
    infinite = [QQ(Jinf[i, i]).denominator()
                for i in range(Jinf.nrows())]
    return (max(finite) if finite else ZZ.zero(), max(infinite))


def order_at_zero(f):
    r"""Return the order of a rational function at zero.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.cohomology import order_at_zero
        sage: R.<x> = QQ[]
        sage: order_at_zero(x^3/(x^2 + 1))
        3
    """
    if f == 0:
        return infinity
    return f.numerator().valuation() - f.denominator().valuation()


def order_matrix_at_zero(A):
    r"""Return the minimum order at zero among entries of ``A``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.cohomology import order_matrix_at_zero
        sage: R.<x> = QQ[]; K = R.fraction_field()
        sage: order_matrix_at_zero(matrix(K, [[x^2, 1/x], [0, x]]))
        -1
    """
    return min(order_at_zero(entry) for entry in A.list())


def _factor_multiplicity(polynomial, factor):
    """Return the multiplicity of ``factor`` in ``polynomial``.

    TESTS::

        sage: from sage.schemes.curves.coleman.cohomology import _factor_multiplicity
        sage: R.<x> = QQ[]
        sage: _factor_multiplicity((x - 1)^3*(x + 1), x - 1)
        3
    """
    if polynomial == 0:
        return infinity
    value = ZZ.zero()
    while polynomial % factor == 0:
        polynomial = polynomial.quo_rem(factor)[0]
        value += 1
    return value


def order_at_polynomial(f, r):
    r"""Return the minimum order of ``f`` at irreducible factors of ``r``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.cohomology import order_at_polynomial
        sage: R.<x> = QQ[]
        sage: order_at_polynomial((x - 1)^2/(x + 1), x^2 - 1)
        -1
    """
    if f == 0:
        return infinity
    factors = [factor.monic() for factor, _ in r.factor()]
    return min(_factor_multiplicity(f.numerator(), factor)
               - _factor_multiplicity(f.denominator(), factor)
               for factor in factors)


def order_matrix_at_polynomial(A, r):
    r"""Return the minimum ``r``-order among entries of ``A``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.cohomology import order_matrix_at_polynomial
        sage: R.<x> = QQ[]; K = R.fraction_field()
        sage: A = matrix(K, [[1/(x - 1), x], [0, x + 1]])
        sage: order_matrix_at_polynomial(A, x^2 - 1)
        -1
    """
    return min(order_at_polynomial(entry, r) for entry in A.list())


def order_at_infinity(f):
    r"""Return the order of a rational function at infinity.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.cohomology import order_at_infinity
        sage: R.<x> = QQ[]
        sage: order_at_infinity(x^3/(x^2 + 1))
        -1
    """
    if f == 0:
        return infinity
    return f.denominator().degree() - f.numerator().degree()


def order_matrix_at_infinity(A):
    r"""Return the minimum order at infinity among entries of ``A``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.cohomology import order_matrix_at_infinity
        sage: R.<x> = QQ[]; K = R.fraction_field()
        sage: order_matrix_at_infinity(matrix(K, [[x^2, 1/x], [0, x]]))
        -2
    """
    return min(order_at_infinity(entry) for entry in A.list())


def residue_at_finite_places(w, Q, r, J0, T0inv):
    r"""Compute the finite residues of ``sum(w_i*b_i^0*dx/r)``.

    TESTS:

    This is exercised while constructing a de Rham basis::

        sage: from sage.schemes.curves.coleman.data import de_rham_cohomology_basis
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: len(de_rham_cohomology_basis(  # indirect doctest
        ....:     y^2 - (x^3 - 10*x + 9), 5, 2, genus=1)[0])
        2
    """
    residues = []
    for index, (factor_raw, _) in enumerate(r.factor()):
        factor = factor_raw.monic()
        field = T0inv[index].base_ring()
        root = -factor[0] if factor.degree() == 1 else field.gen()
        transformed = vector(field, _evaluate_vector(w, root)) * T0inv[index]
        for functional in J0[index].right_kernel().basis():
            value = transformed.dot_product(functional)
            if field is QQ:
                residues.append(QQ(value))
            else:
                residues.extend(QQ(c) for c in value.vector())
    return vector(QQ, residues)


def _laurent_coefficient(f, exponent):
    """Return an exact Laurent coefficient of a rational function at zero.

    TESTS::

        sage: from sage.schemes.curves.coleman.cohomology import _laurent_coefficient
        sage: R.<x> = QQ[]
        sage: _laurent_coefficient((1 + x)/(x^2*(1 - x)), -1)
        2
    """
    if f == 0:
        return QQ.zero()
    valuation = order_at_zero(f)
    if exponent < valuation:
        return QQ.zero()

    numerator = f.numerator()
    denominator = f.denominator()
    variable = numerator.parent().gen()
    if valuation >= 0:
        numerator = numerator.quo_rem(variable**valuation)[0]
    else:
        denominator = denominator.quo_rem(variable**(-valuation))[0]

    index = ZZ(exponent - valuation)
    series_ring = PowerSeriesRing(QQ, names="u", default_prec=index + 1)
    numerator_series = series_ring(numerator.list())
    denominator_series = series_ring(denominator.list())
    return (numerator_series / denominator_series)[index]


def vector_valuation_at_zero(v):
    r"""Return the minimum zero-adic valuation among entries of ``v``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.cohomology import vector_valuation_at_zero
        sage: R.<x> = QQ[]; K = R.fraction_field()
        sage: vector_valuation_at_zero(vector(K, [x^2, 1/x]))
        -1
    """
    return min(order_at_zero(entry) for entry in v)


def _infinity_residue_context(Q, r, W0, Winf, Ginf, Jinf):
    r"""Precompute the invariant data used by infinity-residue reductions.

    TESTS::

        sage: from sage.schemes.curves.coleman.cohomology import _infinity_residue_context
        sage: R.<x> = QQ[]; S.<y> = R[]; K = R.fraction_field()
        sage: W = identity_matrix(K, 2)
        sage: context = _infinity_residue_context(
        ....:     y^2 - x, x, W, W, zero_matrix(K, 2), zero_matrix(QQ, 2))
        sage: context[0], context[1], len(context[-1])
        (2, 1, 2)
    """
    d = Q.degree()
    degree_r = r.degree()
    Kt = FunctionField(QQ, names="t")
    t = Kt.gen()

    W_inverse = (Winf * W0.inverse()).inverse()
    transformed_W_inverse = _substitute_inverse_matrix(W_inverse, Kt)
    transformed_Ginf = _substitute_inverse_matrix(Ginf, Kt)
    residue_connection = -_evaluate_matrix(
        transformed_Ginf / t, QQ.zero(), QQ
    )
    r_in_K = Ginf.base_ring()(r)
    transformed_r = _substitute_inverse(r_in_K, Kt)
    transformed_rG = transformed_r * transformed_Ginf
    residue_functionals = tuple(Jinf.right_kernel().basis())
    return (
        d, degree_r, Kt, t, transformed_W_inverse,
        residue_connection, transformed_rG, transformed_r,
        residue_functionals,
    )


def residue_at_infinity(w, Q, r, W0, Winf, Ginf, Jinf, Tinfinv,
                        _context=None):
    r"""Compute the residues at infinity of ``sum(w_i*b_i^0*dx/r)``.

    TESTS:

    This is exercised while constructing a de Rham basis::

        sage: from sage.schemes.curves.coleman.data import de_rham_cohomology_basis
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: len(de_rham_cohomology_basis(  # indirect doctest
        ....:     y^2 - (x^3 - 10*x + 9), 5, 2, genus=1)[0])
        2
    """
    if _context is None:
        _context = _infinity_residue_context(
            Q, r, W0, Winf, Ginf, Jinf
        )
    (d, degree_r, Kt, t, transformed_W_inverse,
     residue_connection, transformed_rG, transformed_r,
     residue_functionals) = _context
    transformed_w = vector(Kt, [_substitute_inverse(entry, Kt) for entry in w])
    transformed_w *= transformed_W_inverse

    while vector_valuation_at_zero(transformed_w) < -degree_r + 1:
        m = -vector_valuation_at_zero(transformed_w) - degree_r + 1
        reduction_matrix = residue_connection - m * identity_matrix(QQ, d)
        coefficient_exponent = -m - degree_r + 1
        rhs = vector(QQ, [
            _laurent_coefficient(-entry, coefficient_exponent)
            / r.leading_coefficient()
            for entry in transformed_w
        ])
        vbar = rhs * reduction_matrix.inverse()
        vbar_t = vector(Kt, vbar)
        transformed_w -= (
            t**(-m) * vbar_t * transformed_rG
            + transformed_r * m * t**(1 - m) * vbar_t
        )

    transformed_w *= t**(degree_r - 1)
    constant = vector(QQ, [_laurent_coefficient(entry, 0)
                           for entry in transformed_w])
    constant *= Tinfinv
    return vector(QQ, [
        constant.dot_product(functional)
        for functional in residue_functionals
    ])


def _relative_complement_from_basis(space, fixed):
    r"""Return a complement to the independent vectors in ``fixed``.

    TESTS::

        sage: from sage.schemes.curves.coleman.cohomology import _relative_complement_from_basis
        sage: V = VectorSpace(QQ, 3)
        sage: _relative_complement_from_basis(V, [V([1, 0, 0])]).basis()
        [(0, 1, 0), (0, 0, 1)]
    """
    ambient = space.ambient_vector_space()
    candidates = list(reversed(space.echelonized_basis()))
    pivots = matrix(QQ, list(fixed) + candidates).transpose().pivots()
    if len(pivots) != space.dimension():
        raise ValueError("the fixed vectors must span a subspace of the first space")
    chosen = [candidates[index - len(fixed)] for index in pivots
              if index >= len(fixed)]
    # ``chosen`` is a subset of an echelon basis, listed in reverse order.
    return ambient.subspace(
        list(reversed(chosen)), check=False, already_echelonized=True
    )


def _relative_complement(space, subspace):
    """Return a deterministic complement of ``subspace`` in ``space``.

    TESTS::

        sage: from sage.schemes.curves.coleman.cohomology import _relative_complement
        sage: V = VectorSpace(QQ, 3)
        sage: U = V.subspace([V([1, 0, 0])])
        sage: _relative_complement(V, U).basis()
        [(0, 1, 0), (0, 0, 1)]
    """
    # Give priority to the trailing pivots of ``space``.  This choice is
    # mathematically immaterial, but it fixes reproducible coordinates for
    # Coleman integrals.
    return _relative_complement_from_basis(
        space, subspace.echelonized_basis()
    )


def _polynomial_matrix(A, polynomial_ring):
    """Coerce an integral rational-function matrix to a polynomial matrix.

    TESTS::

        sage: from sage.schemes.curves.coleman.cohomology import _polynomial_matrix
        sage: R.<x> = QQ[]; K = R.fraction_field()
        sage: _polynomial_matrix(matrix(K, [[x, 1], [0, 2]]), R)
        [x 1]
        [0 2]
    """
    entries = []
    for entry in A.list():
        try:
            entries.append(polynomial_ring(entry))
        except (TypeError, ValueError):
            denominator = entry.denominator()
            if denominator.degree() > 0:
                raise ArithmeticError("expected a polynomial matrix")
            entries.append(polynomial_ring(entry.numerator()) / denominator[0])
    return matrix(polynomial_ring, A.nrows(), A.ncols(), entries)


def basis_cohomology(Q, p, r, W0, Winf, G0, Ginf, J0, Jinf,
                     T0inv, Tinfinv, use_open_curve=False,
                     basis0=None, basis1=None, basis2=None, genus=None):
    r"""Compute the differential basis, exact primitives, and quotient map.

    TESTS:

    This is exercised by the public de Rham-basis constructor::

        sage: from sage.schemes.curves.coleman.data import de_rham_cohomology_basis
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: len(de_rham_cohomology_basis(  # indirect doctest
        ....:     y^2 - (x^3 - 10*x + 9), 5, 2, genus=1)[0])
        2
    """
    p = _validate_prime(p)
    basis0 = [] if basis0 is None else basis0
    basis1 = [] if basis1 is None else basis1
    basis2 = [] if basis2 is None else basis2

    polynomial_ring, _ = _model_rings(Q, require_monic=True)
    x = polynomial_ring.gen()
    d = Q.degree()
    degree_r = r.degree()
    W = Winf * W0.inverse()
    W_inverse = W.inverse()
    ord0_W = order_matrix_at_zero(W)
    ordinf_W = order_matrix_at_infinity(W)
    ord0_Winv = order_matrix_at_zero(W_inverse)
    ordinf_Winv = order_matrix_at_infinity(W_inverse)

    degree_bound_E0 = ZZ(degree_r - ord0_W - ordinf_W - 2)
    monomials_E0 = [(i, j) for i in range(d)
                    for j in range(degree_bound_E0 + 1)]
    dimension_E0 = len(monomials_E0)
    E0 = VectorSpace(QQ, dimension_E0)

    intersection_width = ZZ(-ordinf_W - ordinf_Winv)
    matrix_E0_Einf = matrix(QQ, dimension_E0, d * intersection_width, 0)
    for i, (power_y, power_x) in enumerate(monomials_E0):
        temp = x**power_x * W_inverse.row(power_y)
        for j in range(d):
            numerator = (W.base_ring()(x)**(-ord0_Winv) * temp[j]).numerator()
            for k in range(intersection_width):
                exponent = k - ord0_W - ord0_Winv + degree_r - 1
                matrix_E0_Einf[i, j * intersection_width + k] = _coefficient(
                    numerator, exponent
                )
    E0_intersection_Einf = _exact_left_kernel(matrix_E0_Einf)

    logarithmic_width = ZZ(-ord0_W - ordinf_W - ordinf_Winv - 1)
    matrix_logarithmic = matrix(QQ, dimension_E0,
                                d * logarithmic_width, 0)
    for i, (power_y, power_x) in enumerate(monomials_E0):
        temp = x**power_x * W_inverse.row(power_y)
        for j in range(d):
            numerator = (W.base_ring()(x)**(-ord0_Winv) * temp[j]).numerator()
            for k in range(logarithmic_width):
                exponent = k - ord0_Winv + degree_r
                matrix_logarithmic[i, j * logarithmic_width + k] = _coefficient(
                    numerator, exponent
                )
    logarithmic_forms = _exact_intersection(
        E0_intersection_Einf, _exact_left_kernel(matrix_logarithmic)
    )

    test_w = vector(polynomial_ring, d)
    test_w[0] = 1
    finite_residue_dimension = len(
        residue_at_finite_places(test_w, Q, r, J0, T0inv)
    )
    finite_residues = matrix(QQ, dimension_E0, finite_residue_dimension, 0)
    infinity_residue_context = _infinity_residue_context(
        Q, r, W0, Winf, Ginf, Jinf
    )
    infinite_residue_dimension = len(residue_at_infinity(
        test_w, Q, r, W0, Winf, Ginf, Jinf, Tinfinv,
        _context=infinity_residue_context,
    ))
    infinite_residues = matrix(QQ, dimension_E0,
                               infinite_residue_dimension, 0)

    for i, (power_y, power_x) in enumerate(monomials_E0):
        w = vector(polynomial_ring, d)
        w[power_y] = x**power_x
        finite = residue_at_finite_places(w, Q, r, J0, T0inv)
        infinite = residue_at_infinity(
            w, Q, r, W0, Winf, Ginf, Jinf, Tinfinv,
            _context=infinity_residue_context,
        )
        for j, coefficient in enumerate(finite):
            finite_residues[i, j] = coefficient
        for j, coefficient in enumerate(infinite):
            infinite_residues[i, j] = coefficient

    finite_residue_kernel = _exact_left_kernel(finite_residues)
    infinite_residue_kernel = _exact_left_kernel(infinite_residues)
    second_kind = _exact_intersection(
        finite_residue_kernel, infinite_residue_kernel
    )
    cocycles = _exact_intersection(E0_intersection_Einf, second_kind)
    first_kind = _exact_intersection(logarithmic_forms, second_kind)
    genus = ZZ(first_kind.dimension() if genus is None else genus)
    if first_kind.dimension() != genus:
        raise ValueError(
            "the regular differential space does not have dimension genus"
        )

    def validate_partition(name, vectors, ambient, expected, previous=None):
        if len(vectors) != expected:
            raise ValueError(f"{name} must contain {expected} vectors")
        vectors = [E0(item) for item in vectors]
        span = E0.subspace(vectors)
        if span.dimension() != expected:
            raise ValueError(f"{name} must be linearly independent")
        combined = E0.subspace(list(ambient.basis()) + vectors)
        if combined.dimension() != ambient.dimension():
            raise ValueError(f"{name} is not contained in the required space")
        if previous is not None:
            combined = E0.subspace(list(previous.basis()) + list(vectors))
            if combined.dimension() != previous.dimension() + expected:
                raise ValueError(
                    f"{name} is not independent modulo the preceding space"
                )

    degree_bound_B0 = ZZ(-ord0_W - ordinf_W - 1)
    monomials_B0 = [(i, j) for i in range(d)
                    for j in range(degree_bound_B0 + 1)]
    dimension_B0 = len(monomials_B0)
    matrix_B0_Binf = matrix(QQ, dimension_B0,
                            d * intersection_width, 0)
    for i, (power_y, power_x) in enumerate(monomials_B0):
        temp = x**power_x * W_inverse.row(power_y)
        for j in range(d):
            numerator = (W.base_ring()(x)**(-ord0_Winv) * temp[j]).numerator()
            for k in range(intersection_width):
                exponent = k - ord0_W - ord0_Winv
                matrix_B0_Binf[i, j * intersection_width + k] = _coefficient(
                    numerator, exponent
                )
    B0_intersection_Binf = _exact_left_kernel(matrix_B0_Binf)

    rG0 = _polynomial_matrix(G0 * G0.base_ring()(r), polynomial_ring)
    derivative_pairs = []
    for coordinates in B0_intersection_Binf.echelonized_basis():
        primitive = vector(polynomial_ring, d)
        for coefficient, (power_y, power_x) in zip(coordinates, monomials_B0):
            primitive[power_y] += coefficient * x**power_x
        derivative = primitive * rG0 + r * differentiate_vector(primitive)
        flattened = E0([
            _coefficient(derivative[power_y], power_x)
            for power_y, power_x in monomials_E0
        ])
        derivative_pairs.append((flattened, primitive))

    nonconstant_pairs = [(derivative, primitive)
                         for derivative, primitive in derivative_pairs
                         if not derivative.is_zero()]
    coboundaries = E0.subspace([pair[0] for pair in nonconstant_pairs])

    if basis0:
        b0 = [E0(polynomials_to_vector(item, degree_bound_E0))
              for item in basis0]
        validate_partition("basis0", b0, first_kind, genus)
    else:
        b0 = list(first_kind.echelonized_basis())

    dual_space = _relative_complement(
        cocycles, first_kind + coboundaries
    )
    if basis1:
        b1 = [E0(polynomials_to_vector(item, degree_bound_E0))
              for item in basis1]
        validate_partition(
            "basis1", b1, cocycles, genus, first_kind + coboundaries
        )
    else:
        b1 = list(dual_space.basis())
    if dual_space.dimension() != genus:
        raise ArithmeticError("the first de Rham cohomology has dimension != 2g")

    dimension_H1X = len(b0) + len(b1)
    if dimension_H1X != 2 * genus:
        raise ArithmeticError("the first de Rham cohomology has dimension != 2g")
    finite_regular_logarithmic = _exact_intersection(
        logarithmic_forms, finite_residue_kernel
    )
    H1Y_mod_H1X = _relative_complement(
        finite_regular_logarithmic, first_kind
    )
    if basis2:
        b2 = [E0(polynomials_to_vector(item, degree_bound_E0))
              for item in basis2]
        validate_partition(
            "basis2", b2, finite_regular_logarithmic,
            H1Y_mod_H1X.dimension(), first_kind
        )
    else:
        b2 = list(H1Y_mod_H1X.basis())

    b3 = list(_relative_complement_from_basis(
        E0_intersection_Einf,
        list(cocycles.echelonized_basis())
        + list(H1Y_mod_H1X.echelonized_basis()),
    ).basis())
    b4 = list(_relative_complement(E0, E0_intersection_Einf).basis())
    b5 = [pair[0] for pair in nonconstant_pairs]
    full_basis = b0 + b1 + b2 + b3 + b4 + b5

    dimension_H1U = len(b0) + len(b1) + len(b2) + len(b3)
    dimension = dimension_H1U if use_open_curve else dimension_H1X
    for i in range(dimension):
        denominator_valuation = min(
            [ZZ.zero()] + [QQ(c).valuation(p) for c in full_basis[i] if c]
        )
        full_basis[i] = p**(-denominator_valuation) * full_basis[i]

    basis_matrix = matrix(QQ, full_basis)
    if basis_matrix.nrows() != dimension_E0 or not basis_matrix.is_invertible():
        raise ArithmeticError("the cohomology decomposition is not a basis of E0")
    quotient_map = basis_matrix.inverse()

    integrals = [r.leading_coefficient() * pair[1]
                 for pair in nonconstant_pairs]
    differential_basis = []
    for coordinates in full_basis[:dimension]:
        differential = vector(polynomial_ring, d)
        for coefficient, (power_y, power_x) in zip(coordinates, monomials_E0):
            differential[power_y] += QQ(coefficient) * x**power_x
        differential_basis.append(differential)

    return differential_basis, integrals, quotient_map
