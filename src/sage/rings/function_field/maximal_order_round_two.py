# sage.doctest: needs sage.rings.function_field sage.rings.number_field
r"""
Round--2 maximal orders for function fields over `\QQ(x)`

This module implements the local part of the Pohst--Zassenhaus (or
``Round 2``) algorithm for an integral simple extension of `\QQ(x)`.
Unlike the general normalization algorithm, Round--2 works prime by prime
at the square factors of the equation-order discriminant.

For an order `O` and an irreducible polynomial `p \in \QQ[x]`, let `I_p`
be the inverse image in `O` of the nilradical of `O/pO`.  The multiplier
ring

.. MATH::

    (I_p:I_p) = \{a \in K : a I_p \subseteq I_p\}

is equal to `O` exactly when `O` is `p`-maximal.  Otherwise it is a
strictly larger order.  Iterating this construction at every square
factor of the discriminant produces the maximal order.

Since the residue fields `\QQ[x]/(p)` have characteristic zero, the
nilradical is the kernel of the trace pairing.  Thus every local step is
linear algebra over either `\QQ` or a number field.

"""

from sage.matrix.constructor import identity_matrix, matrix
from sage.modules.free_module_element import vector

from sage.arith.functions import lcm
from sage.rings.number_field.number_field import NumberField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ


def _polynomial_part(value, polynomial_ring):
    r"""
    Coerce an integral rational function to ``polynomial_ring``.

    A separate helper gives failures in the Round--2 invariants a useful
    error instead of silently moving the computation to a fraction field.

    TESTS::

        sage: from sage.rings.function_field.maximal_order_round_two import _polynomial_part
        sage: R.<x> = QQ[]; K = R.fraction_field()
        sage: _polynomial_part(K((x^2-1)/(x-1)), R)
        x + 1
    """
    try:
        return polynomial_ring(value)
    except (TypeError, ValueError):
        numerator = polynomial_ring(value.numerator())
        denominator = polynomial_ring(value.denominator())
        if denominator.degree() > 0:
            raise ArithmeticError(
                "an order structure constant is not polynomial"
            )
        return numerator / denominator[0]


def _residue_field(polynomial_ring, prime):
    r"""
    Return reduction and lifting maps for ``QQ[x]/(prime)``.

    TESTS::

        sage: from sage.rings.function_field.maximal_order_round_two import _residue_field
        sage: R.<x> = QQ[]
        sage: k, reduce, lift = _residue_field(R, x^2+1)
        sage: reduce(x)^2, lift(reduce(x))
        (-1, x)
    """
    prime = polynomial_ring(prime).monic()
    if not prime.is_irreducible():
        raise ValueError("prime must be irreducible")

    if prime.degree() == 1:
        root = -prime[0]

        def reduce_polynomial(f):
            return QQ(polynomial_ring(f)(root))

        def lift_residue(c):
            return polynomial_ring(QQ(c))

        return QQ, reduce_polynomial, lift_residue

    residue_field = NumberField(prime, name="a")
    generator = residue_field.gen()

    def reduce_polynomial(f):
        return residue_field(polynomial_ring(f)(generator))

    def lift_residue(c):
        return polynomial_ring(residue_field(c).polynomial().list())

    return residue_field, reduce_polynomial, lift_residue


def _canonical_module_basis(field, generators):
    r"""
    Return a canonical `\QQ[x]`-basis for the span of ``generators``.

    TESTS::

        sage: from sage.rings.function_field.maximal_order_round_two import _canonical_module_basis
        sage: K.<x> = FunctionField(QQ); R.<Y> = K[]
        sage: L.<y> = K.extension(Y^2-x)
        sage: _canonical_module_basis(L, [L.one(), L.gen()])
        (1, y)
    """
    from sage.rings.function_field.hermite_form_polynomial import (
        reversed_hermite_form,
    )

    base_field = field.base_field()
    polynomial_ring = base_field.maximal_order()._ring
    _, from_vector, to_vector = field.vector_space()

    vectors = [to_vector(field(g)) for g in generators]
    denominator = lcm(
        [coefficient.denominator()
         for row in vectors for coefficient in row]
    )
    numerator_matrix = matrix(
        polynomial_ring,
        [[_polynomial_part(denominator * coefficient, polynomial_ring)
          for coefficient in row]
         for row in vectors],
    )
    reversed_hermite_form(numerator_matrix)
    rows = [row for row in numerator_matrix.rows() if not row.is_zero()]
    if len(rows) != field.degree():
        raise ArithmeticError("the enlarged order does not have full rank")
    return tuple(from_vector(row / denominator) for row in rows)


def _multiplication_table(field, basis):
    r"""
    Return structure constants of an order basis over `\QQ[x]`.

    TESTS::

        sage: from sage.rings.function_field.maximal_order_round_two import _multiplication_table
        sage: K.<x> = FunctionField(QQ); R.<Y> = K[]
        sage: L.<y> = K.extension(Y^2-x)
        sage: table = _multiplication_table(L, [L.one(), L.gen()])
        sage: table[1][1]
        (x, 0)
    """
    base_field = field.base_field()
    polynomial_ring = base_field.maximal_order()._ring
    _, _, to_vector = field.vector_space()
    basis_matrix = matrix(base_field, [to_vector(element) for element in basis])
    basis_matrix_inverse = basis_matrix.inverse()

    table = []
    for left in basis:
        row = []
        for right in basis:
            coordinates = to_vector(left * right) * basis_matrix_inverse
            row.append(vector(
                polynomial_ring,
                [_polynomial_part(c, polynomial_ring) for c in coordinates],
            ))
        table.append(row)
    return table


def _p_maximal_enlargement(field, basis, prime):
    r"""
    Perform one multiplier-ring enlargement at ``prime``.

    OUTPUT:

    A pair ``(new_basis, changed)``.  If ``changed`` is ``False``, the
    supplied order is already ``prime``-maximal.

    TESTS::

        sage: from sage.rings.function_field.maximal_order_round_two import _p_maximal_enlargement
        sage: K.<x> = FunctionField(QQ); R.<Y> = K[]
        sage: L.<y> = K.extension(Y^2-x^3)
        sage: basis, changed = _p_maximal_enlargement(
        ....:     L, (L.one(), L.gen()), x)
        sage: changed, basis
        (True, (1, 1/x*y))
    """
    from sage.rings.function_field.hermite_form_polynomial import (
        reversed_hermite_form,
    )

    degree = field.degree()
    base_field = field.base_field()
    polynomial_ring = base_field.maximal_order()._ring
    prime = polynomial_ring(prime).monic()
    residue_field, reduce_polynomial, lift_residue = _residue_field(
        polynomial_ring, prime
    )

    # In characteristic zero the nilradical of O/pO is the radical of its
    # trace pairing.  Elements of an order have polynomial traces.
    trace_pairing = matrix(
        residue_field,
        [[reduce_polynomial(_polynomial_part(
            (basis[i] * basis[j]).trace(), polynomial_ring
        )) for j in range(degree)] for i in range(degree)],
    )
    radical = trace_pairing.left_kernel().basis_matrix()
    if radical.nrows() == 0:
        return basis, False

    radical_lifts = matrix(
        polynomial_ring,
        [[lift_residue(c) for c in row] for row in radical.rows()],
    )

    # I_p is generated by pO together with lifts of the trace radical.
    ideal_matrix = matrix(
        polynomial_ring,
        list((prime * identity_matrix(polynomial_ring, degree)).rows())
        + list(radical_lifts.rows()),
    )
    reversed_hermite_form(ideal_matrix)
    ideal_rows = [row for row in ideal_matrix.rows() if not row.is_zero()]
    if len(ideal_rows) != degree:
        raise ArithmeticError("the p-radical does not have full rank")
    ideal_matrix = matrix(polynomial_ring, ideal_rows)
    ideal_inverse = ideal_matrix.change_ring(base_field).inverse()

    multiplication = _multiplication_table(field, basis)
    action_rows = []
    for k in range(degree):
        flattened_action = []
        for ideal_row in ideal_matrix.rows():
            product = vector(polynomial_ring, degree)
            for j, coefficient in enumerate(ideal_row):
                if coefficient:
                    product += coefficient * multiplication[k][j]
            coordinates = product.change_ring(base_field) * ideal_inverse
            flattened_action.extend(
                reduce_polynomial(_polynomial_part(c, polynomial_ring))
                for c in coordinates
            )
        action_rows.append(flattened_action)

    # N/pO is the kernel of the action O/pO -> End(I_p/pI_p), and
    # (I_p:I_p) = O + (1/p)N.
    action = matrix(residue_field, action_rows)
    kernel = action.left_kernel().basis_matrix()
    if kernel.nrows() == 0:
        return basis, False

    kernel_lifts = [
        [lift_residue(c) for c in row]
        for row in kernel.rows()
    ]
    generators = list(basis)
    for row in kernel_lifts:
        generators.append(sum(
            (base_field(row[j]) / base_field(prime)) * basis[j]
            for j in range(degree)
        ))
    return _canonical_module_basis(field, generators), True


def round_two_maximal_order_basis(field, *, return_iterations=False):
    r"""
    Compute a finite maximal-order basis using the Round--2 algorithm.

    INPUT:

    - ``field`` -- a monic integral simple extension of `\QQ(x)`
    - ``return_iterations`` -- boolean (default: ``False``); also return
      local iteration counts, useful for diagnostics and tests

    EXAMPLES::

        sage: from sage.rings.function_field.maximal_order_round_two import round_two_maximal_order_basis
        sage: K.<x> = FunctionField(QQ)
        sage: R.<y> = K[]
        sage: F.<y> = K.extension(y^2 - x^3)
        sage: round_two_maximal_order_basis(F)
        (1, 1/x*y)

    Towers are rejected with a stable public error::

        sage: S.<z> = F[]; E.<z> = F.extension(z^2-y)
        sage: round_two_maximal_order_basis(E)
        Traceback (most recent call last):
        ...
        NotImplementedError: Round--2 currently supports extensions of rational function fields only

    The returned module is closed under multiplication::

        sage: B = round_two_maximal_order_basis(F)
        sage: from sage.rings.function_field.order_basis import FunctionFieldOrder_basis
        sage: O = FunctionFieldOrder_basis(B)
        sage: all(a*b in O for a in B for b in B)
        True
    """
    if field.constant_base_field() is not QQ:
        raise NotImplementedError(
            "Round--2 currently supports constant field QQ only"
        )
    from .function_field_rational import RationalFunctionField
    if not isinstance(field.base_field(), RationalFunctionField):
        raise NotImplementedError(
            "Round--2 currently supports extensions of rational function "
            "fields only"
        )

    defining_polynomial = field.polynomial()
    if not defining_polynomial.is_monic():
        raise ValueError("the defining polynomial must be monic")

    base_field = field.base_field()
    polynomial_ring = base_field.maximal_order()._ring
    for coefficient in defining_polynomial:
        _polynomial_part(coefficient, polynomial_ring)

    generator = field.gen()
    basis = tuple(generator**i for i in range(field.degree()))
    # All coefficients are integral, so compute the discriminant in
    # QQ[x][y].  Keeping it over QQ(x) selects a generic fraction-field
    # resultant and repeatedly normalizes large rational functions.
    integral_polynomial_ring = PolynomialRing(
        polynomial_ring, defining_polynomial.variable_name()
    )
    integral_polynomial = integral_polynomial_ring([
        _polynomial_part(coefficient, polynomial_ring)
        for coefficient in defining_polynomial
    ])
    discriminant = integral_polynomial.discriminant()
    iterations = {}

    repeated_part = discriminant.gcd(discriminant.derivative())
    for factor, _ in repeated_part.factor():
        prime = factor.monic()
        count = 0
        while True:
            basis, changed = _p_maximal_enlargement(field, basis, prime)
            if not changed:
                break
            count += 1
        iterations[prime] = count

    if return_iterations:
        return basis, iterations
    return basis


def round_two_maximal_order_infinite_basis(field):
    r"""
    Compute a maximal infinite-order basis using Round--2 after inversion.

    EXAMPLES::

        sage: from sage.rings.function_field.maximal_order_round_two import round_two_maximal_order_infinite_basis
        sage: K.<x> = FunctionField(QQ)
        sage: R.<y> = K[]
        sage: F.<y> = K.extension(y^2 - (x^3 - x))
        sage: round_two_maximal_order_infinite_basis(F)
        (1, 1/x^2*y)
    """
    inverted_field, from_inverted, _ = field._inversion_isomorphism()
    return tuple(
        from_inverted(element)
        for element in round_two_maximal_order_basis(inverted_field)
    )
