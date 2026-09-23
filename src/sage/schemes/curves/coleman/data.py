# sage.doctest: needs sage.rings.function_field sage.rings.number_field sage.rings.padics
r"""
Coleman integration setup data for general plane curves

This module assembles the integral bases, connection, de Rham basis,
Frobenius lift, and cohomological reductions into one reusable object.

"""

from dataclasses import dataclass

from sage.matrix.constructor import matrix

from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ

from .auxiliary import (
    _model_rings,
    _validate_prime,
    auxiliary_polynomials,
    curve_genus,
    integral_basis_matrices,
    is_p_integral,
    is_smooth_mod_p,
    positive_log,
)
from .cohomology import (
    basis_cohomology,
    connection_matrix,
    gauge_connection_matrix,
    jordan_at_finite_places,
    jordan_at_infinity,
    order_matrix_at_infinity,
    order_matrix_at_zero,
    ramification_bounds,
)
from .frobenius import frobenius_lift, frobenius_pullback
from .reductions import (
    modular_to_rational_laurent_vector,
    reduce_with_functions,
    reduction_matrices,
)


@dataclass
class ColemanIntegrationData:
    r"""Precomputed data for Coleman integration on a plane curve."""

    Q: object
    p: object
    N: object
    genus: object
    W0: object
    Winf: object
    r: object
    Delta: object
    s: object
    G0: object
    Ginf: object
    e0: object
    einf: object
    delta: object
    basis: list
    quotient_map: object
    integrals: list
    frobenius_matrix: object
    f0_list: list
    finf_list: list
    fend_list: list
    Nmax: object
    finite_reduction_matrices: list
    infinite_reduction_matrices: list
    frobenius_ring_matrix: object


def maximum_precision(Q, p, N, genus, W0, Winf, e0, einf):
    r"""Return the working precision needed for a result modulo ``p^N``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.data import maximum_precision
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: W = identity_matrix(R.fraction_field(), 2)
        sage: maximum_precision(y^2-x, 5, 3, 1, W, W, 1, 1)
        4
    """
    p = _validate_prime(p)
    N = ZZ(N)
    if N <= 0:
        raise ValueError("N must be positive")
    W = Winf * W0.inverse()
    Nmax = N + ZZ(positive_log(
        p, -p * (order_matrix_at_zero(W) + 1) * einf
    ).floor())
    while (Nmax
           - ZZ(positive_log(p, p * (Nmax - 1) * e0).floor())
           - ZZ(positive_log(
               p, -(order_matrix_at_infinity(W.inverse()) + 1) * einf
           ).floor()) < N):
        Nmax += 1
    return max(Nmax, ZZ(2))


def cohomological_frobenius(Q, p, N, Nmax, r, W0, Winf, G0, Ginf,
                            frobenius_ring_matrix, finite_matrices,
                            infinite_matrices, basis, integrals,
                            quotient_map):
    r"""Compute Frobenius on cohomology and associated exact primitives.

    TESTS:

    This is an indirect doctest through the full setup::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2-(x^3-10*x+9), 5, 2, genus=1)
        sage: data.frobenius_matrix.nrows()
        2
    """
    rows = []
    f0_list = []
    finf_list = []
    fend_list = []
    for differential in basis:
        pullback = frobenius_pullback(
            differential, Q, p, Nmax, r, frobenius_ring_matrix
        )
        pullback = modular_to_rational_laurent_vector(pullback, Q)
        coefficients, f0, finf, fend = reduce_with_functions(
            pullback, Q, p, N, Nmax, r, W0, Winf, G0, Ginf,
            finite_matrices, infinite_matrices, basis, integrals,
            quotient_map
        )
        rows.append(coefficients)
        f0_list.append(f0)
        finf_list.append(finf)
        fend_list.append(fend)
    return (matrix(QQ, rows), f0_list, finf_list, fend_list)


def _is_irreducible_model(Q):
    r"""Test irreducibility over ``QQ(x)`` without constructing an extension.

    TESTS::

        sage: from sage.schemes.curves.coleman.data import _is_irreducible_model
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: _is_irreducible_model(y^2-x)
        True
        sage: _is_irreducible_model((y-x)*(y+x))
        False
    """
    polynomial_ring, y_ring = _model_rings(Q, require_monic=True)
    function_field = polynomial_ring.fraction_field()
    model_ring = y_ring.change_ring(function_field)
    return model_ring(Q).is_irreducible()


def de_rham_cohomology_basis(Q, p, N, *, genus=None):
    r"""Return the de Rham basis data without computing Frobenius.

    The precision argument validates the intended p-adic setup even though
    the characteristic-zero cohomology calculation itself does not use it.

    The return value is ``(basis, genus, r, W0)``.

    EXAMPLES::

        sage: from sage.schemes.curves.coleman.data import de_rham_cohomology_basis
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: basis, genus, r, W0 = de_rham_cohomology_basis(
        ....:     y^2-(x^3-10*x+9), 5, 2, genus=1)
        sage: len(basis), genus, W0.nrows()
        (2, 1, 2)
        sage: de_rham_cohomology_basis(
        ....:     y^2-(x^3-10*x+9), 5, 2, genus=0)
        Traceback (most recent call last):
        ...
        ValueError: genus must equal the curve genus (1)
    """
    p = _validate_prime(p)
    N = ZZ(N)
    if N <= 0:
        raise ValueError("N must be positive")
    if not _is_irreducible_model(Q):
        raise ValueError("Q must be irreducible over QQ(x)")

    actual_genus = ZZ(curve_genus(Q, p))
    if genus is None:
        genus = actual_genus
    else:
        genus = ZZ(genus)
        if genus != actual_genus:
            raise ValueError(
                f"genus must equal the curve genus ({actual_genus})"
            )
    r, Delta, s = auxiliary_polynomials(Q)
    W0, Winf = integral_basis_matrices(Q)
    W0_inverse = W0.inverse()
    Winf_inverse = Winf.inverse()
    if (QQ(Delta.leading_coefficient()).valuation(p) > 0
            or r.degree() < 1
            or not is_smooth_mod_p(r, p)
            or not all(is_p_integral(A, p) for A in
                       (W0, W0_inverse, Winf, Winf_inverse))):
        raise ValueError("bad prime for this plane model")

    G = connection_matrix(Q, Delta, s)
    G0 = gauge_connection_matrix(G, W0)
    Ginf = gauge_connection_matrix(G, Winf)
    J0, _, T0_inverse = jordan_at_finite_places(r, G0)
    Jinf, _, Tinf_inverse = jordan_at_infinity(Ginf)
    basis, _, _ = basis_cohomology(
        Q, p, r, W0, Winf, G0, Ginf, J0, Jinf,
        T0_inverse, Tinf_inverse, genus=genus
    )
    if len(basis) != 2 * genus:
        raise ArithmeticError("the de Rham cohomology dimension is not 2*genus")
    return basis, genus, r, W0


def coleman_data(Q, p, N, *, use_open_curve=False, basis0=None, basis1=None,
                 basis2=None, genus=None):
    r"""Construct all data needed for Coleman integration on ``Q=0``.

    If ``genus`` is supplied, it is checked against the genus of the smooth
    projective normalization of the reduction modulo ``p``.

    The characteristic polynomial in this elliptic example agrees with its
    point count over `\GF{5}`::

        sage: from sage.schemes.curves.coleman.data import coleman_data
        sage: R.<x> = QQ[]; S.<y> = R[]
        sage: data = coleman_data(y^2 - (x^3 - 10*x + 9), 5, 2, genus=1)
        sage: data.frobenius_matrix.charpoly().change_ring(Integers(25))
        x^2 + 5
        sage: coleman_data(y^2 - (x^3 - 10*x + 9), 5, 2).genus
        1

    User-supplied differential partitions are checked as bases of the
    required subspaces::

        sage: custom = coleman_data(
        ....:     y^2 - (x^3 - 10*x + 9), 5, 2, genus=1,
        ....:     basis0=[vector(R, [0, 2])],
        ....:     basis1=[vector(R, [0, x + 1])])
        sage: len(custom.basis)
        2
        sage: coleman_data(
        ....:     y^2 - (x^3 - 10*x + 9), 5, 2, genus=1,
        ....:     basis0=[vector(R, [1, 0])])
        Traceback (most recent call last):
        ...
        ValueError: basis0 is not contained in the required space

    Small good primes are supported::

        sage: coleman_data(
        ....:     y^2 - (x^3 - 10*x + 9), 3, 2, genus=1).p
        3
    """
    p = _validate_prime(p)
    N = ZZ(N)
    if N <= 0:
        raise ValueError("N must be positive")
    if not _is_irreducible_model(Q):
        raise ValueError("Q must be irreducible over QQ(x)")

    degree = Q.degree()
    actual_genus = ZZ(curve_genus(Q, p))
    if genus is None:
        genus = actual_genus
    else:
        genus = ZZ(genus)
        if genus != actual_genus:
            raise ValueError(
                f"genus must equal the curve genus ({actual_genus})"
            )

    r, Delta, s = auxiliary_polynomials(Q)
    W0, Winf = integral_basis_matrices(Q)
    W0_inverse = W0.inverse()
    Winf_inverse = Winf.inverse()
    W = Winf * W0_inverse
    if (QQ(Delta.leading_coefficient()).valuation(p) > 0
            or r.degree() < 1
            or not is_smooth_mod_p(r, p)
            or not all(is_p_integral(A, p) for A in
                       (W0, W0_inverse, Winf, Winf_inverse))):
        raise ValueError("bad prime for this plane model")

    G = connection_matrix(Q, Delta, s)
    G0 = gauge_connection_matrix(G, W0)
    Ginf = gauge_connection_matrix(G, Winf)
    J0, T0, T0_inverse = jordan_at_finite_places(r, G0)
    Jinf, Tinf, Tinf_inverse = jordan_at_infinity(Ginf)
    e0, einf = ramification_bounds(J0, Jinf)
    delta = (
        ZZ(positive_log(
            p, -(order_matrix_at_zero(W) + 1) * einf
        ).floor())
        + ZZ(positive_log(
            p, (ZZ((2 * genus - 2) // degree) + 1) * einf
        ).floor())
    )

    basis, integrals, quotient_map = basis_cohomology(
        Q, p, r, W0, Winf, G0, Ginf, J0, Jinf,
        T0_inverse, Tinf_inverse, use_open_curve=use_open_curve,
        basis0=basis0, basis1=basis1, basis2=basis2, genus=genus
    )
    if len(basis) < 2 * genus:
        raise ArithmeticError("the de Rham cohomology dimension is below 2*genus")
    Nmax = maximum_precision(Q, p, N, genus, W0, Winf, e0, einf)
    frobenius_ring_matrix = frobenius_lift(
        Q, p, Nmax - 1, r, Delta, s, W0
    )
    finite_matrices, infinite_matrices = reduction_matrices(
        Q, p, Nmax, r, W0, Winf, e0, einf, J0, Jinf,
        T0, Tinf, T0_inverse, Tinf_inverse
    )
    F, f0_list, finf_list, fend_list = cohomological_frobenius(
        Q, p, N, Nmax, r, W0, Winf, G0, Ginf,
        frobenius_ring_matrix, finite_matrices, infinite_matrices,
        basis, integrals, quotient_map
    )
    return ColemanIntegrationData(
        Q=Q, p=p, N=N, genus=genus, W0=W0, Winf=Winf,
        r=r, Delta=Delta, s=s, G0=G0, Ginf=Ginf,
        e0=e0, einf=einf, delta=delta, basis=basis,
        quotient_map=quotient_map, integrals=integrals,
        frobenius_matrix=F, f0_list=f0_list, finf_list=finf_list,
        fend_list=fend_list, Nmax=Nmax,
        finite_reduction_matrices=finite_matrices,
        infinite_reduction_matrices=infinite_matrices,
        frobenius_ring_matrix=frobenius_ring_matrix
    )
