// Operations on ideals of multivariate polynomial rings (handbook,
// Polynomial Rings and Ideals: First Operations on Ideals and Dimension of
// Ideals), and what the Groebner basis computations leave in an ideal: the
// line on homogeneity and dimension, and the Groebner basis in the ring's
// order, which replaces the basis.

// H116E1 but ColonIdeal (the intersection is compared rather than printed:
// its basis depends on the algorithm).
P<x,y,z> := PolynomialRing(RationalField(), 3);
I := ideal<P | x*y - 1, x^3*z^2 - y^2, x*z^3 - x - 1>;
J := ideal<P | x*y - 1, x^2*z - y, x*z^3 - x - 1>;
A := I * J;
A;
M := I meet J;
A eq M;
QuotientDimension(A);
I;

// H116E2 (the element operations but NormalForm).
P<x, y, z> := PolynomialRing(RationalField(), 3);
I := ideal<P | (x + y)^3, (y - z)^2, y^2*z + z>;
x + y in I;
IsInRadical(x + y, I);
IsInRadical((x + y)^2, I);
IsInRadical(z, I);
SPolynomial(x^4 + y - z, x^2 + y - z);

// Membership.
P<x, y, z> := PolynomialRing(RationalField(), 3);
I := ideal<P | x^2 + y, x*y - z>;
x in I;
I;
1/2 in I, 0 in I, x^2 + y in I, x^3 - z in I, (x*y - z)^2 * x in I, x notin I, Integers()!3 in I;
Q<a, b> := PolynomialRing(RationalField(), 2);
a in I;
GF(5)!1 in I;
"a" in I;
[x] in I;
I in I;

// What an operation leaves behind.
G := func<| ideal<P | x^2 + y, x*y - z>>;
I := G(); _ := I eq I; I;
I := G(); _ := x in I; I;
I := G(); _ := I subset P; I;
I := G(); _ := IsZero(I); I;
I := G(); _ := IsProper(I); I;
I := G(); _ := Basis(I); I;
I := G(); _ := I * I; I;
I := G(); _ := I + I; I;
I := G(); _ := Dimension(I); I;
I := G(); _ := IsHomogeneous(I); I;
I := G(); _ := IsZeroDimensional(I); I;
I := G(); _ := IsPrincipal(I); I;
I := G(); _ := QuotientDimension(I); I;
I := G(); _ := LeadingMonomialIdeal(I); I;
I := G(); _ := I subset ideal<P | x>; I;
I := G(); _ := ideal<P | x> subset I; I;
I := G(); _ := I subset I; I;
I := G(); _ := IsInRadical(x, I); I;
I := G(); _ := I meet ideal<P | x - y>; I;
I := G(); _ := IsProper(I); _ := Dimension(I); _ := x in I; I;

// The line on the ideal, and the basis replaced by the reduced Groebner
// basis when the leading monomials of the basis are pairwise coprime.
show := procedure(I)
    lines := Split(Sprint(I), "\n");
    k := Index(lines, "Basis:") + Index(lines, "Groebner basis:");
    printf "%o | %o | %o\n", lines[k - 1], lines[k], Basis(I);
end procedure;
for B in [[x^2 + y, x*y - z], [x^2, y^2, z^2], [x^2 - y*z, x*y], [x - 1, y - 2, z], [x, y], [x^2 + 1, y, z^3 - z], [P | ], [P | 0], [P | 1],
          [x, 1 + x], [x*y, x*z], [x - y, y - z], [2*x, y], [x - y, 0, y - z], [y - z, x - y], [3*x^2 + y, 2*y^2 + z], [x + y^2, y - z^3],
          [x, y, 0, 0], [P | 0, 0], [x, x], [x, 2*x], [x^2, y^2, z^2, x*y], [x + y + z]] do
    I := Ideal(B);
    _ := x in I;
    show(I);
end for;
I := ideal<P | x^2 + y, x*y - z>; _ := x in I; I;
I := ideal<P | x - y, y - z>; _ := IsProper(I); Basis(I);
I := ideal<P | x - y, y - z>; _ := IsHomogeneous(I); Basis(I);
I := ideal<P | x + y^2, y - z^3>; IsHomogeneous(I); I;
L := IdealWithFixedBasis([x^2 + y, x*y - z]); _ := x in L; L; Basis(L);

// Rings with a weighted grevlex order take the Groebner basis at once.
G<u, v> := PolynomialRing(RationalField(), [1, 2]);
I := ideal<G | u^2 + v, u*v>; _ := u in I; I;
I := ideal<G | u^2 + v, u + 1>; _ := u in I; I;
I := ideal<G | u^2 + v, 3*u*v - 1>; _ := u in I; I;
I := ideal<G | v^2 + u^2, u*v>; _ := u in I; I;
H<u, v> := PolynomialRing(RationalField(), 2, "grevlexw", [1, 2]);
I := ideal<H | u^2 + v, u*v>; _ := u in I; I;
F<s, t> := PolynomialRing(GF(5), 2, "grevlex");
I := ideal<F | s^2 + t, 3*s*t - 1>; _ := s in I; I;
I := ideal<F | s^2 + t^2, s*t>; _ := s in I; I;
F<s, t> := PolynomialRing(GF(5), [1, 2]);
I := ideal<F | s^2 + t, 3*s*t - 1>; _ := s in I; I;

// Sums take the easy Groebner bases of the ideals, once computed;
// products and powers the given bases.
I := ideal<P | x^2 + y, x*y - z>; _ := x in I; J := ideal<P | z>;
Basis(I + J);
Basis(J + I);
Basis(I * J);
Basis(I^2);
Basis(I + I);
K := ideal<P | x^3 - y, y^2 - z, x*z - 1>; _ := x in K; K; Basis(K + ideal<P | x>);
L := ideal<P | x*y - 1, x^2 + y^2 - 4>; _ := x in L; L; Basis(L + ideal<P | x>);

// Equality: by the easy Groebner bases when both are in grevlex, else by
// those in the ring's order, which then become the bases.
eqs := procedure(A, B)
    printf "%o %o\n", A eq B, A ne B;
    show(A);
    show(B);
end procedure;
eqs(ideal<P | x^2 + y, x*y - z>, ideal<P | x^2 + y, x*y - z>);
eqs(ideal<P | x^2 + y, x*y - z>, ideal<P | x>);
eqs(ideal<P | x^2 + y>, ideal<P | x^2 + y, x*y - z>);
eqs(ideal<P | x^2, x*y>, ideal<P | x*y, y*z, x*z>);
eqs(ideal<P | x^2 + y, x*y>, ideal<P | x^2 + y, x*z>);
eqs(ideal<P | x^2 - y, x*y - 1>, ideal<P | x^2 + y, x*y - z>);
eqs(ideal<P | x^2, x*y>, ideal<P | x^2, x*y, x^3>);
eqs(ideal<P | x^2, x*y>, ideal<P | x^2, x*y, x*z>);
eqs(ideal<P | x*y - 1, x^2 + y^2 - 4>, ideal<P | x*y - 1, x^2 + y^2 - 4, x^3>);
eqs(ideal<P | x*y - 1, x^2 + y^2 - 4>, ideal<P | x*y - 1, x^2 + y^2 - 4>);
eqs(ideal<P | x*y - 1, x^2 + y^2 - 4>, ideal<P | x*y - 1, x^2 + y^2 - 4, x^2*y - x>);
eqs(ideal<P | x^2 + y, x*y>, ideal<P | x^2 + y, x*y, y^2>);
eqs(ideal<P | x, y>, ideal<P | x, y, x + y>);
eqs(ideal<P | x^2 + y, x*y - 1, z>, ideal<P | x^2 + y, x*y - z>);
eqs(ideal<P | x^2, x*y>, ideal<P | x*y, x^2>);
eqs(ideal<P | x - 1, x*y>, ideal<P | x - 1, y>);
eqs(ideal<P | >, ideal<P | 0>);
eqs(ideal<P | x^2, x*y>, ideal<P | >);
A := ideal<P | x^2, x*y>; A eq P, P eq A, A ne P; show(A);
A := ideal<P | x, x + 1>; A eq P; show(A);
A := ideal<P | x^2 + y, x*y - z>; P eq A; show(A);
G<u, v> := PolynomialRing(RationalField(), 2, "grevlex");
eqs(ideal<G | u^2 + v^2, u*v>, ideal<G | u^2 + v^2, u*v, v^3>);

// Inclusion.
I := ideal<P | x^2 + y, x*y - z>;
P subset I, I subset P, P subset P, I subset I;
I notsubset ideal<P | x, y>, ideal<P | x^2 + y> subset I, ideal<P | x^2 + y> notsubset I;
ideal<P | x*z + y^2> subset I, ideal<P | x*z + y^2, x> subset I, ideal<P | > subset I, I subset ideal<P | >;

// Intersections.
I := ideal<P | x^2, x*y>; J := ideal<P | y^2>; M := I meet J; show(I); show(J); M;
I := ideal<P | x^2, x*y>; J := ideal<P | y^2, x*z>; I meet J;
I := ideal<P | x^2, x*y>; I meet P; P meet I; P meet P;
I meet ideal<P | >;
&meet [ideal<P | x>, ideal<P | y>, ideal<P | z>];
&meet [ideal<P | x>];
ideal<P | x - 1> meet ideal<P | x - 2>;
ideal<P | x - 1, y> meet ideal<P | x - 2, y>;
I := ideal<P | x^2 + y, x*y - z>; J := ideal<P | x - y>;
M := I meet J; M subset I, M subset J, I * J subset M;
M eq ideal<P | x^3 - x*y + x*z - y^2 + y*z, x^2*y - x*y + y^2, x^2*z - x*y + y*z>;

// Predicates and dimensions.
IsProper(ideal<P | x^2 + y, x*y - z>), IsProper(ideal<P | x, x + 1>), IsProper(ideal<P | >), IsProper(P);
IsZeroDimensional(P), IsZeroDimensional(ideal<P | x - 1, y, z>), IsZeroDimensional(ideal<P | x>);
I := ideal<P | x^2 - 1, x*y, z>; IsZeroDimensional(I); I;
Dimension(ideal<P | x^2 + y, x*y - z>);
for B in [[x*y, x*z], [x - 1, y, z], [P | ], [x*y], [y*z], [x*z], [x*y*z], [x^2*y], [y^2, x*z], [x*y, z^2], [x*z, y*z], [x*y, y*z], [x*y - z, x^2 - y]] do
    d, U := Dimension(Ideal(B)); d, U;
end for;
Dimension(P), Dimension(ideal<P | 1>);
I := ideal<P | x, x + 1>; Dimension(I); I;
I := ideal<P | x - 1, y^2, z>; _ := Dimension(I); show(I);
H<s, t, w> := PolynomialRing(RationalField(), [1, 2, 3]);
I := ideal<H | s^2 + t, s*t - w>; d, U := Dimension(I); d, U; I;
IsPrincipal(ideal<P | x^2 - 1, x - 1>);
IsPrincipal(ideal<P | x, y>);
IsPrincipal(ideal<P | >);
IsPrincipal(ideal<P | 0>);
IsPrincipal(P);
QuotientDimension(ideal<P | x^2, y, z^3>), QuotientDimension(ideal<P | x>), QuotientDimension(P);
QuotientDimension(ideal<P | x^2 + y^2 - 1, x - y, z^2 - x*y>);
LeadingMonomialIdeal(ideal<P | x^2 + y, x*y - z>);
HasGrevlexOrder(ideal<P | x>), HasGrevlexOrder(ideal<G | u>), HasGrevlexOrder(ideal<PolynomialRing(RationalField(), [1, 2]) | 1>);
IsHomogeneous(ideal<P | x^2 + y, x*y - z>), IsHomogeneous(ideal<P | x, x + 1>), IsHomogeneous(ideal<P | x - y^2, x^2 - x*y^2 + x - y^2>);
JacobianIdeal(x^3 + y^2*z + z);
JacobianIdeal(x*y*z);

// Other coefficient fields.
F<s, t> := PolynomialRing(GF(7), 2);
I := ideal<F | s^2 + t, s*t - 1>;
t^3 + 1 in I, s + t in I, s^7 in I;
Dimension(I), QuotientDimension(I);
I eq ideal<F | s + t^2, t^3 + 1>;
I;
K<r> := GF(9);
R<s, t> := PolynomialRing(K, 2, "grevlex");
I := ideal<R | s^2 - r, t^3 - r*s>;
s^2 in I, r*s^4 in I, s in I;
QuotientDimension(I);
I meet ideal<R | s>;
