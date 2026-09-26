// Affine algebras (handbook, Affine Algebras: Creation of Affine Algebras
// and Finite Dimensional Affine Algebras): inverses, division, dimensions,
// monomial bases, minimal polynomials. The handbook examples make their
// algebras with AffineAlgebra; here they are made with quo.

// H118E1
Q := RationalField();
P<x, y> := PolynomialRing(Q, 2);
A<x, y> := quo<P | x^2 - y^2 + 2, y^3 - 5>;
A;
x^2;
x^-1;
P<z> := PolynomialRing(Q);
MinimalPolynomial(x);
MinimalPolynomial(x^-1);
MinimalPolynomial(y);

// H118E3
Q := RationalField();
P<x, y> := PolynomialRing(Q, 2);
A<x, y> := quo<P | x^2 - 2, y^3 - 5>;
UP<z> := PolynomialRing(Q);
MinimalPolynomial(x + y);

Dimension(A), HasFiniteDimension(A);
MonomialBasis(A);
IsNilpotent(x), IsUnit(x), IsUnit(A!0);
Sprint(A, "Magma");
Sprint(x + y, "Magma");

P<x, y, z> := PolynomialRing(RationalField(), 3);
Q<a, b, c> := quo<P | x^2 - y, y^2 - z, x*z - 1>;
a^-1;
(a + b)^-1;
a/b;
IsUnit(a), IsUnit(a - 1);
(a - 1)^-1;
a / (a - 1);
a / 0;
#Q;
HasFiniteDimension(Q);
Dimension(Q);
MonomialBasis(Q);
MinimalPolynomial(a + b);
IsNilpotent(a);
Parent(MinimalPolynomial(a));

// Over a finite field.
R<r, s, t> := PolynomialRing(GF(3), 3);
B := quo<R | r^2, s^3, t^2 - t>;
#B, IsFinite(B), Dimension(B);
IsNilpotent(B.1), IsNilpotent(B.2), IsNilpotent(B.3), IsNilpotent(B.1 + B.2);
MinimalPolynomial(B.1 + B.2 + B.3);
MonomialBasis(B);
(B.1 + 1)^-1;
(B.1 + B.2)^5;
B!1 + 2;
IsField(B), IsDomain(B);
F<u, v> := PolynomialRing(GF(5), 2, "grevlex");
A := quo<F | u^3 - v, v^2 - 1>;
#A, IsFinite(A);
IsField(A), IsDomain(A);

// Division by elements that are not units.
B<r, s, t> := quo<R | r^2, s^3, t^2 - t>;
(r*s) / s;
(r*s) / r;
(s^2) / s;
(s^2 + r*s) / s;
t / t;
(r*t) / t;
(t - 1) / (t - 1);
0 / s;
s / s;
s / (s + r);
(s^2) / (s + r);
P<x, y> := PolynomialRing(RationalField(), 2);
A<x, y> := quo<P | x^2, y^2>;
(x*y) / x;
(x*y) / (x + y);
(x*y + x) / x;
x / (x*y);
(x + x*y) / (1 + y);
IsUnit(1 + y), IsUnit(x);

// Algebras of infinite dimension.
C := quo<P | x*y>;
HasFiniteDimension(C);
Dimension(C);
MonomialBasis(C);
MinimalPolynomial(C.1);
IsNilpotent(C.1);
C.1^2 / C.1;
C.1 / C.2;
(C.1 + C.2)^-1;
IsUnit(C!3);
(C!3)^-1;
IsField(C), IsDomain(C), IsFinite(C);
#C;

// The zero ring.
Z := quo<P | 1>;
Z!1 eq Z!0, IsZero(Z!1), IsUnit(Z!0);
(Z!0)^-1;
HasFiniteDimension(Z), Dimension(Z);
MonomialBasis(Z);
#quo<PolynomialRing(GF(2), 2) | 1>;
