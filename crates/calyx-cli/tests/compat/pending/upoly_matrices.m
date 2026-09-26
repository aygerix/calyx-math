// Univariate polynomials: the Berlekamp Q-matrix, the Sylvester matrix and
// the companion matrix (handbook, Univariate Polynomial Rings, text/237).

// The companion matrix of a monic polynomial of degree d is d by d.
P<x> := PolynomialRing(Integers());
C := CompanionMatrix(x^3 + 2*x^2 - 5*x + 7); C; Parent(C); Type(C);
CompanionMatrix(x^2 + 1);
C1 := CompanionMatrix(x + 3); C1; Parent(C1);
CompanionMatrix(x^4);
CompanionMatrix(x);
CompanionMatrix(2*x^2 + 1);
CompanionMatrix(-x^2 + 1);
CompanionMatrix(P!1);
CompanionMatrix(P!0);
Q<y> := PolynomialRing(Rationals());
C := CompanionMatrix(y^3 - y/2 + 1/3); C; Parent(C);
CompanionMatrix(3*y^2 + y + 1);
F<z> := PolynomialRing(GF(7));
C := CompanionMatrix(z^3 + 3*z + 1); C; Parent(C);
CompanionMatrix(2*z^2 + 1);
G<w> := PolynomialRing(GF(4));
CompanionMatrix(w^2 + w + GF(4).1);
Z8<t> := PolynomialRing(Integers(8));
C := CompanionMatrix(t^3 + 5*t + 2); C; Parent(C);
CompanionMatrix(3*t^3 + 5*t + 2);
R<r> := PolynomialRing(RealField(10));
C := CompanionMatrix(r^2 + 1.5*r - 2); C; Parent(C);
CC<c> := PolynomialRing(ComplexField(8));
CompanionMatrix(c^2 + c + ComplexField(8).1);
PP<a> := PolynomialRing(P);
C := CompanionMatrix(a^2 + x*a + 1); C; Parent(C);

// The Sylvester matrix: n rows from f of degree m, then m rows from g of
// degree n; 0 by 0 if f or g is zero.
S := SylvesterMatrix(x^3 + 2*x + 1, 3*x^2 - x + 4); S; Parent(S); Type(S);
SylvesterMatrix(x^2 + 1, x^2 + 1);
SylvesterMatrix(x^2 + 1, x);
SylvesterMatrix(x, x^2 + 1);
S := SylvesterMatrix(x^2 + 1, P!3); S; Parent(S);
SylvesterMatrix(P!3, x^2 + 1);
S := SylvesterMatrix(P!3, P!5); S; Parent(S);
SylvesterMatrix(P!0, x);
SylvesterMatrix(x, P!0);
SylvesterMatrix(P!0, P!0);
SylvesterMatrix(P!0, x^2 + 2);
SylvesterMatrix(x + 1, x - 1);
SylvesterMatrix(2*x^4 - x, x^3 + 5);
S := SylvesterMatrix(y^2/2 + 1, 2*y/3 - 1); S; Parent(S);
S := SylvesterMatrix(z^2 + 3, 2*z + 1); S; Parent(S);
S := SylvesterMatrix(4*t^2 + 1, 2*t + 3); S; Parent(S);
S := SylvesterMatrix(r^2 + 1.5, r - 2); S; Parent(S);
S := SylvesterMatrix(a^2 + x*a + 1, x*a - 1); S; Parent(S);
P2<u> := PolynomialRing(Integers());
SylvesterMatrix(x^2 + 1, u + 2);
SylvesterMatrix(x, y);
SylvesterMatrix(x, 2);

// The Q-matrix over a finite field of q elements: row i holds x^(q i) mod
// f, for any f of positive degree.
M := QMatrix(z^3 + 3*z + 1); M; Parent(M); Type(M);
QMatrix(z^4 + 1);
QMatrix(z^2);
QMatrix(z);
M := QMatrix(z + 1); M; Parent(M);
QMatrix(2*z^3 + 1);
QMatrix(z^8 + z + 2);
M := QMatrix(w^3 + GF(4).1*w + 1); M; Parent(M);
H<v> := PolynomialRing(GF(9));
QMatrix(v^3 + v + GF(9).1);
T<s> := PolynomialRing(GF(2));
QMatrix(s^7 + s + 1);
E<e> := PolynomialRing(GF(2, 3));
QMatrix(e^4 + e + 1);
D<d> := PolynomialRing(GF(3));
QMatrix((d^2 + 1)^2*(d + 1));
B<b> := PolynomialRing(GF(NextPrime(10^20)));
QMatrix(b^3 + b + 1);
Z7<h> := PolynomialRing(Integers(7));
M := QMatrix(h^3 + 3*h + 1); M; Parent(M);
QMatrix(F!1);
QMatrix(F!0);
QMatrix(P!1);
QMatrix(x^3 + 1);
QMatrix(y^3 + 1);
QMatrix(t^3 + 1);
