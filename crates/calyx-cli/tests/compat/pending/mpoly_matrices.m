// Multivariate polynomials: the Jacobian matrix and the symmetric bilinear
// form (handbook, Multivariate Polynomial Rings, text/246).

// The Jacobian matrix: a row for each polynomial, a column for each
// variable, over the polynomial ring.
P<x, y, z> := PolynomialRing(Rationals(), 3);
J := JacobianMatrix([x^2*y, y*z + x, z^3]); J; Parent(J); Type(J);
J := JacobianMatrix([x*y]); J; Parent(J); Type(J);
J := JacobianMatrix([x, y, z, x*y*z]); J; Parent(J);
J := JacobianMatrix([P|]); J; Parent(J);
JacobianMatrix([P!1]);
JacobianMatrix([x^2/3 + y, 2*x*y - z/5]);
Z<a, b> := PolynomialRing(Integers(), 2);
J := JacobianMatrix([a^3*b - 7*b, 5*a + b^2]); J; Parent(J);
G<u, v> := PolynomialRing(GF(3), 2);
J := JacobianMatrix([u^3 + v, u*v^2]); J; Parent(J);
W<w> := PolynomialRing(Rationals(), 1);
J := JacobianMatrix([w^3, w]); J; Parent(J);
JacobianMatrix({x, y});
Q<t> := PolynomialRing(Rationals());
JacobianMatrix([t^2 + 1]);
JacobianMatrix([1, 2]);
JacobianMatrix([x, a]);

// The symmetric bilinear form, from the handbook example H25E7: n by n
// for a homogeneous polynomial in n variables, n + 1 by n + 1 otherwise,
// in the matrix space over the coefficient ring.
Q := RationalField();
PR<x, y, z> := PolynomialRing(Q, 3);
g := 119/44*x^2 - 93759/41440*x*y + 390935/91427*x*z
     + 212/243*x - 3/17*y^2 + 52808/172227*y*z
     - 287/227*y + 537/934*z^2 - 127/422*z;
B := SymmetricBilinearForm(g); B; Parent(B); Type(B);
B := SymmetricBilinearForm(x^2 + x*y + y^2); B; Parent(B);
B := SymmetricBilinearForm(x*y); B; Parent(B);
B := SymmetricBilinearForm(x^2 + 3); B; Parent(B);
SymmetricBilinearForm(x^2 + y);
SymmetricBilinearForm(x*z - 2*y^2 + 5*z);
SymmetricBilinearForm(x^2 + x);
SymmetricBilinearForm(x^3 - x^3 + y^2);
SymmetricBilinearForm(x^2 + x^2*y - x^2*y);
SymmetricBilinearForm(x^2 + 2*x*y + y^2 + 7);
B := SymmetricBilinearForm(x*y + z); B; Parent(B);
SymmetricBilinearForm(x^3);
SymmetricBilinearForm(x);
SymmetricBilinearForm(PR!0);
SymmetricBilinearForm(PR!5);
P4<x1, x2, x3, x4> := PolynomialRing(Rationals(), 4, "grevlex");
SymmetricBilinearForm(x1*x4 + x2^2 - x3);
W<w> := PolynomialRing(Rationals(), 1);
B := SymmetricBilinearForm(3*w^2 - w + 1); B; Parent(B);
G<u, v> := PolynomialRing(GF(5), 2);
B := SymmetricBilinearForm(u^2 + u*v + 3*v^2); B; Parent(B);
SymmetricBilinearForm(u*v + u + 1);
F<s, t> := PolynomialRing(GF(9), 2);
SymmetricBilinearForm(s*t + GF(9).1*t^2);
N9<c, d> := PolynomialRing(Integers(9), 2);
B := SymmetricBilinearForm(c^2 + c*d + 2*d); B; Parent(B);
R<p, q> := PolynomialRing(RealField(10), 2);
B := SymmetricBilinearForm(p^2 + 1.5*p*q); B; Parent(B);

// 2 must be a unit.
Z<a, b> := PolynomialRing(Integers(), 2);
SymmetricBilinearForm(a^2 + 4*a*b);
SymmetricBilinearForm(a*b);
SymmetricBilinearForm(a^3);
N4<m, n> := PolynomialRing(Integers(4), 2);
SymmetricBilinearForm(m*n);
H<h, k> := PolynomialRing(GF(2), 2);
SymmetricBilinearForm(h^2 + k^2);
SymmetricBilinearForm(h*k);
