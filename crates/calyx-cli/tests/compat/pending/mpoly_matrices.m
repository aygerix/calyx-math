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

// The diagonal form and the matrix T with T B T^t diagonal, B the
// symmetric bilinear form: the handbook example H25E7 (a bare call prints
// the form alone), then zero pivots and radicals. Over Q the rows of T are
// integral; over other fields they come from Gram-Schmidt.
Q := RationalField();
PR<x, y, z> := PolynomialRing(Q, 3);
g := 119/44*x^2 - 93759/41440*x*y + 390935/91427*x*z
     + 212/243*x - 3/17*y^2 + 52808/172227*y*z
     - 287/227*y + 537/934*z^2 - 127/422*z;
DiagonalForm(g);
D, T := DiagonalForm(g); T; Parent(T); Type(T);
show := procedure(f)
    D, T := DiagonalForm(f);
    print f, "|", D;
    print T;
end procedure;
for f in [x^2 + x*y + y^2, x*y, -x*y, 3*x*y, x*y + y^2, x*y - y^2, x*y + 2*y^2, x*y + y^2/2, x*y + z^2, x*z, y*z,
          x*y + x*z, x*y + y*z, x*y + x*z + y*z, x*z + y*z, x*z + y^2 + 2*x*y, x*y + 3*x*z, x^2 + y*z, x^2 + x*y + y*z,
          x*z - 2*y^2 + 5*z, 4*x^2 + 4*x*y + y^2 + z, x*y + 1, x*y + x, 3*x*y + 5*y*z - 7*z^2, 2*x*z + y^2 - z^2,
          x^2 + 3, x^2 - y^2, x*y/3 + z^2/5, x*y + y^2 + y*z + z^2] do
    show(f);
end for;
P4<a, b, c, d> := PolynomialRing(Rationals(), 4);
for f in [c*d, a*d + b*c, a*b + b*c + c*d, a^2 + 2*a*b + b^2 + c*d, a*b + a*d + b*c + c*d, b*d + c^2, a*b + c*d] do
    show(f);
end for;
W1<t> := PolynomialRing(Rationals(), 1);
show(3*t^2 - t + 1);
G5<u, v, w> := PolynomialRing(GF(5), 3);
for f in [u*v, u*v + v^2, u*v + 2*v^2, u*v + 4*v^2, u*w + v^2, v*w, u*v + u*w + v*w, 3*u*v + w, u^2 + u*v, u^2 + u*v + 3*v^2] do
    show(f);
end for;
for K in [* GF(7), GF(9), Integers(7), GF(NextPrime(10^20)), RealField(10) *] do
    PK<p, q, r> := PolynomialRing(K, 3);
    for f in [p*q, p*q + q^2, q*r, p*q + 1] do
        show(f);
    end for;
end for;
CK<p, q, r> := PolynomialRing(ComplexField(8), 3);
show(p*q);

// A field of characteristic other than 2, and degree 2.
Z2<m, n> := PolynomialRing(Integers(), 2);
DiagonalForm(m*n);
DiagonalForm(m^3);
N9<m, n> := PolynomialRing(Integers(9), 2);
DiagonalForm(m*n);
H2<m, n> := PolynomialRing(GF(2), 2);
DiagonalForm(m*n);
DiagonalForm(m^2 + n^2);
DiagonalForm(x^3);
DiagonalForm(PR!0);
DiagonalForm(x);
