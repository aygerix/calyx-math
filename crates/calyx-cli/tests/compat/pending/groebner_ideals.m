// Gröbner bases of ideals (handbook, Gröbner Bases: Construction of
// Gröbner Bases, Related Functions).

// The basis of an ideal becomes its Gröbner basis once computed.
P<x,y,z> := PolynomialRing(GF(32003), 3);
I := ideal<P | x^2 + y*z - 1, y^2 - x*z + 2, z^3 - x - y>;
HasGroebnerBasis(I);
SmallBasis(I);
G := GroebnerBasis(I);
G;
I;
SmallBasis(I);
NormalForm(x^5*y, I);
NormalForm(G[1] + G[2]*x, I);

// Coordinates are the quotients of the division by the Gröbner basis.
C := Coordinates(I, x*(x^2 + y*z - 1));
C;
&+[C[i]*G[i] : i in [1..#G]] eq x*(x^2 + y*z - 1);
Coordinates(I, G[1]*x + G[2]*y);
Coordinates(I, x);

// In grevlex the easy basis is the Gröbner basis.
P2<x,y,z> := PolynomialRing(GF(32003), 3, "grevlex");
J := ideal<P2 | x^2 + y*z - 1, y^2 - x*z + 2, z^3 - x - y>;
Groebner(J);
J;
EasyBasis(J);
Universe(EasyBasis(J)) eq P2;
I2 := ideal<P2 | x*y - 1, x^2 - y>;
SmallBasis(I2);
GroebnerBasis(I2);
SmallBasis(I2);
Basis(I2);

// Polynomials of another ring.
Q<a,b,c> := PolynomialRing(GF(32003), 3);
NormalForm(a, J);
Coordinates(J, a);

// Trivial ideals.
GroebnerBasis(ideal<P2 | 1>);
GroebnerBasis(ideal<P2 | 0>);
GroebnerBasis(P2);
HasGroebnerBasis(ideal<PolynomialRing(Integers(), 2) | 1>);
HasGroebnerBasis(ideal<PolynomialRing(Integers(6), 2) | 1>);

// Over the rationals, and in lex through a change of order.
R<u,v> := PolynomialRing(RationalField(), 2);
K := ideal<R | u^2 + v^2 - 1, u - v^3>;
GroebnerBasis(K);
NormalForm(u^4, K);
Coordinates(K, (u - v^3)*u + (u^2 + v^2 - 1)*v);
K;
