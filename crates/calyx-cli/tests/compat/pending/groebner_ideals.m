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

// The easy ideal is an ideal of the ring when the easy order is the ring's
// order; a ring is its own easy ideal.
E := EasyIdeal(J);
E;
EasyIdeal(P2);

// Changing the order: the basis is the easy basis once it is known, else
// the Gröbner basis once known, each polynomial made monic in the new
// order, and else the basis as given.
I := ideal<P2 | x^2 + y*z - 1, y^2 - x*z + 2, z^3 - x - y>;
L := ChangeOrder(I, "lex");
L;
IsZeroDimensional(I);
L, f := ChangeOrder(I, "lex");
L;
f;
f(x^2 + y);
GroebnerBasis(L);
L;
I;
ChangeOrder(I, "lex");
Q2<a,b,c> := PolynomialRing(GF(32003), 3, "glex");
M, g := ChangeOrder(I, Q2);
M;
g;
GroebnerBasis(M);
W := ChangeOrder(I, "weight", [1,2,3, 0,0,1, 0,1,0]);
W;
GroebnerBasis(W);
T := ChangeOrder(I, <"elim", 2>);
T;
GroebnerBasis(T);
F := IdealWithFixedBasis([x^2 + y*z - 1, y^2 - x*z + 2, z^3 - x - y]);
F2 := ChangeOrder(F, "lex");
F2;
U := ChangeOrder(P2, "lex");
U;
ChangeOrder(I, PolynomialRing(GF(32003), 2));
ChangeOrder(I, PolynomialRing(GF(7), 3));
ChangeOrder(I, PolynomialRing(RationalField(), 3));
ChangeOrder(I, "foo");
ChangeOrder(I, "elim", 5);
ChangeOrder(I, <"elim", 5>);
ChangeOrder(I, <3>);

// Marking a basis as the Gröbner basis: it is taken as it is.
P3<x,y,z> := PolynomialRing(GF(32003), 3);
K := ideal<P3 | x*y - z, x^2 - y>;
MarkGroebner(K);
K;
GroebnerBasis(K);
K2 := ChangeOrder(K, "grevlex");
K2;
MarkGroebner(P3);

// In lex the easy basis is in grevlex; changing the order takes it rather
// than the Gröbner basis.
H := ideal<P3 | x^2 - y*z, y^3 - z^3 + x*y*z>;
H2 := ChangeOrder(H, "grevlex");
H2;
IsZeroDimensional(H);
H2 := ChangeOrder(H, "grevlex");
H2;
GroebnerBasis(H);
H3 := ChangeOrder(H, "glex");
H3;
E := EasyIdeal(H);
E;
Generic(E);
C := ideal<P3 | x^2 - 1, y^3 + y, z - 2>;
C2 := ChangeOrder(C, "grevlex");
C2;
IsZeroDimensional(C);
C2 := ChangeOrder(C, "grevlex");
C2;
E := EasyIdeal(C);
E;
