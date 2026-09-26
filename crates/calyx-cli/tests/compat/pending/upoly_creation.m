// Univariate polynomial rings: creating rings and their elements
// (handbook, Univariate Polynomial Rings, Creation Functions).

// H24E1: global and non-global rings.
Q := RationalField();
P<x> := PolynomialRing(Q);
PP := PolynomialRing(Q);
P;
PP;
PP.1;
Pa<a> := PolynomialRing(Q: Global := false);
Pb<b> := PolynomialRing(Q: Global := false);
Pa;
Pb;
a;
b;
P;
x;
x eq a; // Automatic coercion
x + a;
PolynomialAlgebra(Q) eq P, Pa eq P, Pa eq Pb, Parent(x + a) eq P;
Parent(a + x) eq P, Parent(a + b) eq P, Parent(a * 2) eq Pa;

// Names of the indeterminate.
R := PolynomialRing(GF(7): Global := false);
R;
AssignNames(~R, ["t"]);
R; R.1; Name(R, 1); R.1^3 + 2;
R.2;
Name(R, 0);
AssignNames(~R, ["u", "v"]);

// Creating elements.
One(P), Identity(P), Zero(P), Representative(P);
P.1;
Parent(Identity(Pa)) eq Pa, Parent(Zero(Pa)) eq Pa;

// H24E2
P<x> := PolynomialRing(Integers());
f := x^3+3*x+1;
f;
P<x> := PolynomialAlgebra(Integers());
f := elt< P | 2, 3, 0, 1 >;
f;
P ! [ 2, 3, 0, 1 ];
Q := RationalField();
Q ! [1, 2];
P<x> := PolynomialRing(Q);
P ! [1,2];
P ! Q ! [1,2];
P ! [ [1,2], [2,3] ];

// The element constructor and coercion.
elt< P | 5 >;
elt< P | [1, 2, 3] >;
elt< P | 1/2, 0, -1 >;
P ! 3, P ! (1/2), P ! [], P ! [Q|];
P ! x, P ! (x^2 + 1);
Z := Integers();
S<y> := PolynomialRing(Z);
P ! (y^2 - 3*y);
S ! (x^2 + 1);
S ! (x/2);
S ! [1/2];
S ! GF(5)!2;
Z ! S!7;
Z ! y;
Q ! P!(1/2);
GF(5) ! S!7;
x eq y, y eq x, x + y, y - x^2;
3 in P, x in P, y in P, (1/2) in S, x in S, x in Z, (P!3) in Z;

// Polynomials over polynomial rings: an element of the coefficient ring
// is a constant.
G<w> := PolynomialRing(Q);
H<u> := PolynomialRing(G);
H ! w;
H ! (w^2 + 1);
u + w;
H ! [w, 1];
(u + w)^2;
Coefficients((u + w)^2);

// Polynomial
Polynomial([1, 2, 3]);
Parent($1) eq S;
Polynomial([1/2, 1]);
Polynomial([GF(5) | 1, 2]);
Parent(Polynomial([GF(5) | 1, 2])) eq PolynomialRing(GF(5));
Polynomial(GF(5), [1/2, 3]);
Polynomial(GF(5), x^2 + 1/3);
Polynomial(Z, [1, 2, 3]);
Polynomial(Q, y^3 - 1);
Polynomial([Z |]);
Polynomial([]);
Polynomial(Z, x/2);
Polynomial([x, 1]);
Polynomial(GF(9), [1, GF(9).1]);
