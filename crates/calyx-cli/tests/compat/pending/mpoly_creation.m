// Multivariate polynomials: creation of rings and polynomials, print names
// (handbook, Multivariate Polynomial Rings, Polynomial Rings and
// Polynomials).
Z := IntegerRing();
S := PolynomialRing(Z, 2);
x := S.1;
y := S.2;
f := x^3*y +3*y^2;
f;
AssignNames(~S, ["x", "y"]);
x := S.1; y := S.2;
f := x^3*y +3*y^2;
f;
S<x, y> := PolynomialRing(Z, 2);
f := x^3*y +3*y^2;
f;

// Global and non-global rings.
Q := RationalField();
P<x,y,z> := PolynomialRing(Q, 3: Global);
PP := PolynomialRing(Q, 3: Global);
P;
PP;
PP.1;
P1<a,b,c> := PolynomialRing(Q, 3);
P2<d,e,f> := PolynomialRing(Q, 3);
P1;
P2;
a;
d;
P1 ! d;
P ! e;
P eq PP, P1 eq P2, P eq P1, P1 eq P1;

// Monomial orders.
PolynomialRing(Q, 3, "lex");
PolynomialRing(Q, 3, "glex");
PolynomialRing(Q, 3, "grevlex");
PolynomialAlgebra(Z, 2);
PolynomialAlgebra(Z, 2, "grevlex");
R<u, v, w> := PolynomialRing(Q, 3, "grevlex");
u^2*w + v^3 + u*v*w + w^2 + u + 1;
R<u, v, w> := PolynomialRing(Q, 3, "glex");
u^2*w + v^3 + u*v*w + w^2 + u + 1;
R<u, v, w> := PolynomialRing(Q, 3);
u^2*w + v^3 + u*v*w + w^2 + u + 1;
PolynomialRing(Q, 2, "foo");
PolynomialRing(Q, 0);
PolynomialRing(Q, -1);

// Print names.
T := PolynomialRing(GF(5), 4);
T;
T.3;
T.1 + 2*T.4;
AssignNames(~T, ["p", "q"]);
T;
T.1 + T.3;
Name(T, 2);
Name(T, 5);
T.0;
T.5;
AssignNames(~T, ["a", "b", "c", "d", "e"]);

// Creation of polynomials.
One(P), Identity(P), Zero(P), Representative(P);
elt< P | 3 >;
elt< P | 1/2 >;
P ! 5;
P ! (2/3);
P ! x;
P ! "x";
P ! [1, 2], elt< P | [3, 4] >;
G2<w> := GF(9);
PolynomialRing(G2, 2) ! [1, 2];
Z3<r, s, t> := PolynomialRing(Integers(), 3);
Z3 ! (x + y);
P ! (r + s);
Z3 ! (x/2);
U<X> := PolynomialRing(Q);
MultivariatePolynomial(P, X^2 + 2*X + 3, 2);
MultivariatePolynomial(P, X^2 + 2*X + 3, z);
MultivariatePolynomial(P, X^2 + 2*X + 3, 4);
MultivariatePolynomial(P, X^2 + 2*X + 3, x + y);
MultivariatePolynomial(Z3, X^2 + 2*X + 3, 1);
Parent(x), Parent(r);
Category(P), Category(x), Type(P), Type(x);

// Other coefficient rings.
F<g> := GF(4);
G<m, n> := PolynomialRing(F, 2);
(m + g*n)^2, (m + n)^4;
H<h1, h2> := PolynomialRing(Integers(6), 2);
(2*h1 + 3*h2)^2;
K<k1, k2> := PolynomialRing(U, 2);
(X*k1 + k2)^2;
K;
L<l1, l2> := PolynomialRing(P1, 2);
L;
(a*l1 - l2)^2;
Sprint(G, "Magma"), Sprint(P, "Magma");
Sprint(x^2*y - 3/2*z + 1, "Magma");
