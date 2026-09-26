// Ideals of multivariate polynomial rings (handbook, Polynomial Rings and
// Ideals: Creation of Ideals and Accessing their Bases; the sums, products
// and powers of Polynomial Ring Ideal Operations).

P<x, y, z> := PolynomialRing(RationalField(), 3);
I := ideal<P | x^2 + y, x*y - z>;
I;
Type(I), Category(I);
Parent(I);
Basis(I);
Generators(I);
BasisElement(I, 2);
#Basis(I);
Generic(I) eq P;
Generic(I);
Universe(Basis(I)) eq P, Type(Basis(I));
J := ideal<P | [x^2 + y, x*y - z]>;
J;
K := ideal<P | I, z>;
K;
[I, J];
<I, 1>;
Sprint(I, "Magma");
Sprint(ideal<P | x>, "Magma");
Sprint(ideal<P | >, "Magma");

// The functions of the ring.
T := ideal<P | x^3 - y, z^2>;
BaseRing(T), CoefficientRing(T), Rank(T), Ngens(T);
T.1, T.2, Name(T, 3);
MonomialOrder(T), Grading(T), Characteristic(T);
MonomialsOfDegree(T, 1);
Monomial(T, [1, 2, 3]);
IsCommutative(T), IsUnitary(T);

// The constructor also returns the inclusion into the ring.
ideal<P | >;
ideal<P | 0>;
ideal<P | 1>;
ideal<P | 1/2>;
ideal<P | 1/2*x>;
ideal<P | Integers()!3>;
ideal<P | {x}>;
ideal<P | [I, J]>;
ideal<P | x, x, 0, y>;
ideal<P | 2, 3*x>;
ideal<P | [x, y], z, [ideal<P | x*y>]>;
ideal<P | P>;
Q<a, b> := PolynomialRing(RationalField(), 2);
ideal<P | a>;
ideal<P | "a">;
ideal<P | ideal<Q | a>>;


// Ideal and IdealWithFixedBasis.
Ideal([x, y]);
Ideal({x});
Ideal(x);
Ideal([P | ]);
Ideal({P | });
Ideal([]);
L := IdealWithFixedBasis([x, y^2]);
L;
Basis(L);
IdealWithFixedBasis([x + 1, y^2]);
IdealWithFixedBasis([]);
BasisElement(ideal<P | x, y, z, x*y>, 4);
BasisElement(ideal<P | x, y>, 3);
BasisElement(ideal<P | x, y>, 0);
BasisElement(ideal<P | >, 1);
IsZero(ideal<P | x>), IsZero(ideal<P | 0>), IsZero(ideal<P | >), IsZero(ideal<P | 0, 0>), IsZero(P);
Basis(P), BasisElement(P, 1);

// Sums: the bases joined (the ring absorbs everything).
I1 := ideal<P | x^2 + y, x*y - z>;
J1 := ideal<P | z^2, x - y, x^2 + y>;
I1 + J1;
ideal<P | > + ideal<P | x>;
ideal<P | x^2 + y, x*y - z> + ideal<P | x^2 + y>;
P + ideal<P | x>;
ideal<P | x> + P;
P + P;

// Products and powers: the products of the basis elements, normalized,
// once each and in increasing order.
I2 := ideal<P | x^2 + y, x*y - z>;
J2 := ideal<P | z^2, x - y, x^2 + y>;
I2 * J2;
B := func<I | Basis(I)>;
B(ideal<P | x, 2*x> * ideal<P | y>);
B(ideal<P | 2*x> * ideal<P | y>);
B(ideal<P | x, -x> * ideal<P | y>);
B(ideal<P | 2*x + 1> * ideal<P | 3*y>);
B(ideal<P | 2*x + 1, 4*x + 2> * ideal<P | 3*y>);
B(ideal<P | 2*x + y>^2);
B(ideal<P | -x, y>^2);
B(ideal<P | 1/3*x, y>^2);
B(ideal<P | 3, x>^2);
B(ideal<P | x + y, y + z, x + z>^2);
B(ideal<P | x, y>^2);
B(ideal<P | x, x, 0>^2);
B(ideal<P | x, x>^1);
B(ideal<P | 0> * ideal<P | x>);
B(ideal<P | x, y> * ideal<P | >);
B(ideal<P | > * ideal<P | >);
B(ideal<P | >^2);
B(ideal<P | x^2 + y, x*y - z>^2);
B(ideal<P | x^2 + y, x*y - z>^3);
B(ideal<P | x - 2*y>^5);
B(P * ideal<P | x>);
B(ideal<P | x> * P);
B(P^2);
B(P * P);
ideal<P | x^2 + y, x*y - z>^0;
ideal<P | x^2 + y, x*y - z>^1;
ideal<P | >^0;
P^0;
ideal<P | x>^-1;
ideal<P | x>^(2^30);
ideal<P | x>^(2^70);
ideal<P | x>^x;
ideal<P | x> + ideal<Q | a>;
ideal<P | x> * ideal<Q | a>;
ideal<P | x> + x;
x * ideal<P | x>;
ideal<P | x> * x;
Z<c, d> := PolynomialRing(IntegerRing(), 2);
B(ideal<Z | 2*c, c> * ideal<Z | d>);
B(ideal<Z | 2*c, -c> * ideal<Z | d>);
B(ideal<Z | -c> * ideal<Z | d>);
B(ideal<Z | 2*c, 4*c> * ideal<Z | d>);
F<s, t> := PolynomialRing(GF(7), 2);
B(ideal<F | 2*s, s> * ideal<F | t>);
B(ideal<F | 3*s + t, s + 5*t>^2);
G<u, v, w> := PolynomialRing(RationalField(), 3, "grevlex");
B(ideal<G | u + v^2, w^3, u*v>^2);
B(ideal<G | u + v^2, w^3, u*v> * ideal<G | u, v>);

// Other coefficient rings, orders and gradings.
H<u, v> := PolynomialRing(RationalField(), [1, 2]);
ideal<H | u^2 + v, u*v>;
Sprint(ideal<H | u^2 + v, u*v>, "Magma");
R<s, t> := PolynomialRing(GF(5), 2, "grevlex");
ideal<R | s^2 + t, 3*s*t - 1>;
Sprint(ideal<R | s^2 + t, 3*s*t - 1>, "Magma");
ideal<Z | 2*c, d^2 - 3>;
E := PolynomialRing(RationalField(), 2);
ideal<E | E.1^2, E.1*E.2 - 1>;
ChangeRing(ideal<P | x^2 + 1/2*y, 3*x*z>, GF(5));
ChangeRing(ideal<P | x^2 + 1/2*y, 3*x*z>, IntegerRing());
ChangeRing(ideal<Z | 2*c, d^2 - 3>, RationalField());

// Homogeneous ideals (H115E2).
P<x, y, z> := PolynomialRing(RationalField(), [1, 2, 4]);
I := ideal<P | x^2*y + z, (x^4 + z)^2, y^2 + z>;
IsHomogeneous(I);
IsHomogeneous(ideal<P | >), IsHomogeneous(ideal<P | 0, 1>), IsHomogeneous(P);

// Polynomials of another ring of the same rank coerce as by !, variable
// to variable, but ideals of it do not.
K := GF(32003);
P3<x, y, z> := PolynomialRing(K, 3);
Q3<a, b, c> := PolynomialRing(K, 3);
ideal<Q3 | x^2 - y, y*z - 1>;
I3 := ideal<P3 | x^2 - y, y*z - 1>;
ideal<Q3 | I3>;
ideal<Q3 | {x^2 - y}>;
ideal<Q3 | [1, 2]>;
ideal<Q3 | [[1, 2]]>;
ideal<Q3 | x^2 - y> eq ideal<Q3 | a^2 - b>;
x^2 - y in ideal<Q3 | a^2 - b>;
R4<r, s, t, u> := PolynomialRing(K, 4);
ideal<R4 | x^2 - y>;
R2<v, w> := PolynomialRing(K, 2);
ideal<P3 | v>;
Z<p, q, e> := PolynomialRing(Integers(), 3);
QQ<f, g, h> := PolynomialRing(RationalField(), 3);
ideal<QQ | p^2 - 2*q>;
ideal<Z | f^2 - 2*g>;
ideal<Z | f^2 - g/2>;
U<T> := PolynomialRing(K);
ideal<Q3 | T^2 + 1>;
Q1<m> := PolynomialRing(K, 1);
ideal<Q1 | T^2 + 1>;
ideal<Q3 | PolynomialRing(GF(7), 3).1>;
