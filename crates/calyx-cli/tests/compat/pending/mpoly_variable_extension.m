// New variables for ideals of multivariate polynomial rings (handbook,
// Polynomial Ring Ideal Operations: Variable Extension of Ideals and
// Homogenization of Ideals), with the maps back by elimination.

// VariableExtension: the ideal in the ring with the new variables before
// or after the others (named $.i), grevlex by default, and the map. A
// statement printing the call shows only the ideal.
P<x, y, z> := PolynomialRing(RationalField(), 3);
I := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
VariableExtension(I, 1, true);
J, f := VariableExtension(I, 2, true);
J;
f;
Generic(J);
f(x);
f(I);
f(x^2 + y);
f(3);
J.1;
Q := Generic(J);
Q.1, Q.2, Q.3;
f(I) eq J;
J2, f2 := VariableExtension(I, 1, false);
J2;
f2;
f2(z);
J3, f3 := VariableExtension(I, 2, false, "lex");
J3;
J4, f4 := VariableExtension(I, 1, true, "elim", 1);
J4;
V := VariableExtension(I, 2, false, "grevlexw", [1, 2, 3, 1, 1]);
V;

// Preimages: a polynomial free of the new variables, and the elimination
// ideal of an ideal, as the set form of EliminationIdeal gives it.
H := ideal<Generic(J) | Q.1*Q.3 - 1, Q.3^2 - Q.4>;
f(x) @@ f;
H @@ f;
(Q.1 + Q.3) @@ f;
ideal<Q | 1> @@ f;
ideal<Q | 0> @@ f;

// The ideal of I is its easy basis once known, and the new ring has no
// names when P has none. The map coerces into P.
Q := RationalField();
P<x, y, z> := PolynomialRing(Q, 3);
h := hom<P -> PolynomialRing(Q, 2) | [1, 2, 3]>;
h;
I := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
_ := x in I;
I;
J, f := VariableExtension(I, 1, true);
J;
Domain(f);
Codomain(f);
g := f;
g;
Generic(J) eq Codomain(f);
VariableExtension(I, 1, true), 2;
R := PolynomialRing(Q, 3);
K := ideal<R | R.1^2 - R.2, R.3>;
J2, f2 := VariableExtension(K, 2, true);
J2;
f2;
J3, f3 := VariableExtension(K, 1, false);
J3;
f(R.1);
f(ideal<R | R.1>);
S<a, b, c, d> := Generic(J);
M := ideal<S | a*b - 1, b^2 - c, c^2 - d, a*c - d^3, b*d - 1>;
M @@ f;
M2 := ideal<S | a^2 - b, a*c - d, b*c - d^2>;
M2 @@ f;
M3 := ideal<S | b^2 - c, c^2 - d>;
M3 @@ f;
M3;

// Errors.
VariableExtension(I, 0, true);
VariableExtension(I, 1, true, "foo");
VariableExtension(I, 1, true, "elim", 7);
(a + b) @@ f;

// Homogenization: the homogenization of the reduced Groebner basis in
// grevlex of I, with the new variable H before the others by default
// (the handbook says after) and grevlex by default; I keeps its easy
// basis.
P<x, y, z> := PolynomialRing(RationalField(), 3);
I := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
Homogenization(I);
J, f := Homogenization(I);
J;
f;
I;
f(x^2 - y + 1);
f(I) eq J;
J2, f2 := Homogenization(I, true);
J2;
J3, f3 := Homogenization(I, false, "lex");
J3;
J4, f4 := Homogenization(I, "lex");
J4;
H := Generic(J);
H;
(H.1^2 - H.2*H.4) @@ f;
ideal<H | H.1^2 - H.2*H.4, H.3*H.4 - H.1^2> @@ f;
K := ideal<P | x*y - z^2, x^3 - y*z>;
Homogenization(K);
L := ideal<P | x - 1>;
Homogenization(L);
Homogenization(ideal<P | 0>);
Homogenization(ideal<P | 1>);
Homogenization(ideal<P | x^3 + y, x^2*y - 1>);
Homogenization(I), 1;
1, Homogenization(I);

// The maps: the homogenization of a polynomial or of the Groebner basis in
// grevlex of an ideal; back, H set to 1, and for an ideal the Groebner
// basis for grevlex on H and then on the others with H set to 1.
Q := RationalField();
P<x, y, z> := PolynomialRing(Q, 3);
I := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
J, f := Homogenization(I, false, "lex");
f(I);
K := ideal<P | x*y - 1, y^2 - x>;
f(K);
K;
H := Generic(J);
ideal<H | H.4^2 - H.1*H.3, H.1*H.2 - H.3^2, H.2^3 - H.4^3> @@ f;
ideal<H | H.1*H.4 - H.2^2> @@ f;
(H.1*H.4 - H.2^2) @@ f;
f(x^3 - y);
f(P!0);
f(P!5);
J2, f2 := Homogenization(I);
f2(K);
H2 := Generic(J2);
ideal<H2 | 0> @@ f2;
ideal<H2 | 1> @@ f2;
(H2.1 + H2.2) @@ f2;
P2<a, b, c> := PolynomialRing(Q, 3, "grevlexw", [1, 2, 3]);
L := ideal<P2 | a^2 - b + 1, b*a - c + a>;
Homogenization(L);
L;
P3<u, v> := PolynomialRing(GF(5), 2, "grevlex");
Homogenization(ideal<P3 | u^3 - v, u*v - 1>, true, "glex");
R := PolynomialRing(Q, 3);
K := ideal<R | R.1^2 - R.2, R.3 - 1>;
J, f := Homogenization(K); J;
J, f := Homogenization(K, false); J;
f2(R.1);

// Errors.
Homogenization(I, true, "elim", 9);
Homogenization(I, "elim", 9);
Homogenization(I, true, "foo");
