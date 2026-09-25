// Ideals of the integers, quotient rings, residue class fields and
// transcendental extensions.
Z := Integers(); Q := Rationals();
I := ideal<Z | 6>; I;
J := ideal<Z | 4, 6>; J;
ideal<Z | 0>;
ideal<Z | >;
ideal<Z | -3>;
ideal<Z | [4, 6]>;
ideal<Z | 1>;
Z eq ideal<Z | 1>;
ideal<Z | 5> : Minimal;
ideal<Z | 5> : Magma;
[ideal<Z | 5>];
Type(I); Parent(I); Category(J);
PowerIdeal(Z);
Parent(I) eq PowerIdeal(Z);
I + J; I * J; I meet J;
ideal<Z | 0> + ideal<Z | 4>;
ideal<Z | 4> * Z;
ideal<Z | 4> meet ideal<Z | 0>;
I eq J; I ne J; I eq ideal<Z | -6>;
I subset J; J subset I; I notsubset J;
ideal<Z | 4> subset Z; Z subset ideal<Z | 4>;
12 in I; 7 in I; 7 notin I; 1/2 in I; 12/2 in I;
I!12;
I!3;
Generator(I); Generators(J); Basis(J); Norm(I); Minimum(I);
Generator(Z); Generators(Z);
IsPrime(I); IsPrime(ideal<Z | 7>); IsPrime(ideal<Z | -7>);
IsPrime(ideal<Z | 0>); IsPrime(Z);
IsPrincipal(I); IsPrincipal(Z);
IsZero(ideal<Z | 0>); IsZero(Z);
ideal<Z | 1/2>;
ideal<Z | 3, "a">;
ideal<Z | [1/2]>;
ideal<Q | 2>;
Z / I;

Q6 := quo<Z | 6>; Q6;
Q6 eq Integers(6);
quo<Z | 4, 6>;
quo<Z | I>;
quo<Z | 1>;
_, m3 := quo<Z | 6>; m3; m3(15);
quo<Z | 0>;
quo<Z | >;
quo<Q | 2>;

_, m := ResidueClassRing(6); m; m(20);
_, m2 := ResidueClassField(7); m2;
F, m4 := ResidueClassField(ideal<Z | 5>); F; m4; m4(7);
m4 : Minimal;

ext<Z | >;
ext<Q | >;
T<s> := ext<Q | >; T; s^2 + 1;
ext<Q, 2 | >;
Rank(PolynomialRing(Q, 3));
