// Univariate polynomials: aggregates of polynomials and real or complex
// numbers have their universe in the polynomial ring over that field, which
// is made when needed, as for arithmetic (handbook, Univariate Polynomial
// Rings, Creation of Polynomial Rings; Sets, Sequences, universes).
P<x> := PolynomialRing(Integers());
s := [x] cat [1.5]; s; Universe(s);
t := [x, 1.5]; t; Universe(t);
[1.5, x];
Universe({x} join {1.5}), #({x} join {1.5});
Universe(Seqset([x]) join {1.5});
Universe([x] cat [ComplexField()!1]);
Universe([x, 1.5]) eq PolynomialRing(RealField());
Q<y> := PolynomialRing(Rationals());
Universe([y] cat [1.5]);
Universe([y] cat [RealField(10)!1]);
[x] eq [1.5], [P!2] eq [2.0], {x} eq {1.5};
CoveringStructure(P, RealField());
b, C := ExistsCoveringStructure(P, RealField(20)); b, C;
x + 1.5;

// No other rings are made.
[x] cat [1/2];
[1/2] cat [x];
F := PolynomialRing(GF(5)); z := F.1;
[z] cat [1.5];
P2<a, b> := PolynomialRing(Integers(), 2);
[a] cat [1.5];
a + 1.5;
