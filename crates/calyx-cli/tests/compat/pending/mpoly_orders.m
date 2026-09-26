// Monomial orders and graded polynomial rings (handbook, Polynomial Rings
// and Ideals: Creation of Polynomial Rings and Accessing their Monomial
// Orders, Creation of Graded Polynomial Rings, Element Operations Using the
// Grading).

// H115E1.
Z := IntegerRing();
// Construct polynomial ring with DEFAULT lex order
P<a,b,c,d> := PolynomialRing(Z, 4);
MonomialOrder(P);
MonomialOrderWeightVectors(P);
// Construct polynomial ring with grevlex order
P<a,b,c,d> := PolynomialRing(Z, 4, "grevlex");
MonomialOrder(P);
MonomialOrderWeightVectors(P);
// Construct polynomial ring with block elimination and a > d > b > c
P<a,b,c,d> := PolynomialRing(Z, 4, "elim", [1, 4], [2, 3]);
MonomialOrder(P);
MonomialOrderWeightVectors(P);
a + b + c + d;
a + d^10 + b + c^10;
a + d^10 + b + c;
// Construct polynomial ring with weight order and x > y > z
P<x, y, z> := PolynomialRing(Z, 3, "weight", [100,10,1, 1,10,100, 1,1,1]);
MonomialOrder(P);
MonomialOrderWeightVectors(P);
x + y + z;
(x+y^2+z^3)^4;

// Each order: the ring, the order, and the terms of a polynomial in it.
orders := [* <"lex">, <"glex">, <"grevlex">, <"grevlexw", [1, 2, 3, 4]>, <"elim", 2>, <"elim", [1, 4], [2, 3]>, <"elim", [3]>,
    <"invblock", [1, 2], [3, 4]>, <"univ", 2>, <"weight", [100,10,1,0, 1,10,100,0, 1,1,1,0, 0,0,0,1]> *];
for o in orders do
    P<a,b,c,d> := PolynomialRing(Z, 4, o);
    P;
    MonomialOrder(P);
    MonomialOrderWeightVectors(P);
    f := a + b^2 + c^3 + d^4 + a*b*c*d + 3*a^2*d - b*c;
    f;
    LeadingTerm(f), TrailingTerm(f), LeadingMonomial(f), LeadingCoefficient(f), TrailingCoefficient(f);
    Terms(f);
    Monomials(f);
    Coefficients(f);
    Reductum(f);
    LeadingTotalDegree(f);
    Sprint(f, "Magma");
end for;
for o in [* <"lex">, <"glex">, <"grevlex">, <"grevlexw", [3, 1, 2]>, <"elim", 1>, <"elim", [2], [3, 1]>, <"univ", 3>, <"weight", [1,2,3, 0,1,0, 0,0,1]> *] do
    Sprint(PolynomialRing(Z, 3, o), "Magma");
end for;

// The arguments of the orders.
Q := RationalField();
MonomialOrder(PolynomialRing(Q, 3, "grevlexw", [2, 4, 6]));
MonomialOrder(PolynomialRing(Q, 3, "grevlexw", [1/2, 1, 3/2]));
MonomialOrder(PolynomialRing(Q, 3, "elim", [2]));
MonomialOrder(PolynomialRing(Q, 3, "invblock", [2]));
MonomialOrder(PolynomialRing(Q, 3, "weight", [2,4,6, 0,1,0, 0,0,3]));
MonomialOrderWeightVectors(PolynomialRing(Q, 3, "weight", [2,4,6, 0,1,0, 0,0,3]));
P := PolynomialRing(Q, 3, "elim", [2], [3, 1]);
P;
MonomialOrder(P);
P := PolynomialRing(Q, 3, <"elim", 1>);
P;
T := MonomialOrder(P);
Type(T), #T, T[1], Type(T[2]);
MonomialOrderWeightVectors(P)[1];
Type(MonomialOrderWeightVectors(P)[1][1]);
PolynomialRing(Q, 3, "LEX");
PolynomialRing(Q, 3, "GRevLex");
PolynomialRing(Q, 3, <"Elim", [1], [3, 2]>);
PolynomialRing(Q, 3, <"univ", 3>);
PolynomialAlgebra(Q, 3, "univ", 1);

// Errors.
PolynomialRing(Q, 3, "lex", 3);
PolynomialRing(Q, 3, "elim", 5);
PolynomialRing(Q, 3, "elim", 0);
PolynomialRing(Q, 3, "elim");
PolynomialRing(Q, 3, "elim", [1, 2, 3]);
PolynomialRing(Q, 3, "elim", [1, 1]);
PolynomialRing(Q, 3, "elim", [1], [2]);
PolynomialRing(Q, 3, "elim", [1], [1, 2]);
PolynomialRing(Q, 3, "elim", [Integers() | ]);
PolynomialRing(Q, 3, "grevlexw", [1, 0, 1]);
PolynomialRing(Q, 3, "grevlexw", [1, 2]);
PolynomialRing(Q, 3, "grevlexw", ["a"]);
PolynomialRing(Q, 2, "grevlexw", [2^19, 1]);
PolynomialRing(Q, 2, "grevlexw", [2^20, 1]);
PolynomialRing(Q, 3, "univ", "a");
PolynomialRing(Q, 3, "univ", 4);
PolynomialRing(Q, 3, "weight", [1,0,0, 0,1,0]);
PolynomialRing(Q, 3, "weight", [1,0,0, 0,1,0, 1,1,0]);
PolynomialRing(Q, 3, "weight", [1,0,0, 0,1,0, 0,0,-1]);
PolynomialRing(Q, 3, "foo");
PolynomialRing(Q, 3, <"foo">);
PolynomialRing(Q, 3, <"elim", 5>);
PolynomialRing(Q, 3, <"elim">);
PolynomialRing(Q, 3, <1, 2>);
PolynomialRing(Q, 3, <"lex"> : Global);
PolynomialRing(Q, 3, "lex" : Global);

// Arithmetic, coercion and the functions of polynomials under the orders.
P<x, y, z> := PolynomialRing(Q, 3, "univ", 1);
f := (x + y + z + 1)^3;
f;
g := x^2*y - 2*x*z^3 + 5;
f*g - g*f, (f + g)^2 - f^2 - 2*f*g - g^2;
L<u, v, w> := PolynomialRing(Q, 3);
L ! f;
P ! (u^3 + v + w^2);
Gcd((2*x^3 + y)*(x*z + 3), (2*x^3 + y)*(y - 1));
Lcm(2*x^3 + y, x*y - 1);
Normalize(2*x^3 + 3*y);
Factorization(2*(x^2 + y)*(x - z)^2*(y^3 + z));
E<p, q, r> := PolynomialRing(Z, 3, "elim", [3], [1, 2]);
PrimitivePart(-4*p^2 + 6*r), Content(-4*p^2 + 6*r);
Sign(p^3 - r), Abs(p^3 - r);
Factorization(-(p - r)*(p + q^2)*(r^2 + 1));
C := ChangeRing(E, GF(5));
C;
C ! (p^5 - r);

// H115E2, without the ideal.
P<x, y, z> := PolynomialRing(RationalField(), [1, 2, 4]);
P;
VariableWeights(P);
Degree(x);
Degree(y);
Degree(z);
Degree(x^2*y*z^3); // Weighted total degree
TotalDegree(x^2*y*z^3); // Natural total degree
IsHomogeneous(x);
IsHomogeneous(x + y);
IsHomogeneous(x^2 + y);
MonomialsOfDegree(P, 4);
MonomialsOfWeightedDegree(P, 4);

// Graded rings.
Sprint(P, "Magma");
MonomialOrder(P);
Grading(P);
WeightedDegree(x^2*y*z^3), LeadingWeightedDegree(x^2*y + z^2);
Degree(P!0), WeightedDegree(P!0), LeadingWeightedDegree(P!0), Degree(P!3);
IsHomogeneous(P!0), IsHomogeneous(P!3);
x^4 + x^2*y + z + y^2 + x*z;
HomogeneousComponent(x^4 + x^2*y + z + x + 1, 4);
HomogeneousComponent(x^4 + x^2*y + z + x + 1, 3);
HomogeneousComponent(x^4 + x^2*y + z + x + 1, -1);
HomogeneousComponents(x^4 + x^2*y + z + x + 1);
HomogeneousComponents(P!0);
HomogeneousComponents(x^3 + 1);
MonomialsOfDegree(P, 0);
MonomialsOfDegree(P, 2);
MonomialsOfDegree(P, -1);
MonomialsOfWeightedDegree(P, 3);
MonomialsOfWeightedDegree(P, 0);
MonomialsOfWeightedDegree(P, 1);
MonomialsOfWeightedDegree(P, -1);
C := ChangeRing(P, GF(5));
C;
Grading(C), MonomialOrder(C);
PolynomialAlgebra(Q, [2, 3]);
for w in [[0, 2], [0, 0], [3, 0, 5], [2, 4], [6, 4, 2], [0, 3, 6]] do
    G := PolynomialRing(Q, w);
    MonomialOrder(G), Grading(G);
end for;
PolynomialRing(Q, [2^19, 1]);
PolynomialRing(Q, [2^20, 1]);
PolynomialRing(Q, [2^30, 1]);
PolynomialRing(Q, [-1, 2]);
PolynomialRing(Q, [Integers() | ]);
PolynomialRing(Q, [1/2, 1]);
PolynomialRing(Q, [1, 2] : Global := true);

// Zero weights.
G<s, t> := PolynomialRing(Q, [0, 1]);
G;
Sprint(G, "Magma");
s^2 + t + s*t + 1;
f := s^5 + t;
WeightedDegree(f), LeadingWeightedDegree(f), Degree(f), TotalDegree(f), LeadingTotalDegree(f);
Degree(s), Degree(t^2 + s), IsHomogeneous(s + 1);
HomogeneousComponents(f);
HomogeneousComponent(f, 0);
MonomialsOfWeightedDegree(G, 0);
MonomialsOfWeightedDegree(G, 1);
MonomialsOfWeightedDegree(G, 3);
G<s, t, u> := PolynomialRing(Q, [2, 0, 1]);
MonomialsOfWeightedDegree(G, 2);
MonomialsOfWeightedDegree(G, 0);
H := PolynomialRing(GF(7), [2, 3]);
MonomialsOfWeightedDegree(H, 12);
MonomialsOfWeightedDegree(H, 1);
HomogeneousComponents(H.1^3 + H.2^2 + H.1);

// The grading of ungraded rings.
R<a, b, c> := PolynomialRing(Q, 3);
Grading(R), VariableWeights(R);
TotalDegree(R!0), LeadingTotalDegree(R!0), WeightedDegree(R!0), Degree(R!0), Degree(a^2 + b*c^3);
HomogeneousComponents(a^2 + b*c^3 + 1);
IsHomogeneous(a^2 + b*c), IsHomogeneous(a^2 + b*c^3), IsHomogeneous(a + 1);
MonomialsOfWeightedDegree(R, 2);
MonomialsOfDegree(R, 3);
G := PolynomialRing(Q, 3, "grevlexw", [1, 2, 3]);
Grading(G), VariableWeights(G);
G;
Degree(G.3^2), WeightedDegree(G.3^2), IsHomogeneous(G.1^2 + G.2);
U<u, v, w> := PolynomialRing(Q, 3, "univ", 2);
MonomialsOfDegree(U, 2);
Type(MonomialsOfDegree(U, 2));
Universe(MonomialsOfDegree(U, 2)) eq U;
