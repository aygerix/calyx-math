// Gröbner bases of sets and sequences of polynomials (handbook, Gröbner
// Bases: Construction of Gröbner Bases, Related Functions, Degree-d Gröbner
// Bases).

// H115E5.
P<a,b,c,d,e> := PolynomialRing(GF(2), 5);
B := [a*b + c*d + 1, a*c*e + d*e, a*b*e + c*e, b*c + c*d*e + 1];
GroebnerBasis(B);
L := [P.i^2 + P.i: i in [1 .. Rank(P)]];
BB := B cat L;
BB;
GroebnerBasis(BB);

// H115E7 and H115E6 on sequences over fields.
P<x, y, z> := PolynomialRing(RationalField(), 3);
GroebnerBasis([x^2 - 3*y, y^3 - x*y, z^3 - x, x^4 - y*z + 1]);
for p in [101, 103, 27173681, 3] do
    P<x, y, z> := PolynomialRing(GF(p), 3);
    GroebnerBasis([x^2 - 3*y, y^3 - x*y, z^3 - x, x^4 - y*z + 1]);
end for;
for p in [2, 3] do
    P<x, y, z> := PolynomialRing(GF(p), 3);
    GroebnerBasis([x^2 - 1, y^2 - 1, 2*x*y - z]);
end for;

// H115E11.
P<a,b,c,d> := PolynomialRing(RationalField(), [4,3,2,1]);
L := [a*b - c^2*d^3, b*c*d + c^3, c^2*d - d^5, a*d - b*c];
[IsHomogeneous(f): f in L];
[Degree(f): f in L];
G:=GroebnerBasis(L);
G;
#G;
[Degree(f): f in G];
for D := 1 to 10 do
    T := GroebnerBasis(L, D);
    printf "D = %o, #GB = %o, contains all degree-D polynomials: %o\n",
        D, #T, {f: f in G | Degree(f) le D} subset T;
end for;
GroebnerBasis(L, 5);
GroebnerBasis(L, 8);

// The same generators in an ungraded ring, where they are not homogeneous.
P<a,b,c,d> := PolynomialRing(RationalField(), 4, "grevlex");
L := [a*b - c^2*d^3, b*c*d + c^3, c^2*d - d^5, a*d - b*c];
[#GroebnerBasis(L, D): D in [0 .. 10]];
GroebnerBasis(L, 6);
GroebnerBasis(L);

// Bases in each monomial order, over Q and GF(32003).
orders := [* <"lex">, <"glex">, <"grevlex">, <"grevlexw", [3, 1, 2]>, <"elim", 1>, <"elim", [3], [1, 2]>, <"univ", 2>,
    <"weight", [1,1,1, 0,0,1, 0,1,0]> *];
for o in orders do
    for K in [RationalField(), GF(32003)] do
        P<x,y,z> := PolynomialRing(K, 3, o);
        GroebnerBasis([x^2*y - z^2 + 1, x*y*z - y, y^2 - x*z]);
    end for;
end for;
Q<a,b,c,d> := PolynomialRing(GF(32003), 4, "grevlex");
G := GroebnerBasis([a+b+c+d, a*b+b*c+c*d+d*a, a*b*c+b*c*d+c*d*a+d*a*b, a*b*c*d-1]);
#G, G[#G];
F<w> := GF(49);
T<s,t> := PolynomialRing(F, 2);
GroebnerBasis([w*s^2 + t, s*t - w]);
R<a,b> := PolynomialRing(Integers(7), 2);
GroebnerBasis([3*a^2 + b, 2*a*b - 1]);

// Sets, trivial ideals and parameters.
P<x,y,z> := PolynomialRing(RationalField(), 3);
S := [x*y - 1, y^2 - x, 2*x^2*z + y];
GroebnerBasis(S);
GroebnerBasis({x^2, x*y});
Type(GroebnerBasis({x^2, x*y}));
GroebnerBasis([P | ]);
GroebnerBasis([P!0]);
GroebnerBasis([P!3]);
GroebnerBasis([x^2 + y, x*y - 1] : Faugere := false, Al := "Direct");
GroebnerBasisUnreduced([x^2 - y, x*y - 1]);
GroebnerBasis([x^2*y - z, x*y^2 - x], 3);
GroebnerBasis([x^2 - y, x*y - 1], 0);

// Degree-d bases count a pair by the degree of its lcm, and keep what it
// adds whatever its degree; the generators enter as they are.
L<x,y> := PolynomialRing(GF(7), 2);
for d in [0 .. 8] do d, GroebnerBasis([x*y - y^4, x^2 - y], d); end for;
P<x,y> := PolynomialRing(RationalField(), 2, "grevlex");
for d in [3 .. 5] do d, GroebnerBasis([x^3 - y, x*y^2 - 1], d); end for;
P<x,y,z> := PolynomialRing(GF(32003), 3, "grevlex");
GroebnerBasis([-4*y^2*z + 3*y*z, -4*z + 1 - 5], 2);
P<x,y,z> := PolynomialRing(GF(32003), 3, "lex");
GroebnerBasis([2*x - 2*z, 5*y*z + 4*x - 1, -5*x*z, 2 + 1*z], 0);
GroebnerBasis([-3 - 3*x^2*y, -3*x*y*z + 2*z, 2*x], 0);
P<x,y,z> := PolynomialRing(RationalField(), 3, "elim", 1);
GroebnerBasis([-5*x*y^2 + 2 + 5*x^2*z + 1*z, -3*y^2 + 4*x^2*z, 2 - 3*z^2, 5*x + 1*x*y*z + 1*z^2 + 5*x*z], 0);
// The degree is weighted by a grading, else by the weights of a grevlexw
// order, else total.
P<x,y,z> := PolynomialRing(GF(32003), 3, "grevlexw", [2, 1, 3]);
Grading(P);
S := [5*x - 5*y*z + 5, -5*y*z^2 + 5*y^3, -1*x^2*y + 1*y*z];
for d in [2 .. 9] do d, GroebnerBasis(S, d); end for;
[#GroebnerBasis([x*y - z, y^3 - x], d): d in [1 .. 8]];
Q<x,y,z> := PolynomialRing(GF(32003), [2, 0, 3]);
[#GroebnerBasis([x*y - z, y^3 - x], d): d in [1 .. 8]];
R<x,y,z> := PolynomialRing(GF(32003), 3, "weight", [2,1,3, 1,0,0, 0,1,0]);
[#GroebnerBasis([x - y^2, y*z - x^2], d): d in [1 .. 6]];
E<x,y,z> := PolynomialRing(GF(32003), 3, "elim", 1);
[#GroebnerBasis([x - y^2, y*z - x^2], d): d in [1 .. 4]];
U<x,y,z> := PolynomialRing(GF(32003), 3, "univ", 1);
[#GroebnerBasis([x - y^2, y*z - x^2], d): d in [1 .. 4]];

// Normal forms: the division algorithm, which takes the divisors in the
// order given.
P<x,y,z> := PolynomialRing(RationalField(), 3);
NormalForm(x^2*y^2 + x*y, [x*y - 1, y^2 - x]);
f, C := NormalForm(x^2*y^2 + x*y + z, [x*y - 1, y^2 - x]); f; C;
f, C := NormalForm(x^3*y, [y^2 - x, x*y - 1]); f; C;
f, C := NormalForm(2*x^3*y + 3*y^3, [3*x*y - 1, 2*y^2 - x]); f; C;
f, C := NormalForm(x^2 + y, [x - 1, P!0, x]); f; C;
f, C := NormalForm(x*y*z - 1, [x*y - z, P!0, x*z - y]); f, C;
NormalForm(P!0, [x]);
NormalForm(x, [P|]);
NormalForm(x, [P | 1]);
NormalForm([x^2, x*y + y^3], [x*y - 1, y^2 - x]);
NormalForm([x^2, x*y + y^3], [y^2 - x, x*y - 1]);
F<s,t> := PolynomialRing(GF(7), 2);
f, C := NormalForm(s^3 + t, [2*s - t, t^2 - 1]); f; C;
F<w> := GF(49);
T<s,t> := PolynomialRing(F, 2);
NormalForm(s^3, [w*s^2 + t, s*t - w]);

// S-polynomials: over the rationals both leading coefficients are first
// divided by their gcd.
P<x,y,z> := PolynomialRing(RationalField(), 3);
SPolynomial(3*x^2*y - 1, 2*x*y^2 + x);
SPolynomial(x^2 - y, x^2 - z);
SPolynomial(4*x - 1, 6*y - 1);
SPolynomial(4*x^2 - 1, 6*x*y - 1);
SPolynomial(x*y, x*y + z);
SPolynomial(x, y);
SPolynomial(3*x - 3, 3*y - 6);
SPolynomial(2*x - 1, 2*y - 1);
SPolynomial(1/2*x - 1, 1/3*y - 1);
SPolynomial(3/2*x - 1, 5/3*y - 1);
SPolynomial(6*x - 1, 4*y - 1);
SPolynomial(-2*x - 1, 3*y - 1);
SPolynomial(x*y - 1, 2*x^2 - y);
Z<u,v> := PolynomialRing(Integers(), 2);
SPolynomial(4*u - 1, 6*v - 1);
SPolynomial(4*u^2 - 1, 6*u*v - 1);
SPolynomial(6*u - 1, 4*v - 1);
SPolynomial(-2*u - 1, 3*v - 1);
F<s,t> := PolynomialRing(GF(7), 2);
SPolynomial(3*s - 1, 5*t - 1);
SPolynomial(3*s - 1, 3*t - 1);
SPolynomial(2*s - 1, 3*t - 1);
F<w> := GF(49);
T<s,t> := PolynomialRing(F, 2);
SPolynomial(w*s^2 + t, w^3*s*t - w);
C<c,d> := PolynomialRing(ComplexField(), 2);
SPolynomial(2*c - d, 3*d^2 - 1);

// Reduction: each polynomial modulo the others until none changes, the
// least leading monomials reducing first whatever the order given.
P<x,y,z> := PolynomialRing(RationalField(), 3);
Reduce([x^2 - y, x^2*y - z, x*z]);
Reduce([2*x^2 - y, 4*x^2*y - z, 3*x*z]);
Reduce([x - y, y - z, x*y - z^2]);
Reduce([x*y - z, y - z, x - z]);
Reduce([y^2 - x, x*y - z^3, y - z]);
Reduce([P | ]); Reduce([P!0, x, 2*x]); Reduce({x, x + y});
Reduce([x*y - z^2, x - y, y^2 + z^3]);
Reduce([y^2 + z^3, x - y, x*y - z^2]);
Reduce([x*y - z, x*z - y, x*y*z - 1]);
Reduce([x*z - y, x*y - z, x*y*z - 1]);
Reduce([x*y*z - 1, x*y - z, x*z - y]);
Reduce([x*y*z + x, x*y - z, x*z - y]);
Reduce([x*y*z + x, x*z - y, x*y - z]);
Reduce([x*y^2 - 1, x*y - z, x*y^2*z - y]);
Reduce([x^2*y - z, x*y^2 - z, x^2*y^2 - 1]);
Reduce([x*y + z, x*y + z^2, x*z]);
Reduce([x*y + z, x*y + y, y*z - 1]);
Reduce([x^2 + y, x^2 + x] : Faugere := true);
ReduceGroebnerBasis([x^2 - y, x^2*y - z, x*z, 2*x^2 - 2*y]);
ReduceGroebnerBasis([2*x - 2, x - 1, x^2 - 1]);
ReduceGroebnerBasis([x*y*z - 1, x*y - z, x*z - y]);
ReduceGroebnerBasis([x*y - z, 2*x*y - z^2, x*z - y]);
// Of equal leading monomials, the least polynomial stays.
ReduceGroebnerBasis([x*y - z^2, 2*x*y - z]);
ReduceGroebnerBasis([2*x*y - z, x*y - z^2]);
ReduceGroebnerBasis([2*x*y - z, 3*x*y - z]);
ReduceGroebnerBasis([3*x*y - z, 2*x*y - z]);
ReduceGroebnerBasis([x*y - 2*z, x*y - 3*z]);
ReduceGroebnerBasis([x*y - 3*z, x*y + 2*z]);
ReduceGroebnerBasis([x*y + z, x*y]);

// Gröbner basis tests.
IsGroebner([x^2 - y, x*y - 1]);
IsGroebner(GroebnerBasis([x^2 - y, x*y - 1]));
IsGroebner([2*x - 1]);
IsGroebner([P|]); IsGroebner([P!0]); IsGroebner([x, P!0]);
IsGroebner({x^2 + y, x*y - 1});

// Errors.
Q<u,v> := PolynomialRing(RationalField(), 2);
P<x,y> := PolynomialRing(RationalField(), 2);
NormalForm(x, [u]);
SPolynomial(P!0, x);
SPolynomial(x, P!0);
f, C := NormalForm(x^2 + y, {x - 1});
R<a,b> := PolynomialRing(RealField(), 2);
GroebnerBasis([a^2 - b, a*b - 1]);
C<c,d> := PolynomialRing(ComplexField(), 2);
Reduce([c - d]);
NormalForm(c, [c - d]);
GroebnerBasis([]);
Reduce([]);
IsGroebner([]);
GroebnerBasis([x^2 - y, x*y - 1], -1);
GroebnerBasis([x^2 - y, x*y - 1], 2^100);
