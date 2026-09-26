// Univariate polynomial rings: related structures, changing rings,
// invariants and predicates (handbook, Univariate Polynomial Rings,
// Structure Operations).
Z := Integers();
Q := RationalField();
P<x> := PolynomialRing(Z);
Category(P); Parent(P); PrimeRing(P); BaseRing(P); CoefficientRing(P);
CoefficientRing(x); BaseRing(x^2);
Type(P), Type(x), ExtendedType(P), ExtendedType(x);
F<t> := PolynomialRing(GF(9));
PrimeRing(F); BaseRing(F); Category(t);
PrimeRing(PolynomialRing(F));

// H24E3 writes S<y>, h := ChangeRing(P, Q); the names are assigned
// separately here.
S, h := ChangeRing(P, Q);
AssignNames(~S, ["y"]); y := S.1;
h(x^3-2*x+5);
S ! (x^3-2*x+5);
m := hom< Z -> Q | x :-> 3*x >;
S, h := ChangeRing(P, Q, m);
h(x^3-2*x+5);
h;
S eq PolynomialRing(Q);
h(3), h(0);
h(y);
T, g := ChangeRing(S, Z);
g(y^2 - 1);
g(y/2);
T, g := ChangeRing(P, GF(5));
T; g(3*x^7 - 5*x + 11);
T, g := ChangeRing(F, GF(3));
T, g := ChangeRing(PolynomialRing(GF(3)), F);
g(PolynomialRing(GF(3)).1 + 2);
ChangeRing(P, Integers(6));
ChangeRing(P, P);
ChangeRing(P, RealField(10));

// Invariants and predicates.
Characteristic(P), Characteristic(F), Characteristic(PolynomialRing(Integers(6)));
Rank(P), Rank(F), Ngens(P);
for R in [* P, S, F, PolynomialRing(GF(7)), PolynomialRing(Integers(6)), PolynomialRing(P) *] do
    IsCommutative(R), IsUnitary(R), IsFinite(R), IsOrdered(R), IsField(R);
    IsEuclideanDomain(R), IsPID(R), IsUFD(R), IsDivisionRing(R);
    IsEuclideanRing(R), IsDomain(R), IsPrincipalIdealRing(R);
end for;

// Equality of rings: rings over the same coefficient ring are equal.
Pa<a> := PolynomialRing(Z: Global := false);
P eq Pa, P ne Pa, Pa eq PolynomialRing(Z);
P eq S;
P ne S;
P eq Z;
P eq PolynomialRing(Z, 1);
a + x, x + a, a - 2*x, x * a;
x in Pa, a in P, 3 in P, (P!3) in Z, x in Z;
y in P;
(1/2) in P;
