// Structure operations on finite fields: related structures, numerical
// invariants, defining polynomials, predicates, and roots of polynomials.
F7 := GF(7);
P<x> := PolynomialRing(F7);
F49<w> := GF(7^2);
F<z> := ext< F49 | 2 >;
G<u> := ext< F7 | x^4 + x + 1 >;
K<k> := GF(2^100);

// Related structures
Category(F), Category(F7), Category(K), Parent(F), Parent(K);
Centre(F) eq F, Center(G) eq G, PrimeRing(F), PrimeField(G), PrimeRing(K), FieldOfFractions(F) eq F, FieldOfFractions(K);
A, m := AdditiveGroup(F49); A; m(A.1), m(A.2), m(A.1 + 3*A.2), (A.1 + A.2) @ m;
A, m := AdditiveGroup(F7); A; m(A.1), m(3*A.1);
A, m := AdditiveGroup(G); #A, m(A.2) eq u, m(A.4) eq u^3;
U, m := MultiplicativeGroup(F49); U; m(U.1), m(2*U.1), m(U!0), m(-U.1);
U, m := UnitGroup(F7); U; m(U.1), m(3*U.1);
U, m := UnitGroup(G); #U, IsPrimitive(m(U.1)), m(U.1) eq PrimitiveElement(G);
U, m := MultiplicativeGroup(K); #U eq 2^100 - 1, m(U.1) eq k;
A, m := AdditiveGroup(F49); Image(m), Inverse(m), w @@ m;
U, m := MultiplicativeGroup(F49); Image(m), w @@ m;
(F49!0) @@ m;
Set(GF(4)); #Set(F49), #Set(G), Set(GF(5)), Set(F49) eq { w^i : i in [1..48] } join { F49!0 };

// Numerical invariants
Characteristic(F), Characteristic(K), #F, #F7, #K, #G, Degree(F), Degree(F, F49), Degree(F, F7), Degree(F49), Degree(F7), Degree(K);
Degree(G), Degree(G, F7), Degree(GF(7^12), F), Degree(GF(7^12), F49), Degree(GF(2^100), GF(2^10)), Degree(F, F);
Type(#F), Type(Degree(F)), Type(Characteristic(F));

// Defining polynomials
DefiningPolynomial(F7), DefiningPolynomial(F49), DefiningPolynomial(F), DefiningPolynomial(G);
DefiningPolynomial(GF(2^10)), DefiningPolynomial(GF(1009)), DefiningPolynomial(GF(2^61 - 1)), DefiningPolynomial(F7, F7);
DefiningPolynomial(F, F49), DefiningPolynomial(F, F7), DefiningPolynomial(G, F7), DefiningPolynomial(F49, F49);
DefiningPolynomial(GF(7^12), F) eq MinimalPolynomial(Generator(GF(7^12), F), F);
Q<y> := PolynomialRing(F49);
R<r> := ext< F49 | y^3 + y^2 + w^3 >;
DefiningPolynomial(R), DefiningPolynomial(R, F49), DefiningPolynomial(R, F7) eq MinimalPolynomial(r, F7);

// Predicates and booleans
IsCommutative(F), IsUnitary(F), IsFinite(F), IsOrdered(F), IsField(F), IsEuclideanDomain(F);
IsPID(F), IsUFD(F), IsDivisionRing(F), IsEuclideanRing(F), IsPrincipalIdealRing(F), IsDomain(F);
IsCommutative(K), IsFinite(K), IsField(K), IsOrdered(K), IsFinite(F7), IsOrdered(F7);
F eq F, F eq F49, F ne F49, F7 eq GF(7), F eq GF(7^4), K eq GF(2, 100), K ne GF(2^100);
IsConway(F7), IsConway(F49), IsConway(F), IsConway(G), IsConway(K), IsConway(R);
IsDefault(F7), IsDefault(F49), IsDefault(F), IsDefault(G), IsDefault(K), IsDefault(R), IsDefault(GF(1000003, 2)), IsDefault(GF(1009));
IsConway(ext< F7 | ConwayPolynomial(7, 3) >), IsDefault(ext< F7 | ConwayPolynomial(7, 3) >);

// Roots
Roots(x^2 + 1), Roots(x^2 - 2), Roots((x - 1)^3*(x + 2)), Roots(P!0 + 3), Roots(x^7 - x);
Roots(y^2 - w), Roots(y^2 - w^2), Roots(y^49 - y) eq [<a, 1> : a in Sort([b : b in F49])], Roots((y - w^30)*(y - 5)*(y - w^9)^2);
Roots(PolynomialRing(K).1^2 + k), Roots(PolynomialRing(GF(1009)).1^2 - 2), Roots(PolynomialRing(GF(1009)).1^3 - 8);
r, S := RootsInSplittingField(x^2 + 1); S; r;
r, S := RootsInSplittingField((x^2 + 1)^2*(x - 3)); S; r;
r, S := RootsInSplittingField(x^3 + x + 1); S eq GF(7^3), #r, { MinimalPolynomial(t[1]) : t in r } eq { x^3 + x + 1 };
r, S := RootsInSplittingField(y^2 - w); Degree(S), Degree(S, F49), #r;
f, S := FactorizationOverSplittingField(x^2 + 1); S; f;
f, S := FactorisationOverSplittingField((x^3 + x + 1)*(x - 1)^2); Degree(S), #f, &*[t[1]^t[2] : t in f] eq PolynomialRing(S)!((x^3 + x + 1)*(x - 1)^2);
f, S := FactorizationOverSplittingField(P!3); f, S;
RootOfUnity(1, F7), RootOfUnity(2, F7), RootOfUnity(3, F7), RootOfUnity(6, F7), RootOfUnity(8, F7), RootOfUnity(8, F);
RootOfUnity(5, GF(2)), RootOfUnity(48, F49), RootOfUnity(19, F49), Parent(RootOfUnity(19, F49));
IsPrimitive(RootOfUnity(2^30 - 1, GF(2))), RootOfUnity(3, GF(2^100)) eq k^((2^100 - 1) div 3), RootOfUnity(25, K) eq k^((2^100 - 1) div 25);
Order(RootOfUnity(15, GF(2))), Order(RootOfUnity(9, GF(7)));

// H22E3, leaving out Factorization and Evaluate (from the polynomial
// chapter) and naming the generator of S separately.
K := GF(2);
P<x> := PolynomialRing(GF(2));
f := x^20 + x^11 + 1;
r, S := RootsInSplittingField(f); AssignNames(~S, ["w"]);
S;
DefiningPolynomial(S);
#r;
r[1];
{ MinimalPolynomial(t[1]) : t in r } eq { x^3 + x^2 + 1, x^8 + x^7 + x^3 + x^2 + 1, x^9 + x^7 + x^6 + x^4 + 1 };

// errors
P<x> := PolynomialRing(GF(7));
Degree(GF(7^4), GF(7^3));
Degree(GF(7^4), GF(5));
Degree(GF(7^2), GF(7^4));
DefiningPolynomial(GF(7^4), GF(7^3));
DefiningPolynomial(GF(7^2), GF(7^4));
Roots(P!0);
RootsInSplittingField(P!0);
RootsInSplittingField(P!3);
FactorizationOverSplittingField(P!0);
RootOfUnity(7, GF(7));
RootOfUnity(14, GF(7));
RootOfUnity(0, GF(7));
RootOfUnity(-3, GF(7));
RootOfUnity(2^30, GF(3));
RootOfUnity(2^100 - 1, GF(2^100));
// (Magma 2.22 reports these two without naming 'eq'.)
GF(7) eq Integers();
GF(7^2) eq Rationals();
