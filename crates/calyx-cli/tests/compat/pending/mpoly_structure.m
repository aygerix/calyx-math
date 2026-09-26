// Multivariate polynomials: structure operations (handbook, Multivariate
// Polynomial Rings, Structure Operations).
Q := RationalField();
P<x, y, z> := PolynomialRing(Q, 3);
Z<r, s> := PolynomialRing(Integers(), 2);
F<g> := GF(9);
G<u, v> := PolynomialRing(F, 2, "grevlex");
H<h1, h2> := PolynomialRing(Integers(6), 2);
U<t> := PolynomialRing(Q);
K<k1, k2> := PolynomialRing(U, 2);
E := PolynomialRing(Q, 0);

// Related structures.
Category(P), Category(x);
Parent(P);
Parent(x);
PrimeRing(P), PrimeRing(Z), PrimeRing(G), PrimeRing(H);
PrimeRing(K);
BaseRing(P), BaseRing(Z), BaseRing(G), BaseRing(H);
CoefficientRing(K);
BaseRing(E);

// Numerical invariants.
Characteristic(P), Characteristic(G), Characteristic(H), Characteristic(K);
Rank(P), Rank(Z), Rank(K), Rank(E);
#P;
#E;
Ngens(P), Ngens(E);

// Predicates.
for R in [* P, Z, G, H, K, E *] do
    IsCommutative(R), IsUnitary(R), IsFinite(R), IsOrdered(R), IsField(R);
    IsUFD(R), IsDivisionRing(R), IsDomain(R);
end for;
IsEuclideanDomain(P);
IsEuclideanDomain(E);
IsPID(P);
IsPID(E);
IsEuclideanRing(P);
IsPrincipalIdealRing(P);
IsPrincipalIdealRing(E);
P eq P, P ne P;
P eq Z;
P eq PolynomialRing(Q, 3);
Z ne Z;
P eq U;

// Changing the coefficient ring.
ChangeRing(Z, Q);
C := ChangeRing(P, RealField(20));
C;
C.1;
C<a, b, c> := ChangeRing(P, GF(7));
C;
(a + 3*b)^7;
ChangeRing(G, GF(81));
ChangeRing(Z, GF(5));
ChangeRing(P, Integers());
ChangeRing(P, U);
C, h := ChangeRing(P, GF(5));
h;
h(x/3 + y);
h(x/5);
C, h := ChangeRing(Z, GF(5), hom< Integers() -> GF(5) | >);
h(3*r - s);
Rank(ChangeRing(E, GF(2)));

// Homomorphisms.
R<x, y> := PolynomialRing(Q, 2);
h := hom< R -> R | y, x >;
h;
h(x^2 + 3*y);
V<t> := PolynomialRing(Q);
k := hom< R -> V | t, t^2 >;
k(x^11*y^3 - x + 4/5*y - 13/4);
k(R!0), k(R!7);
g := hom< V -> R | x + y >;
g(t^2);
F := GF(5);
m := hom< R -> PolynomialRing(F) | 2, 3 >;
m(x/2 + y);
W<r, s> := PolynomialRing(Integers(), 2);
c := hom< Integers() -> F | >;
n := hom< W -> F | c, 1, 2 >;
n(r^2 + 7*s);
n(W!3);
n;
Codomain(n), Domain(n);
hom< R -> R | x >;
hom< R -> R | x, y, x >;
