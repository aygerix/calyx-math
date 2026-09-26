// The rational field as a structure (Rational Field chapter, "Structure
// Operations"): related structures, numerical invariants and predicates.
// 2.22 lacks MinimalField of a set, which the handbook documents, and
// rejects #Q, which is Infinity in 2.29.
Q := Rationals();
Category(Q); Parent(Q); Type(Q); PrimeField(Q); PrimeRing(Q); Centre(Q); IsPrimeField(Q);
IntegralBasis(Q); Parent(IntegralBasis(Q)[1]);
Basis(Q); Parent(Basis(Q)[1]); AbsoluteBasis(Q);
MinimalField(1/2); MinimalField(-7/3);
MinimalField({1/2, 3});
MinimalField({Q | });
MinimalField(3);
BaseField(Q); BaseField(Q) eq Q;
BaseField(Integers());

// unit and class groups
U := UnitGroup(Q); U;
U, m := UnitGroup(Q);
U; m;
m(U.1); m(U!0); m(2*U.1); m(-U.1); Parent(m(U.1));
Domain(m); Codomain(m);
UnitGroup(Q);
(-1/1) @@ m;
C := ClassGroup(Q); C;
C, mc := ClassGroup(Q);
C; mc; mc(C!0); Parent(mc(C!0)); Codomain(mc);
ClassGroup(Q);

// automorphisms
AutomorphismGroup(Q);
G, P, f := AutomorphismGroup(Q);
G; P; f;
Category(G); Category(P); Parent(P); Order(G);
ISA(PowMapAut, PowMap);
f(Id(G)); Parent(f(Id(G))); f(Id(G))(1/2); f(Id(G)) in P;
G2, P2, f2 := AutomorphismGroup(Q, Q);
G2; P2; f2;
G eq Sym(1);
f(G.1);

// primes
Decomposition(Q, 2); Decomposition(Q, 5); Decomposition(Q, 101);
d := Decomposition(Q, 7); Type(d); Type(d[1]); d[1, 1]; Parent(d[1, 1]); d[1, 2]; Parent(d[1, 2]);
Decomposition(Q, 4);
x := Decomposition(Q, 4);
Decomposition(Rationals(), 4); x := Decomposition(Rationals(), 4);
Decomposition(Q, 1);
Decomposition(Q, 0);
Decomposition(Q, -5);
Decomposition(Q, Infinity()); Decomposition(Q, -Infinity());
d := Decomposition(Q, Infinity()); Type(d); Parent(d[1, 1]); d[1, 2];
Decomposition(Q, 1/2);

// numerical invariants
Characteristic(Q), Conductor(Q), Degree(Q), AbsoluteDegree(Q), Discriminant(Q), AbsoluteDiscriminant(Q);
Parent(Conductor(Q)), Parent(Discriminant(Q));
DefiningPolynomial(Q); Parent(DefiningPolynomial(Q));
Signature(Q);
s, t := Signature(Q); s, t;
Conductor(Integers());

// predicates
IsCommutative(Q), IsUnitary(Q), IsFinite(Q), IsOrdered(Q), IsField(Q), IsEuclideanDomain(Q);
IsPID(Q), IsUFD(Q), IsDivisionRing(Q), IsEuclideanRing(Q), IsPrincipalIdealRing(Q), IsDomain(Q);
Q eq Q, Q eq Integers(), Q ne Q, Q ne Integers();
Integers() eq Q, Integers() ne Q;
Q eq GF(5);
Q eq RealField();
#Q;
