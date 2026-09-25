// Generic ring functions (Part III, Introduction to Rings) on every kind
// of ring: invariants, predicates, related structures, equality and
// membership.
rings := [* Integers(), Rationals(), RealField(), ComplexField(), Integers(6),
    Integers(7), GF(9), GF(7), PolynomialRing(Rationals()),
    PolynomialRing(Integers()), PolynomialRing(Integers(6)),
    PolynomialRing(GF(9)), PolynomialRing(RealField()),
    PolynomialRing(ComplexField()) *];
for R in rings do
    R;
    Parent(R), Category(R);
    Characteristic(R), #R, IsFinite(R);
    IsCommutative(R), IsUnitary(R), IsOrdered(R), IsField(R), IsDivisionRing(R);
    IsEuclideanDomain(R), IsEuclideanRing(R), IsMagmaEuclideanRing(R);
    IsPID(R), IsPIR(R), IsUFD(R), IsDomain(R), HasGCD(R);
    PrimeRing(R);
    Centre(R) eq R;
    Zero(R), One(R), Representative(R);
end for;

// Multivariate polynomial rings: some questions have no algorithm.
M<a, b> := PolynomialRing(GF(5), 2);
MQ := PolynomialRing(Rationals(), 2);
MR := PolynomialRing(RealField(), 3);
for R in [* M, MQ, MR *] do
    Characteristic(R), #R, IsFinite(R), IsOrdered(R), IsField(R);
    IsMagmaEuclideanRing(R), IsUFD(R), IsDomain(R), HasGCD(R), PrimeRing(R);
end for;
IsEuclideanDomain(M);
IsEuclideanRing(M);
IsPID(MQ);
IsPIR(MR);
PrimeField(Rationals());
PrimeField(RealField());
PrimeField(ComplexField());
PrimeField(GF(9));
PrimeField(Integers());
PrimeField(Integers(7));
PrimeField(M);

// Equality of rings.
Z := Integers(); Q := Rationals();
Z eq Q; Z ne Q; Z eq Z;
Integers(6) eq Integers(6); Integers(6) eq Integers(4);
GF(9) eq GF(3, 2); GF(9) eq GF(27);
RealField() eq RealField(20); ComplexField() eq ComplexField();
PolynomialRing(Q) eq PolynomialRing(Q);
PolynomialRing(Q) eq PolynomialRing(Z);
PolynomialRing(Q) ne PolynomialRing(Z);
M eq PolynomialRing(GF(5), 2);
M eq M;
Z eq Integers(6);
Integers() ne Integers(6);
Q eq RealField();
RealField() eq ComplexField();
GF(7) eq Integers(7);
PolynomialRing(Q) eq M;

// Membership.
P<x> := PolynomialRing(Q); PZ<y> := PolynomialRing(Z);
1/2 in Z; 2 in Q; 3 in Integers(6); Integers(6)!3 in Z;
x in P; 2 in P; P!2 in Q; x in Q; 1.5 in Q;
x in PZ;
y in P;
w := GF(9).1;
w in GF(9); w in GF(3); w in GF(27); w in GF(81); GF(3)!1 in GF(9);
w in GF(7);
Integers(6)!2 in Integers(4);
Integers(6)!2 in GF(7);
GF(7)!2 in Integers(7);

// Random needs a finite ring.
Random(GF(7)) in GF(7);
Parent(Random(Integers(6)));
Random(Z);
Random(Q);
Random(ComplexField());
Random(P);
Random(M);
