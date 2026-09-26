// Unit and additive groups of residue class rings and of the integers,
// as abelian groups with their maps, and the natural homomorphisms of
// residue class rings.
R := Integers(735);
U, h := UnitGroup(R);
U; h;
U.1; U.1 + U.2; 3*U.3; -U.3; U!0; Zero(U); Id(U); Identity(U); U.1 - U.1; U.3 * 2; U.0; U.-1;
Eltseq(U.3), ElementToSequence(U.1), Order(U.3), #U, Order(U), Ngens(U);
Invariants(U), IsCyclic(U), Exponent(U), IsFinite(U), IsTrivial(U);
Order(U!0), IsIdentity(U!0), IsIdentity(U.1);
Type(Generators(U)), #Generators(U);
h(U.1 + U.2), h(U!0), h(5*U.3);
(R!2) @@ h;
(R!11) @@ h;
Eltseq((R!11) @@ h);
(R!2) @@ h eq U![1, 1, 26];
[h(U.i) : i in [1..Ngens(U)]];
Inverse(h); Inverse(h)(R!2);
Domain(h); Codomain(h); Parent(h);
print U: Magma;
Parent(U.1); Category(U); Type(U); Type(U.1); Category(U.1);
U ! [1, 2, 3]; U![5, 7, 100]; U![-1, 0, 0]; U!U.1; U ! 0;
U.1 in U; Random(U) in U; U eq U; U ne U; U.1 ne U.2;
U.1 + U.1; U.3 * -1; Order(U.1 + U.2);
x := U.1 + 2*U.2 + 5*U.3; x; Order(x);
x := U.3; x +:= U.3; x; x -:= U.1; x; x *:= 5; x;
U.2 + U.2 + U.2 + U.2;
[Order(u) : u in U | Order(u) eq 42][1..3];
#Set(U), Set(U) eq { u : u in U };
print U.1: Magma; Sprint(U.1 + 3*U.3); Sprintf("%o", U.2);

// errors
(R!5) @@ h;
(R!0) @@ h;
5 @@ h;
(Integers(7)!3) @@ h;
U.4;
U.(2^70);
U ! [1, 2];
U ! 1;
U ! true;
IsZero(U!0);
U.1 eq 0;
U.1 + 1;
U.1 - 1;
U.1 * U.2;
U.1 lt U.2;
U.1 div 2;
U.1 ^ 2;
U.1 * (Integers(5)!2);
3 in U;
h(3);
h(0);
h(U);
Image(h);
V, g := UnitGroup(R);
V eq U;
U.1 eq V.1;
U.1 + V.1;
U ! V.1;
V.1 in U;
g(U.1);

// other moduli
A, f := AdditiveGroup(Integers(12)); A; f; f(3*A.1); (Integers(12)!7) @@ f; 12*A.1; 13*A.1; -A.1;
A!5, A!17, A!(-1), A![5];
Order(5*A.1), Order(6*A.1), Order(A!0);
Order(A), #A, Exponent(A), Invariants(A), IsCyclic(A);
Generators(A);
_, f := AdditiveGroup(Integers(12)); f;
AdditiveGroup(Integers(1));
Z1 := AdditiveGroup(Integers(1)); Z1.1; Z1.1 eq Z1!0; Eltseq(Z1.1); Order(Z1.1);
print Z1: Magma;
UnitGroup(Integers(1));
T := UnitGroup(Integers(2)); T; #T; Invariants(T), Ngens(T), IsTrivial(T), IsCyclic(T), Exponent(T);
Order(T!0), Eltseq(T!0);
[t : t in T];
Generators(T);
T.1;
print T: Magma;
M, k := MultiplicativeGroup(Integers(15)); M; [k(x) : x in M]; [x : x in M];
UnitGroup(Integers(4));
U4 := UnitGroup(Integers(4)); U4.1; U4; U4!1;
U8 := UnitGroup(Integers(8)); U8!1;
U8![1];
Sprint(U8);
UnitGroup(Integers(16));
[Eltseq(u) : u in UnitGroup(Integers(16))];
UnitGroup(Integers(48));
UnitGroup(Integers(2^20));
G := UnitGroup(Integers(2*7^3)); G;
_, g := UnitGroup(Integers(2*7^3)); g(G.1);
_, g := UnitGroup(Integers(5)); g;
for m in [8, 9, 18, 30030, 2^5*3^3*29^2, 1093^2, 3511^2, 40487, 6692367337, 1000000007] do
    V, g := UnitGroup(Integers(m));
    m, [g(V.i) : i in [1..Ngens(V)]], [Order(V.i) : i in [1..Ngens(V)]];
    [Eltseq(x @@ g) : x in [Integers(m) | 3, 7, 10, 11, 13, m - 1, 2^31 + 11] | IsUnit(x)];
end for;
[U, U];
<U, [1, 2]>;
<[U.1, U.2], U>;
[* U, 1, U *];
Sprint([U.1, U.2]);

// the integers
A, f := AdditiveGroup(Integers()); A; f; f(A.1); f(-3*A.1); (Integers()!5) @@ f;
Invariants(A), IsFinite(A), IsCyclic(A), Ngens(A), Exponent(A), Order(A), #A, IsTrivial(A);
A!0; A!5; f(A!0); 1000000000000000000000*A.1; Eltseq(-7*A.1); IsIdentity(A!0);
print A: Magma;
[x : x in A];
Set(A);
f(5);
M, m := MultiplicativeGroup(Integers()); M; m; m(M.1); m(M!0); (Integers()!-1) @@ m; (Integers()!1) @@ m;
(Integers()!2) @@ m;
C, c := ClassGroup(Integers()); C; c; c(C!0);
ideal<Integers() | 6> @@ c;

// homomorphisms
h4 := hom< Integers(12) -> Integers(4) | >; h4; h4(Integers(12)!7); h4(5); Type(h4);
hom< Integers(12) -> Integers(5) | >;
hom< Integers(12) -> Integers() | >;
hom< Integers(12) -> Rationals() | >;
hom< Integers(12) -> GF(2) | >;
(Integers(4)!3) @@ h4;
h5 := hom< Integers(12) -> Integers(4) | >; h5 eq h4;
