// Dirichlet characters over the rationals, the integers and finite fields:
// the handbook example H20E7 without the cyclotomic field and the elliptic
// curve, then the groups, how they and their characters print, and their
// elements.
G<a> := DirichletGroup(5);  G;  // The default base field is Q.
#G;
[Evaluate(a, n) : n in [1..5]];
Eltseq(a);
a eq G![2];
IsEven(a);
IsOdd(a);
IsTrivial(a);
G1<a4> := DirichletGroup(4);
Conductor(a4);
G2<a5> := DirichletGroup(25);
Conductor(a5);
eps := a4*a5;
Modulus(eps);
Conductor(eps);
Evaluate(eps,7) eq Evaluate(a4,7)*Evaluate(a5,7);
G<a> := DirichletGroup(7,GF(7));
#G;
Evaluate(a,2);
chi := KroneckerCharacter(209);
for n in [1..209] do
   assert Evaluate(chi,n) eq KroneckerSymbol(209,n);
end for;
// Groups.
G := DirichletGroup(5);
Type(G); Type(G.1); Parent(G.1);
print G: Minimal;
print G: Magma;
print G.1: Magma;
NumberOfGenerators(G), Ngens(G), Order(G), Exponent(G), Modulus(G), BaseRing(G);
UnitGenerators(G);
for N in [1, 2, 4, 8, 9, 16, 24, 40, 100, 105, 1078] do UnitGenerators(DirichletGroup(N)); end for;
Elements(DirichletGroup(24));
[Eltseq(x) : x in Elements(DirichletGroup(24))];
DirichletGroup(1); Elements(DirichletGroup(1)); Generators(DirichletGroup(1));
Order(DirichletGroup(1)); Exponent(DirichletGroup(1)); Eltseq(DirichletGroup(1).0);
DirichletGroup(8, IntegerRing());
H<b, c> := DirichletGroup(35, GF(13));
H; #H; Order(b), Order(c);
b; c; b*c; b^2*c^3; (b*c)^-1;
Eltseq(b), Eltseq(c), Eltseq(b*c);
Elements(H);
Generators(H);
H.0; H.1 eq b, H.2 eq c;
Exponent(H);
b, c;
b, 1;
AssignNames(~H, ["u", "v"]);
H.1; H.1*H.2^2; b;
G3 := DirichletGroup(9, GF(13));
Elements(G3);
[Eltseq(x) : x in Elements(G3)];
G4 := DirichletGroup(16, GF(17));
Elements(G4);
[Eltseq(x) : x in Elements(G4)];
DirichletGroup(9, GF(4)); Elements(DirichletGroup(9, GF(4)));
G5 := DirichletGroup(15, GF(4)); #G5; NumberOfGenerators(G5); Elements(G5);
H := DirichletGroup(13, GF(27)); H;
Order(H), Exponent(H), NumberOfGenerators(H);
Elements(H); Eltseq(H.1);
#Elements(DirichletGroup(100, GF(101)));
// Given roots of unity.
DirichletGroup(9, GF(7), GF(7)!2, 3);
Elements(DirichletGroup(9, GF(7), GF(7)!2, 3));
Elements(DirichletGroup(9, Integers(), -1, 2));
Elements(DirichletGroup(9, Integers(), 1, 1));
K := DirichletGroup(9, GF(7), GF(7)!2, 6);
Elements(K); Order(K.1);
DirichletGroup(9, GF(7), GF(7)!2, 0);
// Abstract groups.
G := DirichletGroup(5);
A, f := AbelianGroup(G);
A;
f(A.1); f(A.1) eq G.1;
G.1 @@ f;
AbelianGroup(G);
AbelianGroup(DirichletGroup(24));
AbelianGroup(DirichletGroup(35, GF(13)));
AbelianGroup(DirichletGroup(15, GF(4)));
AbelianGroup(DirichletGroup(1));
// Elements.
Random(G) in Elements(G);
Random(DirichletGroup(1));
G!1; G![4]; G![-2];
DirichletGroup(15)!DirichletGroup(5).1;
DirichletGroup(8)!KroneckerCharacter(-4);
Parent(DirichletGroup(8)!KroneckerCharacter(-4));
DirichletGroup(15, GF(7))!DirichletGroup(5).1;
DirichletGroup(5, GF(7))!DirichletGroup(5).1;
DirichletGroup(5, GF(49))!DirichletGroup(5, GF(7)).1;
DirichletGroup(12)!DirichletGroup(12, Integers()).1;
DirichletGroup(5) eq DirichletGroup(5);
DirichletGroup(5) eq DirichletGroup(5, Integers());
DirichletGroup(5) eq DirichletGroup(7);
