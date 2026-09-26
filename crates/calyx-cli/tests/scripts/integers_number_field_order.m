// A copy of compat/pending/integers_number_field_order.m, so that calyx's output, checked against
// Magma 2.22, is kept until #24 records the output of 2.29.
// Z as a number field order (Ring of Integers chapter), and the unit group
// of Z. Valuations and the Chinese remainder theorem at non-prime or zero
// ideals fail inside Magma's package code, so they are not tested.
Z := Integers();

// the unit group
U, m := UnitGroup(Z); U; m; m(U.1); m(U!0); m(U.1 + U.1); U.1 @ m; (-1) @@ m; 1 @@ m;
Domain(m); Codomain(m);
UnitGroup(Z);
x := UnitGroup(Z); Type(x); #x;
2 @@ m;
(1/1) @@ m;
m(3);

// decomposition of primes
Decomposition(Z, 5); Decomposition(Z, -5);
D := Decomposition(Z, 7); Type(D); Universe(D); D[1]; Type(D[1][1]); D[1][1] eq ideal< Z | 7 >;
Decomposition(Z, 2^31 - 1);
Decomposition(Z, 6);
Decomposition(Z, 0);
Decomposition(Z, 1);
Decomposition(Z, -1);
Decomposition(Z, 5/1);

// generators, ramification and inertia
I := ideal< Z | 6 >; J := ideal< Z | -35 >; P := ideal< Z | 7 >;
Generator(I); Generator(J); Generator(P); Generator(ideal< Z | 0 >); Generator(Z);
RamificationIndex(P); RamificationIndex(ideal< Z | -7 >); RamificationIndex(P, 7); RamificationIndex(ideal< Z | -7 >, 7);
RamificationIndex(I);
RamificationIndex(ideal< Z | 0 >);
RamificationIndex(Z);
RamificationIndex(I, 7);
RamificationIndex(P, -7);
RamificationIndex(P, 14);
RamificationIndex(P, 49);
RamificationIndex(P, 0);
RamificationIndex(ideal< Z | 14 >, 7);
RamificationIndex(ideal< Z | 49 >, 7);
RamificationIndex(ideal< Z | 0 >, 7);
RamificationIndex(Z, 5);
RamificationIndex(P, 7/1);
Degree(P); Degree(ideal< Z | -7 >); Degree(ideal< Z | 2^31 - 1 >); Degree(Z); Degree(ideal< Z | 1 >);
Degree(I);
Degree(ideal< Z | 0 >);
TwoElementNormal(P); TwoElementNormal(I); TwoElementNormal(J); TwoElementNormal(ideal< Z | 0 >); TwoElementNormal(Z);
a, b := TwoElementNormal(ideal< Z | 10 >); a; b;
TwoElementNormal(Rationals());

// the Chinese remainder theorem: -1 when there is no solution
ChineseRemainderTheorem(I, J, 1, 2); ChineseRemainderTheorem(ideal< Z | 4 >, ideal< Z | 6 >, 1, 3);
ChineseRemainderTheorem(ideal< Z | 4 >, ideal< Z | 6 >, 1, 2);
ChineseRemainderTheorem(ideal< Z | 4 >, ideal< Z | 6 >, -1, 3);
ChineseRemainderTheorem(ideal< Z | 5 >, ideal< Z | 7 >, -100, 1000);
ChineseRemainderTheorem(ideal< Z | 1 >, ideal< Z | 7 >, 3, 5); ChineseRemainderTheorem(Z, Z, 3, 5);
ChineseRemainderTheorem(ideal< Z | -5 >, ideal< Z | -7 >, 1, 1); ChineseRemainderTheorem(ideal< Z | 5 >, ideal< Z | 7 >, 0, 0);
ChineseRemainderTheorem(ideal< Z | 10^20 >, ideal< Z | 3^40 >, 10^19, -1);
ChineseRemainderTheorem(ideal< Z | 5 >, ideal< Z | 3 >, 2/1, 1);

// valuations at prime ideals return the cofactor too
Valuation(56, P); Valuation(56, ideal< Z | 2 >); Valuation(56, ideal< Z | -2 >); Valuation(-49, P); Valuation(0, P);
v := Valuation(56, ideal< Z | 2 >); v;
v, c := Valuation(0, P); v; c; Type(c);
v, c := Valuation(-98, P); v; c; Type(c);
Valuation(3^100 * 10, ideal< Z | 3 >);
Valuation(0, 7); v, c := Valuation(0, 7); v; c;

// class representatives
r, f := ClassRepresentative(I); r; f; Type(r); Type(f); f(-3); f(1/1); 3 @@ f; Domain(f); Codomain(f);
ClassRepresentative(ideal< Z | 0 >); ClassRepresentative(Z);
g := ClassRepresentative(P); g;
f(ideal< Z | 6 >);
