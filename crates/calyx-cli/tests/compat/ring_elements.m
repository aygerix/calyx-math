// Generic functions on ring elements: predicates, comparison and order.
Z := Integers(); Q := Rationals(); RR := RealField(); CC<i> := ComplexField();
Z6 := Integers(6); Z7 := Integers(7); F9<w> := GF(9); F7 := GF(7);
P<x> := PolynomialRing(Q); PZ<y> := PolynomialRing(Z);
M<a, b> := PolynomialRing(GF(5), 2); P6<t> := PolynomialRing(Z6);
elts := [* 0, 1, -1, 2, 6, -2, 1/2, RR!0, RR!1, RR!-1, RR!1.5, i, CC!1, Z6!0,
    Z6!1, Z6!5, Z6!2, Z6!3, Z6!4, Z7!3, Z7!-1, w, F9!1, F9!0, F7!3, x,
    x^2 + 1, P!2, P!0, P!-1, 2*y, PZ!2, PZ!-1, a, a*b, M!1, M!0, 2*t, t^2 *];
for e in elts do
    e, Parent(e);
    IsZero(e), IsOne(e), IsMinusOne(e), IsUnit(e), IsIdempotent(e);
end for;
for e in [* 0, 1, 6, 1/2, RR!0, RR!1.5, i, Z6!0, Z6!2, Z6!3, Z6!4, Z6!5, Z7!3,
    Integers(8)!2, Integers(8)!4, Integers(8)!6, Integers(12)!6, w, F9!0 *] do
    IsNilpotent(e);
end for;
IsNilpotent(P!0);
IsNilpotent(M!0);
IsNilpotent(x);
IsNilpotent(a);
for e in [* 0, 2, 1/2, RR!0, i, Z6!0, Z6!1, Z6!2, Z6!3, Z6!4, Z7!3, w, x,
    P!0, 2*y, a *] do
    IsZeroDivisor(e);
end for;
IsZeroDivisor(2*t);
for e in [* 0, 1, -1, 2, -2, 6, 7, -9, 1/2, RR!2, i, w, F9!1, F9!0, F7!3 *] do
    IsIrreducible(e), IsPrime(e);
end for;
IsIrreducible(Z6!2);
IsPrime(Z7!3);
IsIrreducible(P!0);
IsPrime(M!0);

// Arithmetic forms.
+3; +(Z6!3); +x; -w;
u := x; u /:= 2; u;
v := Z7!3; v /:= 2; v;
u := Z6!5; u *:= 5; u;

// Order: numbers, residues by value, finite fields by representation,
// polynomials by degree then coefficients from the top.
2 lt 3; 1/2 gt 1/3; RR!1.5 ge 1; -1 le -1;
Z6!5 lt Z6!1; Z6!1 lt Z6!5;
[w^j lt w^k : j, k in [0..7]];
F9!0 lt w; w lt F9!0;
Sort([F7!k : k in [0..6]]);
Sort([w^k : k in [0..7]] cat [F9!0]);
x lt x^2; x^2 lt x; x + 1 lt x^2; 2*x lt x; x lt 2*x; -x lt x;
P!2 lt P!3; P!-1 lt P!0; x + 1 lt x + 2; x^2 + x lt x^2 + 1;
Sort([Z6!5, Z6!1, Z6!3]);
Sort([x^2, x, 1, x + 1, -x, P!0]);
Sort([y^2, -y, 2*y, 3, -3]);
a lt b; b lt a; a lt a^2; a*b lt a^2;
Sort([a, b, a^2, a*b, b^2, M!1]);
G := GF(2^30); u := G.1;
Sort([G!1, u, u + 1, u^2, G!0]);
G2 := GF(2^20); v := G2.1;
Sort([G2!1, v, v + 1, v^2]);
i lt 1;
CC!1 lt CC!2;
Maximum(2, 3); Minimum(1/2, 1/3); Max(RR!1.5, 2); Min(-1, 1/2);
Maximum([3, 1, 2]); Minimum([1/2, 1/3]);
Maximum(Z6!2, Z6!3);
Minimum(w, w^2);
