// Linear and algebraic dependencies: IntegerRelation, MinimalPolynomial,
// and the deprecated LinearRelation and PowerRelation. The handbook gives
// IntegerRelation(q) two values; Magma 2.22 returns only the first, so the
// statements here that print both follow the handbook.

S := RealField(20); C<i> := ComplexField(20);
r2 := Sqrt(S!2); r3 := Sqrt(S!3);

// IntegerRelation: the bound H defaults to Ceiling(10^(p/d)).
IntegerRelation([r2, S!1]);
x, y := IntegerRelation([r2, S!1]); x, y, Type(x), Universe(x), Parent(y);
for N in [1, 2, 3, 4, 9, 10, 22, 24, 54, 55, 130, 135, 300, 350, 700, 800, 1000, 10^6, 10^30, 2^70] do
  x, y := IntegerRelation([r2, S!1], N); print N, x, y;
end for;
IntegerRelation([S!1, S!2]);
IntegerRelation([S!2, S!1]);
IntegerRelation([S!1, r2, r3, r2 + r3]);
IntegerRelation([Pi(S), S!1, r2]);
IntegerRelation([r2^2, S!1]);
IntegerRelation([r2, r3, r2*r3, S!1]);
IntegerRelation([Log(S!2), Log(S!3), Log(S!6)]);
IntegerRelation([Log(S!2), Log(S!3), Log(S!12)]);
r := r2 + r3;
for d in [1..6] do IntegerRelation([r^k : k in [0..d]]); end for;
for N in [1, 5, 10, 100, 10^6] do IntegerRelation([r^k : k in [0..4]], N); end for;
IntegerRelation([S!1]);
IntegerRelation([S!5]);
IntegerRelation([S!-5], 3);
IntegerRelation([S!0, S!1, S!0], 10);
IntegerRelation([S!0, S!1, S!0]);
IntegerRelation([S!1, S!1], 10);
IntegerRelation([S!1, S!-1], 10);
IntegerRelation([S!3, S!6, S!9], 10);
IntegerRelation([RealField(5) | 1.5, 2.5]);
IntegerRelation([RealField(50) | Sqrt(RealField(50)!2), 1]);
IntegerRelation([Pi(RealField(100)), Pi(RealField(100))^2, 1]);
// The second value sums the terms as &+ does, each half first.
for r in [Pi(S)*3/7, Log(S!5), Sqrt(Pi(S))] do
  for H in [10, 1000, 10^5] do
    for A in [[r^k : k in [0..3]], [r^k : k in [3..0 by -1]], [r^2, S!1, r, r^3], [r, -r^2, S!3, r^3/5, S!-1, r^4]] do
      x, y := IntegerRelation(A, H); print H, x, y;
    end for;
  end for;
end for;

// Complex numbers: the real and imaginary parts are both weighted.
IntegerRelation([1 + i, 2 + 2*i], 10);
IntegerRelation([i, C!1, 1 + i], 10);
IntegerRelation([C!1, C!2]);
IntegerRelation([Sqrt(C!2), C!1]);
IntegerRelation([Exp(2*Pi(C)*i/5)^k : k in [0..4]]);
x, y := IntegerRelation([C!1, 1 + i, 2*i]); x, y, Parent(y);
for z in [C![Pi(S)*3/7, Pi(S)^(1/3)], C![Log(S!5), Log(S!11)/2]] do
  x, y := IntegerRelation([z^k : k in [0..3]], 1000); print x, y;
  x, y := IntegerRelation([z, z^2, C!1], 1000); print x, y;
end for;

// Delta: LLL reduces with the Lovasz constant Delta + 0.01, at most
// (Delta + 1)/2.
for D in [0.26, 0.3, 0.5, 0.75, 0.9, 0.99, 0.995, 0.999] do
  IntegerRelation([Pi(S), S!1, r2, r3] : Delta := D);
end for;
IntegerRelation([r2, S!1], 100 : Delta := RealField(5)!0.5);

// All zero: the polynomial 1 without a bound, an error with one.
x := IntegerRelation([S!0, S!0]); x, Parent(x);
x := IntegerRelation([C!0]); x;
IntegerRelation([S!0, S!0], 10);

// Errors.
IntegerRelation([S|]);
x := IntegerRelation([S|], 5);
IntegerRelation([r2, S!1], 0);
x := IntegerRelation([r2, S!1], -5);
IntegerRelation([r2, S!1], 100.0);
IntegerRelation([1, 2]);
IntegerRelation([1/2, 1/3], 10);
IntegerRelation([* S!1, S!2 *]);
IntegerRelation({S!1, S!2});
IntegerRelation([r2, S!1], 10 : Foo := 1);
IntegerRelation([r2, S!1], 100 : Delta := 0.25);
IntegerRelation([r2, S!1] : Delta := 0.2);
IntegerRelation([r2, S!1], 100 : Delta := 1.5);
IntegerRelation([r2, S!1], 100 : Delta := 1.0);
IntegerRelation([r2, S!1], 100 : Delta := 0.251);
IntegerRelation([r2, S!1], 100 : Delta := 0);
IntegerRelation([r2, S!1], 100 : Delta := 1/2);
IntegerRelation([r2, S!1], 100 : Delta := "a");
IntegerRelation([r2, S!1] : Delta := C!0.5);
IntegerRelation([r2, S!1] : Delta := true);
IntegerRelation([r2, S!1] : Delta := 0.2510009);
IntegerRelation([r2, S!1] : Delta := 0.25100101);
IntegerRelation([S!0, S!0], 10 : Delta := 0.1);
IntegerRelation([S|] : Delta := 0.1);
f := func<q | IntegerRelation(q : Delta := 1.0)>; f([r2, S!1]);

// MinimalPolynomial: H defaults to Ceiling(10^(p/(d+1))).
for d in [1..6] do f, g := MinimalPolynomial(r, d); print d, f, g; end for;
for N in [1, 2, 5, 10, 100, 1000, 10^6] do f, g := MinimalPolynomial(r, 4, N); print N, f, g; end for;
f, g := MinimalPolynomial(r, 4); Parent(f), Parent(g);
MinimalPolynomial(r2, 1);
MinimalPolynomial(r2, 4);
MinimalPolynomial(r2, 4 : ExactDegree);
MinimalPolynomial(r2, 4, 100 : Squarefree := false);
MinimalPolynomial(r2, 4, 100 : ExactDegree);
MinimalPolynomial(r2, 2 : Delta := 0.5);
MinimalPolynomial(r2, 2 : Squarefree := 0);
MinimalPolynomial(S!2, 3);
MinimalPolynomial(S!2, 3 : ExactDegree);
MinimalPolynomial(S!0, 3);
MinimalPolynomial(S!0, 2 : ExactDegree);
MinimalPolynomial(S!1/3, 1);
MinimalPolynomial(-S!1/3, 1);
MinimalPolynomial(Pi(S), 3);
MinimalPolynomial(S!10^-10, 2, 10);
f, g := MinimalPolynomial(S!10^10, 2, 10); f, g, Parent(g);
MinimalPolynomial(S!2^40 + 1/3, 2);

// Complex numbers.
MinimalPolynomial(i, 2);
MinimalPolynomial(1 + i, 4);
MinimalPolynomial(Sqrt(C!2), 2);
MinimalPolynomial(C!0, 2);
f, g := MinimalPolynomial(Exp(2*Pi(C)*i/5), 4); f, g, Parent(g);
f, g := MinimalPolynomial(C!10^10, 2, 10); f, g, Parent(g);

// ExactDegree takes the relation of degree d; Squarefree then removes
// repeated factors, and constant ones.
rs := [Pi(S)*3/7, Exp(S!1/3), Log(S!5), Pi(S)^(1/3), Exp(S!2)/9, Log(S!11)/2];
for c in [[1, 2, 10], [3, 4, 10], [5, 4, 30], [6, 2, 30], [6, 2, 100], [2, 5, 10], [4, 5, 10]] do
  t, d, H := Explode(c); a := rs[t];
  printf "%o %o %o\n", t, d, H;
  MinimalPolynomial(a, d, H);
  MinimalPolynomial(a, d, H : Squarefree := false);
  MinimalPolynomial(a, d, H : ExactDegree);
  MinimalPolynomial(a, d, H : ExactDegree, Squarefree := false);
end for;
for t in [1..#rs] do
  for d in [3, 5] do
    for H in [5, 20, 100] do printf "%o %o %o: %o\n", t, d, H, MinimalPolynomial(rs[t], d, H); end for;
  end for;
end for;

// Errors.
MinimalPolynomial(r2, 0);
x := MinimalPolynomial(r2, -1);
MinimalPolynomial(r2, 2, 0);
MinimalPolynomial(r2, 2, -3 : ExactDegree);
MinimalPolynomial(r2, 2.5);
MinimalPolynomial(2, 2);
MinimalPolynomial(r2, 2 : Foo := 0);
MinimalPolynomial(r2, 2 : ExactDegree := 1);
MinimalPolynomial(r2, 2, 0 : ExactDegree := 1);
MinimalPolynomial(r2, 2 : ExactDegree := 1, Delta := 0.2);
MinimalPolynomial(r2, 2 : ExactDegree, Squarefree := 0);
MinimalPolynomial(S!10^10, 2 : ExactDegree);
MinimalPolynomial(S!10^10, 2, 10 : ExactDegree);
MinimalPolynomial(r2, 2, 10 : Delta := 1.0);
MinimalPolynomial(r2, 2 : Delta := 0.2);
MinimalPolynomial(r2, 2, 5 : Delta := 0.2, ExactDegree);
MinimalPolynomial(1 + i, 2 : Delta := 1/2);
f := func<| MinimalPolynomial(r2, 2, 0)>; f();

// The handbook's example (H26E8), the Kannan-Lenstra-Lovasz factorization.
// The factors depend on the order of the roots, which is calyx's own
// (reals_complex_roots.m), so they are printed sorted.
C<i> := ComplexField(1000);
P<X> := PolynomialRing(Integers());
P_C<Z> := PolynomialRing(C);
p0 := 5*X^12 + 64*X^11 + 51*X^10 + 38*X^9 - 60*X^8 - 56*X^7
    - 51*X^6 - 14*X^5 - X^4 + 12*X^3 + 8*X^2 + 4*X;
R := Roots (P_C!p0);
root := R[1][1];
res0 := MinimalPolynomial (root, 12, 100);
p1 := P!(p0/res0);
//
R := Roots (P_C!p1);
root := R[1][1];
res1 := MinimalPolynomial (root, 11, 100);
p2 := P!(p1/res1);
//
R := Roots (P_C!p2);
root := R[1][1];
res2 := MinimalPolynomial (root, 5, 100);
p3 := P!(p2/res2);
//
R := Roots (P_C!p3);
root := R[1][1];
res3 := MinimalPolynomial (root, 4, 100);
//
assert p0 eq res0*res1*res2*res3;
res := Sort([res0, res1, res2, res3], func<f, g | Evaluate(f, 2) - Evaluate(g, 2)>); res;

// PowerRelation (deprecated) takes PARI's algdep and removes factors x.
// For real r, Magma gives PARI the digits of r's precision in 32-bit words
// less two, so there are none below 20 digits and the result is 1. Magma
// 2.22's PARI reduces in floating point, and its reduced basis can differ
// from calyx's (and newer PARI's) exact one when both are reduced: the
// relation among the powers of Log(3)*2 + Sqrt(10)/9 to degree 4 at 30
// digits.
S := RealField(20); C<i> := ComplexField(20);
r := Sqrt(S!2) + Sqrt(S!3);
f := PowerRelation(r, 4); f, Parent(f);
PowerRelation(r, 3); PowerRelation(r, 5); PowerRelation(r, 2);
PowerRelation(Pi(S), 3);
PowerRelation(Pi(S), 3 : Al := "Hastad");
PowerRelation(-Sqrt(S!2), 2); PowerRelation(S!10^8 + Sqrt(S!2), 2); PowerRelation(-S!3/7, 1);
PowerRelation(S!2, 1); PowerRelation(S!1/3, 1); PowerRelation(S!0, 2);
PowerRelation(2, 2); PowerRelation(2/3, 1);
for q in [1/12345678901, 12345678901/10^20] do
  printf "%o | %o %o %o\n", PowerRelation(q, 1), PowerRelation(RealField(20)!q, 1), PowerRelation(RealField(30)!q, 1), PowerRelation(RealField(40)!q, 1);
end for;
T := RealField(30); PowerRelation(Sqrt(T!10)/9 + Log(T!9), 4);
for p in [5, 10, 19, 20, 29, 30, 38, 39, 40, 50] do
  T := RealField(p); printf "%o: %o | %o\n", p, PowerRelation(Pi(T), 3), PowerRelation(Sqrt(T!3) + Log(T!2), 2);
end for;
PowerRelation(Sqrt(C!2) + i, 4);
PowerRelation(C!2, 1); PowerRelation(C!2, 3); PowerRelation(i, 2);
for p in [10, 20, 30] do
  T<j> := ComplexField(p); printf "%o: %o\n", p, PowerRelation(T![Sqrt(RealField(p)!3)/2, Log(RealField(p)!2)], 3);
end for;
PowerRelation(i, 1);
PowerRelation(1 + i, 1);
PowerRelation(r, 0);
PowerRelation(r, -1);
PowerRelation(Pi(S), 3 : Al := "Foo");
PowerRelation(3, 2 : Al := "Foo");
PowerRelation(Pi(C), 2 : Al := 1);
PowerRelation(Pi(C), 0 : Al := "Foo");
PowerRelation(Pi(S), 3, 5);

// LinearRelation (deprecated) takes PARI's lindep to half the precision,
// with the first non-zero entry positive.
x := LinearRelation([Sqrt(C!2), C!1]); x, Parent(x);
LinearRelation([Sqrt(ComplexField(40)!2), 1]);
LinearRelation([C!1, C!2]);
LinearRelation([C!1, C!2, C!3]);
LinearRelation([C!1, C!-2]);
LinearRelation([Pi(C), C!1, Sqrt(C!2)]);
LinearRelation([Pi(C), C!1, Sqrt(C!2)] : Al := "Hastad");
LinearRelation([i, C!1, 1 + i]);
LinearRelation([C!0, C!0]);
LinearRelation([C!0, C!1]);
LinearRelation([i, C!0]);
LinearRelation([C!3, C!6]);
LinearRelation([C!10^20, C!1]);
LinearRelation([1 + i, 1 + (1 + 10^-25)*i]);
for p in [5, 10, 20, 30, 40] do
  T<j> := ComplexField(p); R := RealField(p);
  printf "%o: %o\n", p, LinearRelation([T![Sqrt(R!(2*k + 1))/(k + 1), Log(R!(k + 1))/2] : k in [1..3]]);
end for;
LinearRelation([1 + i, 2 + i]);
LinearRelation([1 + 10^-8*i, C!1]);
LinearRelation([C!1, 1 + 10^-100*i]);
LinearRelation([3 + i, 1 + (1/3)*i]);
LinearRelation([C|]);
LinearRelation([C!1]);
LinearRelation([Pi(C), C!1, Sqrt(C!2)] : Al := "Foo");
LinearRelation([Pi(C), C!1] : Al := 1);
LinearRelation([C|] : Al := "Foo");
LinearRelation([Sqrt(S!2), S!1]);
LinearRelation([1, 2]);
