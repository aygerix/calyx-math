// Continued fractions and best approximations of real numbers (Element
// Operations: Continued Fractions). A real number of p bits is m*2^e
// exactly; its continued fraction is that of this rational, up to the
// first convergent c with |x - c| < |x|*2^-p, so it depends on how x was
// rounded (2/3 at 17 bits is [0, 1, 1, 1], at 34 bits [0, 1, 2]). With
// Bound, at most Bound terms, but the whole expansion of m*2^e when it has
// fewer than Bound terms. The handbook's BestApproximation returns a real
// number; Magma 2.22 returns a rational, as here.

for d in [5, 10, 20, 30, 40] do
  R := RealField(d);
  for x in [Pi(R), Sqrt(R!2), R!2/3, R!1/3, Exp(R!1), R!355/113, R!1/10, -Pi(R), R!7, R!-7, R!15/2, R!1/1024, R!10^25, R!1/10^25,
            (1 + Sqrt(R!5))/2, R!22/7, R!1/10^5, R!-2/3, R!3/4, R!123456789/1000] do
    m, e := MantissaExponent(x);
    printf "%o %o %o : %o\n", d, m, e, ContinuedFraction(x);
  end for;
end for;
R := RealField(20);
x := ContinuedFraction(Pi(R)); x, Universe(x);
ContinuedFraction(R!0), ContinuedFraction(R!-1), ContinuedFraction(R!-0.5), ContinuedFraction(R!-1/7), ContinuedFraction(R!10^-30);
ContinuedFraction(R!2^100), ContinuedFraction(R!-2^200), ContinuedFraction(R!2^65 + 1/3), ContinuedFraction(R!1 + 2^-66);
ContinuedFraction(Sqrt(RealField(100)!2));
ContinuedFraction(Exp(RealField(60)!1));
[ContinuedFraction(RealField(d)!Pi(R)) : d in [1..3]];
ContinuedFraction(RealField(20 : Bits := true)!Pi(R));

// Bound: the length for Bound := 1..45.
for d in [10, 20, 30] do
  R := RealField(d);
  for x in [Pi(R), Sqrt(R!2), Exp(R!1), R!1/3, R!1/7] do
    m, e := MantissaExponent(x);
    printf "%o %o %o :", d, m, e;
    for b in [1..45] do printf " %o", #ContinuedFraction(x : Bound := b); end for;
    printf "\n";
  end for;
end for;
R := RealField(20);
ContinuedFraction(Pi(R) : Bound := 3), ContinuedFraction(Pi(R) : Bound := 21), ContinuedFraction(Pi(R) : Bound := 50);
ContinuedFraction(Pi(R) : Bound := 2^70), ContinuedFraction(Pi(RealField(1000)) : Bound := 60);
ContinuedFraction(R!0 : Bound := 0), ContinuedFraction(R!0 : Bound := 1);

// Complex numbers that are real.
C<i> := ComplexField(20);
ContinuedFraction(C!1), ContinuedFraction(C![1.5, 0]), ContinuedFraction(C!Pi(R) : Bound := 3);
BestApproximation(C!Pi(R), 1000), BestApproximation(C!0.5, 1);

// Best approximations: PARI's bestappr, whose floating point Magma
// reproduces beyond the precision of x.
for d in [5, 10, 19, 20, 30, 38, 39, 40, 60, 100] do
  R := RealField(d);
  for x in [Pi(R), -Pi(R), Sqrt(R!2), Exp(R!1), R!1/3, R!-1/7, Log(R!10)] do
    m, e := MantissaExponent(x);
    printf "%o %o %o :", d, m, e;
    for k in [10, 10^3, 10^6, 2^20, 2^30, 2^40, 2^50, 2^60, 2^64, 2^70, 2^80, 2^100, 2^128, 2^140, 2^200, 2^300, 10^60, 10^100] do
      try printf " %o", BestApproximation(x, k); catch err printf " ERR"; end try;
    end for;
    printf "\n";
  end for;
end for;
R := RealField(20);
[BestApproximation(Pi(R), k) : k in [1, 2, 7, 100, 105, 106, 1000, 10^6, 10^20, 2^70]];
[BestApproximation(t[1], t[2]) : t in [<R!0, 5>, <R!-0.5, 1>, <R!-0.5, 2>, <R!0.5, 1>, <R!1.5, 1>, <R!2.5, 1>, <R!2.5, 3>, <R!-2.5, 1>]];
[BestApproximation(R!-1/3, 2), BestApproximation(R!-1/3, 3), BestApproximation(R!1/3, 3), BestApproximation(-Sqrt(R!2), 100)];
x := BestApproximation(R!7, 10); x, Type(x), Parent(x);
BestApproximation(R!7.25, 10), BestApproximation(R!2^100 + 1/3, 10), BestApproximation(R!2^127, 10);
BestApproximation(R!10^-30, 10), BestApproximation(R!10^-30, 10^31), BestApproximation(R!-10^-30, 10);

// Errors.
ContinuedFraction(Pi(R) : Bound := 0);
ContinuedFraction(R!5 : Bound := 0);
ContinuedFraction(Pi(R) : Bound := -1);
ContinuedFraction(Pi(R) : Bound := 1/2);
ContinuedFraction(Pi(R) : Bound := "a");
ContinuedFraction(C![1.5, 2]);
ContinuedFraction(Pi(RealField(20)), 5);
a, b := ContinuedFraction(Pi(R));
BestApproximation(Pi(R), 0);
BestApproximation(Pi(R), -1);
BestApproximation(R!0, 0);
BestApproximation(R!5, 0);
BestApproximation(R!1/3, 10^30);
BestApproximation(R!2^128, 10);
BestApproximation(R!-2^200, 10);
BestApproximation(Pi(R), 1/2);
BestApproximation(C![1.5, 2], 10);
BestApproximation(Pi(R), 1 : Bound := 3);
