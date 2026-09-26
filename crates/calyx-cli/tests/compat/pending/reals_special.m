// Other special functions: the error functions, the exponential and
// logarithmic integrals, Dawson's integral, the Riemann zeta function, the
// arithmetic-geometric mean and the Bernoulli numbers.

R := RealField(20);
C<i> := ComplexField(20);
E := RealField(30);
x := R!2/3; y := R!-7/3; w := R!5/2;
inf := (R!10)^1000000000; nan := inf - inf;

// The error functions; integers and rationals are in the default field.
for v in [x, y, w, R!0, -R!0, R!1, R!-1, R!100, R!-100, R!1/10^10, inf, -inf] do
  e := Erf(v); c := Erfc(v);
  v, e, MantissaExponent(e), c, MantissaExponent(c), ErrorFunction(v) eq e, ComplementaryErrorFunction(v) eq c;
end for;
Erf(3), Erf(1/2), Erf(-2), Erf(0), Erfc(3), Erfc(1/2), Parent(Erfc(1));
Erf(nan);
Erfc(nan);

// The exponential integrals Ei and E1, where E1(x) = -Ei(-x). (Magma
// 2.22's MPFR 2.4.1 has no Ei(x) for x < 0, so no E1(x) for x > 0; these
// follow the handbook.)
for v in [x, w, R!1, R!100, R!1/10^10] do
  ei := ExponentialIntegral(v); e1 := ExponentialIntegralE1(-v);
  v, ei, MantissaExponent(ei), e1 eq -ei;
end for;
ExponentialIntegral(3), ExponentialIntegral(1/2), ExponentialIntegralE1(-2);
for v in [x, w, R!1, R!100, R!1/10^10] do
  e1 := ExponentialIntegralE1(v);
  v, e1, MantissaExponent(e1), ExponentialIntegral(-v) eq -e1;
end for;
ExponentialIntegralE1(3), ExponentialIntegralE1(1/2), ExponentialIntegral(-2), ExponentialIntegralE1(inf);
ExponentialIntegral(R!0);
ExponentialIntegral(0);
ExponentialIntegral(inf);
ExponentialIntegral(nan);
ExponentialIntegralE1(-R!0);
ExponentialIntegralE1(-inf);

// The logarithmic integral. Magma 2.22's values are a few units in the
// last place off (up to 50 at 30 digits), so they are printed to 15
// digits.
F := RealField(15);
[F!LogIntegral(E!v) : v in [2/3, 5/2, 3, 7, 10, 100, 1000, 1/2, 1/3, 1/10, 9/10, 101/100, 10^10, 1/10^5]];
F!LogIntegral(3), F!LogIntegral(1/2), Parent(LogIntegral(2));
LogIntegral(y);
LogIntegral(-2);
LogIntegral(-inf);
LogIntegral(R!1);
LogIntegral(1);

// Dawson's integral.
for v in [x, y, w, R!1, R!-1, R!100, R!-100, R!1/10^10, R!-3, R!1/2] do
  d := DawsonIntegral(v);
  v, d, MantissaExponent(d);
end for;
DawsonIntegral(3), DawsonIntegral(1/2), DawsonIntegral(-2), Parent(DawsonIntegral(1));

// The Riemann zeta function.
for v in [x, y, w, R!0, -R!0, R!-1, R!100, R!-100, R!1/10^10, R!-3, R!-2, R!1/2, inf] do
  z := ZetaFunction(v);
  v, z, MantissaExponent(z);
end for;
ZetaFunction(3), ZetaFunction(1/2), ZetaFunction(-2), ZetaFunction(0), Parent(ZetaFunction(3));
ZetaFunction(R!1);
ZetaFunction(1);
ZetaFunction(nan);
ZetaFunction(-inf);
// Of a complex argument (Magma 2.22 lacks this; it follows the handbook).
ZetaFunction(C![1/3, -2/5]), ZetaFunction(C![-7/3, 5/2]), ZetaFunction(C![1/2, 14]);
ZetaFunction(C!1);
// Of an integer, in a given real field.
[ZetaFunction(R, n) : n in [2, 3, 0, -1, -2, -3, 100, -100, -101, 1001, 10^6, -10^6]];
ZetaFunction(RealField(10), 3), Parent(ZetaFunction(RealField(10), 3));
ZetaFunction(R, 2^30 - 1), ZetaFunction(R, -(2^30 - 1)), ZetaFunction(R, -(2^29 + 1)), ZetaFunction(R, -(10^7 + 1));
ZetaFunction(R, 1);
ZetaFunction(R, 2^30);
ZetaFunction(R, -2^40);
ZetaFunction(ComplexField(10), 3);

// The arithmetic-geometric mean, of reals in the smaller precision, and of
// complex numbers.
AGM(x, w), AGM(w, x), AGM(R!1, R!2), AGM(R!0, w), ArithmeticGeometricMean(x, w);
AGM(x, E!5/2), Parent(AGM(x, E!5/2));
AGM(-x, w), AGM(-x, -w), AGM(nan, x), AGM(inf, x);
AGM(C![1, 1], C![2, -1]), ArithmeticGeometricMean(C![1, 1], C![2, -1]);
AGM(R!2, C![1, 1]), AGM(C![1, 1], R!2), AGM(C!1, R!2), Parent(AGM(R!2, C!1));
AGM(C!0, C![1, 1]);
AGM(1, 2);
AGM(1/3, w);

// Bernoulli numbers: B_n is 0 for n < 0.
[BernoulliNumber(n) : n in [0, 1, 2, 3, 4, 10, 1001, -1]];
BernoulliNumber(50);
BernoulliNumber(100);
[BernoulliApproximation(n) : n in [0, 1, 2, 3, 4, 10, 50, 100, -1, -2, 1001]];
BernoulliApproximation(100000);
