// The gamma function and its logarithm and logarithmic derivative, the
// incomplete gamma function, and the Bessel functions.

R := RealField(20);
C<i> := ComplexField(20);
x := R!2/3; y := R!-7/3; w := R!5/2;
z := C![1/3, -2/5]; u := C![-7/3, 5/2];

// Gamma, LogGamma and Psi (also LogDerivative) of reals, with their
// mantissas; integers and rationals are in the default field.
for v in [x, y, w, R!100, R!-1/2, R!1/10^10] do
  g := Gamma(v); p := Psi(v);
  g, MantissaExponent(g), p, MantissaExponent(p), LogDerivative(v) eq p;
end for;
for v in [x, w, R!100, R!-7/2, R!1/10^10, R!10^10] do
  l := LogGamma(v);
  l, MantissaExponent(l);
end for;
Gamma(3), Gamma(1/2), Gamma(-3/2), Parent(Gamma(3));
LogGamma(3), LogGamma(1/2), LogGamma(-3/2);
Psi(3), Psi(1/2), Psi(-3/2), LogDerivative(1);
Gamma(RealField(10)!2/3), Psi(RealField(10)!2/3);

// Large and small arguments: Gamma underflows to zero, and is an error
// where it overflows.
Gamma(R!171), Gamma(R!172), Gamma(R!1000), Gamma(R!-170.5), Gamma(R!-171.5), Gamma(R!-1001.5);
Gamma(R!1/10^30), Gamma(R!-1/10^30), Gamma(R!-10^10 - 1/2);
LogGamma(R!171), LogGamma(R!1000), LogGamma(R!10^9), LogGamma(R!-171.5), LogGamma(R!-1001.5), LogGamma(R!1/10^30);
Gamma(R!10^9);
LogGamma(y);
LogGamma(R!-1/10^30);

// Complex arguments.
for v in [z, u, C![-5/2, 1/100], C![1/2, 50], C![1/2, -50], C!5, C!-5/2] do
  g := Gamma(v); l := LogGamma(v); p := Psi(v);
  g, l, p, LogDerivative(v) eq p;
end for;
LogGamma(C![-2, 1/10^30]);

// LogGamma is the principal branch: its imaginary part is in (-pi, pi],
// and pi on the negative real axis.
LogGamma(C![-1/2, 0]), LogGamma(-C![1/2, 0]), LogGamma(C![-3/2, 0]);
LogGamma(C![-7/2, 1/10^10]), LogGamma(C![-7/2, -1/10^10]);
LogGamma(C![-100, 1/3]), LogGamma(C![3/2, 10^6]), LogGamma(C![-10^6 + 1/2, 1]);

// The poles.
Gamma(0);
Gamma(-2);
Gamma(R!0);
Gamma(-R!0);
Gamma(R!-2);
Gamma(C!0);
Gamma(C!-2);
LogGamma(0);
LogGamma(R!-2);
LogGamma(C!0);
LogGamma(C!-2);
Psi(-R!0);
Psi(-2);
Psi(C!0);
LogDerivative(C!-2);

// Infinities and NaN.
inf := (R!10)^1000000000; nan := inf - inf;
Gamma(inf);
Gamma(-inf);
Gamma(nan);
LogGamma(inf);
LogGamma(nan);

// The incomplete gamma function and its complement.
for t in [<x, w>, <w, x>, <R!5, R!1>, <R!-1/2, w>, <y, w>, <x, R!0>, <R!3, R!0>, <R!100, R!90>, <R!1/10, R!50>, <R!1/2, R!1/10^30>, <R!-1/2, R!1>, <R!-5/2, R!1/2>, <R!1, R!100>] do
  g := Gamma(t[1], t[2]); G := Gamma(t[1], t[2] : Complementary);
  t, g, MantissaExponent(g), G, MantissaExponent(G);
end for;
Gamma(R!0, w : Complementary), Gamma(R!-2, w : Complementary);
Gamma(R!1, R!10^6), Gamma(R!1, R!10^6 : Complementary), Gamma(R!10^6, R!1), Gamma(R!10^6, R!1 : Complementary);
// In the field of the arguments if they are reals of the same precision,
// else in the default field.
F := RealField(40); D := RealField(10);
Gamma(F!2/3, F!5/2), Gamma(D!2/3, D!5/2);
Gamma(F!2/3, w), Gamma(D!2/3, F!5/2), Gamma(2/3, F!5/2), Gamma(x, 5/2), Gamma(2/3, 5/2), Gamma(1, 1);
// Given Gamma(s), the function is computed from its complement.
Gamma(x, w : Gamma := Gamma(x));
Gamma(x, w : Gamma := R!1);
Gamma(x, w : Gamma := RealField(30)!1);
Gamma(x, w : Complementary := false, Gamma := R!1);
Gamma(x, w : Complementary, Gamma := R!1);
Gamma(x, w : Gamma := 1);
Gamma(x, w : Complementary := 1);
Gamma(R!0, w);
Gamma(R!-2, w);
Gamma(R!0, R!0 : Complementary);

// GammaD(s) is Gamma(s + 1/2).
for v in [x, w, y, R!3, R!-1, R!0, R!100, R!-1/2 - 10^-19] do
  v, GammaD(v);
end for;
GammaD(3), GammaD(1/2), GammaD(1/3), GammaD(D!2/3);
GammaD(R!-1/2);
GammaD(R!-3/2);
GammaD(-1/2);
GammaD(C![1/3, 1/2]);

// Bessel functions of the first and second kinds, of integer order:
// J_n(-x) = (-1)^n J_n(x), and Y_n(x) is NaN for x < 0.
for n in [0, 1, 2, 5, 100] do
  for v in [x, w, -w, R!100, R!0, -R!0] do
    jn := BesselFunction(n, v); yn := BesselFunctionSecondKind(n, v);
    n, v, jn, yn;
  end for;
  MantissaExponent(BesselFunction(n, x)), MantissaExponent(BesselFunctionSecondKind(n, w));
end for;
BesselFunction(1000, w), BesselFunction(10^5, w), BesselFunction(10^6, w), BesselFunction(2^20, w);
BesselFunction(2^28, w), BesselFunction(2^30 - 1, R!1/10);
BesselFunctionSecondKind(1000, w), BesselFunctionSecondKind(10^4, w);
BesselFunction(0, 2), BesselFunctionSecondKind(0, 2), BesselFunction(1, 1/2), BesselFunctionSecondKind(1, 1/2);
BesselFunction(3, 1/3), BesselFunctionSecondKind(3, 1/3), Parent(BesselFunction(3, 1/3));
BesselFunction(3, D!1/3), BesselFunctionSecondKind(3, D!1/3);
BesselFunction(-3, x);
BesselFunctionSecondKind(-3, w);
BesselFunction(2^30, w);
BesselFunction(2^63, w);
BesselFunction(R!1, w);

// JBessel(n, x) is J_(n+1/2)(x).
JBessel(0, x), JBessel(2, w), JBessel(0, R!0), JBessel(3, R!0), JBessel(0, R!10^6);
JBessel(3, D!5/2);
JBessel(-3, w);

// The modified Bessel function of the second kind, of real or complex
// order: for a real order in the smaller precision of the arguments, for
// a complex one in the precision of the order.
for t in [<R!0, x>, <R!1/3, w>, <R!5, R!1/10>, <R!1/3, R!10^6>, <R!100, R!1/10>, <R!1/3, 1>, <1/3, w>, <0, w>, <R!1/3, 5/2>] do
  k := KBessel(t[1], t[2]);
  t, k, KBessel2(t[1], t[2]) eq k, Parent(k);
end for;
KBessel(R!1/3, RealField(30)!5/2), KBessel(R!1/3, D!5/2), KBessel(1/3, D!5/2);
KBessel(C![1/3, 1/2], w), KBessel2(C![1/3, 1/2], w), KBessel(C!2, w);
KBessel(C![1/3, 1/2], RealField(30)!5/2), KBessel(ComplexField(10)![1/3, 1/2], w);
KBessel(C![1/3, 1/2], D!5/2);
KBessel(R!0, R!0);
KBessel2(R!0, -w);
KBessel(1/3, 5/2);
