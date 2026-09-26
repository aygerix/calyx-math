// Numerical integration: polynomial interpolation, the discrete Fourier
// transform, the integration points of Gauss-Legendre, Gauss-Jacobi,
// Clenshaw-Curtis and tanh-sinh quadrature, the Romberg-type rules and
// numerical derivatives. (Magma 2.22 lacks DiscreteFourierTransform and the
// integration points; those cases follow the handbook.)

R := RealField(20); F := RealField(30); C<i> := ComplexField(20);

// Interpolation by Neville's algorithm: the value and an error estimate.
P := [R!1, R!2, R!3, R!4];
y, e := Interpolation(P, [R!1, R!4, R!9, R!16], R!5/2); y, e;
y, e := Interpolation(P, [Exp(p) : p in P], R!5/2); y, e, MantissaExponent(y), MantissaExponent(e);
y, e := Interpolation(P, [R!1/p : p in P], R!10); y, e, MantissaExponent(y);
y, e := Interpolation(P, [Exp(p) : p in P], R!4); y, e;
y, e := Interpolation([R!1/3, R!2/7, R!5], [R!2, R!-1, R!1/9], R!3/11); y, e, MantissaExponent(y), MantissaExponent(e);
// The computation is kept in the field of the values.
y, e := Interpolation([RealField(10)!1, 2, 3], [R!1, 4, 9], R!5/2); y, e, Parent(y);
y := Interpolation([F | 1, 1/4, 1/16], [R | 1/3, 1/5, 1/7], F!0); Parent(y), MantissaExponent(y);
y := Interpolation([F | 1, 1/4, 1/16], [F | 1/3, R!1/5, R!1/7], F!0); Parent(y), MantissaExponent(y);
Interpolation(P, [R!1, R!2, R!3], R!2);
Interpolation([R!1, R!1], [R!1, R!2], R!2);
try y, e := Interpolation([R | ], [R | ], R!2); catch e print e`Object; end try;
Interpolation([1, 2, 3], [1, 4, 9], 5/2);
Interpolation(P, [R!1, R!4, R!9, R!16], 5/2);
Interpolation([C!1, C!2, C!3], [C!1, C![4, 1], C!9], C![5/2, 1]);

// The discrete Fourier transform.
DiscreteFourierTransform([C!1, C!2, C!3, C!4]);
DiscreteFourierTransform([C!1, i, C!2, C![3, 1], C!5]);
DiscreteFourierTransform([C!1]);
D := DiscreteFourierTransform([ComplexField(10)!1, ComplexField(10)!2]); D, Universe(D);
DiscreteFourierTransform([R!1, R!2]);

// Gauss-Legendre, Gauss-Jacobi, Clenshaw-Curtis and tanh-sinh points.
A, W := GaussLegendreIntegrationPoints(4, 20); A; W; Universe(A);
A, W := GaussJacobiIntegrationPoints(3, 20, -1/3, -1/5); A; W;
A, W := GaussJacobiIntegrationPoints(2, 20, 1/2, 1/2); A; W;
A, W := ClenshawCurtisIntegrationPoints(4, 20); A; W;
A, W1, W2 := TanhSinhIntegrationPoints(2, RealField(20)!1/2); A; W1; W2;
GaussLegendreIntegrationPoints(0, 20);
ClenshawCurtisIntegrationPoints(0, 20);
TanhSinhIntegrationPoints(3, RealField(20)!0);
TanhSinhIntegrationPoints(3, 1/2);

// The handbook's examples.
N := 20;
D := 50;
function f(x)
   return x*Log(1+x);
end function;
A_GL, W_GL := GaussLegendreIntegrationPoints(N,D);
/* Map abscissas to the interval [0,1] */
A_GL := [ (1/2)*(a+1) : a in A_GL ];
int_GL := (1/2) * &+[ W_GL[k] * f(A_GL[k]) : k in [1..N] ];
Abs(int_GL - 1/4);
A_CC, W_CC := ClenshawCurtisIntegrationPoints(N,D);
A_CC := [ (1/2)*(a+1) : a in A_CC ];
int_CC := (1/2) * &+[ W_CC[k] * f(A_CC[k]) : k in [1..N+1] ];
Abs(int_CC - 1/4);
h := RealField(D)!6/N;
A_DE, W_DE := TanhSinhIntegrationPoints(N,h);
A_DE := [ (1/2)*(a+1) : a in A_DE ];
int_DE := (1/2) * &+[ W_DE[k] * f(A_DE[k]) : k in [1..2*N+1] ];
Abs(int_DE - 1/4);
c := 0.128866348618482136010608730745;
N := 10;
D := 30;
function f(x)
   return Sin(x)*Cos(x);
end function;
A, W := GaussJacobiIntegrationPoints(N,D,-1/3,-1/5);
int_GJ := &+[ W[k] * f(A[k]) : k in [1..N] ];
Abs(int_GJ - c);
h := Real(2^-3);
N := Ceiling(6/h);
A, W1, W2 := TanhSinhIntegrationPoints(N,h);
int_DE := &+[ W1[k]*W2[k]^(1/3)*(1+A[k])^(1/3-1/5)*f(A[k]) : k in [1..2*N+1] ];
Abs(int_DE - c);
h := RealField(1000)!(2^-10);
N := Ceiling(7.2/h);
A_DE, W_DE := TanhSinhIntegrationPoints(N,h);
assert A_DE[1] gt -1;
assert A_DE[2*N+1] lt 1;
A_DE := [ (1/2)*(a+1) : a in A_DE ];
function f(z)
   return (Exp(1-1/z) * Cos(1/z-1)/z^2);
end function;
int_DE := (1/2) * &+[ W_DE[k] * f(A_DE[k]) : k in [1..2*N+1] ];
Abs(int_DE - 1/2) lt 10^-300;

// Romberg's method; the points it evaluates, and the result in the default
// real field.
g := func< x | Exp(x) >;
f := function(x) printf "%o ", x; return Exp(x); end function;
x := RombergQuadrature(f, R!0, R!1); print ""; x, MantissaExponent(x), Parent(x);
x := RombergQuadrature(g, R!1/3, R!17/7); x, MantissaExponent(x);
x := RombergQuadrature(g, R!1, R!0); x, MantissaExponent(x);
x := RombergQuadrature(g, F!1/3, F!17/7); x, MantissaExponent(x);
x := RombergQuadrature(func< x | Exp(RealField(50)!x) >, R!1/3, R!17/7); x, MantissaExponent(x);
x := RombergQuadrature(func< x | x^2 >, R!1/3, R!17/7); x, MantissaExponent(x);
x := RombergQuadrature(func< x | Sin(x)^2 >, R!0, Pi(R)); x, MantissaExponent(x);
x := RombergQuadrature(func< x | 1/(1 + x^2) >, F!0, F!1); x, MantissaExponent(x);
x := RombergQuadrature(func< x | 1/3 >, R!1/3, R!17/7); x, MantissaExponent(x);
x := RombergQuadrature(Exp, R!0, R!1); x;
x := RombergQuadrature(func< x | C!x >, R!0, R!1); x;
// The parameters: the relative accuracy and the number of steps.
for p in [* 1.0e-10, R!1/10^15, 1/10^3, -1/10^3 *] do
  x := RombergQuadrature(g, R!0, R!1 : Precision := p); x, MantissaExponent(x);
end for;
x := RombergQuadrature(g, RealField(10)!0, RealField(10)!1 : Precision := 1.0e-12); x, MantissaExponent(x);
for s in [1, 5, 6] do
  try x := RombergQuadrature(g, R!0, R!1 : MaxSteps := s); x; catch e print e`Object; end try;
end for;
try x := RombergQuadrature(f, R!0, R!1 : MaxSteps := 0); x; catch e print e`Object; end try;
x := RombergQuadrature(g, R!0, R!1 : K := 8); x;
// (Magma 2.22 prints false when K < 2.)
x := RombergQuadrature(g, R!0, R!1 : K := 1); x;
try x := RombergQuadrature(g, R!0, R!1 : K := "a"); x; catch e print e`Object; end try;
try x := RombergQuadrature(g, R!0, R!1 : MaxSteps := 1/2); x; catch e print e`Object; end try;
try x := RombergQuadrature(g, R!0, R!1 : Precision := "a"); x; catch e print e`Object; end try;
try x := RombergQuadrature(func< x | "a" >, R!0, R!1); x; catch e print e`Object; end try;
try x := RombergQuadrature(func< x | 1/x >, R!0, R!1); x; catch e print e`Object; end try;
try x := RombergQuadrature(func< x | C![x, 1] >, R!0, R!1); x; catch e print e`Object; end try;
RombergQuadrature(g, 0, 1);
RombergQuadrature(g, R!0, 1);
RombergQuadrature(map< R -> R | x :-> x^2 >, R!0, R!1);

// The trapezoidal rule and Simpson's rule: the points they evaluate. The
// values at the inner points are added in the default real field.
x := TrapezoidalQuadrature(f, R!0, R!1, 4); print ""; x, MantissaExponent(x), Parent(x);
x := SimpsonQuadrature(f, R!0, R!1, 4); print ""; x, MantissaExponent(x), Parent(x);
x := TrapezoidalQuadrature(f, R!1, R!0, 2); print ""; x, MantissaExponent(x);
for n in [1, 7, 10, 25] do
  x := TrapezoidalQuadrature(g, R!1/3, R!17/7, n); x, MantissaExponent(x);
end for;
for n in [2, 6, 10, 26] do
  x := SimpsonQuadrature(g, R!1/3, R!17/7, n); x, MantissaExponent(x);
end for;
x := TrapezoidalQuadrature(g, F!1/3, F!17/7, 7); x, MantissaExponent(x);
x := SimpsonQuadrature(g, F!1/3, F!17/7, 6); x, MantissaExponent(x);
x := TrapezoidalQuadrature(g, RealField(50)!1/3, RealField(50)!17/7, 7); x, MantissaExponent(x), Parent(x);
x := SimpsonQuadrature(g, RealField(50)!1/3, RealField(50)!17/7, 6); x, MantissaExponent(x), Parent(x);
x := TrapezoidalQuadrature(func< x | Exp(RealField(50)!x) >, R!1/3, R!17/7, 7); x, MantissaExponent(x);
x := SimpsonQuadrature(func< x | Exp(RealField(50)!x) >, R!1/3, R!17/7, 6); x, MantissaExponent(x);
V := [R | 0, 2^80, 1, -2^80, 0];
x := TrapezoidalQuadrature(func< x | V[Round(4*x) + 1] >, R!0, R!1, 4); x;
V := [R | 0, 2^120, 1, -2^120, 0];
x := TrapezoidalQuadrature(func< x | V[Round(4*x) + 1] >, R!0, R!1, 4); x;
V := [R | 0, 2^80, 0, 1, 0, -2^80, 0, 0, 0];
x := SimpsonQuadrature(func< x | V[Round(8*x) + 1] >, R!0, R!1, 8); x;
x := TrapezoidalQuadrature(func< x | 1/3 >, R!0, R!1, 3); x, MantissaExponent(x);
x := SimpsonQuadrature(func< x | 1/3 >, R!1/3, R!17/7, 4); x, MantissaExponent(x);
x := TrapezoidalQuadrature(func< x | 1 >, RealField(50)!0, RealField(50)!1, 1); x, Parent(x);
x := TrapezoidalQuadrature(func< x | C![x, 1] >, R!0, R!1, 1); x;
x := TrapezoidalQuadrature(func< x | C!x >, R!0, R!1, 2); x, Parent(x);
x := SimpsonQuadrature(Exp, R!0, R!1, 2); x;
try x := TrapezoidalQuadrature(func< x | C![x, 1] >, R!0, R!1, 2); x; catch e print e`Object; end try;
try x := SimpsonQuadrature(func< x | x gt 0 and x lt 1 select "a" else x >, R!0, R!1, 2); x; catch e print e`Object; end try;
try x := TrapezoidalQuadrature(func< x | "a" >, R!0, R!1, 2); x; catch e print e`Object; end try;
TrapezoidalQuadrature(g, R!0, R!1, 0);
TrapezoidalQuadrature(g, R!0, R!1, -1);
SimpsonQuadrature(g, R!0, R!1, 0);
SimpsonQuadrature(g, R!0, R!1, 3);
SimpsonQuadrature(g, R!1/3, 1, 2);
TrapezoidalQuadrature(g, R!0, R!1, R!2);
TrapezoidalQuadrature(g, C!0, R!1, 2);

// Numerical derivatives, from the values at n + 1 points around z.
f := func<x|Exp(2*x)>;
NumericalDerivative(f, 10, ComplexField(30)! 1.0) / f (1.0);
NumericalDerivative(func<x|LogGamma(x)>,1,ComplexField()!3.0);
Psi(3.0); // Psi is Gamma'/Gamma
pf := function(x) print " ", x, Parent(x); return Exp(2*x); end function;
for d in [5, 15, 1] do
  x := NumericalDerivative(pf, 1, ComplexField(d)!1); x, Parent(x);
end for;
x := NumericalDerivative(pf, 3, ComplexField(15)!1); x;
x := NumericalDerivative(pf, 2, R!0); x, Parent(x);
x := NumericalDerivative(pf, 2, R!-1); x;
x := NumericalDerivative(pf, 1, R!1000); x;
x := NumericalDerivative(func< x | Exp(x/1000) >, 3, C![300, 400]); x;
for n in [1, 2, 3, 5] do
  x := NumericalDerivative(func< x | Exp(2*x) >, n, R!1/3); x, MantissaExponent(x);
end for;
NumericalDerivative(func< x | Sin(x) >, 2, R!1/2), NumericalDerivative(func< x | x^3 >, 3, R!1);
NumericalDerivative(func< x | R!x^2 >, 2, R!1), NumericalDerivative(func< x | 1/3 >, 2, R!1);
x := NumericalDerivative(func< x | 1 >, 1, C!1); x, Parent(x);
x := NumericalDerivative(func< x | 1/3 >, 0, R!1); x, Parent(x);
NumericalDerivative(func< x | Exp(x) >, -1, R!1);
NumericalDerivative(func< x | Exp(x) >, 1, 1);
NumericalDerivative(Exp, 1, C!1);
NumericalDerivative(func< x | Exp(x) >, R!1, C!1);
try x := NumericalDerivative(func< x | "a" >, 1, C!1); x; catch e print e`Object; end try;
try x := NumericalDerivative(func< x | "a" >, 0, C!1); x; catch e print e`Object; end try;
