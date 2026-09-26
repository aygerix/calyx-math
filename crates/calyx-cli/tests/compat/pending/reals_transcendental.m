// Transcendental functions of real and complex numbers: exponential,
// logarithms, polylogarithms, trigonometric and hyperbolic functions and
// their inverses.

R := RealField(20);
C<i> := ComplexField(20);
x := R!2/3; y := R!-7/3; w := R!5/2;
z := C![1/3, -2/5]; u := C![-7/3, 5/2];

// Real arguments: results in the field of the argument, integers and
// rationals in the default field.
Exp(x), Log(x), Dilog(x), Dilog(w);
Sin(x), Cos(x), Tan(x), Cot(x), Sec(x), Cosec(x);
Sin(y), Cos(y), Tan(y), Cot(y), Sec(y), Cosec(y);
Arcsin(x), Arccos(x), Arctan(x), Arctan(y), Arccot(x), Arccot(y);
Arcsec(w), Arcsec(y), Arccosec(w), Arccosec(y);
Sinh(x), Cosh(x), Tanh(x), Coth(x), Sech(x), Cosech(x);
Sinh(y), Cosh(y), Tanh(y), Coth(y), Sech(y), Cosech(y);
Argsinh(x), Argsinh(y), Argcosh(w), Argtanh(x), Argsech(x), Argcosech(y), Argcoth(w), Argcoth(y);
Exp(1); Log(2); Sin(1/2); Parent(Cos(3)); Arctan(-3/4);
Dilog(-3); Dilog(2); Parent(Dilog(1/2));
Sincos(x);
s, c := Sincos(-3);
s, c;
MantissaExponent(Exp(x)), MantissaExponent(Arctan(y)), MantissaExponent(Argcosech(y));
Exp(RealField(50)!1);
Sin(RealField(5)!7);

// Special values.
inf := (R!10)^1000000000;
nan := inf - inf;
Exp(inf), Exp(-inf), Exp(nan), Log(inf), Log(nan);
Arctan(inf), Arctan(-inf), Tanh(inf), Coth(-inf), Sech(inf), Cosech(-inf);
Arccot(R!0), Arccot(-R!0), Arccot(inf), Arcsec(inf), Arcsec(-inf), Arcsec(nan), Argsech(nan);
Dilog(R!0), Dilog(-R!0), Dilog(inf), Dilog(-inf), Dilog(R!1);
Sincos(inf);
Sincos(-R!0);
Exp(R!10^20);
Exp(-R!10^20);

// Arguments outside the domain, and values that are not finite.
Log(y);
Log(-R!0);
Log(0);
Arcsin(w);
Arccos(-3/2);
Arcsec(x);
Arccosec(1/2);
Coth(R!0);
Cosech(0);
Argcosech(-R!0);
Argcosh(x);
Argtanh(1);
Argtanh(nan);
Argsech(y);
Argsech(w);
Argcoth(x);
Argcoth(nan);
Cot(R!0);
Cosec(-R!0);
Sin(inf);
Cos(nan);
Sinh(R!10^10);
Arcsin(nan);
Argcosh(inf);

// Logarithms to a base: in the common field of the arguments, else in
// the default field.
Log(R!2, R!8);
Log(R!3, R!7);
Log(2, 8);
Log(R!10, 1000);
Log(RealField(10)!2, R!8);
Log(1/2, 8);
Log(R!2, inf);
Log(R!2, R!1);
Log(R!-2, 8);
Log(R!2, -8);
Log(R!1, 5);
Log(R!0, 5);
Log(R!2, 0);
Log(nan, R!2);

// The angle of a point: Arctan(x, y) is the argument of x + y*i.
Arctan(R!1, R!0), Arctan(R!0, R!1), Arctan(R!-1, R!0), Arctan(R!0, R!-1);
Arctan(R!-1, -R!0), Arctan(R!-1, R!-1), Arctan2(R!2, R!3), Arctan(R!3, R!2);
Arctan(2, 3), Arctan(1/2, 1/3), Arctan(RealField(10)!2, R!3);
MantissaExponent(Arctan(R!-5, R!7)), MantissaExponent(Arctan(R!-13, R!-17));
// Magma 2.22 crashes here; the handbook says it is an error.
// Arctan(R!0, R!0);

// Complex arguments.
Exp(z), Log(z), Log(u);
Sin(z), Cos(z), Tan(z), Cot(z), Sec(z), Cosec(z);
Arcsin(z), Arccos(z), Arctan(z), Arccot(z), Arcsec(z), Arccosec(z);
Sinh(u), Cosh(u), Tanh(u), Coth(u), Sech(u), Cosech(u);
Argsinh(u), Argcosh(u), Argtanh(u), Argsech(u), Argcosech(u), Argcoth(u);
Arcsin(C!2), Arccos(C!2), Argcosh(C!-3), Argtanh(C!2), Log(C!-1);
Sincos(z);
Exp(ComplexField(40)![1, 1]);
[MantissaExponent(Real(v)) : v in [Log(u), Cot(u), Sec(z), Arccot(u), Argcoth(z)]];

// On the axes, zero parts have signs, and those on the branch cuts
// select a side, as with MPC.
pz := R!0; nz := -R!0;
pts := [C![2, pz], C![2, nz], C![-2, pz], C![-2, nz], C![1/2, pz], C![-1/2, nz], C![pz, 2], C![pz, -2], C![nz, 2], C![pz, 1/2]];
for f in [* Exp, Log, Sin, Cos, Tan, Sinh, Cosh, Tanh, Arcsin, Arccos, Arctan, Argsinh, Argcosh, Argtanh *] do
  [<Real(f(p)), Imaginary(f(p))> : p in pts];
end for;
for f in [* Exp, Sin, Cos, Tan, Sinh, Cosh, Tanh, Arcsin, Arccos, Arctan, Argsinh, Argcosh, Argtanh *] do
  [<Real(f(p)), Imaginary(f(p))> : p in [C![pz, pz], C![nz, pz], C![pz, nz]]];
end for;
for f in [* Cot, Sec, Cosec, Coth, Sech, Cosech, Arccot, Arcsec, Arccosec, Argsech, Argcosech, Argcoth *] do
  [<Real(f(p)), Imaginary(f(p))> : p in pts];
end for;
v := Arctan(-i);
Real(v), Imaginary(v);
v := Argtanh(C![1, pz]);
Real(v), Imaginary(v);

// Poles and singular points.
Log(C!0);
Cot(C!0);
Cosech(C![nz, pz]);
Argcoth(C!0);
Arctan(i);

// Dilogarithm and polylogarithms: on the cut (1, infinity), the limit
// from below. (Magma 2.22 computes some of these with PARI, and its
// results for short arguments such as 1 or 3/4 are not accurate in
// fields of low precision.)
Dilog(z), Dilog(C![1/5, -1/7]);
CC := ComplexField();
Dilog(CC!1), Dilog(CC.1), Dilog(CC!2), Dilog(CC!-2);
Dilog(3);
Polylog(2, z), Polylog(3, u), Polylog(7, z);
Polylog(1, z), Polylog(2, R!3/2);
Polylog(3, 2/3);
Parent(Polylog(3, 2));
Polylog(0, z);
Polylog(1, C!1);
PolylogD(2, z), PolylogD(3, u), PolylogD(1, z), PolylogD(4, z);
PolylogD(3, R!1/3), PolylogD(3, R!-7/3), PolylogD(2, R!-7/3);
Parent(PolylogD(3, 1/2));
PolylogD(0, z);
// PolylogDold and PolylogP have no complex signatures in Magma 2.22;
// these follow the handbook.
PolylogDold(3, z), PolylogP(3, z), PolylogDold(4, u), PolylogP(4, u);
PolylogDold(3, R!1/3), PolylogP(4, R!-7/3), PolylogP(3, 1/5);
PolylogP(-1, R!1/3);
