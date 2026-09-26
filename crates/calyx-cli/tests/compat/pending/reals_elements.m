// Real and complex fields, element operations.
R := RealField(20); C<i> := ComplexField(20);
x := R!2/3; z := C![1/3, -2/5];
inf := (R!10)^1000000000; nan := inf - inf; nan, inf, -inf;

// Predicates: IsZero matches either zero; the others compare as Magma
// does (NaN equals everything).
IsZero(R!0), IsZero(-R!0), IsZero(nan), IsZero(C!0), IsZero(-C!0);
IsOne(R!1), IsOne(nan), IsOne(C!1), IsOne(i), IsMinusOne(-R!1), IsMinusOne(nan);
IsUnit(R!0), IsUnit(nan), IsUnit(inf), IsUnit(C!0), IsUnit(i);
IsZeroDivisor(x), IsZeroDivisor(z), IsIdempotent(R!1), IsIdempotent(C!0), IsIdempotent(x), IsNilpotent(R!0), IsNilpotent(C!0), IsNilpotent(z);
IsIdempotent(nan), IsNilpotent(nan), IsIdempotent(inf), IsIdempotent(-inf), IsIdempotent(C!1), IsIdempotent(i);
IsIrreducible(x), IsIrreducible(z), IsPrime(x), IsPrime(z);
IsIntegral(R!2), IsIntegral(x), IsIntegral(C!2), IsIntegral(z), IsIntegral(nan), IsIntegral(inf), IsIntegral(R!10^30), IsIntegral(C![2, 1]);
IsReal(z), IsReal(C!2), IsReal(C![2, 0]), IsReal(-C!2);

// Comparison and membership.
x in R, x in RealField(10), z in C, z in ComplexField(10), x in C, 1 in R, 1/2 in R, i in R;
x notin R, z notin C;
(C!2) in R; i in C; 1 in C; (R!2) in C;
z lt 1;
z ge z;
Maximum(x, R!1), Minimum(x, R!1), Maximum([x, R!1, R!0]), Minimum([x, R!1, R!0]);
Maximum(x, 1), Maximum(1, x), Maximum(RealField(10)!1, x), Maximum(x, RealField(10)!1);
Maximum([RealField(10)!1, x]);
Maximum(RealField(10)!0, x); Minimum(x, RealField(10)!1); Maximum([RealField(10)!0, x]);

// Arithmetic.
+x; +z; -x; -z; x + z; x - z; x*z; x/z; z/x; z^2; z^-3; z^x; x^z; z^z; (-x)^x;
x +:= 1; x; z +:= 1; z; z -:= i; z; z *:= i; z; z /:= 2; z; x ^:= 2; x; z ^:= z; z;
x := R!2/3; z := C![1/3, -2/5];
for n in [6, 7, 11, 13, 22, -6, -7, 100] do
  w := z^n; print n, MantissaExponent(Real(w)), MantissaExponent(Imaginary(w));
end for;
for n in [7, -5, 100, 12345] do
  w := x^n; print n, MantissaExponent(w);
end for;
w := (R!11/10)^100000; print MantissaExponent(w);
w := (C![11/10, 0])^1000; print MantissaExponent(Real(w)), MantissaExponent(Imaginary(w));
w := (C![-11/10, 0])^1001; print MantissaExponent(Real(w)), MantissaExponent(Imaginary(w));
w := (C![0, 11/10])^1001; print MantissaExponent(Real(w)), MantissaExponent(Imaginary(w));
(C![0, 11/10])^1001;
(C![-11/10, 0])^1001;
(C![11/10, 0])^-3;
for pq in [[1,3],[1,4],[1,5]] do
  p := pq[1]; q := pq[2];
  u := C![p/q, -q/(p+q)]^C![q/(p+7), 1/(q+3)]; print MantissaExponent(Real(u)), MantissaExponent(Imaginary(u));
end for;
w := x/z; MantissaExponent(Real(w)); MantissaExponent(Imaginary(w));
w := (C![3/7, 5/11])/(C![-2/13, 1/17]); MantissaExponent(Real(w)); MantissaExponent(Imaginary(w));
(R!2)^(1/2); (R!2)^(R!1/2); 2^(R!1/2); (1/2)^(R!2); (R!-8)^(1/3); (C!-8)^(1/3); (R!-8)^(C!1/3);
x^0; (R!0)^0; (C!0)^0; (C!0)^(C!0); (C!0)^(C!1); (C!0)^(C!-1);
(C!0)^-1;
(C!2)^1073741824;

// Conversions.
MantissaExponent(x); MantissaExponent(R!1); MantissaExponent(R!-3.5); MantissaExponent(R!0); MantissaExponent(-R!0);
MantissaExponent(RealField(10)!1/3); MantissaExponent(RealField(2 : Bits)!3); MantissaExponent(R!10^30); MantissaExponent(nan);
PolarToComplex(R!2, Pi(R)/3); PolarToComplex(2, 1); PolarToComplex(2, RealField(10)!1); PolarToComplex(RealField(10)!2, x); PolarToComplex(1/2, 1/3);
Parent(PolarToComplex(2, 1));
w := PolarToComplex(x, R!5/7); MantissaExponent(Real(w)); MantissaExponent(Imaginary(w));
w := PolarToComplex(R!3/2, R!-9/11); MantissaExponent(Real(w)); MantissaExponent(Imaginary(w));
Arg(z); Argument(z); Arg(C!0); Arg(-C!0); Arg(C![-1, 0]); Arg(-One(C)); Arg(x); Arg(-x); Arg(-R!0); Arg(R!0); Arg(nan); Arg(2);
Modulus(z); Modulus(x); Modulus(-x); Modulus(C![3, 4]); Modulus(2);
Real(z); Re(z); Imaginary(z); Im(z); Real(x); Imaginary(x); Re(2); Im(2); Real(1/2);
MantissaExponent(Norm(z)); MantissaExponent(Modulus(z)); MantissaExponent(Arg(z));

// Rounding.
Round(x); Round(-x); Round(R!2.5); Round(R!-2.5); Round(R!3.5); Round(R!10^25); Round(nan); Round(inf);
Truncate(x); Truncate(-x); Truncate(R!-2.5);
Ceiling(x); Ceiling(-x); Ceiling(R!-2.5); Ceiling(nan);
Floor(x); Floor(-x); Floor(R!-2.5); Floor(-inf);
Floor(Infinity()); Ceiling(MinusInfinity()); Round(Infinity()); Ceiling(Infinity()); Floor(MinusInfinity());
Truncate(Infinity());

// Precision.
Precision(x); Precision(z); BitPrecision(x); BitPrecision(z); Precision([x, x]); Precision([z]); Precision([x, RealField(10)!1]);
Precision([RealField(10)!1, x]);
BitPrecision([x]);
ChangePrecision(x, 5); ChangePrecision(z, 5); Parent(ChangePrecision(z, 5)); ChangePrecision(x, 40); ChangePrecision(RealField(5)!x, 30);

// Constants.
Catalan(R); Catalan(C); EulerGamma(R); EulerGamma(C); Pi(R); Pi(C); Parent(Pi(C));
Pi(RealField(100));

// Simple functions.
Abs(x); Abs(-x); Abs(z); AbsoluteValue(z); AbsoluteValue(-x); Abs(nan); Abs(-inf); Abs(-R!0); Parent(Abs(z));
Sign(x); Sign(-x); Sign(R!0); Sign(-R!0); Sign(nan); Sign(-inf);
ComplexConjugate(x); ComplexConjugate(z); Conjugate(z); ComplexConjugate(2);
Conjugate(x);
Norm(z); Norm(x); Norm(-x); Norm(C![3,4]); Parent(Norm(z)); Norm(2);
MantissaExponent(Norm(C![3/7, 5/11]));

// Roots.
Root(R!27, 3); Root(R!-27, 3); Root(R!16, 4); Root(x, 1); Root(1/2, 0); Root(x, 0);
Root(R!-16, 4);
Root(z, 3); Root(C!0, 3); Root(27, 3); Root(2, 2); Root(1/8, 3);
Root(-8, 3); Root(-8, 2); Root(-16, 4); Root(-1/16, 4); Root(-16, 6); Root(-27, 5); Root(-2, 2); Root(0, 2); Root(-8, 1);
Parent(Root(-8, 3)); Parent(Root(8, 3)); Parent(Root(-8, 2)); Parent(Root(1/8, 3)); Parent(Root(-1/8, 3)); Parent(Root(-8, 1));
for n in [2, 4, 5, 6] do print n, Root(C![-1, 0], n), "|", Root(-C!1, n); end for;
for n in [2, 3] do print n, Root(C![0, 1], n), "|", Root(C![0, -1], n), "|", Root(C![-1, 1], n), "|", Root(C![-1, -1], n), "|", Root(C![1, 1], n); end for;
Root(C![1, 1], 5);
for n in [2,3,5,7] do w := Root(z, n); print n, MantissaExponent(Real(w)), MantissaExponent(Imaginary(w)); end for;
for n in [2,3,5,7] do print n, MantissaExponent(Root(x, n)); end for;
SquareRoot(z); Sqrt(z); SquareRoot(x); Sqrt(-x); Sqrt(C!-4); Sqrt(-C!4); Sqrt(C![-4, -0]); Sqrt(-C!0); Sqrt(R!-0);
Sqrt(nan); Sqrt(inf);
w := Sqrt(z); MantissaExponent(Real(w)); MantissaExponent(Imaginary(w));
w := Sqrt(C![-3/7, 2/9]); MantissaExponent(Real(w)); MantissaExponent(Imaginary(w));
Sqrt(4); Sqrt(2); Sqrt(4/9); Sqrt(2/9); Sqrt(-4); Sqrt(-2); Sqrt(-2.0); Sqrt(0.0); Sqrt(-0.0);
Type(Sqrt(4)); Type(Sqrt(4/9));
SquareRoot(4); SquareRoot(2); Sqrt(1/4); SquareRoot(-1/4);
Parent(Sqrt(4)); Parent(Sqrt(-4));

// Distance and diameter.
L := [R!1, R!2.5, R!-3];
Distance(x, L); Distance(z, L); Distance(x, [z, C!1]); Distance(z, [z, C!1]);
Distance(x, L : Max := 1); Distance(R!100, L : Max := 1); Distance(R!100, L);
Diameter(L); Diameter([z, C!1, C!0]); Diameter(L : Max := 1); Diameter([R!1]); Diameter([R!1, R!1]);
Diameter([R!1, R!1, R!2]);
Distance(x, []);
Diameter([]);

// H26E5
C := ComplexField(30);
x := -One(C);
Imaginary(x); // imaginary part is negative zero
Arg(x); // approximately negative pi as Arg
y := C!-1; // coerce, so imag part is positive zero
Imaginary(y); // positive zero
Arg(y); // approximately positive pi as Arg
assert x eq y; // note that x and y are indeed equal!
