// Real and complex fields, introduction: precision, mixed precisions,
// special values, the default real field and the name of sqrt(-1).
S1 := RealField(20);
S2 := RealField(10);
a := S1 ! 0.5;
a;
b := S2 ! 0.05;
b;
a + b;
Precision(a + b);

// Mixed precisions: the more precise operand is first rounded to the
// smaller precision; integers and rationals go into the real's field.
a := RealField(10)!(1/3); b := RealField(30)!(1/3);
a eq b; b eq a; a lt b; b gt a; a - b; b - a; Parent(a-b);
c := RealField(10)!(2/3); d := RealField(30)!(2/3); c eq d; c - d;
x := RealField(10)!2; x eq 2; 2 eq x; x eq 2/1; x eq RealField(30)!2;
Parent(1/3 + x); Parent(x + 1); 1/3 + x;
{1.5, 1.5, 3/2};
{1.5, RealField(10)!1.5};
[1.5, 1]; [1, 1.5]; [1/2, 1.5];

// Infinities and NaN (MPFR semantics; NaN compares equal to everything).
e := 10.0^1000000000; e; -e; e eq e; e gt 1; -e lt 1;
n := e*0; n; n eq n; n eq 1; n lt 1; n gt 1;
Sign(n); Sign(e); Sign(-e); Sign(-0.0); Sign(0.0);
IsZero(-0.0); -0.0 eq 0.0; -0.0 lt 0.0; Abs(-0.0);
Floor(e); Round(n); Parent(e);
10.0^-1000000000;
(10.0^1000000000)*0;
x := 1.5; x ^ 100000;

// Division by zero and powers.
x/0;
x/0.0;
0.0/0.0;
1/0.0;
x^-1; x^0; 0.0^0; 0.0^-1; (-1.5)^2; (-1.5)^0.5; 2.0^0.5; 2^0.5; (1/2)^0.5; 0.0^0.5; 0.0^0.0;
(-8.0)^(1/3);
x^(1/2); 2^1.5;
(RealField(20)!2)^1073741823;
(RealField(20)!2)^1073741824;
(RealField(20)!2)^-1073741824;
(RealField(20)!1)^(10^20);

// The default real field.
GetDefaultRealField();
SetDefaultRealField(RealField(15));
1.5; RealField(); ComplexField(); Sqrt(2); Pi(RealField()); Parent(1.5);
SetDefaultRealField(RealField(30));
1.5;

// The name of sqrt(-1): shared by the complex fields of a precision.
C := ComplexField(); C; C.1; Name(C, 1);
D := ComplexField(); D.1;
E<j> := ComplexField(); j; C.1;
AssignNames(~C, ["k"]); C.1; j; E.1;
F := ComplexField(20); F.1; Sqrt(F!-1);
G<ii> := ComplexField(25); ii; G;
ComplexField(25).1;
H := ComplexField(25); H.1;
print ComplexField(25) : Magma;
Sprint(ComplexField(25).1, "Magma");
