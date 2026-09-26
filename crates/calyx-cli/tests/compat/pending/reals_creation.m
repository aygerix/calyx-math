// Real and complex fields, creation functions: fields of a precision in
// decimal digits or bits, generic elements and coercion.
R := RealField(100 : Bits := true); R; Precision(R); BitPrecision(R);
R eq RealField(30);
R := RealField(34 : Bits := true); R; Precision(R); BitPrecision(R); R eq RealField(10);
R := RealField(35 : Bits := true); R; Precision(R); BitPrecision(R); R eq RealField(10);
R := RealField(33 : Bits := true); R; Precision(R); BitPrecision(R);
R := RealField(1 : Bits := true);
R := RealField(2 : Bits := true); R; Precision(R); BitPrecision(R);
R := RealField(3 : Bits := true); R; Precision(R); BitPrecision(R);
R := RealField(4 : Bits := true); R; Precision(R); BitPrecision(R);
R := RealField(10 : Bits := true); R; Precision(R); BitPrecision(R); R!1/3;
R := RealField(53 : Bits := true); R; Precision(R); BitPrecision(R); R!1/3;
R := RealField(64 : Bits := true); R; Precision(R); BitPrecision(R); R!1/3;
C := ComplexField(64 : Bits := true); C; Precision(C); BitPrecision(C);
[BitPrecision(RealField(p)) : p in [1..40]];
RealField(0);
RealField(-3);
ComplexField(0);

// H26E3
C<i> := ComplexField(20);
Pi(C)+ 1/4*i;
AssignNames(~C, ["k"]);
Pi(C)+ 1/4*i;
k := Name(C, 1);
Pi(C)+ 1/4*k;

// Generic elements (zeros are positive).
R := RealField(20); C := ComplexField(20);
One(R); One(C); Identity(R); Identity(C); Zero(R); Zero(C); Representative(R); Representative(C);
Parent(One(C)); Parent(Zero(R));
ComplexField(R); ComplexField(RealField(7 : Bits));
RealField(C);

// Coercion.
S := RealField(15); S!Pi(R); R!Pi(S);
C!Pi(R); C!Pi(S); Parent(C!Pi(S));
C![Pi(S), 1];
C![1/3, 2/3];
C![R!1, C.1];
C!"abc";
R!"1.5";
R![1,2];
Rationals()!(R!2);
Integers()!(R!2);
Integers()!(C!2);
R!C![1,0];
R!(C!1);
IsCoercible(R, 1/3); IsCoercible(C, 1/3); IsCoercible(R, C.1); IsCoercible(C, R!2);
IsCoercible(C, [R!1, C.1]); IsCoercible(C, [1, 2]);
C![C.1, 1];
z := ComplexField(10)![1,2]; z; Parent(z);
ComplexField(10)![1];
ComplexField(10)!<1,2>;
ComplexField(10)![1,2,3];
RealField(10)!ComplexField(10)![1,0];
RealField(10)!ComplexField(10)![1,2];
Integers()!ComplexField(10)![1,0];
Integers()!RealField(10)!2.5;
Integers()!RealField(10)!2;
Rationals()!RealField(10)!2.5;
Rationals()!RealField(10)!2;
Rationals()!(1/3.0);
