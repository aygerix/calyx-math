// Elliptic and modular functions: Eisenstein series, Jacobi's theta
// function, Dedekind's eta function, the j-invariant, the discriminant and
// Weber's functions.
//
// Magma 2.22 computes the Eisenstein series and the modular functions with
// errors of a few units in the last place, and gives values that are real
// a tiny imaginary part. So these are computed in ComplexField(30) and
// printed rounded to 20 digits, and real values by their real part.
// (Its Eisenstein series are also far off when Im(t) is small.) Jacobi's
// theta function is computed with PARI, and correctly rounded.

C<i> := ComplexField(30);
D<I> := ComplexField(20);
R := RealField(20);
t1 := C![1/3, 4/5]; t2 := C![-2/7, 3/2]; t3 := C![1/5, 1/10];

// Eisenstein series: E_k(t), normalized with constant term 1.
for t in [t1, t2] do
  [D!Eisenstein(k, t) : k in [2, 4, 6, 12, 14]];
end for;
Parent(Eisenstein(4, t1)), Parent(Eisenstein(4, D!t1));

// The handbook's example: the value is real.
v := Eisenstein(4, 2.5 + i);
R!Real(v), Abs(Imaginary(v)) lt 10^-25;
R!Real(Eisenstein(4, i)), Abs(Eisenstein(6, i)) lt 10^-25, R!Real(Eisenstein(8, i));

// Dedekind's eta function, the j-invariant, the discriminant and Weber's
// functions.
for t in [t1, t2, t3] do
  D!DedekindEta(t), D!Delta(t);
  D!WeberF(t), D!WeberF1(t), D!WeberF2(t);
end for;
D!jInvariant(t1), D!jInvariant(t2);
// Real values at special points.
rho := C![-1/2, Sqrt(RealField(30)!3)/2];
[R!Real(jInvariant(t)) : t in [i, 2*i, t3, i + 1/2]], Abs(jInvariant(rho)) lt 10^-25;
R!Real(DedekindEta(i)), R!Real(Delta(i)), R!Real(WeberF(i)), R!Real(WeberF1(i)), R!Real(WeberF2(i));
Parent(DedekindEta(D!t1)), Parent(jInvariant(t1));

// Lattices [a, b]: the value at a/b or b/a, whichever is in the upper half
// plane.
L := [C![2, 1], C![1, -3]];
D!Eisenstein(4, L), D!Eisenstein(6, L), D!Eisenstein(2, L);
D!jInvariant(L), D!Delta(L);
L2 := [L[2], L[1]];
D!Eisenstein(4, L2), D!jInvariant(L2), D!Delta(L2);
R!Real(Eisenstein(4, [1, i])), R!Real(Delta([i, C!1]));
Parent(jInvariant([ComplexField(10)![2, 1], ComplexField(10)![1, -3]]));
// A sequence of integers or rationals is taken as a complex number.
R!Real(jInvariant([1, 2])), R!Real(jInvariant([1/2, 2]));

// Jacobi's theta function.
q := R!1/3; z := R!2/5;
x := JacobiTheta(q, z); x, Parent(x);
x := JacobiTheta(D![1/4, 1/5], D![1/2, -1/3]); x, Parent(x);
JacobiTheta(D!-1/2, D!1), JacobiTheta(D![0, 1/2], D!1);
JacobiTheta(q, R!10^6), JacobiTheta(q, R!0), JacobiTheta(R!0, z), JacobiTheta(q, -z);
// Arguments of different types or precisions: the default precision.
// (Magma 2.22 returns these as constant power series.)
JacobiTheta(1/3, 2/5);
JacobiTheta(q, D!2/5);
JacobiTheta(RealField(10)!1/3, z);

// Its derivatives at 0 (also for negative k).
[JacobiThetaNullK(q, k) : k in [-5, -3, -1, 0, 1, 2, 3, 5, 7]];
JacobiThetaNullK(q, 101), JacobiThetaNullK(q, -101);
x := JacobiThetaNullK(1/3, 3); x, Parent(x);
x := JacobiThetaNullK(D!1/3, 3); x, Parent(x);
JacobiThetaNullK(RealField(40)!1/3, 5);

// Errors.
Eisenstein(-2, t1);
Eisenstein(0, t1);
Eisenstein(3, t1);
Eisenstein(2^30, t1);
Eisenstein(4, C!1);
Eisenstein(4, C![1, -1]);
DedekindEta(C![1, -1]);
jInvariant(C!0);
Delta(C!-1);
WeberF(C!1);
WeberF1(C![1, -1]);
WeberF2(C!0);
jInvariant([C!1, C!2]);
jInvariant([C!1, C!2, i]);
jInvariant([i]);
Delta([C!1]);
Delta([C!1, C!0]);
Eisenstein(4, [1, 2]);
Eisenstein(3, [C!1, C!2]);
jInvariant([1, -2]);
jInvariant([1, 2, 3]);
JacobiTheta(R!1, R!1);
JacobiTheta(D![0, 1], D!2);
JacobiTheta(1, 2);
JacobiThetaNullK(R!1, 3);
JacobiThetaNullK(D![1/4, 1/5], 3);
