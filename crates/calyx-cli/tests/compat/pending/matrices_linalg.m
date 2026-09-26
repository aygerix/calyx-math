// Linear algebra: rank, determinant and trace, minors, cofactors, the
// adjoint and Pfaffians, echelon and Hermite forms, and the nullspaces
// and solutions of linear systems over fields, the integers and Z/nZ.

// H27E8: all the solutions of V*X = W over GF(3)
K := GF(3);
X := Matrix(K, 4, 3, [1,2,1, 2,2,2, 1,1,1, 1,0,1]);
X;
W := Vector(K, [0,1,0]);
V, N := Solution(X, W);
V;
N;
[V + U: U in N];
[(V + U)*X eq W: U in N];

// H27E10: an echelon form over GF(8), and the rank and Hermite form of
// a matrix over Z
K<w> := GF(8);
A := Matrix(K, 4, 3, [1,w,w^5, 0,w^3,w^4, w,1,w^6, w^3,1,w^4]);
A;
EchelonForm(A);
A := Matrix(4, 5,
    [ 2,-4,12,7,0,
      3,-3,5,-1,4,
      2,-1,-4,-5,-12,
      0,3,6,-2,0]);
A;
Rank(A);
HermiteForm(A);

// A nullspace over Z, after H27E7
m := 31; n := 30;
X := Matrix(n, [(i^3 + 7*i^2 + i) mod 101 - 50 : i in [1 .. m*n]]);
N := NullspaceMatrix(X);
Nrows(N), Ncols(N);
IsZero(N*X);
{#Sprint(N[1,i]): i in [1..Ncols(N)]};

// Transpose and AddScaledMatrix
A := Matrix(Integers(), 2, 3, [1,2,3, 4,5,6]);
B := Matrix(Integers(), 2, 3, [1,0,1, 0,1,0]);
Transpose(A);
Parent(Transpose(A));
AddScaledMatrix(A, 2, B);
Parent(AddScaledMatrix(A, 2, B));
AddScaledMatrix(~A, -1, B);
A;
C := Matrix(Integers(), 2, 2, [1,2,3,4]);
AddScaledMatrix(C, 3, C);
AddScaledMatrix(Matrix(GF(5), 2, 2, [1,2,3,4]), 7, Matrix(GF(5), 2, 2, [1,1,1,1]));
x := AddScaledMatrix(Vector([1,2]), 2, Vector([3,4]));
x, Parent(x);
AddScaledMatrix(C, 1/2, C);
AddScaledMatrix(A, 2, C);
AddScaledMatrix(Matrix(Integers(), 2, 2, [1,2,3,4]), 2, Matrix(Integers(), 3, 2, [1,2,3,4,5,6]));
AddScaledMatrix(C, 2, Matrix(Rationals(), 2, 2, [1,2,3,4]));

// Rank, determinant and trace
A := Matrix(Integers(), 3, 3, [1,2,3, 4,5,6, 7,8,10]);
Rank(A), Determinant(A), Trace(A);
Rank(Matrix(Integers(), 3, 3, [1,2,3, 4,5,6, 7,8,9]));
TraceOfProduct(A, Transpose(A));
Determinant(Matrix(Rationals(), 2, 2, [1/2, 1/3, 1/4, 1/5]));
Determinant(Matrix(GF(7), 3, 3, [1,2,3, 4,5,6, 7,8,10]));
Rank(Matrix(GF(2), 3, 3, [1,1,0, 0,1,1, 1,0,1]));
Determinant(Matrix(Integers(), 0, 0, []));
Rank(Matrix(Integers(), 0, 3, []));
Rank(Matrix(Integers(12), 2, 2, [2, 4, 3, 6]));
P<x> := PolynomialRing(Integers());
Determinant(Matrix(P, 2, 2, [x, 1, 1, x]));
IsUnit(Matrix(Integers(), 2, 2, [2, 1, 1, 1])), IsUnit(Matrix(Integers(), 2, 2, [2, 0, 0, 1]));
IsSingular(Matrix(GF(5), 2, 2, [1, 2, 2, 4])), IsSingular(Matrix(GF(5), 2, 2, [1, 2, 3, 4]));
Determinant(Matrix(Integers(), 2, 3, [1,2,3, 4,5,6]));

// Rank and echelon form over the reals
R := RealField(10);
A := Matrix(R, 2, 2, [1.5,2,3,4]);
Rank(A);
EchelonForm(A);
Rank(Matrix(R, 3, 3, [1/3, 2/3, 1, 1, 2, 3, 2, 4, 6]));
Rank(Matrix(R, 2, 2, [0.1, 0.2, 0.3, 0.6]));
Rank(Matrix(ComplexField(10), 2, 2, [1, 2, 3, 4]));

// Rank over polynomial rings
P<x,y> := PolynomialRing(Rationals(), 2);
Rank(Matrix(P, 2, 2, [x, y, x^2, x*y]));
Rank(Matrix(P, 2, 3, [2*x, 2*y, 0, y, x, 1]));
Rank(Matrix(P, 3, 3, [x, y, x+y, x^2, x*y, x^2+x*y, 1, 0, 1]));
Q<a,b,c> := PolynomialRing(Integers(), 3);
Rank(Matrix(Q, 3, 3, [b*c, a*c, a*b, 1, 1, 1, a, b, c]));
U<t> := PolynomialRing(Rationals());
Rank(Matrix(U, 2, 2, [t, t^2, 1, t]));
F<u,v> := PolynomialRing(GF(5), 2);
Rank(Matrix(F, 2, 2, [u, v, 5*u, v]));

// Minors, cofactors and the adjoint
A := Matrix(Integers(), 4, 4, [1,2,3,4, 5,6,7,8, 9,10,12,11, 13,15,14,16]);
Minor(A, 2, 3);
Minor(A, [1,2], [2,4]);
Cofactor(A, 2, 3);
Minors(A, 2);
Cofactors(A, 2);
Minors(A, 3);
Cofactors(A);
Minors(Matrix(Integers(), 3, 4, [1,2,3,4,5,6,7,9,9,1,2,3]), 2);
Adjoint(A);
A * Adjoint(A) eq ScalarMatrix(4, Determinant(A));
Adjoint(Matrix(Integers(), 3, 3, [1,2,3, 2,4,6, 1,1,1]));
Adjoint(Matrix(GF(5), 2, 2, [1,2,3,4]));

// Pfaffians
M := Matrix(Integers(), 4, 4, [0,1,2,3, -1,0,4,5, -2,-4,0,6, -3,-5,-6,0]);
Pfaffian(M), Determinant(M);
Pfaffians(M, 4);
Pfaffians(M, 3);
N := Matrix(Integers(), 6, 6, [0,0,2,3,4,5, 0,0,6,7,8,9, -2,-6,0,10,11,12,
    -3,-7,-10,0,13,14, -4,-8,-11,-13,0,15, -5,-9,-12,-14,-15,0]);
Pfaffian(N), Determinant(N);
P<a,b,c,d,e,f> := PolynomialRing(Rationals(), 6);
Pfaffian(Matrix(P, 4, 4, [0,a,b,c, -a,0,d,e, -b,-d,0,f, -c,-e,-f,0]));
Pfaffian(Matrix(GF(2), 2, 2, [1,1,1,1]));
Pfaffian(Matrix(Integers(6), 4, 4, [0,1,2,3, -1,0,4,5, -2,-4,0,1, -3,-5,-1,0]));
Pfaffian(Matrix(RealField(10), 4, 4, [0,1.1,2.3,3.7, -1.1,0,4.9,5.3, -2.3,-4.9,0,6.1, -3.7,-5.3,-6.1,0]));
Pfaffian(Matrix(Integers(), 0, 0, []));
Pfaffian(Matrix(GF(7), 3, 3, [0,1,2, -1,0,3, -2,-3,0]));
Pfaffian(M, [1,3], [1,3]);
Pfaffian(M, [2,1,3,4], [2,1,3,4]);
Pfaffian(Matrix(Integers(), 2, 2, [1, 2, 3, 4]));
x := Pfaffian(Matrix(Integers(), 2, 3, [0, 1, 2, -1, 0, 3]));
Pfaffians(M, 0);
x := Pfaffians(M, 5);

// Echelon forms over fields, Z and Z/nZ
A := Matrix(GF(7), 3, 4, [1,2,3,4, 2,4,6,1, 3,6,2,5]);
E, T := EchelonForm(A);
E;
T;
T*A eq E;
A := Matrix(Rationals(), 3, 3, [1,2,3, 4,5,6, 7,8,10]);
E, T := EchelonForm(A);
E;
T;
EchelonForm(Matrix(Rationals(), 2, 3, [1/2, 1, 3/2, 2, 4, 6]));
EchelonForm(Matrix(Integers(), 3, 3, [2,4,6, 1,3,5, 0,1,2]));
H, T := HermiteForm(Matrix(Integers(), 3, 3, [2,4,6, 1,3,5, 0,1,2]));
H;
T*Matrix(Integers(), 3, 3, [2,4,6, 1,3,5, 0,1,2]) eq H;
EchelonForm(Matrix(Integers(12), 3, 3, [0,2,9, 0,11,0, 0,1,0]));
EchelonForm(Matrix(Integers(36), 4, 1, [12,0,18,12]));
EchelonForm(Matrix(Integers(10), 3, 4, [2,8,8,5, 0,1,1,9, 1,1,3,6]));
Rank(Matrix(Integers(10), 3, 4, [2,8,8,5, 0,1,1,9, 1,1,3,6]));

// Nullspaces
A := Matrix(GF(5), 3, 2, [1,2, 2,4, 3,1]);
Kernel(A);
KernelMatrix(A);
Nullspace(Matrix(GF(5), 2, 2, [1,2, 3,4]));
NullspaceOfTranspose(Matrix(GF(5), 2, 3, [1,2,3, 2,4,6]));
Kernel(Matrix(Rationals(), 3, 3, [1,2,3, 4,5,6, 7,8,9]));
Kernel(Matrix(Integers(), 3, 3, [1,2,3, 4,5,6, 7,8,9]));
KernelMatrix(Matrix(Integers(), 4, 2, [2,4, 3,6, 1,2, 5,10]));
Basis(Kernel(Matrix(Integers(12), 3, 3, [0,2,9, 0,11,0, 0,1,0])));
Basis(Kernel(Matrix(Integers(4), 3, 2, [2,0, 0,1, 2,0])));

// Solutions over fields
A := Matrix(Rationals(), 3, 2, [1,2, 3,4, 5,6]);
V, N := Solution(A, Vector(Rationals(), [1, 1]));
V;
N;
IsConsistent(A, Vector(Rationals(), [1, 1]));
b, V := IsConsistent(A, Vector(Rationals(), [1, 1]));
b, V;
Solution(A, [Vector(Rationals(), [1, 1]), Vector(Rationals(), [0, 2])]);
Solution(A, Matrix(Rationals(), 2, 2, [1, 1, 0, 2]));
IsConsistent(Matrix(Rationals(), 2, 2, [1, 2, 2, 4]), Vector(Rationals(), [1, 1]));
IsConsistent(Matrix(GF(7), 2, 2, [1, 2, 3, 4]), Vector(GF(7), [1, 1]));
Solution(Matrix(GF(7), 3, 3, [1,2,3, 2,4,6, 1,1,1]), Vector(GF(7), [1, 1, 1]));
V := Solution(Matrix(Rationals(), 5, 4, [-9,1,1,5, -13,11,18,-29, -17,12,19,-23, -7,4,6,-5, 14,-5,-9,14]), Vector(Rationals(), [49,-26,-41,41]));
V;
V := Solution(Matrix(Rationals(), 4, 3, [-2,-2,1, 2,2,-1, 2,2,8, -3,-3,-3]), Vector(Rationals(), [-1,-1,14]));
V;

// Solutions over Z
Solution(Matrix(Integers(), 2, 2, [2, 0, 0, 3]), Vector(Integers(), [4, 9]));
IsConsistent(Matrix(Integers(), 2, 2, [2, 0, 0, 3]), Vector(Integers(), [4, 8]));
V := Solution(Matrix(Integers(), 5, 4, [-9,1,1,5, -13,11,18,-29, -17,12,19,-23, -7,4,6,-5, 14,-5,-9,14]), Vector(Integers(), [49,-26,-41,41]));
V;
V := Solution(Matrix(Integers(), 3, 2, [13,16, -2,-8, 15,24]), Vector(Integers(), [6,24]));
V;
b := IsConsistent(Matrix(Integers(), 2, 1, [2, 4]), Vector(Integers(), [3]));
b;

// Solutions over Z/nZ
IsConsistent(Matrix(Integers(4), 2, 2, [1,1, 0,1]), Vector(Integers(4), [3,2]));
IsConsistent(Matrix(Integers(18), 1, 1, [9]), Vector(Integers(18), [8]));

// Sequences of vectors: the nullspace comes too, and a failure names the
// vector
B := Matrix(Rationals(), 3, 2, [1,2, 2,4, 3,6]);
IsConsistent(B, [Vector(Rationals(), [1, 2])]);
IsConsistent(B, [Vector(Rationals(), [1, 2]), Vector(Rationals(), [1, 1])]);
Solution(B, [Vector(Rationals(), [1, 2]), Vector(Rationals(), [1, 1])]);
Solution(Matrix(GF(7), 3, 2, [1,2, 2,4, 3,6]), [Vector(GF(7), [1, 1])]);
IsConsistent(Matrix(Integers(), 2, 2, [2, 1, 0, 3]), [Vector(Integers(), [4, 5]), Vector(Integers(), [2, 7])]);
IsConsistent(Matrix(Integers(6), 3, 2, [1,2, 2,4, 3,0]), [Vector(Integers(6), [1, 2])]);

// Parameters: those of Rank, Determinant, HermiteForm and the kernels are
// checked; minors, cofactors and Pfaffians are written in Magma's language
M := Matrix(Rationals(), 2, 2, [1,2,3,4]);
Z := Matrix(Integers(), 3, 2, [1,2,3,4,5,6]);
Rank(M : Proof := false, MonteCarloLevel := 1);
Rank(M : Foo := 1);
Rank(M : Proof := 1);
Rank(M : pAdic := true);
Determinant(M : Proof := false);
Determinant(M : MonteCarloLevel := false);
Determinant(M : pAdic := 1);
Determinant(M : Divisor := false);
HermiteForm(Z : Al := "Classical", Optimize := false, InitialSort := true);
HermiteForm(Z : Al := "Foo");
HermiteForm(Z : Al := 1);
HermiteForm(Z : Integral := 1);
KernelMatrix(Z : Al := "LLL");
NullspaceMatrix(Z : Al := "Modular");
Kernel(Z : Al := "Hermite");
Kernel(M : Al := "Foo");
KernelMatrix(M : Al := 1);
Nullspace(M : Al := "Default");
EchelonForm(M : Foo := 1);
Minor(M, 1, 1 : Foo := 1);
Minors(M, 1 : Foo := 1);
Cofactors(M : Foo := 1);
Pfaffian(M : Foo := 1);
Pfaffians(M, 2 : Foo := 1);
Adjoint(M : Foo := 1);
Trace(M : Foo := 1);

// Without a solution, IsConsistent leaves the other values unassigned
A := Matrix(Rationals(), 2, 2, [1, 2, 2, 4]);
w := Vector(Rationals(), [1, 1]);
IsConsistent(A, w);
V := 5;
b, V := IsConsistent(A, w);
b;
V;
b, V2, N2 := IsConsistent(A, w);
N2;
b, V3 := IsConsistent(A, [w]);
V3;
b, V4 := IsConsistent(A, Matrix(Rationals(), 1, 2, [1, 1]));
V4;
procedure p(A, w)
  b, U := IsConsistent(A, w);
  b;
  assigned U;
end procedure;
p(A, w);
x, y := IsConsistent(A, Vector(Rationals(), [1, 2]));
x, y;
IsConsistent(A, Vector(Rationals(), [1, 2]));
