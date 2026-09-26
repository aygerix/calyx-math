// Elementary properties of matrices and access to their entries
// (H27E4, H27E5, H27E6): indexing, blocks, row and column operations.

// H27E4
X := Matrix(4, [1,2,3,4, 5,4,3,2, 1,2,3,4]);
X;
X[1];
X[1, 2];
X[1, 2] := 23;
X;
X[3] := Vector([9,8,7,6]);
X[2] := 0;
X;

// H27E5
A := Matrix(6,
    [ 9, 1, 7, -3, 2, -1,
      3, -4, -5, 9, 2, 7,
      7, 1, 0, 1, 8, 22,
      -3, 3, 3, 8, 8, 37,
      -9, 0, 7, -1, 2, 3,
      7, 2, -2, 4, 3, 47 ]);
A;
Submatrix(A, 2,2, 3,3);
SubmatrixRange(A, 2,2, 3,3);
S := $1;
InsertBlock(~A, S, 5,5);
A;
RowSubmatrix(A, 5, 2);
RowSubmatrixRange(A, 2, 3);
RowSubmatrix(A, 2, 0);

// H27E6
A := Matrix(5, 6,
    [ 3, 1, 0, -4, 2, -12,
      2, -4, -5, 5, 23, 6,
      8, 0, 0, 1, 5, 12,
      -2, -6, 3, 8, 9, 17,
      11, 12, -6, 4, 2, 27 ]);
A;
SwapColumns(~A, 1, 2);
A;
AddRow(~A, 4, 1, 2);
AddRow(~A, 6, 1, 4);
AddRow(~A, -12, 1, 5);
A;
RemoveRow(~A, 1);
A;
RemoveRowColumn(~A, 4, 6);
A;

// Elementary properties
B := Matrix(GF(7), 2, 3, [0, 1, 0, 3, 0, 0]);
Nrows(B), Ncols(B), NumberOfRows(B), NumberOfColumns(B);
NNZEntries(B), NumberOfNonZeroEntries(B), Density(B);
BaseRing(B), CoefficientRing(B);
Eltseq(B); ElementToSequence(B);
RowSequence(B);
Density(ZeroMatrix(Integers(), 0, 3));
v := Vector([4, 5, 6]);
Nrows(v), Ncols(v), Eltseq(v), v[2];
v[2] := 7; v;
X := Matrix(2, [1,2,3,4]);
X[[2,1]];
X[1..2];
X[2..1];
X[2][1];
X[2][1] := 5; X;
X[1, 1] +:= 10; X;

// Blocks
C := Matrix(3, [1..9]);
Submatrix(C, [1,3], [3,1]);
Submatrix(C, [2,1], [2,1,2]);
ExtractBlock(C, 2, 1, 2, 2);
ExtractBlockRange(C, 1, 2, 2, 3);
ColumnSubmatrix(C, 2, 2);
ColumnSubmatrix(C, 1);
ColumnSubmatrixRange(C, 2, 3);
RowSubmatrix(C, 2);
InsertBlock(C, Matrix(1, [0, 0]), 3, 2);
C;
Submatrix(C, 3, 2, 0, 0);
Submatrix(C, 4, 4, 0, 0);

// Row and column operations as functions
SwapRows(C, 1, 3);
ReverseRows(C);
ReverseColumns(C);
AddColumn(C, -1, 1, 3);
MultiplyRow(C, 10, 2);
MultiplyColumn(C, -1, 1);
RemoveColumn(C, 2);
RemoveZeroRows(Matrix(3, [0,0, 1,2, 0,0]));
C;
D := C;
SwapRows(~D, 1, 2);
ReverseColumns(~D);
MultiplyRow(~D, 2, 3);
MultiplyColumn(~D, 3, 1);
AddColumn(~D, 1, 1, 2);
RemoveColumn(~D, 3);
RemoveZeroRows(~D);
D, C;

// Errors
X := Matrix(2, [1,2,3,4]);
v := Vector([1,2,3]);
X[3];
X[1, 5];
X[0];
X[1,2,1];
X[[1,2,5]];
v[4];
v[1,1];
SwapRows(X, 1, 3);
SwapColumns(X, 0, 1);
Submatrix(X, 2, 2, 3, 3);
Submatrix(X, 4, 2, 0, 0);
SubmatrixRange(X, 1, 1, 3, 3);
SubmatrixRange(X, 2, 2, 0, 0);
RowSubmatrix(X, 3, 1);
RowSubmatrix(X, 3);
RowSubmatrixRange(X, 1, 3);
AddRow(X, 2, 1, 3);
AddRow(X, 1/2, 1, 2);
MultiplyRow(X, 2, 3);
RemoveRow(X, 3);
RemoveColumn(X, 0);
RemoveRowColumn(X, 1, 3);
InsertBlock(X, Matrix(1, [1,2,3]), 1, 1);
InsertBlock(X, Matrix(GF(2), 1, [1]), 1, 1);
X[1,1] := 1/2;
X[1] := Vector([1,2,3]);
X[1] := [1,2];
X[1] := 5;
v[1] := 1/2;
v[4] := 1;
X[3,1] := 1;
X[1,3] := 1;
X;
Submatrix(X, [1,3], [1]);
Submatrix(X, [1], [0]);

// Parameters: RowSequence, Density and Submatrix with sequences are
// written in Magma's language and report them without the argument types
X := Matrix(Rationals(), 2, 2, [1,2,3,4]);
RowSequence(X : Foo := 1);
Density(X : Foo := 1);
Submatrix(X, [1], [1] : Foo := 1);
Submatrix(X, 1, 1, 1, 1 : Foo := 1);
NumberOfRows(X : Foo := 1);
SwapRows(~X, 1, 2 : Foo := 1);
