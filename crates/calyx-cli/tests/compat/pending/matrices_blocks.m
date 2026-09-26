// Building block matrices (joins, block matrices, Kronecker products) and
// changing the ring of matrices and vectors.

A := Matrix(Integers(), 2, 2, [1,2,3,4]);
B := Matrix(Integers(), 2, 3, [5,6,7,8,9,10]);
C := Matrix(Rationals(), 1, 2, [1/2, 3]);
v := Vector([1,2]); w := Vector([3]);

// Joins of two matrices: the results are in the algebra or space of their
// shape, even for vectors
HorizontalJoin(A, B);
Parent($1);
VerticalJoin(A, Matrix(Integers(), 1, 2, [0, 1]));
Parent($1);
DiagonalJoin(A, B);
Parent($1);
Parent(DiagonalJoin(A, A));
Parent(HorizontalJoin(Matrix(2,1,[1,2]), Matrix(2,1,[3,4])));
HorizontalJoin(v, w);
Parent($1);
VerticalJoin(v, Vector([5,6]));
Parent($1);
VerticalJoin(v, A);
DiagonalJoin(v, w);
Parent(HorizontalJoin(v, v));
Parent(DiagonalJoin(v, v));
F := GF(4);
Parent(HorizontalJoin(Matrix(F, 1, 1, [F.1]), Matrix(F, 1, 1, [1])));
Parent(VerticalJoin(Matrix(RealField(10), 1, 1, [1.5]), Matrix(RealField(10), 1, 1, [2])));
DiagonalJoin(Matrix(Integers(), 0, 0, []), Matrix(Integers(), 0, 1, []));
HorizontalJoin(Matrix(Integers(), 0, 2, []), Matrix(Integers(), 0, 1, []));
Parent($1);
Parent(DiagonalJoin(B, Matrix(Integers(), 1, 0, [])));

// Joins of sequences and tuples
HorizontalJoin(<A, B>);
VerticalJoin([A, A]);
Parent($1);
VerticalJoin(<A, Matrix(Integers(), 1, 2, [7,7])>);
DiagonalJoin(<A, B, A>);
HorizontalJoin([A, A, A]);
VerticalJoin(<A, v, v>);
HorizontalJoin([A]);
VerticalJoin(<A>);
DiagonalJoin([A]);
Parent(HorizontalJoin([A]));
Parent(DiagonalJoin(<v>));
HorizontalJoin(<Vector([1,2])>);
Parent($1);

// Errors of joins
VerticalJoin(A, C);
VerticalJoin(C, A);
HorizontalJoin(A, Matrix(Integers(), 3, 1, [1,2,3]));
VerticalJoin(A, B);
HorizontalJoin(A, Matrix(GF(5), 2, 1, [1,2]));
DiagonalJoin(A, Matrix(GF(5), 1, 1, [1]));
HorizontalJoin(A, Matrix(GF(5), 3, 1, [1,2,3]));
VerticalJoin(A, Matrix(GF(5), 1, 3, [1,2,3]));
VerticalJoin(Matrix(RealField(10), 1, 1, [1.5]), Matrix(RealField(20), 1, 1, [2]));
VerticalJoin(Matrix(GF(5), 1, 1, [1]), Matrix(GF(5, 2), 1, 1, [2]));
HorizontalJoin(v, A);
HorizontalJoin(<A, v>);
HorizontalJoin(<A, Matrix(GF(5), 3, 1, [1,2,3])>);
HorizontalJoin(<A, Matrix(GF(5), 2, 1, [1,2])>);
HorizontalJoin(<A, A, Matrix(Integers(), 3, 1, [1,2,3])>);
VerticalJoin(<A, 1>);
VerticalJoin(<1, A>);
DiagonalJoin(<A, "x">);
HorizontalJoin(<>);
DiagonalJoin(<>);
HorizontalJoin([]);
VerticalJoin([]);
HorizontalJoin([Integers()|]);
HorizontalJoin([A, B, A]);

// Kronecker products
KroneckerProduct(A, B);
Parent($1);
Parent(KroneckerProduct(A, A));
KroneckerProduct(v, v);
Parent(KroneckerProduct(v, v));
KroneckerProduct(v, Matrix(2, 1, [1, 2]));
Parent($1);
KroneckerProduct(Matrix(Integers(), 0, 2, []), A);
F<w> := GF(4);
KroneckerProduct(Matrix(F, 1, 2, [w, 1]), Matrix(F, 2, 1, [w, w^2]));
KroneckerProduct(Matrix(RealField(10), 1, 1, [1.5]), Matrix(RealField(10), 1, 2, [2, -1]));
KroneckerProduct(A, Matrix(GF(5), 1, 1, [1]));
KroneckerProduct(A, C);

// Block matrices from a list of blocks or from rows of blocks; missing
// blocks at the ends of rows are zero
BlockMatrix(2, 2, [A, A, A, A]);
Parent(BlockMatrix(2, 2, [A, A, A, A]));
BlockMatrix(2, 2, [A, A, A, A, A]);
BlockMatrix(1, 1, [A]);
Parent(BlockMatrix(1, 1, [A]));
BlockMatrix(2, 2, [[A, A], [A, A]]);
BlockMatrix([[A, A], [A, A]]);
BlockMatrix(2, 2, [[A, A], [A]]);
BlockMatrix(1, 2, [[A, A]]);
BlockMatrix([[A, A], [A, A], [A, A]]);
BlockMatrix([[B, B]]);
BlockMatrix([[v, v], [v, v]]);
Parent($1);
BlockMatrix(2, 1, [Matrix(1, 2, [1, 2]), Matrix(1, 2, [3, 4])]);
BlockMatrix(1, 1, [Matrix(Integers(), 0, 0, [])]);
BlockMatrix([[Matrix(Integers(), 2, 0, [])], [Matrix(Integers(), 2, 0, [])]]);

// Errors of block matrices
BlockMatrix(1, 2, [A, B]);
BlockMatrix([[A, B], [B, A]]);
BlockMatrix(2, 2, [A, A, A]);
BlockMatrix(1, 2, [A]);
BlockMatrix(2, 2, [1, 2, 3, 4]);
BlockMatrix(2, 2, [GF(5)!1, 2, 3, 4]);
BlockMatrix(2, 1, [A, C]);
BlockMatrix([[A], [C]]);
BlockMatrix(2, 1, [[A, A]]);
BlockMatrix(2, 2, [[A, A]]);
BlockMatrix(3, 3, [[A]]);
BlockMatrix(1, 1, [[A, A]]);
BlockMatrix(2, 2, [[A, A], [A, A], [A, A]]);
BlockMatrix(1, 2, [[A], [A]]);
BlockMatrix(1, 2, [[Matrix(GF(5), 1, 1, [1])]]);
BlockMatrix([[A], [A, A]]);
BlockMatrix(0, 0, []);
BlockMatrix(-1, 2, [A]);

// Changing the ring: ChangeRing keeps the shape, Matrix(R, A) gives a
// matrix in the algebra or space of its shape
ChangeRing(A, Rationals());
Parent($1);
ChangeRing(A, GF(5));
ChangeRing(A, Integers());
ChangeRing(A, Integers(6));
ChangeRing(B, GF(2));
Parent($1);
ChangeRing(Matrix(Rationals(), 1, 1, [2]), Integers());
ChangeRing(Matrix(Integers(6), 1, 1, [5]), Integers());
ChangeRing(Matrix(GF(5), 1, 1, [3]), Integers());
ChangeRing(Matrix(GF(5), 1, 1, [3]), GF(25));
ChangeRing(Matrix(GF(25), 1, 1, [3]), GF(5));
ChangeRing(Matrix(Rationals(), 1, 2, [1/2, 1]), GF(5));
ChangeRing(Matrix(Rationals(), 1, 1, [1/2]), Integers(7));
ChangeRing(Matrix(Rationals(), 1, 1, [1/3]), RealField(10));
ChangeRing(Matrix(Integers(), 1, 1, [2]), PolynomialRing(Integers()));
Parent($1);
ChangeRing(v, Rationals());
Parent($1);
X := RMatrixSpace(Integers(), 2, 2) ! [1,2,3,4];
Parent(ChangeRing(X, Rationals()));
Parent(Matrix(Rationals(), X));
Matrix(Rationals(), A);
Matrix(GF(7), A);
Parent($1);
Matrix(Rationals(), Vector([1,2]));
Parent($1);
Matrix(Vector([1,2]));
Parent($1);

// Errors of changing rings
ChangeRing(C, Integers());
Matrix(Integers(), C);
ChangeRing(Matrix(GF(25), 1, 1, [GF(25).1]), GF(5));
ChangeRing(Matrix(Rationals(), 1, 2, [1/5, 1]), GF(5));
ChangeRing(Matrix(Rationals(), 1, 1, [1/2]), Integers(6));
ChangeRing(Matrix(RealField(10), 1, 1, [1.5]), Rationals());

// CanChangeRing
CanChangeRing(C, Integers());
CanChangeRing(A, GF(5));
CanChangeRing(A, Integers());
CanChangeRing(Matrix(Rationals(), 1, 1, [2]), Integers());
CanChangeRing(Matrix(Rationals(), 1, 2, [1/5, 1]), GF(5));
CanChangeRing(v, GF(5));
b, Y := CanChangeRing(X, GF(5)); Parent(Y);

// Changing the ring by a map
f := map<Integers() -> GF(5) | x :-> x^2>;
ChangeRing(A, GF(5), f);
ChangeRing(A, f);
Parent($1);
ChangeRing(v, f);
Parent($1);
Parent(ChangeRing(X, Coercion(Integers(), Rationals())));
ChangeRing(Matrix(Integers(), 1, 2, [1, 2]), Coercion(Integers(), Rationals()));
Parent($1);
P<x> := PolynomialRing(Rationals());
e := hom<P -> Rationals() | 2>;
ChangeRing(Matrix(P, 2, 2, [x, x^2, 1, x+1]), e);
ChangeRing(Matrix(P, 2, 2, [x, x^2, 1, x+1]), Rationals(), e);
ChangeRing(Matrix(Integers(), 1, 2, [1, 2]), map<Integers() -> Integers() | x :-> 2*x>);
ChangeRing(Matrix(Integers(), 1, 2, [1, 2]), map<Integers() -> Rationals() | x :-> 1/(x+1)>);
ChangeRing(A, Rationals(), f);
ChangeRing(A, Integers(5), f);
ChangeRing(Matrix(Rationals(), 1, 1, [1/2]), f);
ChangeRing(Matrix(Rationals(), 1, 1, [1/2]), Rationals(), f);
ChangeRing(Matrix(P, 2, 2, [x, x^2, 1, x+1]), Rationals());

// Parameters: BlockMatrix is written in Magma's language
HorizontalJoin(A, A : Foo := 1);
VerticalJoin([A, A] : Foo := 1);
DiagonalJoin(<A, A> : Foo := 1);
KroneckerProduct(A, A : Foo := 1);
BlockMatrix(1, 1, [A] : Foo := 1);
BlockMatrix([[A]] : Foo := 1);
ChangeRing(A, Rationals() : Foo := 1);
ChangeRing(A, f : Foo := 1);
Matrix(Rationals(), A : Foo := 1);
CanChangeRing(A, Rationals() : Foo := 1);
