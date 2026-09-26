// Predicates on matrices: zero, identity, scalar, diagonal, symmetric,
// Hermitian, triangular and integral symplectic matrices.

I2 := Matrix(Integers(), 2, 2, [1,0,0,1]);
B := Matrix(Integers(), 2, 3, [1,0,0,0,1,0]);
v := Vector([1,2]);

// Zero, one and minus one
IsZero(I2); IsZero(ZeroMatrix(Integers(), 2, 3)); IsZero(v); IsZero(Vector([0,0]));
IsOne(I2); IsOne(-I2); IsOne(Matrix(Integers(), 0, 0, [])); IsOne(Vector([1]));
IsOne(B);
IsOne(v);
IsMinusOne(-I2); IsMinusOne(I2); IsMinusOne(Matrix(GF(2), 2, 2, [1,0,0,1]));
IsMinusOne(B);

// Scalar, diagonal and symmetric matrices, which must be square
IsScalar(3*I2); IsScalar(Matrix(2,2,[1,2,3,4])); IsScalar(Matrix(Integers(), 0, 0, []));
IsScalar(Matrix(GF(5), 2, 2, [3,0,0,3])); IsScalar(Matrix(RealField(10), 2, 2, [1.5,0,0,1.5]));
IsScalar(B);
IsScalar(v);
IsDiagonal(Matrix(2,2,[1,0,0,5])); IsDiagonal(Matrix(2,2,[1,1,0,5]));
IsDiagonal(B);
IsDiagonal(Matrix(2,3,[1,0,0,0,5,0]));
IsDiagonal(Vector([1,0]));
IsSymmetric(Matrix(2,2,[1,2,2,3])); IsSymmetric(Matrix(2,2,[1,2,3,3]));
IsSymmetric(Matrix(RealField(10), 2, 2, [1,0,-(RealField(10)!0),1]));
IsSymmetric(B);
IsSymmetric(v);

// Triangular matrices of any shape
IsUpperTriangular(Matrix(2,2,[1,2,0,3])); IsUpperTriangular(Matrix(2,2,[1,2,1,3]));
IsUpperTriangular(Matrix(2,3,[1,2,3,0,4,5])); IsUpperTriangular(Matrix(3,2,[1,2,0,3,0,0]));
IsUpperTriangular(Matrix(3,2,[1,2,0,3,1,0])); IsUpperTriangular(v); IsUpperTriangular(Matrix(2,1,[1,1]));
IsLowerTriangular(Matrix(2,2,[1,0,2,3])); IsLowerTriangular(Matrix(2,2,[1,2,1,3]));
IsLowerTriangular(Matrix(2,3,[1,0,0,4,5,0])); IsLowerTriangular(Matrix(2,3,[1,0,1,4,5,0]));
IsLowerTriangular(Matrix(3,2,[1,0,3,4,5,6]));
IsLowerTriangular(Vector([1]));
IsLowerTriangular(v);

// Hermitian matrices for an involution
F<w> := GF(4); f := hom<F -> F | w^2>;
IsHermitian(Matrix(F, 2, 2, [1, w, w^2, 1]), f);
IsHermitian(Matrix(F, 2, 2, [1, w, w, 1]), f);
IsHermitian(Matrix(F, 2, 2, [w, 0, 0, 1]), f);
g := map<Integers() -> Integers() | x :-> x>;
IsHermitian(Matrix(Integers(), 2, 2, [1, 2, 2, 1]), g);
IsHermitian(Matrix(Integers(), 2, 2, [1, 2, 3, 1]), g);

// Integral symplectic matrices, for J = [0 I; -I 0]
IsSymplecticMatrix(Matrix(Integers(), 2, 2, [1,1,0,1]));
IsSymplecticMatrix(Matrix(Integers(), 2, 2, [2,0,0,1]));
IsSymplecticMatrix(Matrix(Integers(), 4, 4, [1,0,1,0, 0,1,0,0, 0,0,1,0, 0,0,0,1]));
IsSymplecticMatrix(Matrix(Integers(), 4, 4, [1,1,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1]));
IsSymplecticMatrix(Matrix(Integers(), 4, 4, [1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,1,1]));
IsSymplecticMatrix(Matrix(Integers(), 3, 3, [1,0,0,0,1,0,0,0,1]));
IsSymplecticMatrix(Matrix(Integers(), 0, 0, []));
IsSymplecticMatrix(RandomSymplecticMatrix(3, 5));
IsSymplecticMatrix(Matrix(Rationals(), 2, 2, [1,0,0,1]));
IsSymplecticMatrix(Matrix(Integers(), 2, 3, [1,0,0,0,1,0]));
IsSymplecticMatrix(Matrix(GF(5), 2, 2, [1,0,0,1]));

// Parameters: the triangular and symplectic predicates are written in
// Magma's language
IsZero(I2 : Foo := 1);
IsOne(I2 : Foo := 1);
IsMinusOne(I2 : Foo := 1);
IsScalar(I2 : Foo := 1);
IsDiagonal(I2 : Foo := 1);
IsSymmetric(I2 : Foo := 1);
IsUpperTriangular(I2 : Foo := 1);
IsLowerTriangular(I2 : Foo := 1);
IsSymplecticMatrix(I2 : Foo := 1);
