// Real and complex fields, structure operations.
R := RealField(20); C := ComplexField(20);
Category(R); Category(C); Parent(R); Parent(C); PrimeField(R); PrimeField(C);
Characteristic(R); Characteristic(C);
IsCommutative(R), IsUnitary(R), IsFinite(R), IsOrdered(R), IsField(R), IsEuclideanDomain(R), IsPID(R), IsUFD(R), IsDivisionRing(R), IsEuclideanRing(R), IsPrincipalIdealRing(R), IsDomain(R);
IsCommutative(C), IsUnitary(C), IsFinite(C), IsOrdered(C), IsField(C), IsEuclideanDomain(C), IsPID(C), IsUFD(C), IsDivisionRing(C), IsEuclideanRing(C), IsPrincipalIdealRing(C), IsDomain(C);
R eq RealField(20); R ne RealField(21); C eq ComplexField(20); C ne ComplexField(20);
R eq C;
Precision(R); Precision(C); BitPrecision(R); BitPrecision(C);
Precision(ComplexField(64 : Bits)); BitPrecision(ComplexField(64 : Bits));
Type(R); Type(C); Type(R!1); Type(C!1);
ExtendedType(R); ExtendedType(C!1);
print R : Magma; print C : Magma;
