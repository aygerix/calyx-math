// Polynomials for finite fields: irreducible, sparse, primitive and
// Conway polynomials.
P<x> := PolynomialRing(GF(2));
P3<y> := PolynomialRing(GF(3));
P7<t> := PolynomialRing(GF(7));

// Irreducible polynomials: the Conway polynomial when there is one.
IrreduciblePolynomial(GF(2), 5), IrreduciblePolynomial(GF(7), 3), IrreduciblePolynomial(GF(3), 60);
IrreduciblePolynomial(GF(2), 1), IrreduciblePolynomial(GF(7), 1), IrreduciblePolynomial(GF(49), 1);
IrreduciblePolynomial(GF(5), 4) eq ConwayPolynomial(5, 4), IrreduciblePolynomial(GF(2), 16) eq ConwayPolynomial(2, 16);
Parent(IrreduciblePolynomial(GF(2), 5)) eq P, Parent(IrreduciblePolynomial(GF(7), 3)) eq P7;
// (Magma chooses random irreducible polynomials.)
f := RandomIrreduciblePolynomial(GF(7), 5); Degree(ext< GF(7) | f >), Parent(f) eq P7;
f := RandomIrreduciblePolynomial(GF(2), 30); Degree(ext< GF(2) | f >);

// Sparse irreducible polynomials over GF(2)
IrreducibleLowTermGF2Polynomial(1), IrreducibleLowTermGF2Polynomial(2), IrreducibleLowTermGF2Polynomial(3), IrreducibleLowTermGF2Polynomial(8);
IrreducibleLowTermGF2Polynomial(100), IrreducibleLowTermGF2Polynomial(1000), IrreducibleLowTermGF2Polynomial(2000);
IrreducibleLowTermGF2Polynomial(4096), IrreducibleLowTermGF2Polynomial(5000);
IrreducibleSparseGF2Polynomial(4), IrreducibleSparseGF2Polynomial(5), IrreducibleSparseGF2Polynomial(8), IrreducibleSparseGF2Polynomial(100);
IrreducibleSparseGF2Polynomial(1000), IrreducibleSparseGF2Polynomial(4096), IrreducibleSparseGF2Polynomial(12800);
IrreducibleSparseGF2Polynomial(12799) - x^12799;
Parent(IrreducibleLowTermGF2Polynomial(10)) eq P, Parent(IrreducibleSparseGF2Polynomial(10)) eq P;

// Primitive polynomials
PrimitivePolynomial(GF(2), 5), PrimitivePolynomial(GF(7), 3), PrimitivePolynomial(GF(2), 1), PrimitivePolynomial(GF(7), 1);
IsPrimitive(PrimitivePolynomial(GF(2), 20)), IsPrimitive(PrimitivePolynomial(GF(5), 6));

// All irreducible polynomials
Sort(Setseq(AllIrreduciblePolynomials(GF(2), 4)));
Sort(Setseq(AllIrreduciblePolynomials(GF(3), 2)));
#AllIrreduciblePolynomials(GF(2), 8), #AllIrreduciblePolynomials(GF(2), 1), #AllIrreduciblePolynomials(GF(7), 2);
x^4 + x + 1 in AllIrreduciblePolynomials(GF(2), 4), x^4 + x^2 + 1 in AllIrreduciblePolynomials(GF(2), 4);

// Conway polynomials
ConwayPolynomial(2, 10);
ConwayPolynomial(3, 7);
ConwayPolynomial(7, 1);
ConwayPolynomial(2, 1);
ConwayPolynomial(5, 12);
ConwayPolynomial(7, 4) eq DefiningPolynomial(GF(7^4)), ConwayPolynomial(2, 8) eq DefiningPolynomial(GF(2^8));
ExistsConwayPolynomial(5, 12);
ExistsConwayPolynomial(2, 1);
ExistsConwayPolynomial(3, 2);
b1, c := ExistsConwayPolynomial(2, 20); b1, c eq ConwayPolynomial(2, 20);

// errors
IrreduciblePolynomial(GF(7), 0);
IrreduciblePolynomial(GF(7), -1);
RandomIrreduciblePolynomial(GF(7), 0);
PrimitivePolynomial(GF(7), 0);
AllIrreduciblePolynomials(GF(7), 0);
IrreducibleLowTermGF2Polynomial(0);
IrreducibleLowTermGF2Polynomial(100001);
IrreducibleSparseGF2Polynomial(3);
IrreducibleSparseGF2Polynomial(12801);
IrreducibleSparseGF2Polynomial(-1);
ConwayPolynomial(6, 2);
ConwayPolynomial(7, 0);
ExistsConwayPolynomial(6, 2);
ExistsConwayPolynomial(7, 0);
