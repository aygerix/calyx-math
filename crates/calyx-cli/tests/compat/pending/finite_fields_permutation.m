// Permutation polynomials: Dickson polynomials and the probabilistic test
// for permutation polynomials.

// H22E6, leaving out the counts of values (Evaluate is in the polynomial
// chapter)
Factorization(16^2 - 1);
K<w> := GF(16);
R<x> := PolynomialRing(K);
a := w^5;
p1 := DicksonFirst(3, a);
p1;
IsProbablyPermutationPolynomial(p1);
p1 := DicksonFirst(4, a);
p1;
IsProbablyPermutationPolynomial(p1);

// Dickson polynomials over other rings
DicksonFirst(1, 3), DicksonFirst(2, 3), DicksonFirst(5, 3), DicksonFirst(6, -1), DicksonFirst(7, 1/2);
DicksonSecond(1, 3), DicksonSecond(2, 3), DicksonSecond(5, 3), DicksonSecond(6, -1), DicksonSecond(7, 1/2);
DicksonFirst(5, GF(7)!3), DicksonSecond(5, GF(7)!3), DicksonFirst(7, a), DicksonSecond(7, a), DicksonFirst(9, GF(3)!1);
Parent(DicksonFirst(3, 2)), Parent(DicksonFirst(3, GF(5)!2)) eq PolynomialRing(GF(5)), Parent(DicksonFirst(3, a)) eq R;
DicksonFirst(5, 0), DicksonSecond(5, 0), DicksonFirst(4, Integers(8)!3), DicksonFirst(10, 1/3);
DicksonFirst(0, 3), DicksonSecond(0, 3), DicksonFirst(0, GF(7)!2), DicksonSecond(0, GF(7)!2), DicksonFirst(1, 0);

// The permutation test
P5<y> := PolynomialRing(GF(5));
IsProbablyPermutationPolynomial(y^3), IsProbablyPermutationPolynomial(y^2), IsProbablyPermutationPolynomial(y), IsProbablyPermutationPolynomial(y + 2);
IsProbablyPermutationPolynomial(2*y^3 + 1), IsProbablyPermutationPolynomial(y^5), IsProbablyPermutationPolynomial(y^5 - y), IsProbablyPermutationPolynomial(P5!3);
IsProbablyPermutationPolynomial(DicksonFirst(5, a)), IsProbablyPermutationPolynomial(DicksonFirst(7, a)), IsProbablyPermutationPolynomial(x^2), IsProbablyPermutationPolynomial(x^3);
IsProbablyPermutationPolynomial(y^3 : NumAttempts := 10), IsProbablyPermutationPolynomial(y^4 : NumAttempts := 1000);
IsProbablyPermutationPolynomial(y^3 : NumAttempts := 2^30 - 1), IsProbablyPermutationPolynomial(PolynomialRing(GF(7^2)).1^0);
Q<z> := PolynomialRing(GF(2^100));
IsProbablyPermutationPolynomial(z^2), IsProbablyPermutationPolynomial(z^3), IsProbablyPermutationPolynomial(z^7 + z);
T<v> := PolynomialRing(GF(1000003));
IsProbablyPermutationPolynomial(v^5), IsProbablyPermutationPolynomial(v^3);

// errors
DicksonSecond(-1, 3);
DicksonFirst(2^30, 1);
IsProbablyPermutationPolynomial(PolynomialRing(Integers()).1^3);
IsProbablyPermutationPolynomial(PolynomialRing(Rationals()).1);
IsProbablyPermutationPolynomial(y^3 : NumAttempts := 0);
IsProbablyPermutationPolynomial(y^3 : NumAttempts := -1);
IsProbablyPermutationPolynomial(y^3 : NumAttempts := 2^30);
