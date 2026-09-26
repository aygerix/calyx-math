// The examples of the Rational Field chapter of the handbook (H21E1 to
// H21E3), without the line of H21E1 that needs cyclotomic fields, and the
// natural homomorphisms from Q.
1/2 - 0.12345;
1/2 * 2;
Parent(1/2 * 2);
R<x> := PolynomialRing(Integers());
// The following produces an error:
1/2 + x;
Z11 := Integers(11);
Q := RationalField();
h := hom< Q -> Z11 | >;
h(1/2);
Numerator(10/-4);
Denominator(10/-4);

// natural homomorphisms from Q
h;
h(3); h(0); h(-5/3);
h(1/11);
h(Z11!3);
6 @@ h;
Type(h); Domain(h); Codomain(h);
Z11!(1/2); Z11!(-5/3); GF(11)!(1/2);
Z11!(1/11);
Integers(12)!(1/5);
Integers(12)!(1/2);
GF(11)!(1/11);
h := hom< Q -> Integers() | >; h; h(4/2);
h(1/2);
h := hom< Q -> Q | >; h; h(1/2);
h := hom< Q -> GF(7) | >; h; h(1/2);
h := hom< Q -> RealField(20) | >; h; h(1/3);
h := hom< Q -> Integers(12) | >; h(1/5);
h(1/2);
h := hom< Q -> {1, 2} | >;
h := hom< Q -> Z11 | 1 >;
h := hom< Q -> Z11 | x :-> x >; h; h(1/2);
