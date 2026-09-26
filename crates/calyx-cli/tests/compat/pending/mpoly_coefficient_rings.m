// Multivariate polynomials over other coefficient rings: polynomial
// rings, whose polynomials are flattened into one multivariate ring,
// composite residue class rings and the real field (handbook,
// Multivariate Polynomial Rings, GCDs, Factorization and Resultants).
PQ<u> := PolynomialRing(Rationals()); M<a, b> := PolynomialRing(PQ, 2);
F, U := Factorization(-2*u*a^2 + 2*u*b^2); F, U, Parent(U);
F, U := Factorization(-6*u*a^2*b + 6*u*b^3); F, U;
F, U := Factorization(M!(2*u^2)); F, U;
IsIrreducible(M!u), IsIrreducible(a + u), IsIrreducible(u*a + u);
Content(-2*u*a^2 + 2*u*b^2), PrimitivePart(-2*u*a^2 + 2*u*b^2);
Gcd(-2*u*a^2 + 2*u*b^2, 3*u^2*a - 3*u^2*b), Lcm(u*a, 2*u^2*b);
Resultant(a^2 - u*b, a - b, a), Resultant(a^2 - u*b, a - b, 2);
Discriminant(a^2 - u*b, a);
SquarefreeFactorization(u*(a - b)^2*(a + u)), SquarefreePart(u*(a - b)^2*(a + u));
IsDivisibleBy(u*a^2 - u*b^2, a - b), ExactQuotient(u*a^2 - u*b^2, u*a - u*b);
(u*a^2 - u*b^2) div (a - b);

PZ<w> := PolynomialRing(Integers()); MZ<a, b> := PolynomialRing(PZ, 2);
F, U := Factorization(-6*w*a^2 + 6*w*b^2); F, U, Parent(U);
Gcd(6*w*a^2 - 6*w*b^2, 4*w^2*a - 4*w^2*b), Content(6*w*a^2 - 6*w*b^2);
Resultant(a^2 - w*b, a - b, a), Discriminant(a^2 - w*b, a);

// A composite residue class ring.
M6<a, b> := PolynomialRing(Integers(6), 2);
Content(2*a^2 + 4*b), PrimitivePart(2*a^2 + 4*b);
Resultant(a^2 + 5*b, a + 2, a), Discriminant(a^2 + 5*b, a);
Gcd(a^2 + 5*b, a + 2);
Factorization(a^2 + 5*b);
SquarefreeFactorization(a^2 + 5*b);
SquarefreePart(a^2 + 5*b);
IsIrreducible(a^2 + 5*b);

// The real field.
MR<a, b> := PolynomialRing(RealField(20), 2);
f := (a - 2*b)^2*(a + b); g := (a - 2*b)*(a + 2*b);
Content(f), PrimitivePart(f);
IsDivisibleBy(f, a - 2*b), ExactQuotient(f, a - 2*b);
Gcd(f, g);
Factorization(f);
SquarefreeFactorization(f);
IsIrreducible(f);
Resultant(a^2 - b, a - 2*b, a), Resultant(a^2 - b, a - 2*b, 2);
Resultant(a^2 + 1.5*a*b - b^3, 3*a - b + 0.25, a);
Resultant((a - 2*b)*(a + b), (a - 2*b)*(a + 3), a);
Resultant(MR!3, a^2 + b, a), Resultant(MR!0, a^2 + b, a), Resultant(a*b + 1, MR!2, 1);
Discriminant(a^2 - b, a), Discriminant(a^3 + b*a + 1.5, a);
Discriminant(2*a^2 + b*a + 1/3, 1), Discriminant((a - b)^2*(a + 1), a);
Discriminant(a + b, a), Discriminant(MR!2, a);

// The complex field.
MC<u, v> := PolynomialRing(ComplexField(20), 2);
i := ComplexField(20).1;
Resultant(u^2 + i*v, u - v, u);
Discriminant(u^2 + i*v + 1, u), Discriminant(u^3 - v, u);

// Discriminants in a variable of degree at most 1.
P<a, b> := PolynomialRing(Rationals(), 2);
Discriminant(P!2, a), Discriminant(P!0, a), Discriminant(b + 1, a), Discriminant(3*b^2, 1);
Discriminant(a + b, a), Discriminant(3*a + b, a), Discriminant(b*a + 1, a);
Z<c, d> := PolynomialRing(Integers(), 2);
Discriminant(Z!2, c), Discriminant(Z!0, c), Discriminant(d + 1, c), Discriminant(3*c + d, c);
F<e, h> := PolynomialRing(GF(7), 2);
Discriminant(F!2, e), Discriminant(h + 1, e), Discriminant(3*e + h, e);
M<m, n> := PolynomialRing(PQ, 2);
Discriminant(M!(2*PQ.1), m), Discriminant(PQ.1*m + n, m);
