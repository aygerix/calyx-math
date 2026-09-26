// Univariate polynomials over other coefficient rings: polynomial rings,
// whose polynomials are flattened into multivariate ones, composite
// residue class rings and the real and complex fields (handbook,
// Univariate Polynomial Rings, Common Divisors, Factorization and Roots).
PQ<u> := PolynomialRing(Rationals()); PP<v> := PolynomialRing(PQ);
F, U := Factorization(2*u*v^2 - 2*u^3); F, U, Parent(U);
F, U := Factorization(-3*v^2 + 3*u^2); F, U;
Factorization(PP!(u^2 - 1)), Factorization(PP!3);
IsIrreducible(PP!u), IsIrreducible(PP!2), IsIrreducible(2*v + 2*u), IsIrreducible(u*v + u);
Gcd(PP!0, 2*u*v + 2*u), Gcd(PP!(2*u), PP!(4*u^2)), Gcd(-2*u*v^2 + 2*u, 3*u*v - 3*u);
Lcm(2*u*v, 3*u^2);
Content(-2*u*v^2 + 2*u), PrimitivePart(-2*u*v^2 + 2*u);
Roots((2*v - u)*(v + 1)*(u*v - 1));
Normalize(-2*u*v + 1);

PZ<w> := PolynomialRing(Integers()); PZZ<z> := PolynomialRing(PZ);
F, U := Factorization(-6*z^2 + 6*w^2); F, U, Parent(U);
Roots((2*z - w)*(z + 1)*(z - w^2));
IsIrreducible(2*z + 2*w), IsIrreducible(z + w), IsIrreducible(PZZ!w);
Content(-6*w*z^2 + 6*w), PrimitivePart(-6*w*z^2 + 6*w);
Gcd(-6*w*z^2 + 6*w, 4*w^2*z - 4*w^2), Lcm(-6*w*z + 6*w, 4*w^2*z);
Discriminant(z^2 - w), Resultant(z^2 - w, z - w);

F9<g> := GF(9); PF<h> := PolynomialRing(F9); PFF<y> := PolynomialRing(PF);
Factorization(y^2 - h), Factorization(y^3 - h^3), Gcd(y^3 - h^3, y^2 - h^2);

MQ<c, d> := PolynomialRing(Rationals(), 2); PM<e> := PolynomialRing(MQ);
Factorization(c*e^2 - c*d^2), Gcd(c*e^2 - c*d^2, 2*c^2*e - 2*c^2*d);
Roots((e - c*d)*(c*e - d)), Content(2*c*e^2 - 2*c*d^2), Discriminant(e^2 - c*d);

PPP<s> := PolynomialRing(PP);
Factorization(s^2 - u^2*v^2), Gcd(s^2 - v^2, s - v);

// Composite residue class rings.
P6<x> := PolynomialRing(Integers(6));
f := (x - 2)^2*(x + 1); g := (x - 2)*(x + 2);
Gcd(f, g);
Factorization(f);
SquarefreeFactorization(f);
Content(2*x^2 + 4), PrimitivePart(2*x^2 + 4);
Resultant(f, g), Discriminant(f);
P4<x> := PolynomialRing(Integers(4));
SquarefreeFactorization(x^2 + 1);
IsIrreducible(x^2 + 1);
Roots(x^2 + 3);
SquarefreeFactorization(v^2 - u^2);

// The real and complex fields: Xgcd by the Euclidean algorithm, but no
// gcds or factorization.
R := RealField(20); P<x> := PolynomialRing(R);
f := (x - 2)^2*(x + 1); g := (x - 2)*(x + 2);
Xgcd(f, g);
d, a, b := Xgcd(f, g); a*f + b*g eq d;
Xgcd(f, P!0), Xgcd(P!0, 2*x - 1);
f div g, f mod g, IsDivisibleBy(f, x - 2), ExactQuotient(f, x - 2);
Normalize(2*f), Discriminant(f);
Gcd(f, g);
Lcm(f, g);
Factorization(f);
IsIrreducible(f);
Content(f);
PrimitivePart(f);
C<i> := ComplexField(20); Q<y> := PolynomialRing(C);
Xgcd((y - 2)^2*(y + 1), (y - 2)*(y + 2));
Xgcd(y^2 + 1, y - i);
Gcd(y^2 + 1, y - i);
Factorization(y^2 + 1);
Content(y^2 + 1);
