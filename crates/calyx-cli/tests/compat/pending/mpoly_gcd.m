// Multivariate polynomials: greatest common divisors, factorization,
// resultants and the functions for integer polynomials (handbook,
// Multivariate Polynomial Rings, sections on GCDs to Polynomials over the
// Integers).
P<x, y, z> := PolynomialRing(Integers(), 3);
f := (x + y)^2*(x - 2*z)*(3*y + 1);
g := (x + y)*(x - 2*z)^2*(2*x + 1);
GCD(f, g), Gcd(f, g), GreatestCommonDivisor(f, g);
GCD(-f, -g);
GCD(f, P!0), GCD(P!0, -g), GCD(P!0, P!0);
GCD(6*x*y, 4*x*z);
GCD([f, g, (x + y)*(x + 1)]);
GCD([P | ]);
LCM(f, g);
LCM(6*x*y, -4*x*z);
LCM(f, P!0);
LCM([x, y, z, x*y]);
LCM([P | ]);
Normalize(-2*x + 3), Normalize(P!0);
Content(-6*x*y + 4*z), PrimitivePart(-6*x*y + 4*z);
ContentAndPrimitivePart(10*x^2 - 15*y);
Contpp(P!0);

Q<a, b> := PolynomialRing(Rationals(), 2);
GCD(a^2 - b^2, 2*a + 2*b);
LCM(a/2, 3*b);
Normalize(-3/2*a + b);
Content(a/2 + 1/3), PrimitivePart(a/2 + 1/3);
ClearDenominators(a/2 + b/3 + 1/6);
ClearDenominators([a/2, b/3, Q!1]);
CoefficientDenominator(a/2 + b/3), CoefficientNumerator(a/2 + b/3);

G<u, v> := PolynomialRing(GF(7), 2);
GCD(u^2 - v^2, 3*u + 3*v);
Normalize(3*u + v);
F<w> := GF(9);
H<s, t> := PolynomialRing(F, 2);
GCD((s + w*t)*(s - t), (s + w*t)*(s + 1));
Normalize(w*s + t);

// Factorization.
Factorization(x^2 - y^2);
Factorization(-12*x^3*y + 12*x*y^3);
F2, unit := Factorization(-12*x^3*y + 12*x*y^3);
unit;
Factorization(P!6);
Factorization(x^4 + 4*y^4);
Factorization((x + y + z)^3*(x - y)^2);
SquarefreeFactorization(12*(x + y + z)^3*(x - y)^2*(x + z));
SquarefreePart(12*(x + y + z)^3*(x - y)^2*(x + z));
IsIrreducible(x^2 + y^2), IsIrreducible(x^2 - y^2), IsIrreducible(2*x + 2*y), IsIrreducible(-x + 2);
IsIrreducible(P!7), IsIrreducible(P!1), IsIrreducible(P!-1), IsIrreducible(2*x);
IsPrime(x^2 + y^2), IsPrime(P!7);
Factorization(P!0);
IsIrreducible(P!0);
Factorization(a^2 - 4*b^2);
Factorization(3/2*a^2*b - 3/2*b);
Factorization(u^2 + v^2);
Factorization(u^7 - v^7);
Factorization(s^2 - w*t^2);
Factorization(s^9 - t^9);

// Resultants and discriminants.
Resultant(x^2 + y^2 - 1, x - y, x);
Resultant(x^2 + y^2 - 1, x - y, 2);
Discriminant(x^2 + y*x + z, x);
Discriminant(x^3 + y*x + z, 1);
Resultant(a^2 + b, a*b - 1, a);
Discriminant(u^3 + v, u);

// Polynomials over the integers.
Sign(-3*x + y), Sign(3*x - y), Sign(P!0);
AbsoluteValue(-3*x + y), Abs(3*x - y);
MaxNorm(-7*x + 5*y - 2), SumNorm(-7*x + 5*y - 2);
Sign(a);
MaxNorm(a);
Abs(a);
Sign(P!0), Abs(P!0), MaxNorm(P!0), SumNorm(P!0);
