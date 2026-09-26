// Univariate polynomials over the integers: sign, absolute value, norms
// and Dedekind's criterion (handbook, Univariate Polynomial Rings,
// Polynomials over the Integers).
P<x> := PolynomialRing(Integers());
f := -3*x^4 + 5*x^2 - x + 7;
Sign(f), Sign(-f), Sign(P!0), Sign(P!-2);
Abs(f), AbsoluteValue(-f), Abs(P!0), Abs(P!-2);
MaxNorm(f), MaxNorm(P!0), MaxNorm(P!-9), MaxNorm(x^3 - 100*x);
SumNorm(f), SumNorm(P!0), SumNorm(P!-9), SumNorm(x^3 - 100*x);
[DedekindTest(x^2 + 1, p) : p in [2, 3, 5]];
[DedekindTest(x^2 - 5, p) : p in [2, 3, 5]];
[DedekindTest(x^3 - 2, p) : p in [2, 3, 5, 7]];
[DedekindTest(x^3 + x^2 - 2*x + 8, p) : p in [2, 3, 5]];
[DedekindTest(x^2 + 3, p) : p in [2, 3]];
DedekindTest(P!1, 2), DedekindTest(x, 2);
DedekindTest(2*x^2 + 1, 2);
S<y> := PolynomialRing(Rationals());
DedekindTest(y^2 + 1, 2);
Sign(-y);
Abs(y);
MaxNorm(y);
SumNorm(y);
