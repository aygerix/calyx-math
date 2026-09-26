// Special families of univariate polynomials: orthogonal polynomials,
// Dickson (permutation) polynomials, Bernoulli and Swinnerton-Dyer
// polynomials (handbook, Univariate Polynomial Rings, Special Families of
// Polynomials).
for f in [ChebyshevFirst, ChebyshevT, ChebyshevSecond, ChebyshevU, LegendrePolynomial, LaguerrePolynomial, HermitePolynomial, BernoulliPolynomial] do
  [f(n) : n in [0..5]];
  Parent(f(3));
end for;
ChebyshevT(10);
ChebyshevU(10);
LegendrePolynomial(7);
LaguerrePolynomial(4);
HermitePolynomial(6);
BernoulliPolynomial(8);
LaguerrePolynomial(3, 2);
LaguerrePolynomial(3, 1/2);
Parent(LaguerrePolynomial(3, 1/2));
LaguerrePolynomial(3, GF(7)!2);
Parent(LaguerrePolynomial(3, GF(7)!2));
LaguerrePolynomial(2, 2.5);
LaguerrePolynomial(3, -1), LaguerrePolynomial(3, -3);
LaguerrePolynomial(7, GF(7)!2), LaguerrePolynomial(8, GF(7)!2);
GegenbauerPolynomial(3, 2);
GegenbauerPolynomial(4, 1/2);
Parent(GegenbauerPolynomial(3, 2));
GegenbauerPolynomial(3, GF(5)!2);
GegenbauerPolynomial(0, 3), GegenbauerPolynomial(1, 3), GegenbauerPolynomial(3, -1);
GegenbauerPolynomial(2, 0.5);
Parent(GegenbauerPolynomial(2, 0.5));
GegenbauerPolynomial(5, GF(5)!1);
LaguerrePolynomial(2, Integers(6)!5);
GegenbauerPolynomial(2, Integers(6)!5);
DicksonFirst(5, 1);
DicksonFirst(5, 2);
DicksonFirst(0, 2), DicksonFirst(1, 2), DicksonFirst(3, 0), DicksonFirst(6, -1);
Parent(DicksonFirst(5, 2));
DicksonFirst(5, GF(7)!3);
Parent(DicksonFirst(5, GF(7)!3));
DicksonFirst(4, 1/2);
DicksonSecond(5, 1);
DicksonSecond(5, 2);
DicksonSecond(0, 2), DicksonSecond(1, 2);
DicksonSecond(6, GF(7)!3);
DicksonSecond(3, Integers(6)!5);
Parent(DicksonSecond(3, Integers(6)!5));
P<x> := PolynomialRing(Integers());
DicksonFirst(3, x);
Parent(DicksonFirst(3, x));
ChebyshevT(0), ChebyshevU(0), LegendrePolynomial(0), HermitePolynomial(0), BernoulliPolynomial(0);
ChebyshevT(1), BernoulliPolynomial(1);
Parent(ChebyshevT(1)) eq P;
// Dickson polynomials permute GF(q) when gcd(n, q^2 - 1) = 1.
F := GF(11);
#{Evaluate(DicksonFirst(7, F!3), c) : c in F}, #{Evaluate(DicksonFirst(5, F!3), c) : c in F};
ChebyshevT(-1);
ChebyshevU(-1);
LegendrePolynomial(-1);
LaguerrePolynomial(-1);
HermitePolynomial(-1);
BernoulliPolynomial(-1);
GegenbauerPolynomial(-1, 2);
DicksonFirst(-1, 2);
DicksonSecond(-1, 2);
ChebyshevT(2^30);

// The other names of the Chebyshev polynomials.
ChebyshevFirst(5), ChebyshevSecond(5);
