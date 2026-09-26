// Multivariate polynomials: element operations (handbook, Multivariate
// Polynomial Rings, Element Operations).
R<x, y, z> := PolynomialAlgebra(RationalField(), 3);
f := (2*x+y)*z^3+11*x*y*z+x^2*y^2;
f;
Coefficients(f);
Monomials(f);
CoefficientsAndMonomials(f);
Terms(f);
Coefficients(f, y);
Terms(f, 2);
MonomialCoefficient(f, x*y*z);
LeadingTerm(f);
LeadingTerm(f, z);
LeadingCoefficient(f, z);
Polynomial([1, 2, 3], [x*y, y, z^2]);

P<x,y> := PolynomialRing(GF(5), 2);
f := x^2 - y + 3;
g := y^3 - x*y + x;
Evaluate(f, x, 3);
Evaluate(g, x, 3);
Evaluate(f, y, 2);
Evaluate(g, y, 2);

Q := RationalField();
P<x, y, z> := PolynomialRing(Q, 3);
f := Interpolation([Q | 1, 2, 3], [y, z, y + z], 1);
f;
[ Evaluate(f, 1, v) : v in [1, 2, 3] ];

// Resultants, as in the handbook (H25E5).
P<x,y> := PolynomialRing(GF(5), 2);
f := x^2 - y + 3;
g := y^3 - x*y + x;
ry := Resultant(f, g, y);
ry;
Roots(UnivariatePolynomial(ry));
Evaluate(f, x, 3);
Evaluate(g, x, 3);
GCD($1, $2);
rx := Resultant(f, g, x);
rx;
Roots(UnivariatePolynomial(rx));
Evaluate(f, y, 2);
Evaluate(g, y, 2);
GCD($1, $2);

// Factorization (H25E8, H25E10).
P<x, y, z> := PolynomialRing(IntegerRing(), 3);
f := &*[x^i+y^j+z^k: i,j,k in [1..2]];
#Terms(f);
TotalDegree(f);
Factorization(f);
P<a, b, c> := PolynomialRing(RationalField(), 3);
A2 := 1/16 * (4*a^2*b^2 - (a^2 + b^2 - c^2)^2);
A2;
F, u := Factorization(A2);
F;
u;

// Arithmetic.
P<x, y, z> := PolynomialRing(Integers(), 3);
f := 3*x^2*y - 2*x*z^3 + y^2 - 5;
g := x*y - z + 1;
-f, +f;
f + g, f - g, f*g;
g^3;
g^0, (P!0)^0;
(f*g) div g;
(f*g) div f;
(2*x*y) div (2*x);
x div y;
(2*x) div (4*x);
f div (P!0);
ExactQuotient(f*g, g);
ExactQuotient(x, y);
IsDivisibleBy(f*g, f);
IsDivisibleBy(x + y, x);
h := x;
h +:= y; h;
h -:= 2*z; h;
h *:= x; h;
h div:= x; h;
f eq f, f eq g, f ne g, f eq 3*x^2*y - 2*x*z^3 + y^2 - 5;
f in P, 1 in P, x in PolynomialRing(Integers(), 3);
1/2 in P;
x in PolynomialRing(Rationals(), 3);
x notin P;
Q<a, b> := PolynomialRing(Rationals(), 2);
(a^2 + b)/3;
(a + b)/(2/3);
a/(Q!0);

// Predicates.
IsZero(P!0), IsZero(x), IsOne(P!1), IsOne(x), IsMinusOne(-P!1), IsMinusOne(x);
IsUnit(P!1), IsUnit(-P!1), IsUnit(P!2), IsUnit(x), IsUnit(Q!2);
IsZeroDivisor(x), IsZeroDivisor(P!0);
IsRegular(x), IsRegular(P!0);
IsIdempotent(P!1), IsIdempotent(P!0), IsIdempotent(x);
H<h1, h2> := PolynomialRing(Integers(6), 2);
IsUnit(1 + 2*h1), IsUnit(H!5), IsRegular(h1), IsRegular(2*h1);
IsZeroDivisor(2*h1 + 4*h2);

// Coefficients, monomials and terms.
f := 3*x^2*y - 2*x*z^3 + y^2 - 5;
Coefficients(f), Coefficients(P!0);
Coefficients(f, 1);
Coefficients(f, z);
Coefficients(P!0, x);
Coefficient(f, x, 2), Coefficient(f, 2, 1), Coefficient(f, z, 7);
Coefficient(f, x, -1);
LeadingCoefficient(f), LeadingCoefficient(P!0), TrailingCoefficient(f), TrailingCoefficient(P!0);
LeadingCoefficient(f, z), TrailingCoefficient(f, z), LeadingCoefficient(P!0, z);
Length(f), Length(P!0);
Monomials(f);
LeadingMonomial(f), LeadingMonomial(P!0);
Terms(f);
Terms(f, x);
Term(f, x, 1), Term(f, 3, 3), Term(f, x, 5);
LeadingTerm(f), LeadingTerm(P!0), TrailingTerm(f), TrailingTerm(P!0);
LeadingTerm(f, y), TrailingTerm(f, y);
Exponents(-7*x^2*z^3);
Exponents(P!1);
Exponents(x + y);
Monomial(P, [1, 2, 3]), Monomial(P, [0, 0, 0]);
Monomial(P, [1, 2]);
Polynomial([1, -2, 3], [x*y, y, z^2]);
Polynomial([Integers() | ], [P | ]);
MonomialCoefficient(f, x*z^3), MonomialCoefficient(f, x), MonomialCoefficient(f, P!1);
MonomialCoefficient(f, 2*x);

// Degrees.
Degree(f, x), Degree(f, 2), Degree(f, z), Degree(P!0, x), Degree(P!7, y);
TotalDegree(f), TotalDegree(P!0), TotalDegree(P!7);
LeadingTotalDegree(f), LeadingTotalDegree(P!0);
Degree(f, 4);
Degree(f, x + y);
Degree(f, 2*x);
R<u, v, w> := PolynomialRing(Rationals(), 3, "grevlex");
k := u*v^3 + u^4 + w^5;
k;
LeadingTotalDegree(k), TotalDegree(k), LeadingTerm(k), TrailingTerm(k);

// Univariate polynomials.
IsUnivariate(3*y^2 - y + 1);
IsUnivariate(x*y);
IsUnivariate(P!5);
IsUnivariate(3*y^2 - y + 1, y);
IsUnivariate(3*y^2 - y + 1, 1);
UnivariatePolynomial(z^3 - 2);
UnivariatePolynomial(P!4);
UnivariatePolynomial(x + y);
Parent(UnivariatePolynomial(z^3 - 2));

// Derivative, integral.
Derivative(f, x), Derivative(f, 3), Derivative(f, 2, z), Derivative(f, 4, z);
Derivative(f, 0, x);
Integral(a^2*b + b, a), Integral(a^2*b + b, 2);
Integral(f, x);
G<g1, g2> := PolynomialRing(GF(5), 2);
Derivative(g1^5 + g1^2*g2, g1);

// Evaluation.
Evaluate(f, [1, 2, 3]);
Evaluate(f, <1, 2, 3>);
Evaluate(f, [1/2, 1, 1]);
Evaluate(f, [y, z, x]);
Evaluate(f, [1, 2]);
Evaluate(f, x, 2), Evaluate(f, 3, 0), Evaluate(f, y, x + z);
Evaluate(f, z, 1/2);
Evaluate(a^2 + b, 1, GF(5)!2);
U<t> := PolynomialRing(Rationals());
Evaluate(a^2 + b, [t, t^3]);
Evaluate(a^2 + b, a, t);
Interpolation([1, 2], [a, b], 1);
Interpolation([1, 1], [b, b], 1);
Interpolation([1, 2], [b], 1);
Interpolation([1, 2], [a, b], a);

// Quotient and reductum.
Reductum(f), Reductum(P!0), Reductum(x);
Reductum(f, x), Reductum(f, z);

// Edge cases: division, integrals over rings, zero, membership,
// evaluation in other rings and interpolation.
Q := Rationals();
P<x, y> := PolynomialRing(Integers(), 2);
A<a, b> := PolynomialRing(Q, 2);
G<g, h> := PolynomialRing(GF(7), 2);
B<c, d, e> := PolynomialRing(Q, 3);
U<t> := PolynomialRing(Q);
a div (A!0);
g div (G!0);
x div (P!0);
ExactQuotient(a, A!0);
ExactQuotient(x, P!0);
a div b;
Integral(2*x*y, x), Integral(x^2, y), Integral(g, g);
Integral(g, 3);
LeadingTerm(A!0), LeadingCoefficient(A!0), TrailingTerm(A!0), TrailingCoefficient(A!0);
Monomials(A!0), Terms(A!0), Coefficients(A!0);
LeadingMonomial(A!0);
Exponents(A!0);
Exponents(A!3);
MonomialCoefficient(a, A!0);
MonomialCoefficient(a, A!1);
IsUnivariate(A!0);
UnivariatePolynomial(A!0);
u, i := UnivariatePolynomial(b^2); u, i;
t in A;
a in U;
a in Q, (A!1) in Q, x in A, a in P, (A!1) in P, (P!1) in A, a in B;
1/2 in A, 3 in A;
GF(5)!1 in A;
x in PolynomialRing(Integers(), 2), x notin A;
Evaluate(a^2 + b, 1, 2/3), Evaluate(a^2 + b, 1, 2), Evaluate(x^2 + y, 1, a);
Evaluate(x^2 + y, 1, P!3), Evaluate(x^2 + y, 2, x*y), Evaluate(a^2 + b, 1, P!1);
Evaluate(a/2 + b, 1, x);
Evaluate(a^2 + b, 1, c);
Evaluate(x^2 + y, 1, t);
Interpolation([Q | 1, 2], [a, b], 1);
Interpolation([Q | 1, 1], [b, b^2], 1), Interpolation([Q | 1, 2, 1], [b, 3, b], 1);
Interpolation([Q | 0, 0], [b, b], 2);
Interpolation([Q | 1, 2], [b, a + b], 1);
Interpolation([Q | 1, 2], [b, b^2], 3);
Interpolation([GF(7) | 1, 2], [h, h^2], 1);
Interpolation([GF(7) | 1, 2], [b, b^2], 1);
Interpolation([Integers() | 1, 2], [x, y], 1);
