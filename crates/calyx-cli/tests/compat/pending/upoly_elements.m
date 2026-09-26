// Univariate polynomials: arithmetic, predicates, coefficients, degrees,
// roots, derivatives, evaluation and interpolation (handbook, Univariate
// Polynomial Rings, Element Operations).
Z := Integers();
Q := RationalField();
P<x> := PolynomialRing(Z);
f := 3*x^4 - 2*x^2 + x - 7;
g := x^2 + 1;
Parent(f); Category(f);
+f; -f; f + g; f - g; f * g; g^3; f^0; (x - 1)^10;
f + 1/2;
g^-1;
(P!-1)^-1;
(P!0)^0;
h := f; h +:= g; h; h -:= 1; h; h *:= x; h;
f eq g, f ne g, f eq 3*x^4 - 2*x^2 + x - 7, P!3 eq 3, 3 eq P!3;
f / 3;
(6*x^2 + 3) / 3;
S<y> := PolynomialRing(Q);
(y^2 + 1) / 2;
(y^2 + 1) / 0;
T<t> := PolynomialRing(GF(7));
(t^2 + 1) / 3;

// Predicates.
[IsZero(p) : p in [P!0, x, P!1]];
[IsOne(p) : p in [P!0, x, P!1, P!-1]];
[IsMinusOne(p) : p in [P!0, x, P!1, P!-1]];
[IsUnit(p) : p in [P!0, x, P!1, P!-1, P!2]];
[IsUnit(p) : p in [S!0, y, S!2]];
IsIdempotent(P!1), IsIdempotent(x), IsIdempotent(P!0);
IsNilpotent(x);
IsZeroDivisor(x), IsZeroDivisor(P!0);
[IsRegular(p) : p in [P!0, x, P!1]];
R<r> := PolynomialRing(Integers(4));
IsZeroDivisor(2*r);
IsRegular(2*r);
IsUnit(1 + 2*r), IsUnit(R!3);
[IsMonic(p) : p in [P!0, P!1, x, 2*x + 1, x^3 - x, -x]];
IsMonic(y/2 + 1), IsMonic(t + 3);

// Coefficients and terms.
Coefficients(f); Eltseq(f); ElementToSequence(f);
Coefficients(P!0); Eltseq(S!0);
Coefficient(f, 0), Coefficient(f, 2), Coefficient(f, 4), Coefficient(f, 10);
Coefficient(f, -1);
MonomialCoefficient(f, x^2), MonomialCoefficient(f, P!1), MonomialCoefficient(f, x^7);
MonomialCoefficient(f, 2*x);
MonomialCoefficient(f, x + 1);
LeadingCoefficient(f), TrailingCoefficient(f), ConstantCoefficient(f);
LeadingCoefficient(x^3 + x^2), TrailingCoefficient(x^3 + x^2), ConstantCoefficient(x^3 + x^2);
LeadingCoefficient(P!0);
TrailingCoefficient(P!0);
ConstantCoefficient(P!0);
Parent(LeadingCoefficient(y^2/3)), LeadingCoefficient(y^2/3);
Terms(f); Terms(P!0); Terms(x^5);
LeadingTerm(f), TrailingTerm(f);
LeadingTerm(P!0);
TrailingTerm(P!0);
Monomials(f); Monomials(x^3 + 1); Monomials(P!0); Monomials(P!5);
Support(f);
s, c := Support(f); s, c;
Support(P!0);
Reductum(f), Reductum(x), Reductum(P!3);
Reductum(P!0);
Round(y^2/3 + 5/2*y - 7/2);
Round(P!0), Parent(Round(y/2));
Round(PolynomialRing(RealField(10))![1.5, -2.5, 0.49]);
Round(f);
Valuation(f), Valuation(x^3 + x^5), Valuation(P!0), Valuation(P!7);
Degree(f), Degree(P!7), Degree(P!0);

// Roots.
Roots((x - 1)^2 * (x + 5) * (2*x + 1));
Roots((y - 1)^2 * (y + 5) * (2*y + 1));
Roots(x^2 + 1), Roots(P!3);
Roots(P!0);
Roots(t^3 - 1);
Roots(t^7 - t);
Roots(t^7 - t : Max := 3);
Roots(x^2 - 2, GF(7));
Roots(x^2 + 1, Q);
Roots((x^2 - 4)*(3*x - 1), Q);
HasRoot(x^2 + 1), HasRoot((x - 3)*(x^2 + 1));
b, r := HasRoot(x^2 + 1); b, assigned r;
// Over finite fields Magma finds some root.
HasRoot(t^2 + 1);
b, r := HasRoot(t^2 + 6); b, r in [1, 6];
b, r := HasRoot(x^2 - 2, GF(7)); b, r^2 eq 2, Parent(r);
F9<w> := GF(9);
Roots(PolynomialRing(F9)![1, 0, 1]);
Roots(t^2 + 1, F9);
Roots(PolynomialRing(Integers(7))![6, 0, 1]);
// The root HasRoot and Roots(f : Max := 1) pick over a finite field: 0 if
// it is a root, else one of the first squarefree part (in the ring's
// order) with roots: its only root, (s + Sqrt(D))/2 for two roots in the
// prime field with sum s and discriminant D, and the least root for more.
// Magma's square roots in GF(p) for p = 1 mod 8, and its choice among
// roots in extension fields of order 25 or more, depend on its random
// state, so these avoid them.
[r where _, r := HasRoot(f) : f in [(t - 1)*(t - 2), (t - 1)*(t - 5), (t - 3)*(t - 4), (t - 2)*(t - 6), (t - 1)*(t - 2)*(t - 4), t*(t - 5)]];
[r where _, r := HasRoot(f) : f in [(t - 2)^2*(t - 3), (t - 3)^2*(t - 5)*(t - 6), (t - 5)^3*(t - 1)^2, (t - 1)*(t - 6)*(t^2 + 1), (t^2 + 1)^2*(t - 4)]];
[r where _, r := HasRoot(f) : f in [(t - 1)*(t - 2)*(t - 3)^2*(t - 4)^2, (t - 6)*(t - 2)^2*(t - 5)^2, (t - 1)^2*(t - 2)^2*(t - 3)]];
Roots((t - 1)*(t - 2)*(t - 3)^2*(t - 4)^2 : Max := 1);
Roots((t - 1)*(t - 2)*(t - 3)^2*(t - 4)^2 : Max := 3);
Roots((t - 6)*(t - 2)^2*(t - 5)^2*(t - 3)^3 : Max := 2);
Roots((t - 6)*(t - 2)^2*(t - 5)^2*(t - 3)^3 : Max := 0);
Roots(t*(t - 1)*(t - 2) : Max := 1);
U11<u> := PolynomialRing(GF(11));
U13<v> := PolynomialRing(GF(13));
[r where _, r := HasRoot((u - a)*(u - b)) : a, b in [1..10] | a lt b and a + b le 7];
[r where _, r := HasRoot((v - a)*(v - b)) : a, b in [1..12] | a lt b and a + b le 7];
[r where _, r := HasRoot(x^2 - a, GF(11)) : a in [1, 3, 4, 5, 9]];
[r where _, r := HasRoot(y^2 - a, GF(13)) : a in [1, 3, 4, 9, 10, 12]];
// Modulo a prime 0 if it is a root, else the largest root; over the
// integers and the rationals the largest.
W7<z> := PolynomialRing(Integers(7));
[r where _, r := HasRoot(f) : f in [(z - 1)*(z - 2), (z - 5)*(z - 3)*(z - 6), z*(z - 4), (z - 2)^3*(z - 6)]];
[r where _, r := HasRoot(f) : f in [(x - 1)*(x - 3), (x + 5)*(x - 2)^2, (x + 1)*(x + 2)*(x^2 + 1)]];
[r where _, r := HasRoot(f) : f in [(y - 1/2)*(y + 3), (2*y - 1)*(3*y - 1)]];
HasRoot((x - 3)*(x - 5), GF(7)), HasRoot((x - 1)*(x - 2), Integers(7));
F8<e> := GF(8);
E8<s> := PolynomialRing(F8);
[r where _, r := HasRoot((s - e^i)*(s - e^j)) : i, j in [0..6] | i lt j and i + j le 6];
E9<d> := PolynomialRing(F9);
[r where _, r := HasRoot((d - w^i)*(d - w^j)) : i, j in [0..7] | i lt j and i + j le 7];
// Roots with Max := m: over the integers and the rationals the largest m;
// over a field of order q the least m if deg f <= 2 or deg f >= q, else
// for m = 1 the root HasRoot would pick (though not 0 first) with
// multiplicity 1, and for more the roots of the squarefree parts in turn
// until there are m, the least m of those.
[Roots((x - 1)*(x - 2)^2*(x + 3)*(x - 5)^3 : Max := m) : m in [0..5]];
Roots((y - 1/2)^2*(y + 1)*(y - 4) : Max := 2);
Roots((t - 3)^2 : Max := 1), Roots(3*(t - 3)*(t - 5) : Max := 1), Roots((t - 3)*(t - 5)*(t - 1) : Max := 1);
Roots((t - 1)^3*(t - 2)^3*(t - 5) : Max := 1), Roots((t - 1)^3*(t - 2)^3*(t - 5) : Max := 2);
Roots(t^2*(t - 1)^2 : Max := 1), Roots((t - 3)^2*(t^2 + 1) : Max := 1), Roots((z - 1)*(z - 2)*(z - 3)^2*(z - 4)^2 : Max := 1);
Roots((u - 1)*(u - 2)^2*(u - 3)*(u - 5)^2 : Max := 2), Roots((u - 1)*(u - 2)^2*(u - 3)*(u - 5)^2 : Max := 3);
Roots(x^2 - 4 : Max := -1);
Roots(x^2 - 4 : Max := 2^30);
Roots(x^2 - 4 : Max := 1/2);
Roots(x^2 - 4, GF(7) : Max := "a");
// Roots(f, S) and HasRoot(f, S) change the coefficient ring as ! does.
Roots(y^2 - 3, GF(13)), Roots(y^2 - 4, Integers()), Roots(t^2 - 1, Integers()), Roots(t^2 - 1, Integers(7));
HasRoot(t^2 - 1, Integers()), HasRoot(y^2 - 4, Integers());
Roots(y^2 - 1/13, GF(13));
HasRoot(y^2 - 1/2, Integers());
Roots(t^2 - 1, Rationals());
HasRoot(t^2 - 1, GF(5));
Rationals() ! (GF(7) ! 3);
Rationals() ! (Integers(7) ! 3);
Roots(PolynomialRing(Integers(8)) ! [7, 0, 1]);
HasRoot(PolynomialRing(Integers(8)) ! [7, 0, 1]);

// Derivatives and integrals.
Derivative(f), Derivative(f, 2), Derivative(f, 5), Derivative(f, 0);
Derivative(f, -1);
Derivative(t^7 + t^2);
Integral(y^2 + 2*y + 3), Integral(S!0);
Integral(f);
Integral(t^2);

// Evaluation and interpolation.
Evaluate(f, 2), Evaluate(f, -1), Evaluate(f, 0);
Evaluate(f, 1/2), Parent(Evaluate(f, 1/2));
Evaluate(f, x + 1);
Evaluate(f, y);
Evaluate(y^2 + 1, 1/3);
Evaluate(t^2 + 1, 3), Parent(Evaluate(t^2 + 1, 3));
Evaluate(f, GF(5)!2), Parent(Evaluate(f, GF(5)!2));
Evaluate(f, RealField(10)!0.5);
Interpolation([1, 2, 3], [1, 4, 9]);
Interpolation([Q | 0, 1, 2], [1, 3, 7]);
Interpolation([GF(7) | 1, 2, 3], [GF(7) | 1, 1, 2]);
Interpolation([1/2, 2], [3, 0]);
Interpolation([1, 2], [1, 2, 3]);
Interpolation([1, 1], [1, 2]);
Interpolation([GF(7) | 1, 2], [Q | 1, 2]);

// Quotient and remainder.
Quotrem(x^3 + 2*x + 1, x - 2);
Quotrem(3*x^3 - 5*x + 7, 2*x + 1);
Quotrem(x^2, 2*x + 1);
q, rr := Quotrem(y^3 + 2*y + 1, 2*y - 1); q, rr;
Quotrem(t^5 + 1, 3*t^2 + t);
Quotrem(f, P!0);
(x^3 + 2*x + 1) div (x - 2), (x^3 + 2*x + 1) mod (x - 2);
(3*x^3 - 5*x + 7) div (2*x + 1), (3*x^3 - 5*x + 7) mod (2*x + 1);
f div 2, f mod 2;
f div P!0;
IsDivisibleBy(x^2 - 1, x + 1), IsDivisibleBy(x^2 - 1, x - 2), IsDivisibleBy(2*x^2 - 2, 2*x + 2);
IsDivisibleBy(x^2 + 2*x + 1, 2*x + 2);
ExactQuotient(x^2 - 1, x + 1), ExactQuotient(y^2 - 1, 2*y - 2);
ExactQuotient(x^2 - 1, x - 2);
Valuation(x^5 - x^3, x), Valuation((x^2 - 1)^3*(x + 3), x + 1), Valuation(x^2 + 1, x - 1);
PseudoRemainder(x^3 + 2*x + 1, 2*x + 1), PseudoRemainder(x, x^2), PseudoRemainder(2*x^4 + x, 3*x^2 - 1);
PseudoRemainder(y^3 + 1, 2*y + 3);
EuclideanNorm(f), EuclideanNorm(P!0), EuclideanNorm(P!5), EuclideanNorm(t^3);

// Modular arithmetic.
Modexp(t + 1, 100, t^3 + 2), Modexp(t + 1, 0, t^3 + 2), Modexp(t, 10, T!3);
Modexp(y + 1, 10, y^2 + 1);
Modexp(x + 1, 10, x^2 + 1);
Modexp(t + 1, -1, t^2 + 1);
CRT([y + 1, y - 1], [y^2 + 1, y - 3]);
ChineseRemainderTheorem([t, T!1, t^2], [t^2 + 1, t + 3, t^3]);
CRT([y, y], [y^2, y]);
CRT([y], [y, y^2]);

// Other operations.
ReciprocalPolynomial(f), ReciprocalPolynomial(x^3 + x^2), ReciprocalPolynomial(P!0);
PowerPolynomial(y^2 - 2, 2), PowerPolynomial(y^3 - y - 1, 3), PowerPolynomial(t^2 + 1, 3);
PowerPolynomial(x^2 + x + 1, 2);

// Printing at the Magma level: compact integer sequences over the
// integers, prime fields and residue rings.
Sprint(x^2 - 3*x, "Magma"), Sprint(P!0, "Magma"), Sprint(y^3/2 - 5, "Magma"), Sprint(S!0, "Magma");
Sprint(3*t + 1, "Magma"), Sprint(T!0, "Magma"), Sprint(3*r + 1, "Magma");
F9<w> := GF(9);
Sprint(PolynomialRing(F9)![2, 0, w], "Magma");
Sprint(PolynomialRing(S)![1, 0, y], "Magma");
print y^2 + 1 : Magma;
