// The elements of the rational field (Rational Field chapter, "Element
// Operations"): arithmetic, numerators and denominators, predicates,
// comparison, conjugates, absolute values, rounding and conversions.
// Valuations at ideals that are not prime fail inside Magma's package code
// (with a traceback calyx does not print), so they are not tested here.
Q := Rationals();
Parent(1/2), Category(1/2), Type(1/2);
+(1/2), -(1/2), 1/2 + 1/3, 1/2 - 1/3, 1/2 * 1/3, (2/3)^-3, (1/2)/(1/3), (2/3)^0;
1/2 + 1, 1 + 1/2, 3/2 * 2, Parent(3/2 * 2), 1/2 - 1/2, Parent(1/2 - 1/2);
(-2/3)^3, (-2/3)^-3, (1/2)^100;
a := 1/2; a +:= 1/3; a; a -:= 1/7; a; a *:= 3; a; a /:= 5; a; a ^:= 2; a;
(1/2)/0;
(0/1)^-1;
1/(0/1);
Numerator(10/-4); Denominator(10/-4); Numerator(0/7); Denominator(0/7);
Numerator(-12/1), Denominator(-12/1), Parent(Numerator(1/2)), Parent(Denominator(1/2));
Numerator(7), Denominator(7);

// equality and membership
1/2 eq 2/4, 1/2 ne 1/3, 1/2 eq 0.5, 2/1 eq 2, 1/2 in Q, 1/2 in Integers(), 1/2 notin Integers(), 4/2 in Integers();
1/2 in RealField(), 1/2 in GF(5);

// predicates
IsZero(0/1), IsZero(1/2), IsOne(1/1), IsOne(1/2), IsMinusOne(-1/1), IsMinusOne(1/1);
IsNilpotent(0/1); IsNilpotent(1/2);
IsIdempotent(0/1), IsIdempotent(1/1), IsIdempotent(1/2);
IsUnit(1/2), IsUnit(0/1), IsZeroDivisor(1/2), IsZeroDivisor(0/1), IsRegular(1/2), IsRegular(0/1);
IsIrreducible(1/2), IsIrreducible(2/1), IsIrreducible(0/1), IsPrime(1/2), IsPrime(2/1), IsPrime(0/1);
IsIntegral(4/2), IsIntegral(1/2), IsIntegral(0/1);

// comparison
1/2 gt 1/3, 1/2 ge 1/3, 1/2 lt 1/3, 1/2 le 1/3, 1/2 ge 1/2, -1/2 lt -1/3;
Maximum(1/2, 1/3), Minimum(1/2, 1/3), Maximum(-1/2, -1/3), Minimum(-1/2, -1/3);
Maximum([1/2, 3/4, 1/5]); Minimum([1/2, 3/4, 1/5]);
Maximum({1/2, 3/4, 1/5}); Minimum({1/2, 3/4, 1/5});
Max(1/2, 2); Parent(Max(1/2, 2)); Max(2, 1/2); Parent(Max(2, 1/2)); Min(3/2, 1); Parent(Min(3/2, 1));
Maximum([1/2, 3, 1/5]); Parent(Maximum([1/2, 3, 1/5]));
Maximum([Q | ]);

// conjugates, norms and traces
ComplexConjugate(-3/4), Conjugate(-3/4), Norm(-3/4), Trace(-3/4);
Parent(Norm(-3/4)), Parent(Trace(4/2));
MinimalPolynomial(1/2); MinimalPolynomial(0/1); MinimalPolynomial(-1/1); MinimalPolynomial(4/2);
Parent(MinimalPolynomial(1/2));
P<x> := PolynomialRing(Q);
MinimalPolynomial(1/2); MinimalPolynomial(-7/3);

// absolute value, sign and height
AbsoluteValue(-1/2), Abs(-1/2), Abs(1/2), Abs(0/1), Parent(Abs(-1/2));
Sign(-1/2), Sign(0/1), Sign(1/2), Parent(Sign(1/2));
Height(-7/3), Height(3/7), Height(0/1), Height(5/1), Height(-1/1), Height(-10^20/3);
Parent(Height(1/2));

// rounding and truncating
Ceiling(7/3), Ceiling(-7/3), Ceiling(2/1), Floor(7/3), Floor(-7/3), Floor(-2/1);
Round(7/2), Round(-7/2), Round(5/2), Round(-5/2), Round(7/3), Round(-7/3), Round(8/3);
[Round(x/2) : x in [-7..7]];
Truncate(7/3), Truncate(-7/3), Truncate(0/1);
Parent(Floor(1/2)), Parent(Ceiling(1/2)), Parent(Round(1/2)), Parent(Truncate(1/2));

// valuations
Valuation(12/5, 2); Valuation(12/5, 5); Valuation(12/5, 3); Valuation(12/5, 7); Valuation(-12/5, 2);
v, u := Valuation(12/5, 2); v, u, Parent(u);
v, u := Valuation(12/5, 5); v, u;
v, u := Valuation(-3/4, 7); v, u;
Valuation(0/1, 2);
Valuation(1/8, 2); Valuation(4/1, 2); Valuation(12/5, 2^61 - 1);
Valuation(12/5, 4);
Valuation(12/5, 1);
Valuation(12/5, 0);
Valuation(12/5, -2);
Valuation(12/5, 5/1);
Valuation(12/5, ideal<Integers() | 2>);
v, u := Valuation(12/5, ideal<Integers() | 5>); v, u;

// sequence conversions
ElementToSequence(1/2); Eltseq(-3/7); Eltseq(3/1); Parent(Eltseq(1/2));
Q!Eltseq(-3/7);
