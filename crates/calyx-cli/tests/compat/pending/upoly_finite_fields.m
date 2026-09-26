// Univariate polynomials over finite fields: prime polynomials, their
// number, random prime polynomials and the Jacobi symbol (handbook,
// Univariate Polynomial Rings, Polynomials over Finite Fields).
P2<x> := PolynomialRing(GF(2));
PrimePolynomials(P2, 1);
PrimePolynomials(P2, 2);
PrimePolynomials(P2, 3);
PrimePolynomials(P2, 4);
P3<y> := PolynomialRing(GF(3));
PrimePolynomials(P3, 1);
PrimePolynomials(P3, 2);
[Eltseq(f) : f in PrimePolynomials(P3, 3)];
PrimePolynomials(P3, 3, 4);
PrimePolynomials(P3, 3, 0);
// More than there are of degree 2: the sequence continues in degree 3.
PrimePolynomials(P3, 2, 10);
F<w> := GF(4);
P4<z> := PolynomialRing(F);
PrimePolynomials(P4, 1);
#PrimePolynomials(PolynomialRing(GF(101)), 2);
PrimePolynomials(PolynomialRing(GF(101)), 2, 3);
[#PrimePolynomials(P2, d) : d in [1..8]];
&and[IsIrreducible(f) and IsMonic(f) and Degree(f) eq 6 : f in PrimePolynomials(P3, 6)];
#Set(PrimePolynomials(P3, 6));
PrimePolynomials(PolynomialRing(Integers(5)), 2);
PrimePolynomials(P3, 0);
PrimePolynomials(P3, -1);
PrimePolynomials(PolynomialRing(Rationals()), 2);
PrimePolynomials(P3, 2, -1);

// Random prime polynomials.
P<t> := PolynomialRing(GF(7));
f := RandomPrimePolynomial(P, 5); Degree(f), IsIrreducible(f), IsMonic(f);
f := RandomPrimePolynomial(P4, 3); Degree(f), IsIrreducible(f), IsMonic(f);
f := RandomPrimePolynomial(P2, 1); Degree(f), IsIrreducible(f), IsMonic(f);
RandomPrimePolynomial(P, 0);
RandomPrimePolynomial(P, -1);
RandomPrimePolynomial(PolynomialRing(Rationals()), 2);

// The number of prime polynomials.
[NumberOfPrimePolynomials(2, d) : d in [1..10]];
[NumberOfPrimePolynomials(9, d) : d in [1..6]];
NumberOfPrimePolynomials(GF(7), 3), NumberOfPrimePolynomials(P, 3);
NumberOfPrimePolynomials(2, 100);
Type(NumberOfPrimePolynomials(2, 100));
NumberOfPrimePolynomials(6, 2);
NumberOfPrimePolynomials(1, 2);
NumberOfPrimePolynomials(0, 2);
NumberOfPrimePolynomials(-2, 2);
NumberOfPrimePolynomials(7, 0);
NumberOfPrimePolynomials(7, -1);
NumberOfPrimePolynomials(PolynomialRing(Rationals()), 2);
NumberOfPrimePolynomials(PolynomialRing(Integers(7)), 2);

// The Jacobi symbol.
JacobiSymbol(t^2 + 1, t + 1), JacobiSymbol(t^2 + 1, t + 2), JacobiSymbol(t^2 + 1, t^2 + 1);
JacobiSymbol(t, t^2 + 1), JacobiSymbol(t + 3, (t^2 + 1)*(t + 1)), JacobiSymbol(P!3, t^2 + 1), JacobiSymbol(P!3, t + 1);
JacobiSymbol(P!0, t + 1), JacobiSymbol(t^3 + 1, (t + 1)^2), JacobiSymbol(t^3 + 2, 3*t + 1);
JacobiSymbol(t + 1, P!3);
JacobiSymbol(t + 1, P!0);
JacobiSymbol(x + 1, x^2 + x + 1);
R<r> := PolynomialRing(Rationals());
JacobiSymbol(r + 1, r^2 + 1);
F9<v> := GF(9); U<u> := PolynomialRing(F9);
JacobiSymbol(u + v, u^2 + v), JacobiSymbol(u^2 + v, u + 1), JacobiSymbol(u^3 + v*u + 1, u^2 + u + v^3);
// The symbol against every prime polynomial of degree 2 agrees with
// squares modulo them.
&and[JacobiSymbol(t^3 + t + 5, g) eq (IsSquare(quo<P | g> ! (t^3 + t + 5)) select 1 else -1) : g in PrimePolynomials(P, 2)];
