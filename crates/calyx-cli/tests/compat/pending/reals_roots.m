// Roots of polynomials over real fields (Element Operations: Roots).
// Magma 2.22 gives the real roots of the polynomial with its exact
// coefficients (integers, rationals or reals, not rounded into the field of
// the roots), rounded correctly, in increasing order, with their exact
// multiplicities. (It does so to an absolute accuracy of about 2^-(p+4) for
// p bits, so roots below 1/16 or so lose their last bits in 2.22; the roots
// here are larger.) Al and Digits make no difference, and Max is ignored.

R := RealField(20); P<x> := PolynomialRing(R);
Roots(x^2 - 2);
Roots(x^2 + 1);
Roots(x^3 - 1);
Roots((x - 1)^2*(x - 2));
Roots(x^2 - 2*x + 1);
Roots(P!3);
Roots(x);
Roots(x^4 - 10*x^2 + 1);
Roots(x^5 - x - 1);
r := Roots(x^2 - 2); Universe(r), Parent(r[1][1]);
Universe(Roots(x^2 + 1));
Roots(3*x^2 - 6);
Roots(2*x + 1);
Roots(-x^2 + 2);
Roots(x^4 + x^3);
Roots(x^2 - 9/4);
Roots(x^3 - 3*x + 1);
Roots(x^4 - 5*x^2 + 4);
Roots(x^6 - 1);
Roots((x - 1)*(x - 2)*(x - 3)*(x - 4)*(x - 5)*(x - 6)*(x - 7)*(x - 8)*(x - 9)*(x - 10));
Roots(10^-30*x^2 - 1);
Roots(x^2 - 10^40);

// Exact multiplicities of the polynomial as it is: a rounded square has
// two distinct roots or none.
Roots((x^2 - 2)^2);
Roots(x^3);
Roots(x^2*(x - 1)^3);
Roots((x^2 + 1)^2*(x - 3));
Roots((x - 1/3)^2);
Roots((x - 1.1)^2);
Roots(x^3 - 3*x^2 + 3*x - 1 + 10^-30);
for c in [5/3, 1/7, 2/7, 1/10, 2/5] do
  printf "%o:", c;
  for t in Roots((x - c)^2) do m, e := MantissaExponent(t[1]); printf " %o,%o,%o", m, e, t[2]; end for;
  print "";
end for;

// Correct rounding, also next to the midpoint of two numbers.
for d in [20, 30, 10] do
  F := RealField(d); Q<y> := PolynomialRing(F);
  for f in [y^2 - 2, y^3 - y - 1, y^5 - 3*y + 1, 3*y^3 - 7*y^2 + y/3 + 2, y^4 - 10*y^2 + 1, y^7 - 2, y^3 - 3*y + 1, y^2 - y - 1, y^6 - 5*y^4 + 3*y - 1/5, Pi(F)*y^2 - Exp(F!1)] do
    printf "%o:", d;
    for t in Roots(f) do m, e := MantissaExponent(t[1]); printf " %o,%o,%o", m, e, t[2]; end for;
    print "";
  end for;
end for;
for n in [28978, 112754, 70535, 48166, 144559, 188389, 100723, 154261, 6891] do
  r := Roots(x^2 - n); m, e := MantissaExponent(r[2][1]); printf "%o %o %o\n", n, m, e;
end for;
S<w> := PolynomialRing(RealField(5));
Roots(w^2 - 2), Roots(w^3 - w - 1);
T<w> := PolynomialRing(RealField(40));
Roots(w^3 - w - 1);
Roots(w^2 - 1/3);

// The parameters.
Roots(x^2 - 2 : Digits := 10);
Roots(x^2 - 2 : Digits := 50);
Roots(x^2 - 2 : Al := "Laguerre");
Roots(x^2 - 2 : Al := "NewtonRaphson");
Roots(x^2 - 2 : Al := "Combination");
Roots(x^2 - 2 : Al := "Schonhage", Digits := 5);
Roots(x^2 - 2 : Max := 1);
Roots(x^2 - 2 : Max := 0);

// Roots in a real field of polynomials over the integers, the rationals
// and other real fields.
Z<t> := PolynomialRing(Integers()); Qu<u> := PolynomialRing(Rationals());
r := Roots(t^2 - 2, R); r, Universe(r);
r := Roots(u^2 - 1/3, R); r, Universe(r);
Roots(t^3 - 2, RealField(30));
r := Roots(t^3 - 2, RealField()); r, Universe(r);
Roots(t^2 + 1, R);
Roots((t - 1)^2*(t + 2), R);
Roots(t^2 - 2, R : Al := "Laguerre");
Roots(t^2 - 2, R : Max := 1);
for q in [7/3, 13/5, 11/6, 9/7] do
  r := Roots(u^2 - q, R); m, e := MantissaExponent(r[2][1]); printf "%o %o %o\n", q, m, e;
end for;
r := Roots(x^2 - 2, RealField(30)); r, Universe(r);
r := Roots(x^2 - 2, RealField(10)); r, Universe(r);
r := Roots(x^2 - R!(1/3), RealField(30)); MantissaExponent(r[2][1]);
Q30<y> := PolynomialRing(RealField(30));
r := Roots(y^2 - 1/3, R); MantissaExponent(r[2][1]);

// HasRoot: zero if it is a root, else the least root.
HasRoot(x^2 - 2);
HasRoot(x^2 + 1);
HasRoot(x^3 - x);
HasRoot(x^3 + x);
HasRoot(x^3 - 2*x^2 - x + 2);
HasRoot(x^2 - 3*x + 2);
HasRoot((x - 1)^2*(x + 5));
HasRoot(x^4 - 5*x^2 + 4);
HasRoot(P!0);
HasRoot(P!3);
b, v := HasRoot(x^2 + 1); b;
HasRoot(t^2 - 2, R);
HasRoot(u^2 - 7/3, R);
HasRoot(u^2 + 1, R);

// Errors.
Roots(P!0);
Roots(Z!0, R);
Roots(x^2 - 2 : Al := "Foo");
Roots(x^2 - 2 : Al := "schonhage");
Roots(x^2 - 2 : Al := 3);
Roots(x^2 - 2 : Digits := -1);
Roots(x^2 - 2 : Digits := 0);
Roots(x^2 - 2 : Digits := "a");
Roots(x^2 - 2 : Digits := 1.5);
Roots(x^2 - 2 : Max := -1);
Roots(x^2 - 2 : Max := 2^40);
Roots(x^2 - 2 : Max := "a");
Roots(x^2 - 2 : Foo := 1);
Roots(t^2 - 2, R : Al := "Foo");
Roots(x^2 - 2, GF(7));
HasRoot(x^2 - 2 : Al := "Laguerre");
