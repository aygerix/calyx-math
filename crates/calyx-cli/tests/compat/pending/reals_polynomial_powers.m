// Powers of polynomials over real and complex fields (#73). Magma rounds
// every operation of its binary powering to the precision of the field, so
// an ill-conditioned power such as (z - 1.1)^6 depends on the last bits of
// each step. The coefficients are printed as mantissa and exponent. Only
// the cases whose rounding is understood are here: squares of at most
// eight terms, and products by polynomials of at most two terms.

R := RealField(20); P<x> := PolynomialRing(R);
pr := procedure(s, f)
  printf "%o", s;
  for c in Coefficients(f) do if c ne 0 then m, e := MantissaExponent(c); printf " %o,%o", m, e; else printf " 0"; end if; end for; print "";
end procedure;
l := x - R!11/10;
for e in [2..15] do pr("l" cat IntegerToString(e), l^e); end for;
c := R!11/10; d := R!-7/3; b := R!5/2;
for e in [2, 3, 5, 7, 13] do
  s := IntegerToString(e);
  pr("U" cat s, (b*x + c)^e);
  pr("V" cat s, (d*x + c)^e);
  pr("W" cat s, (c*x^2 + d*x)^e);
  pr("X" cat s, (c*x + 1)^e);
  pr("Y" cat s, (d*x^3 + c*x^2)^e);
end for;

// A constant is squared and multiplied like any polynomial, but (b*x)^e
// takes the power of the number b.
for e in [7, 13, 22] do
  s := IntegerToString(e);
  pr("P" cat s, (P!c)^e);
  pr("M" cat s, (c*x)^e);
  pr("T" cat s, (c*x^3)^e);
  pr("m" cat s, (d*x)^e);
end for;

// Squares of up to eight terms, and powers of two of short polynomials.
f := R!1/3 + R!2/7*x - R!5/11*x^2;
g := f + R!3/13*x^3;
pr("f2", f^2); pr("f4", f^4); pr("g2", g^2); pr("g4", g^4);
for n in [5..8] do
  h := &+[R!((-1)^(i div 3)*(2*i+3))/(5*i+11)*x^i : i in [0..n-1]];
  pr("h" cat IntegerToString(n), h^2);
end for;
pr("q", (x^2 + R!1/3)^2); pr("r", (x^4 - R!2/3*x + R!1/7)^2);

// Complex coefficients: each part of each operation is rounded correctly.
C<i> := ComplexField(20); Q<z> := PolynomialRing(C);
pc := procedure(s, f)
  printf "%o", s;
  for c in Coefficients(f) do
    for t in [Real(c), Imaginary(c)] do if t ne 0 then m, e := MantissaExponent(t); printf " %o,%o", m, e; else printf " 0"; end if; end for;
    printf " |";
  end for; print "";
end procedure;
a := C![R!11/10, R!7/10]; b := C![R!-2/3, R!5/7]; c := C![R!3/11, R!-4/13];
for e in [2, 3, 5, 6, 7, 12] do pc("Z" cat IntegerToString(e), (z - a)^e); end for;
for e in [3, 7] do pc("S" cat IntegerToString(e), (b*z^2 + a)^e); end for;
for e in [7, 13] do pc("A" cat IntegerToString(e), (a*z)^e); end for;
h := a + b*z + c*z^2 + C![R!5/17, R!1/19]*z^3 + C![R!-6/23, R!2/29]*z^4;
pc("H2", h^2);
k := &+[C![R!((-1)^j*(2*j+1))/(3*j+7), R!((-1)^(j div 2)*(j+2))/(5*j+3)]*z^j : j in [0..7]];
pc("K2", k^2);

// The handbook's polynomial from H26E6, printed in full.
P<z> := PolynomialRing(ComplexField());
(z - 1.1)^6;
(z - 1.1)^2, (z - 1.1)^3;
P<y> := PolynomialRing(RealField(30));
(y - 1.1)^6;
(y + 1/3)^7;
