// HenselLift (Element Operations: Roots): Newton's iteration from x to a
// root of f, returned in the real or complex field of k digits. Magma 2.22
// needs Kantorovich's condition |f(x) f''(x)| < |f'(x)|^2/2 at x, and stops
// after the first step smaller than 10^-t max(1, |x|), t = (3k - 3) div 4,
// so a double root comes out correct to about 3k/4 digits only. A root 0,
// or a part 0 of a complex root, comes out as a tiny number made of the
// rounding errors of the steps: the first at 37 bits for the polynomials
// here (for others at 7 to 14 digits), the last ones at 2k + 19 digits,
// and the ones in between at precisions that show beyond 25 digits, where
// these cases stop. Not tested: polynomials with
// small coefficients such as 10^-4 (x^2 - 2), for which 2.22 returns x or
// fails to make a field of precision below 1; starting points far from the
// root, such as 1.5*10^m for x^2 - 2, from which it returns x for k up to
// 3m - 1; and starting points from which the iteration diverges, where it
// loops forever.

R := RealField(20); P<y> := PolynomialRing(R);
C<i> := ComplexField(20); Q<w> := PolynomialRing(C);
for k in [1, 2, 5, 10, 19, 20, 21, 30, 50, 100] do
  z := HenselLift(y^2 - 2, R!1.4, k); z, Precision(Parent(z));
end for;
z := HenselLift(y^2 - 2, R!1.4, 25); z, Type(z), Parent(z);
HenselLift(y^2 - 2, RealField(5)!1.4, 60);
HenselLift(y^2 - 2, RealField(40)!1.4, 20);
HenselLift(y^2 - 2, 1.4, 20);
HenselLift(y^2 - 2, R!10, 20), HenselLift(y^2 - 2, R!-1.01, 20), HenselLift(y^2 - 2, R!-3, 30);
HenselLift(y^3 - 2, R!1.2, 30), HenselLift(y^5 - y - 1, R!1.2, 30);
HenselLift(y^3 - 3*y + 1, R!0.5, 25), HenselLift(y^3 - 3*y + 1, R!1.5, 25);
HenselLift(Pi(R)*y^2 - Exp(R!1), R!0.9, 40);

// Linear polynomials; the root is that of the coefficients as they are.
HenselLift(y - 2, R!1, 20), HenselLift(y - 2, R!2, 20);
HenselLift(y - R!1/3, R!0.3, 50);
HenselLift(3*y - 1, R!0.3, 50);

// Polynomials over the integers, the rationals and other fields.
Z<t> := PolynomialRing(Integers()); Qu<u> := PolynomialRing(Rationals());
HenselLift(t^2 - 2, R!1.4, 20), HenselLift(u^2 - 2/3, R!0.8, 20);
HenselLift(PolynomialRing(RealField(10))![-2, 0, 1], RealField(30)!1.4, 25);
z := HenselLift(w^2 - 2, R!1.4, 20); z, Type(z);
z := HenselLift(y^2 - 2, C!1.4, 20); z, Type(z);
z := HenselLift(t^2 - 2, C!1.4, 20); z, Type(z);
[HenselLift(y^2 - 2, R!1.4, k) : k in [1..6]];

// Complex roots.
HenselLift(w^2 - 2*w + 5, C![1.1, 1.9], 20), HenselLift(w^2 - 2*w + 5, C![1.1, -1.9], 30);
HenselLift(w^3 - 2, C![-0.6, 1.1], 25);
HenselLift(w^4 + 1, C![0.7, 0.7], 20);
HenselLift(w^2 - (1 + 2*i)*w + i, C![0.4, 0.2], 20);
HenselLift(t^2 + t + 1, C![-0.5, 0.8], 20);
z := HenselLift(w^2 + 1, C![0.1, 0.9], 20); z, Parent(z);
[HenselLift(w^2 + 1, C![0.1, 0.9], k) : k in [1..6]];
for k in [1..25] do
  z := HenselLift(w^2 + 1, C![0.1, 0.9], k); m, e := MantissaExponent(Real(z));
  printf "%o: %o %o, %o\n", k, m, e, Imaginary(z);
end for;
HenselLift(w^2 + 4, C![0.3, 1.8], 20), HenselLift(w^2 + 1, C![-0.05, 1.1], 20);
HenselLift(y^3 + y, R!0.1, 20), HenselLift(y^2 + y, R!0.1, 20), HenselLift(y^2 + y, R!0.3, 20);

// Linear convergence to a double root: the result has about 3k/4 digits
// right. Below 1 the last step is small in absolute terms, above 1
// relative to the root.
for k in [3..20] do
  m, e := MantissaExponent(HenselLift(y^4 - 4*y + 3, R!0, k)); printf "%o: %o %o\n", k, m, e;
end for;
S := RealField(60); T<v> := PolynomialRing(S);
for s in [S!10^-3, S!10^-1, S!10, S!10^3] do
  g := s^4 * Evaluate(v^4 - 4*v + 3, v/s);
  printf "%o:", s;
  for k in [8, 12, 16, 20] do m, e := MantissaExponent(S!HenselLift(g, S!0, k)/s); printf " %o %o;", m, e; end for;
  printf "\n";
end for;

// Errors: Kantorovich's condition (checked first for f'(x) = 0), the
// precision, a complex polynomial at a real x, and other coefficient rings.
HenselLift(y^2 - 2, R!1, 20);
HenselLift(y^2 - 2, R!0.99, 20);
HenselLift(y^3 - 2, R!1, 20);
HenselLift(y^2, R!1, 20);
HenselLift(w^3 - 2, C![1, 1], 20);
HenselLift(w^2 + 1, R!1, 20);
HenselLift(y^2 - 2, R!0, 20);
HenselLift(P!3, R!1, 20);
HenselLift(P!0, C!1, 20);
HenselLift(y^2 - 2, C!0, 20);
HenselLift(P!3, R!1, 0);
HenselLift(y^2, R!1, 0);
HenselLift(y^2 - 2, R!1.4, 0);
HenselLift(y^2 - 2, R!1.4, -1);
HenselLift(w^2 + 1, C![0.1, 0.9], 0);
HenselLift(w - i, R!0, 20);
HenselLift(PolynomialRing(GF(5))![3, 0, 1], R!1.4, 20);
HenselLift(y^2 - 2, R!1.4, 20.0);
HenselLift(y^2 - 2, 3/2, 20);
HenselLift(y^2 - 2, 2, 20);
