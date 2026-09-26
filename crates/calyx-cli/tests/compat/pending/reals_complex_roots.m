// Roots of polynomials over complex fields (Element Operations: Roots).
// Magma 2.22 finds these with PARI. The roots come in the order of PARI's
// splitting-circle method and carry PARI's rounding errors: a root i can
// come out as 6.6E-40 + 1.0*i. An exact multiple root is merged only when
// PARI returns equal approximations. calyx rounds the exact roots
// correctly, merges exact multiple roots and lists the roots by real part,
// then by imaginary part. The polynomials here have exact coefficients.

C<i> := ComplexField(20); P<z> := PolynomialRing(C);
Roots(z^2 + 1);
Roots(z^3 - 1);
Roots(z^4 - 1);
Roots(z^4 + 1);
Roots(z^5 - 1);
Roots(z^6 - 1);
Roots(z^2 - 2*i);
Roots(z^3 - (1 + i));
Roots(z^3 + i);
Roots(z^5 - z - 1);
Roots(z^2 - 2*z + (1 + i));
Roots((z - 1)^2);
Roots((z - 1)^2*(z + 2));
Roots((z - (2 + i))^2*(z - i));
Roots(z^2 + (1 + 2*i)*z + (3 - i));
Roots((z - (1 + 2*i))*(z - (1 - 2*i))*(z - 3)*(z + 4));
Roots((z - (1 + 2*i))*(z - (-1 + 2*i))*(z - (3 - i))*(z + 5*i));
r := Roots(z^2 + 1); Universe(r), Parent(r[1][1]);
Roots(P!3);
Roots(z);
Roots(z^3 - 2 : Al := "Laguerre");
Roots(z^3 - 2 : Digits := 5, Max := 1);

// Roots in a complex field of polynomials over other rings.
R<x> := PolynomialRing(RealField(20));
Z<t> := PolynomialRing(Integers());
Q<u> := PolynomialRing(Rationals());
Roots(x^2 - 2, C);
Roots(x^2 + 1, C);
r := Roots(x^2 - 2, C); Universe(r);
Roots(t^3 - 2, C);
Roots(u^2 - 7/3, C);
Roots(t^4 + 1, ComplexField(30));

// HasRoot: zero if it is a root, else the first root.
HasRoot(z^3 - 1);
HasRoot(z^3 - z);
HasRoot(P!0);
HasRoot(u^2 + 1, C);
HasRoot(t^2 - 2, C);

// Errors.
Roots(P!0);
Roots(z^2 + 1 : Al := "Foo");
Roots(t^2 - 2, C : Al := "Foo");
HasRoot(z^2 + 1 : Digits := 5);

// The handbook's example (H26E6). Its polynomial is ill-conditioned: 2.22's
// Roots gives these roots to about 14 digits, while its RootsNonExact gives
// the same roots as calyx to all 30 (reals_roots_non_exact.m).
P<z> := PolynomialRing(ComplexField());
p := (z-1.1)^6;
p;
R := Roots(p);
R;
P<x> := PolynomialRing(Rationals());
q := (x-11/10)^6;
Roots(q);
