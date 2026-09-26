// RootsNonExact (Element Operations: Roots): the roots of p repeated by
// multiplicity, and bounds E on how far they move when p changes by
// 10^-d |p|, where Magma can derive them. Magma 2.22 takes the roots from
// Gourdon's splitting circle code, in its order and to about 64 bits at 20
// digits, and computes the bounds at 64 bits from them, so the order, the
// last digits of the roots and the last few digits of the bounds are its
// own. This script sorts the roots, prints them rounded to k decimals (as
// integers times 10^-k), and prints the bounds to 12 digits. The relative
// change 10^-d is 2^-w in 2.22, with w = 64 (floor(d log2(10) / 32) - 1),
// so there are no bounds below 20 digits.

show := procedure(p, k)
  R, E := RootsNonExact(p);
  s := 10^k;
  T := Sort([<Round(s*Real(R[j])), Round(s*Imaginary(R[j])), j> : j in [1..#R]], func<a, b | a[1] ne b[1] select a[1] - b[1] else a[2] - b[2]>);
  print [<t[1], t[2]> : t in T];
  if assigned E then print [RealField(12)!Real(E[t[3]]) : t in T]; else print "no bounds"; end if;
end procedure;

P<z> := PolynomialRing(ComplexField());
p := (z-1.1)^6;
R, E := RootsNonExact(p);
#R, #E, Universe(R), Universe(E);
show(p, 12);

R := RealField(20); P<y> := PolynomialRing(R);
C<i> := ComplexField(20); Q<w> := PolynomialRing(C);
x := RootsNonExact(y^2 - 2); x;
r, e := RootsNonExact(y^2 - 2); r, [RealField(12)!x : x in e], Universe(r), Universe(e);
r, e := RootsNonExact(w^2 + 1); r, [RealField(12)!Real(x) : x in e], Universe(r), Universe(e);
r, e := RootsNonExact(y^2 + 1); ExtendedType(r), ExtendedType(e);
r, e := RootsNonExact(w^2 - 2); ExtendedType(r), ExtendedType(e);
for p in [y - 3, 2*y - 3, 3*y + 1, y^2 - 3, 3*y^2 - 4, 100*y^2 - 2, y^2 - 200, y^3 - 2, y^3 - y, y^5 - y - 1, (y - 1)*(y - 2)*(y - 3),
          y^4 - 5*y^2 + 4, y^4 + 5*y^2 + 4, y^6 + y^5 + y^4 + y^3 + y^2 + y + 1, (y^2 + 2*y + 5)*(y^2 - 2*y + 5)*(y - 1)] do
  show(p, 12);
end for;
for p in [w^2 - i, w^2 + w + 1, w^4 - 1, w^2 - (1.5 + 1.5*i), w^2 - 3*i, i*w^2 - 1, (1.5 + 1.5*i)*w^2 - 1, w^5 - 2*w^4 - w + 2] do
  show(p, 12);
end for;

// Multiple roots: the bound of a cluster of m roots is an m-th root.
show((y - 1)^2, 12);
show((y - 1)^3, 12);
show(y^3, 12);
show((w^2 + 1)^2, 12);
show((y - 1)*(y - 1 - 10^-5), 12);

// Large roots, and the limit beyond which there are no bounds.
show(y^2 - 2^57, 0);
show(y^2 - 2^58, 0);
show(y^2 - 2^60, 0);
show(y^2 - 2^61, 0);
show(y^3 - 2^59, 0);
show(y^3 - 2^60, 0);
show(y - 2^61, 0);
show(y^4 - 2^58, 0);
show(y^4 - 2^59, 0);
show(y^12 - 2^55, 6);
show(y^12 - 2^56, 6);
show(y^2 + 2^40*y - 2^60, 0);
show(10^-30*y^2 - 1, 0);
show(y^2 - 10^-30, 30);

// The precision: 2^-64 from 20 digits, 2^-128 from 29, 2^-192 from 39.
for d in [5, 19, 20, 28, 29, 38, 39, 40] do
  S := RealField(d); T<t> := PolynomialRing(S);
  r, e := RootsNonExact(t^2 - 2);
  printf "%o: %o\n", d, assigned e select RealField(12)!e[1] else "no bounds";
end for;
show(PolynomialRing(ComplexField(40))![1, 0, 1], 12);

// Constant polynomials have no roots and no bounds.
r, e := RootsNonExact(P!3); r, #r, assigned e;
r, e := RootsNonExact(Q!i); r, #r, assigned e;
RootsNonExact(P!3);

// Errors.
RootsNonExact(P!0);
RootsNonExact(Q!0);
RootsNonExact(y - 2^62);
RootsNonExact(PolynomialRing(Integers())![1, 0, 1]);
RootsNonExact(PolynomialRing(Rationals())![1, 0, 1]);
RootsNonExact(R!3);
RootsNonExact(y^2 - 2 : Digits := 5);
