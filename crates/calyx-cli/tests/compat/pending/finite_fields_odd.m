// Fields of odd characteristic past the Zech range (q > 2^20, p < 2^16)
for pn in [<3, 13>, <3, 16>, <3, 17>, <3, 40>, <3, 64>, <5, 9>, <7, 8>, <7, 30>, <127, 3>, <251, 10>, <257, 3>, <257, 20>, <1009, 3>, <32003, 2>, <65521, 2>] do
  p, n := Explode(pn);
  F<a> := GF(p, n);
  x := a^5 + a + 1; y := a^(n + 3) - 2*a^2;
  p, n, x*y, x/y, x^-3, x^(p^n - 2) eq x^-1, Trace(x), Norm(y), (x + y)^p eq x^p + y^p;
  Eltseq(x*y)[1..Min(n, 5)], Sqrt(x^2)^2 eq x^2, [IsSquare(y), IsSquare(x^2)], Frobenius(x, 3) eq x^(p^3);
  MinimalPolynomial(x) eq MinimalPolynomial(x^p), Degree(MinimalPolynomial(x)), CharacteristicPolynomial(y);
  #{a^i : i in [1..20]}, F ! Eltseq(x) eq x, x ne y, IsZero(x - x), IsOne(x / x), -x + x, (p - 1)*x eq -x;
end for;
F<a> := GF(251, 64);
x := a^5 + a + 1; y := a^63 + 3*a^2;
x^(251^64 - 2) eq x^-1, (x*y)/y eq x, Trace(x), Norm(x), Frobenius(x, 64) eq x, Sqrt(y^2)^2 eq y^2;
F<a> := GF(1009, 17);
x := a^5 + a + 1; y := a^16 + 3*a^2;
x^(1009^17 - 2) eq x^-1, (x*y)/y eq x, Trace(x), Norm(x), Frobenius(x, 17) eq x, Sqrt(y^2)^2 eq y^2;
F<a> := GF(4099, 24);
x := a^5 + a + 1; y := a^23 + 3*a^2;
x^(4099^24 - 2) eq x^-1, (x*y)/y eq x, Trace(x), Norm(x), Frobenius(x, 24) eq x, [IsSquare(y)];

// default moduli where no Conway polynomial is known: past p = 127, a
// binomial only when n divides p - 1
for pn in [<17, 64>, <113, 32>, <127, 27>, <137, 16>, <181, 25>, <211, 25>, <673, 64>, <1009, 27>, <2521, 64>, <32003, 16>, <65521, 16>, <65521, 17>, <65521, 32>] do
  DefiningPolynomial(GF(pn[1], pn[2]));
end for;
F<a> := GF(65521, 32);
x := a^5 + a + 1;
Norm(x), Trace(x^7), x^(65521^32 - 2) eq x^-1, Frobenius(x, 32) eq x;

// orders and logarithms
F<a> := GF(3^13);
Order(a), IsPrimitive(a), IsPrimitive(a^2), Order(a^2 + 1), Log(a^12345), Log(a^5, a^12345 * a^5), FactoredOrder(a + 1);
F<a> := GF(7^8);
Order(a), IsPrimitive(a + 1), Order(a^1200), Log(a^123456), PrimitiveElement(F) eq a;
F<a> := GF(3^40);
Order(a), IsPrimitive(a), Order(a^(3^20 + 1)), IsPrimitive(a^7 + 1), FactoredOrder(a^2 + a);

// a small field on a modulus that is not primitive
P<x> := PolynomialRing(GF(3));
K<i> := ext<GF(3) | x^2 + 1>;
i^2, i^4, Order(i), Order(i + 1), [i^k : k in [1..8]], (i + 1)^-1, Sqrt(i), IsPrimitive(i + 1), MinimalPolynomial(i + 1);
[x : x in K], [Log(i + 1, x) : x in K | x ne 0];

// polynomials
F<a> := GF(3^13);
P<t> := PolynomialRing(F);
f := (t - a)*(t - a^2)^2*(t^2 + t + a);
fac := Factorization(f);
#fac, [h : h in fac | h[2] eq 2], &*[h[1]^h[2] : h in fac] eq f, &and[IsIrreducible(h[1]) : h in fac];
#Roots(f), [r[2] : r in Roots(f) | r[1] in {a, a^2}], &and[Evaluate(f, r[1]) eq 0 : r in Roots(f)];
SquarefreeFactorization(f);
IsIrreducible(t^2 + t + a), GCD(f, Derivative(f)), XGCD(t^3 + a, t^2 + 1);
Modexp(t + a, 3^20, t^5 + t^2 + a);
DistinctDegreeFactorization(t^7 + a*t + 1);
R<u, v> := PolynomialRing(F, 2);
g := (u + a*v)^2 * (u*v + a);
Factorization(g), GCD(g, (u + a*v)*(u - v));
GroebnerBasis([u^2 + a*v, u*v + 1]);
S<u, v> := PolynomialRing(F, 2, "grevlex");
I := ideal<S | u^3 + a*v^2 + 1, u*v^2 + a^5*u + v>;
GroebnerBasis(I);
GroebnerBasis(ChangeOrder(I, R));
R<u, v, w> := PolynomialRing(GF(7^30), 3, "grevlex");
#GroebnerBasis([u^2 + v*w, v^2 + u*w + 1, w^2 + u + v]);
F<a> := GF(65521^3);
P<t> := PolynomialRing(F);
g := (t - a)*(t - a^2 - 1)*(t^2 - a);
#Roots(g), &and[Evaluate(g, r[1]) eq 0 : r in Roots(g)], [Degree(h[1]) : h in Factorization(t^4 + a)];

// subfields and extensions
F<a> := GF(3^24);
K<b> := GF(3^30);
Degree(K), b^(3^30 - 1) eq 1;
E<c> := ext<F | 2>; Degree(E, F), c^2 + c;
L := GF(3^12); Embed(L, F); L.1 in F, F ! L.1;
S := sub<F | 8>; #S, S.1 in F, MinimalPolynomial(F ! S.1);
K<k> := GF(3^13);
[K ! s : s in [[1, 2, 0, 1], [0, 1, 1, 0, 0, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]]];
