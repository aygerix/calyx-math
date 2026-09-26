// Binary fields past the Zech range (2^20 < q <= 2^512)
for n in [21, 40, 63, 64, 65, 100, 128, 150, 256, 300] do
  F<a> := GF(2^n);
  x := a^5 + a + 1; y := a^(n + 3) + a^2;
  n, x*y, x/y, x^-3, x^(2^n - 2) eq x^-1, Trace(x), Norm(y), x^2 + y^2 eq (x + y)^2;
  Eltseq(x*y)[1..5], Sqrt(x)^2 eq x, IsSquare(y), Frobenius(x, 3) eq x^8;
  MinimalPolynomial(x) eq MinimalPolynomial(x^2), Degree(MinimalPolynomial(x));
  #{a^i : i in [1..20]}, F ! Eltseq(x) eq x, x ne y, IsZero(x + x), IsOne(x / x);
end for;
F<a> := GF(2^512);
x := a^5 + a + 1; y := a^511 + a^2;
x^(2^512 - 2) eq x^-1, (x*y)/y eq x, Trace(x), Norm(x), Frobenius(x, 512) eq x, Sqrt(y)^2 eq y;

// orders and logarithms
F<a> := GF(2^40);
Order(a), IsPrimitive(a), IsPrimitive(a^3), Order(a^1023), Log(a^12345), Log(a^5, a^12345 * a^5);

// polynomials
P<t> := PolynomialRing(F);
f := (t - a)*(t - a^2)^2*(t^2 + t + a);
Factorization(f);
Roots(f);
SquarefreeFactorization(f);
IsIrreducible(t^2 + t + a), GCD(f, Derivative(f)), XGCD(t^3 + a, t^2 + 1);
Modexp(t + a, 2^20, t^5 + t^2 + a);
DistinctDegreeFactorization(t^7 + a*t + 1);
R<u, v> := PolynomialRing(F, 2);
g := (u + a*v)^2 * (u*v + a);
Factorization(g), GCD(g, (u + a*v)*(u - v));
GroebnerBasis([u^2 + a*v, u*v + 1]);
S<u, v> := PolynomialRing(F, 2, "grevlex");
I := ideal<S | u^3 + a*v^2 + 1, u*v^2 + a^5*u + v>;
GroebnerBasis(I);
GroebnerBasis(ChangeOrder(I, R));
R<u, v, w> := PolynomialRing(GF(2^100), 3, "grevlex");
#GroebnerBasis([u^2 + v*w, v^2 + u*w + 1, w^2 + u + v]);

// subfields and extensions
K<b> := GF(2^80);
Degree(K), b^(2^80 - 1) eq 1;
E<c> := ext<F | 2>; Degree(E, F), c^2 + c;
L := GF(2^20); Embed(L, F); L.1 in F, F ! L.1;
S := sub<F | 10>; #S, S.1 in F, MinimalPolynomial(F ! S.1);
K<k> := GF(2^21); [x : x in K | x ne 0 and Trace(x) eq 0 and Log(x) lt 5];
