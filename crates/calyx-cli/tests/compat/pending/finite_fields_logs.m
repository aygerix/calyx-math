// Discrete logarithms in finite fields: Log to the primitive element and
// to other bases, and Zech logarithms.

// H22E5, without the timings (its second part is at the end)
F<z> := FiniteField(7^4);
PrimitiveElement(F);
Log(z);
Log(z^2);
Log(z + 1);
z^419 eq z + 1;
b := z + 1;
b;
Log(b, b);
Log(b, z);
b^779 eq z;

// Logarithms in other fields
Log(GF(7)!3), Log(GF(7)!1), Log(GF(7)!6), Log(GF(1009)!2), Log(GF(1009)!11), Log(GF(2^61 - 1)!3);
Log(GF(1000003)!2), Log(GF(1000003)!999999);
K<k> := GF(2^100); Log(k), Log(k^12345), Log(k + 1), Log(k^3 + k + 1);
L<l> := GF(3, 40); Log(l), Log(l^2 + 1), Log(l + 2);
M<m> := GF(1000003, 2); Log(m), Log(m + 1), Log(M!5);
P<x> := PolynomialRing(GF(7));
G<u> := ext< GF(7) | x^4 + x + 1 >;
Log(PrimitiveElement(G)), Log(PrimitiveElement(G)^77), Log(u^0);
S<s> := ext< GF(7) | x^2 + x + 3 >;
Log(s), Log(s^30), Log(S!3), Log(s + 1);

// Logarithms to other bases
F<z> := GF(7^4);
Log(z^2, z^10), Log(z^2, z^11), Log(z^5, z^5), Log(z^3, F!1), Log(F!1, F!1), Log(F!1, z);
Log(z^12, z^36), Log(z^12, z^37), Log(z^2400, z), Log(F!-1, z^1200);
Log(k^3, k^300), Log(k^3, k^301) eq Log(k^3, k^301), Log(k + 1, (k + 1)^1000);
Log(GF(7)!2, GF(7)!4), Log(GF(7)!2, GF(7)!3), Log(GF(7)!3, GF(7)!2);

// Zech logarithms
ZechLog(F, 0), ZechLog(F, 1), ZechLog(F, 1200), ZechLog(F, 2399), ZechLog(F, 2400), ZechLog(F, 419), ZechLog(F, -1);
ZechLog(GF(7), 1), ZechLog(GF(7), 3), ZechLog(GF(7), 0), ZechLog(GF(2^8), 7), ZechLog(GF(2), 0);
[ZechLog(GF(9), n) : n in [0..7]];
ZechLog(K, 1), ZechLog(K, 0);
z^ZechLog(F, 419) eq z^419 + 1;

// errors
Log(F!0);
Log(z, F!0);
Log(F!0, z);
Log(z, GF(7^2).1);
Log(z, GF(5)!2);
ZechLog(F, 1/2);

// The second part of H22E5. (Magma 2.22 lacks the logarithm tables for
// GF(2^73); the values are those of the handbook.)
F<z> := GF(2, 73);
Factorization(#F-1);
PrimitiveElement(F);
Log(z + 1);
z^4295700317032218908392;
Log(z + 1);
Log(z^2);
Log(z^2134914112412412);
b := z + 1;
b;
Log(b, b);
Log(b, z);
b^2260630912967574270198;
