// Univariate polynomials: greatest common divisors, least common
// multiples, content and primitive part (handbook, Univariate Polynomial
// Rings, Common Divisors and Common Multiples).
P<x> := PolynomialRing(Integers());
S<y> := PolynomialRing(Rationals());
T<t> := PolynomialRing(GF(7));
F<w> := GF(9);
U<u> := PolynomialRing(F);
f := 6*x^4 - 6; g := 4*x^3 - 4*x^2 + 2*x - 2;
Gcd(f, g), GCD(f, -g), GreatestCommonDivisor(-f, g);
Gcd(f, P!0), Gcd(P!0, -g), Gcd(P!0, P!0), Gcd(P!-3, P!0), Gcd(P!6, P!4);
Gcd(x^2 - 1, x + 2);
Gcd(S!f, S!g), Gcd(y^2/2 - 1/2, 3*y + 3), Gcd(S!0, 2*y + 1);
Gcd(T!f, T!g), Gcd(t^7 - t, t^3 - 2*t);
Gcd(u^9 - u, u^3 + w*u), Gcd(w*u^2 + u, w*u);
Gcd(f, S!g);
Parent($1);
Gcd(f, T!g);

Xgcd(S!f, S!g);
d, a, b := Xgcd(y^3 + 1, y^2 + 3*y); d, a, b, a*(y^3 + 1) + b*(y^2 + 3*y) eq d;
Xgcd(y^2 - 1, y - 1);
Xgcd(y - 1, y^2 - 1);
Xgcd(2*y - 2, 3*y - 3);
Xgcd(S!0, S!0), Xgcd(S!0, 2*y), Xgcd(3*y + 1, S!0);
Xgcd(S!5, y^2);
XGCD(t^5 + 1, t^3 + t), ExtendedGreatestCommonDivisor(u^2 + 1, u + w);
Xgcd(f, g);

Lcm(f, g), LCM(-x, 2*x^2), LeastCommonMultiple(P!0, x);
Lcm(S!f, S!g), Lcm(y/2, y^2 + y), Lcm(t^2 - 1, t + 1);
Lcm(P!-3, P!2);
Normalize(-2*x^2 + 1), Normalize(P!0), Normalize(2*y^2 + 1), Normalize(3*t + 1), Normalize(w*u + 1);
U<v> := PolynomialRing(Integers(6));
Normalize(5*v + 3), Normalize(2*v + 1), Normalize(4*v + 1), Normalize(3*v^2 + 2), Normalize(U!0), Normalize(U!4);
Normalize(PolynomialRing(Integers(8))![1, 6]);
Normalize(PolynomialRing(RealField(10))![1, -2]);
Normalize(PolynomialRing(P)![1, -2]);
Gcd(v + 1, v + 5);
Gcd(PolynomialRing(RealField(10))![1, 1], PolynomialRing(RealField(10))![2, 2]);
Content(v^2 + 3), Content(2*v + 4), PrimitivePart(2*v + 4);
Content(PolynomialRing(P)![x, x^2]), PrimitivePart(PolynomialRing(P)![2*x, x^2 - x]);

Content(f), Content(-6*x + 4), Content(P!0), Content(P!-7);
PrimitivePart(f), PrimitivePart(-6*x + 4), PrimitivePart(P!0), PrimitivePart(P!-7);
ContentAndPrimitivePart(-6*x + 4);
c, p := Contpp(6*x^2 - 4); c, p;
Content(y^2/2 + 3), PrimitivePart(y^2/2 + 3), Content(S!0);
Content(3*t + 1), PrimitivePart(3*t + 1);
Content(w*u + w), PrimitivePart(w*u + w);
