// Element operations in finite fields: arithmetic, predicates, minimal
// and characteristic polynomials, norms, traces, the Frobenius, orders
// and roots.
F7 := GF(7);
P<x> := PolynomialRing(F7);
F49<w> := GF(7^2);
F<z> := ext< F49 | 2 >;
G<u> := ext< F7 | x^4 + x + 1 >;
K<k> := GF(2^100);
L<l> := GF(1000003, 2);
M := GF(2^61 - 1);

// Arithmetic
+z, -z, z + z^2, z - 1, 3*z, z*w, z/w, z^100, z^-1, z^(7^4), z^(2^100), (-z)^0, (F!0)^0, (F!0)^5;
z + 1/3, z*(2/5), 1/z, 2/z, w - z, (z^2 - 1)/(z - 1) eq z + 1, -F7!3, F7!3/5, F7!2^-1;
u^2 + u, u*u^3, (u + 1)/(u - 1), u^-5, u^(7^4 - 1), -u, u - u;
k^100 + k, k^-1 * k, (k + 1)^-1 * (k + 1), k^(2^100 - 1), k^(2^200) eq k;
l^2 + 3*l, l^-1 * l, (l + 1)/(l - 1), l^1000003 eq -l + Trace(l), M!2^61, (M!3)^-1 * 3, M!(2^61) - 2;
a := z; a +:= w; a; a -:= 1; a; a *:= z; a; a /:= z; a; a ^:= 2; a;
b := u; b *:= u; b; b +:= 1; b;

// Equality and membership
z eq z^2401, z ne z^2401, z^50 eq w, z eq 1, F!3 eq 3, 3 eq F!3, z^2400 eq 1, z^1200 eq -1;
z in F, z notin F, w in F, z in F49, z^50 in F49, z^50 notin F49, 3 in F, (1/2) in F, u in G, u^400 in G;
F7!3 eq 10, F7!3 eq 1/5, F!(1/5) eq 3;

// Parent and category
Parent(z), Parent(w + z) eq F, Parent(F7!3) eq F7, Parent(k) eq K, Category(z), Category(k), Category(F7!1);

// Predicates on ring elements
IsZero(z), IsZero(F!0), IsOne(z^2400), IsOne(z), IsMinusOne(z^1200), IsMinusOne(z), IsMinusOne(F7!6);
IsNilpotent(z), IsNilpotent(F!0), IsIdempotent(F!1), IsIdempotent(z), IsIdempotent(F!0);
IsUnit(z), IsUnit(F!0), IsZeroDivisor(z), IsZeroDivisor(F!0), IsRegular(z), IsRegular(F!0);
IsIrreducible(z), IsIrreducible(F!0), IsPrime(z), IsPrime(F!0);
IsPrimitive(z), IsPrimitive(z^2), IsPrimitive(w), IsPrimitive(z^50), IsPrimitive(u), IsPrimitive(F7!3), IsPrimitive(F7!2), IsPrimitive(F!0);
IsPrimitive(k), IsPrimitive(k^3), IsPrimitive(k^7), IsPrimitive(l), IsPrimitive(M!3), IsPrimitive(M!37);
IsPrimitive(x^2 + x + 3), IsPrimitive(x^2 + 1), IsPrimitive(x^4 + x + 1), IsPrimitive(ConwayPolynomial(7, 5)), IsPrimitive(x - 3), IsPrimitive(x - 2);
IsPrimitive(PolynomialRing(GF(2))!ConwayPolynomial(2, 100)), IsPrimitive(PolynomialRing(F49).1^2 + w);
IsNormal(z), IsNormal(z^2), IsNormal(z, F49), IsNormal(z, F7), IsNormal(w), IsNormal(F!1), IsNormal(F!1, F), IsNormal(z, F);
IsNormal(u), IsNormal(u^3), IsNormal(k), IsNormal(k^3), IsNormal(F7!3), IsNormal(F7!0), IsNormal(F!0, F);
IsSquare(z), IsSquare(z^2), IsSquare(w), IsSquare(F!w), IsSquare(F7!2), IsSquare(F7!3), IsSquare(F!0), IsSquare(k), IsSquare(k^2);
b1, s := IsSquare(F7!2); b1, s^2; b1, s := IsSquare(z^6); b1, s^2 eq z^6; b1, s := IsSquare(l^2); b1, s^2 eq l^2;
// (The roots Magma finds in a field like G depend on how it was embedded.)
b1, s := IsSquare(u^2); b1, s^2 eq u^2; b1, s := IsPower(u^5, 5); b1, s^5 eq u^5;

// Minimal and characteristic polynomials
MinimalPolynomial(z), MinimalPolynomial(z, F49), MinimalPolynomial(z, F7), MinimalPolynomial(w), MinimalPolynomial(z^50);
MinimalPolynomial(z^50, F7), MinimalPolynomial(F!3), MinimalPolynomial(F!0), MinimalPolynomial(z, F), MinimalPolynomial(u);
MinimalPolynomial(u^400), MinimalPolynomial(k^((2^100 - 1) div 3)), MinimalPolynomial(l);
CharacteristicPolynomial(z), CharacteristicPolynomial(z^50, F7), CharacteristicPolynomial(z^50), CharacteristicPolynomial(F!3, F7);
CharacteristicPolynomial(F!0), CharacteristicPolynomial(u^400), CharacteristicPolynomial(z, F), CharacteristicPolynomial(F7!3);

// Norm, trace and Frobenius
Norm(z), Norm(z, F49), Norm(z, F7), Norm(z, F), Norm(w), Norm(F!w), Norm(F!0), Norm(u), Norm(k), Norm(l), Norm(F7!3);
Trace(z), Trace(z, F49), Trace(z, F7), Trace(z, F), Trace(w), Trace(F!w), Trace(F!1), Trace(u), Trace(k), Trace(l), Trace(F7!3);
AbsoluteNorm(z), NormAbs(z), AbsoluteTrace(z), TraceAbs(z), AbsoluteNorm(w), AbsoluteTrace(u^3), AbsoluteNorm(k^3), AbsoluteTrace(k^3);
Frobenius(z), Frobenius(z, 2), Frobenius(z, F7), Frobenius(z, F7, 3), Frobenius(z, F49), Frobenius(z, 0), Frobenius(z, -1);
Frobenius(u), Frobenius(u, 4), Frobenius(k) eq k^2, Frobenius(k, 100) eq k, Frobenius(k, GF(2^4), 3) eq k^(2^12), Frobenius(l) eq l^1000003;
Frobenius(F7!3), Frobenius(w, F7), Frobenius(w, F49), Frobenius(F!w), Frobenius(z, F);
// (Magma chooses the solution of a norm equation at random.)
b1, s := NormEquation(F, F7!3); b1, Norm(s);
b1, s := NormEquation(F, w^30); b1, Norm(s, F49) eq w^30, Parent(s) eq F;
b1, s := NormEquation(F, F49!0); b1, s;
b1, s := NormEquation(G, F7!5); b1, Norm(s) eq 5;
b1, s := NormEquation(K, GF(2^4).1); b1, Norm(s, GF(2^4)) eq GF(2^4).1;
// (Hilbert90 and AdditiveHilbert90 return one value, as in the handbook.)
s := Hilbert90(z^8, 49); s^48 eq z^8, Degree(Parent(s));
s := Hilbert90(z^8, 7); s^6 eq z^8, Degree(Parent(s));
s := Hilbert90(F!0, 7); s;
s := Hilbert90(w, 7); s^6 eq w, Degree(Parent(s));
s := AdditiveHilbert90(z^8, 49); s^49 - s eq z^8, Degree(Parent(s));
s := AdditiveHilbert90(z, 7); s^7 - s eq z, Degree(Parent(s));
s := AdditiveHilbert90(F7!3, 7); s^7 - s eq 3, Degree(Parent(s));

// Order and roots
Order(z), Order(z^50), Order(w), Order(F!1), Order(F!-1), Order(u), Order(u^100), Order(F7!2), Order(k), Order(k^3), Order(l^2), Order(M!2);
FactoredOrder(z), FactoredOrder(z^50), FactoredOrder(F!1), FactoredOrder(k), FactoredOrder(M!2), FactoredOrder(F7!2);
Sqrt(z^2), SquareRoot(w^2), Sqrt(F!4), Sqrt(F7!2), Sqrt(F!0), Sqrt(z^6), Sqrt(F!w);
Sqrt(u^2)^2 eq u^2, Sqrt(k)^2 eq k, Sqrt(k^3)^2 eq k^3, Sqrt(l^2)^2 eq l^2, Sqrt(M!4)^2 eq 4, Sqrt(GF(1019)!5), Sqrt(GF(11)!5);
Root(z^6, 3), Root(z^73, 7), Root(w, 7), Root(F!1, 5), Root(F!0, 3), Root(z^10, 5), Root(z, 1), Root(z^2400, 2400);
Root(k^3, 3)^3 eq k^3, Root(u^4, 4)^4 eq u^4, Root(l^5, 5)^5 eq l^5;
IsPower(z, 2), IsPower(z^2, 2), IsPower(z^3, 3), IsPower(z^6, 4), IsPower(F!0, 5), IsPower(F7!6, 3), IsPower(F7!6, 2);
IsPower(k, 3), IsPower(k^3, 3), IsPower(k, 5), IsPower(u^10, 4);
AllRoots(z^6, 3), AllRoots(F!1, 5), AllRoots(F!1, 1), AllRoots(z^8, 16), AllRoots(z, 2), AllRoots(F!0, 4), AllRoots(F7!1, 6), AllRoots(F7!2, 3);
#AllRoots(F!1, 2400), #AllRoots(k^3, 3), #AllRoots(u^16, 16), Sort(AllRoots(F7!6, 2));

// H22E4
F7 := FiniteField(7);
F49<w> := ext< F7 | 2 >;
F<z> := ext< F49 | 2 >;
Root(z^73, 7);
Trace(z^73);
Trace(z^73, F49);
Norm(z^73);
Norm(z^73, F49);
Norm(w^37);
MinimalPolynomial(z^73);
MinimalPolynomial(z^73, F7);
Norm(z);
Norm(z^30, F49);
Parent(z) eq F;

// errors
z/0;
(F!0)^-1;
z/(F!0);
Order(F!0);
FactoredOrder(F!0);
Sqrt(z);
Sqrt(F7!3);
Root(z, 2);
Root(z, 0);
Root(z, -2);
Root(F!0, 0);
IsPower(z, 0);
IsPower(z, -3);
AllRoots(z, 0);
AllRoots(z, -1);
Norm(z, GF(7^3));
Norm(z, GF(5));
Trace(z, GF(7^3));
Trace(w, F);
MinimalPolynomial(z, GF(7^3));
CharacteristicPolynomial(z, GF(5));
Frobenius(z, GF(7^3));
Frobenius(z, GF(7^3), 2);
IsNormal(z, GF(7^3));
NormEquation(F, GF(7^3).1);
NormEquation(F, GF(5)!2);
Hilbert90(z, 1);
Hilbert90(z, 6);
Hilbert90(z, 5);
AdditiveHilbert90(z, 0);
AdditiveHilbert90(z, 3);
z + GF(5)!1;
z * GF(7^3).1^0 + GF(11)!1;
