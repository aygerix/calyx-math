// Relations between finite fields: embeddings, coercion, membership and
// equality across the lattice of subfields, isomorphisms, and the power
// printing option.
F7 := GF(7);
P<x> := PolynomialRing(F7);
F<z> := GF(7^4);
F49<w> := GF(7^2);

// Default fields are related through their Conway polynomials.
F!w; F!w eq z^50; w in F, z in F49, z^50 in F49, z^100 in F7, z^400 in F7;
F49!(z^100); F7!(z^400); F49!F7!3; GF(7^12)!z eq (GF(7^12)!z^50)^(7^12 - 1) * GF(7^12)!z;
w + z; Parent(w + z) eq F; Parent(w + GF(7^3).1); Parent(w * GF(7^3).1) eq GF(7^6);
w eq z^50, z^50 eq w, z eq w;

// Embeddings chosen by the user.
K<a> := ext< F7 | x^2 + 1 >;
r := AllRoots(F!-1, 2);
Embed(K, F, r[2]);
F!a eq r[2], F!(a + 1) eq r[2] + 1, a in F, (F!a)^2;
K!r[2]; K!(r[2]^2 + 3); r[1] in K, z in K;
a + z eq r[2] + z, Parent(a + z) eq F, Parent(a * w) eq F;
Embed(K, F);
// (Magma forgets an embedding into a default field nothing refers to.)
F6 := GF(7^6);
L<b> := ext< F7 | x^3 + x + 1 >;
Embed(L, F6);
MinimalPolynomial(F6!b), b in F6, b in GF(7^3), L eq F6;
Embed(F49, F);
E := ext< F7 | x^2 + 1 >;
Embed(E, F6);
MinimalPolynomial(F6!E.1);

// Subfields created in a field are related to each other through it.
G<u> := ext< F7 | x^4 + x + 1 >;
E1 := sub< G | 2 >; E2 := sub< G | 2 >;
E1 eq E2, E1 eq G, Parent(E1.1 + E2.1) eq G, Parent(E1.1 * E1.1) eq E1;
E1.1 + E2.1 eq 2*(G!E1.1), E1.1 eq E2.1, E2!E1.1 eq E2.1;
Parent(E1.1 + E2.1) eq G;
E3 := sub< G | 2 >; E4 := sub< G | 2 >;
_ := E3.1 in E4; Parent(E3.1 + E4.1) eq G;
Q<y> := PolynomialRing(GF(2));
H<t> := ext< GF(2) | y^8 + y^4 + y^3 + y + 1 >;
B := sub< H | 4 >; A := sub< B | 2 >; A2 := sub< H | 2 >; A3 := sub< B | 2 >;
Degree(Parent(A.1 + A2.1)), Degree(Parent(A2.1 + A.1)), Degree(Parent(A.1 + A3.1)), Degree(Parent(A3.1 + A2.1));
Degree(Parent(A.1 + B.1)), Degree(Parent(A2.1 + B.1)), A.1 in B, B!A2.1 eq B!(H!A2.1);
H2 := ext< H | 2 >; A4 := sub< H2 | 2 >; B4 := sub< H2 | 4 >;
Degree(Parent(A4.1 + A.1)), Degree(Parent(A4.1 + A2.1)), Degree(Parent(B4.1 + B.1)), Degree(Parent(A4.1 + B4.1)), Degree(Parent(A.1 + B4.1));
C := sub< H | B.1^5 >; Degree(C), Degree(Parent(C.1 + B.1)), Degree(Parent(C.1 + A.1));
D := sub< GF(2^8) | 4 >; D eq GF(2^4), Parent(D.1 + GF(2^4).1) eq GF(2^4);

// Fields embedded in the same field.
K1<a1> := ext< F7 | x^2 + 1 >; K2<a2> := ext< F7 | x^2 + 1 >;
Embed(K1, F, r[1]); Embed(K2, F, r[2]);
K1 eq K2, Parent(a1 + a2) eq F, a1 + a2 eq r[1] + r[2], a1 * a2;
_ := K2!a1; Parent(a1 + a2) eq F;

// Isomorphisms of fields of the same size. IsIsomorphic(E, F) is in the
// handbook but not in Magma 2.22.
b1, i := IsIsomorphic(GF(7^2), ext< F7 | x^2 + 1 >); b1; i(w)^2 eq -1 or MinimalPolynomial(i(w)) eq MinimalPolynomial(w);
b1 := IsIsomorphic(GF(7^2), GF(7^3)); b1;
b1, i := IsIsomorphic(K, F49); b1; MinimalPolynomial(i(a));

// Power printing
F<z> := GF(3^4);
z^10; z + 1; -z^0;
SetPowerPrinting(F, false);
z^10; z + 1; F!2; F!0; [z^i : i in [0..4]];
HasAttribute(F, "PowerPrinting");
AssertAttribute(F, "PowerPrinting", true);
z^10; HasAttribute(F, "PowerPrinting");
R3<v> := PolynomialRing(GF(3));
S<s> := ext< GF(3) | v^2 + v + 2 >;
s^5; SetPowerPrinting(S, false); s^5; s + 2; SetPowerPrinting(S, true); s^5; s + 2;
G<g> := ext< GF(3) | v^2 + 1 >;
g + 1; HasAttribute(G, "PowerPrinting");
K<k> := GF(2^100);
k^3; HasAttribute(K, "PowerPrinting");
HasAttribute(GF(5), "PowerPrinting");

// errors
Embed(GF(5), GF(7^2));
Embed(GF(7^3), GF(7^4));
Embed(GF(7^2), F);
Embed(ext< F7 | x^2 + 1 >, GF(7^4), z);
Embed(K1, GF(7^4), z);
a1 + ext< F7 | x^2 + 1 >.1;
GF(49)!ext< F7 | x^2 + 1 >.1;
ext< F7 | x^2 + 1 >.1 eq w;
ext< F7 | x^2 + 1 >.1 in GF(49);
ext< F7 | x^2 + 1 > eq GF(49);
GF(5) eq GF(7);
GF(7^2) eq GF(7^3);
w in GF(5);
GF(5)!w;
F7!w;
SetPowerPrinting(GF(5), true);
SetPowerPrinting(GF(2^100), true);
SetPowerPrinting(G, true);
AssertAttribute(GF(7^2), "PowerPrinting", 1);
