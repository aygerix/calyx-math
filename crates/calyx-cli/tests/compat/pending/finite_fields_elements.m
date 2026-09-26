// Elements of finite fields: creation, the generator, primitive and
// normal elements, and conversion to and from sequences over subfields.
F7 := GF(7);
P<x> := PolynomialRing(F7);
F<z> := GF(7^4);
F49<w> := GF(7^2);

// Creation of elements
One(F), Identity(F), Zero(F), Representative(F), F.1, F!3, F!(-1), F!(3/5), F!w, F7!10;
elt< F | 5 >; elt< F | 1, 2, 3, 4 >; elt< F | 1, 2 >; F![1, 2, 3, 4]; F![0, 1]; F7![3];
elt< F49 | 2, 3 >; F49![2, 3] eq 2 + 3*w;
Random(F) in F, Random(F7) in F7, Random(GF(2^100)) in GF(2^100), Parent(Random(F)) eq F;
Integers()!(F7!5), Integers()!(F!3), IntegerRing()!F7!6;
Type(F!1), Category(F!1), Parent(z) eq F, Parent(F7!1) eq F7;
AssignNames(~F, ["t"]); F.1; Name(F, 1);
F<z> := GF(7^4); F.1;
G<u> := ext< F7 | x^4 + x + 1 >;
u^2; u^4; u^400; u^-1; G![1, 1]; elt< G | 0, 1, 2, 3 >;
H<h> := ext< F49 | 3 >; H.1 eq GF(7^6).1;
Q<y> := PolynomialRing(F49);
R<r> := ext< F49 | y^2 + y + 6*w + 4 >;
r^2; R![w, 1]; elt< R | 1, w >; R!w; R![1, 2]; w*r + 1; Eltseq(w*r + 1);

// The generator, primitive and normal elements
Generator(F), Generator(G), Generator(R), Generator(F7), Generator(F, F49), Generator(R, F49);
Generator(R, F7) eq R.1, Generator(G, F7) eq u, Generator(F, F7);
PrimitiveElement(F), PrimitiveElement(F7), PrimitiveElement(F49), PrimitiveElement(GF(2)), PrimitiveElement(GF(1009));
PrimitiveElement(GF(2^90)), PrimitiveElement(GF(3^50));
PrimitiveElement(GF(1000003)), PrimitiveElement(GF(2^61 - 1)), PrimitiveElement(GF(1000003, 2));
S<s> := ext< F7 | x^2 + x + 3 >; PrimitiveElement(S);
IsPrimitive(PrimitiveElement(G)), IsPrimitive(PrimitiveElement(R)), MinimalPolynomial(PrimitiveElement(G)) eq ConwayPolynomial(7, 4);
// GF(2), where q - 1 has no prime factors.
Order(GF(2)!1); IsPrimitive(GF(2)!1); PrimitiveElement(GF(2));
Order(GF(2^3)!1), IsPrimitive(GF(2^3)!1), Order(GF(2, 70)!1), IsPrimitive(GF(2, 70)!1), Order(GF(3)!2), IsPrimitive(GF(3)!1);
K<k> := GF(2^100);
SetPrimitiveElement(K, k^7); PrimitiveElement(K) eq k^7, Log(k^7), Log(k) eq Modinv(7, 2^100 - 1), Log(k^14);
SetPrimitiveElement(K, k^7);
R5<t> := PolynomialRing(GF(5));
L<l> := ext< GF(5) | t^3 + 3*t + 2 >;
IsPrimitive(l), PrimitiveElement(L) eq l, Log(l^4);
// (Magma chooses normal elements at random.)
IsNormal(NormalElement(F)), IsNormal(NormalElement(F49)), IsNormal(NormalElement(F, F49), F49), NormalElement(F7), NormalElement(F, F);
IsNormal(NormalElement(G)), IsNormal(NormalElement(GF(2^8))), IsNormal(NormalElement(GF(3^5))), IsNormal(NormalElement(GF(2^100)));
IsNormal(NormalElement(R)), IsNormal(NormalElement(R, F49), F49), IsNormal(NormalElement(R, F7), F7), IsNormal(NormalElement(H, GF(7^3)), GF(7^3));

// Sequences over subfields
Eltseq(z^100), ElementToSequence(z^100), Eltseq(z^100, F49), Eltseq(z, F), Eltseq(F7!3), Eltseq(z, F7);
Eltseq(w), Eltseq(w, F7), Eltseq(F!w, F49), Eltseq(F!w), Eltseq(F!3, F49);
Eltseq(u^5), Eltseq(u^5, F7), Eltseq(r^3), Eltseq(r^3, F49), Eltseq(r^3, F7), Eltseq(R!w, F49);
Eltseq(h^20), Eltseq(h^20, F49), Eltseq(h^20, GF(7^3)), Eltseq(h^20, GF(7^6));
Seqelt([1, 2, 3, 4], F), SequenceToElement([F7 | 1, 2, 3, 4], F), Seqelt([w, w^2], F), Seqelt([F7!5], F7);
Seqelt(Eltseq(z^1234, F49), F) eq z^1234, Seqelt(Eltseq(r^7, F7), R) eq r^7, Seqelt(Eltseq(h^20, GF(7^3)), H) eq h^20;
Seqelt([w, 1], R), Seqelt([1, 0, 0, 1], G), Seqelt([F49 | 1, 2], R);
[Eltseq(a, F49) : a in [z^0, z, z^50, z^2400]];
Eltseq(GF(2^100).1^101)[1..10];

// errors
F.2;
F.0;
elt< F | 1, 2, 3, 4, 5 >;
F![1, 2, 3, 4, 5];
F!(1/7);
F!GF(5)!1;
Eltseq(z, GF(5));
Eltseq(z, GF(7^3));
Eltseq(z, ext< F7 | x^2 + 1 >);
Seqelt([1, 2, 3], F);
Seqelt([1, 2, 3, 4, 5], F);
Seqelt([GF(7^3) | 1, 2], F);
Seqelt([GF(5) | 1, 2, 3, 4], F);
Generator(F, GF(7^3));
Generator(F, GF(5));
NormalElement(F, GF(7^3));
SetPrimitiveElement(F, z^2);
SetPrimitiveElement(F, z^7);
SetPrimitiveElement(F, F49.1);
SetPrimitiveElement(G, u);
SetPrimitiveElement(GF(5^3), GF(5^3).1^7);
SetPrimitiveElement(L, l^3);
SetPrimitiveElement(K, k);
SetPrimitiveElement(K, k^3);
