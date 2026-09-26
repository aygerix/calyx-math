// Homomorphisms from finite fields: hom< F -> R | x > sends the generator
// of F over its prime field to x.
F<w> := GF(4);
h := hom< F -> F | w^2 >;
h;
[h(a) : a in [F!0, F!1, w, w^2, w + 1]];
G<z> := GF(16);
e := hom< F -> G | z^5 >;
e;
[e(a) : a in [F!0, F!1, w, w^2]];
e(w)^2 + e(w) + 1;
e(1), e(3);

// Magma gives these maps no inverse and no image.
(z^5) @@ e;
HasPreimage(z^5, e);
Inverse(e);
Image(e);
e(z);

// A field that is not prime takes one image, and a prime field none; the
// image must lie in the codomain, which need not be a field.
hom< F -> F | w, w >;
hom< F -> F | >;
iso< F -> F | w, w >;
hom< GF(7) -> GF(49) | 3 >;
hom< F -> Integers() | w >;
hom< F -> F | [w] >(w);
j := hom< F -> Integers() | 1 >; j; j(w), j(w^2), j(F!1);
j := hom< F -> Rationals() | 3 >; j(w), j(w^2);
j := hom< F -> GF(3) | 2 >; j; j(w), j(w^2);

// A field whose generator is not that of its Zech table, and larger fields
P<x> := PolynomialRing(GF(2));
K<k> := ext< GF(2) | x^4 + x^3 + 1 >;
m := hom< K -> G | z^14 >;
m;
m(k) eq z^14, m(k^2 + 1) eq z^28 + 1, m(k^7 + k^3) eq z^98 + z^42;
&and[m(k^i) eq z^(14*i) : i in [0..14]];
q := hom< K -> G | [z^14] >; q(k^3);
L<l> := GF(7^3);
M<u> := GF(7^6);
r := hom< L -> M | u^(1 + 7^3) >;
r(l)^3 - 3*r(l) eq (l^3 - 3*l) @ r;
B := GF(2^100);
t := hom< B -> B | B.1^2 >; t(B.1^3) eq B.1^6, t(B.1 + 1) eq B.1^2 + 1;

// (Magma leaves it to the user that the map is a homomorphism.)
s := hom< F -> F | 1 >; s(w), s(w^2);
