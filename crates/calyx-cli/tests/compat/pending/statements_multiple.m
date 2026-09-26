// Generator names in multiple assignments (#58), and func< > with several
// return values.
P<x> := PolynomialRing(Rationals());
Q<q>, h := quo<P | x^2 + 1>;
Q; q; h; q^2;
S<y>, g := ChangeRing(P, GF(5));
S; y; g;
f := func< | 7, PolynomialRing(GF(3))>;
a, R<t> := f();
a; R; t;
T<u>, _ := quo<P | x^3 - 2>;
T; u^3;
k := func< | quo<P | x^2 + 2>, quo<P | x^2 - 5> >;
B<b>, C<c> := k();
B; C; b^2; c^2;
g2 := func<z | z, z^2>;
m, n := g2(3);
m, n;
g2(4);
g2(5) + 1;
