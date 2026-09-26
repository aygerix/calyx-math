// Isomorphisms between Dickson nearfields: IsIsomorphic and the maps it
// returns.

// Variants s and t of a pair are isomorphic when t = s p^j modulo v; the
// isomorphism is then x -> x^(p^j) for the least such j. (When p^j > v,
// Magma 2.22 raises to the power p^j modulo v instead, which is no
// isomorphism, so those cases are left out.)
D := DicksonNearfield(625, 4);
D3 := DicksonNearfield(625, 4 : Variant := 3);
D5 := DicksonNearfield(625, 4 : Variant := 5);
IsIsomorphic(D, D3);
IsIsomorphic(D3, D5);
IsIsomorphic(D, D5);
l, f := IsIsomorphic(D3, D5); l;
l, g := IsIsomorphic(D, D);
g;
K<k> := D`gf;
[g(D!(k^i)) : i in [1..4]];
N := DicksonNearfield(3^3, 13 : Variant := 2);
M := DicksonNearfield(3^3, 13 : Variant := 6);
IsIsomorphic(N, M);
IsIsomorphic(M, N);
IsIsomorphic(N, DicksonNearfield(3^3, 13 : Variant := 4));
IsIsomorphic(N, DicksonNearfield(3^3, 13 : Variant := 15));
l, g := IsIsomorphic(N, M);
F<a> := N`gf;
x := N!a;
g(x), x @ g, g(N!(a^2 + 1)) eq M!(a^6 + 1), g(N!0), g(1), g(a), Type(g);
Domain(g) eq N, Codomain(g) eq M, Domain(g), Codomain(g);
y := g(x); y @@ g, (M!a) @@ g eq N!(a^(3^38)), a @@ g eq N!(a^(3^38));
h := Inverse(g); h; h(M!(a^3));
(g * h)(x) eq x;
E := [N!(a^i + i) : i in [1..6]] cat [N!(a^100), N!1, N!0];
&and[g(u + w) eq g(u) + g(w) and g(u*w) eq g(u)*g(w) : u, w in E];
for t in [<27, 13, 2, 5>, <27, 13, 6, 2>, <27, 13, 1, 9>, <25, 8, 1, 5>, <25, 8, 3, 7>, <9, 4, 1, 3>, <7, 9, 2, 5>, <7, 9, 5, 8>, <7, 9, 8, 2>, <3, 2, 1, 1>] do
    A := DicksonNearfield(t[1], t[2] : Variant := t[3]);
    B := DicksonNearfield(t[1], t[2] : Variant := t[4]);
    l, h := IsIsomorphic(A, B);
    G := A`gf; z := G.1;
    t, l, [j : j in [0..Degree(G) - 1] | h(A!z) eq B!(z^(A`p^j))];
end for;

// Nearfields with different pairs are not isomorphic.
IsIsomorphic(DicksonNearfield(9, 4), DicksonNearfield(81, 2));
IsIsomorphic(DicksonNearfield(5, 2), DicksonNearfield(25, 1));
IsIsomorphic(DicksonNearfield(25, 1), DicksonNearfield(5, 1));
IsIsomorphic(DicksonNearfield(5, 2), DicksonNearfield(3, 2));
IsIsomorphic(DicksonNearfield(25, 1), DicksonNearfield(25, 1));

// Maps between nearfields without names: Magma prints them in full, and
// what it prints for them does not count toward the width of the line.
IsIsomorphic(DicksonNearfield(3, 2), DicksonNearfield(3, 2));
D32 := DicksonNearfield(3, 2);
l, h := IsIsomorphic(D32, DicksonNearfield(3, 2)); h;
l, h := IsIsomorphic(DicksonNearfield(3, 2), D32); h;
1234567890, h;
<h, h>;
<h, 12345678901234567890123456789012345, h>;
print D32 : Minimal;
<D32, 1234567890123456789012345678901234567890123456789012345678901234567890123>;
c := N!(a^5 + 2*a^2 + 1);
<c, 1234567890123456789012345678901234567890123456789012345678901234567890>;

// Errors
IsIsomorphic(DicksonNearfield(5, 2), ZassenhausNearfield(1));
IsIsomorphic(ZassenhausNearfield(1), ZassenhausNearfield(1));
IsIsomorphic(N, GF(3^39));
g(M!a);
(N!a) @@ g;
Image(g);
