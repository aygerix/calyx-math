// A finite field that nothing refers to any more is freed, and a later
// GF(q) builds a new one, without the names, power printing and attributes
// the old one was given (#71). Identifiers, elements, values holding them,
// the results $1, $2, $3 and loops over the field refer to it; subfields,
// overfields and other fields of its size do not. Each case has its own
// field.
F<f> := GF(2^6); F<f> := GF(2^7); GF(2^6).1;
for n in [8, 9] do F<e> := GF(2^n); end for; GF(2^8).1;
F<h> := GF(3^4); F := GF(3^5); GF(3^4).1;
F<k> := GF(2^10); F := 0; GF(2^10).1;
K<a> := GF(5^2); x1 := a; K := 0; a := 0; GF(5^2).1;
K<b> := GF(5^3); x2 := <b, 1>; K := 0; b := 0; GF(5^3).1;
K<c> := GF(5^4); x3 := [* c *]; K := 0; c := 0; GF(5^4).1;
K<d> := GF(5^5); x4 := {d}; K := 0; d := 0; GF(5^5).1;
K<g> := GF(5^6); x5 := rec<recformat<t> | t := g>; K := 0; g := 0; GF(5^6).1;
K<m> := GF(5^7); A := AssociativeArray(); A[1] := m; K := 0; m := 0; GF(5^7).1;
K<n> := GF(5^8); fn := func<| n>; K := 0; n := 0; GF(5^8).1; fn();
K<o> := GF(7^2); hm := hom<K -> K | o^7>; K := 0; o := 0; GF(7^2).1;
K<r> := GF(11^2); r; K := 0; r := 0; 1; 2; GF(11^2).1; 3; 4; 5; GF(11^2).1;
K<s> := GF(3^3); SetPowerPrinting(K, false); K := 0; s := 0; GF(3^3).1^5;
K<s> := GF(13^2); SetPowerPrinting(K, false); K; K := 0; s := 0; 1; 2; GF(13^2).1^5;
K<u> := GF(2^4); L := GF(2^12); y := L!u; K := 0; u := 0; GF(2^4).1;
P<X> := PolynomialRing(GF(2)); K<u> := GF(2^5); M<v> := ext<GF(2) | X^5 + X^3 + 1>; K := 0; u := 0; GF(2^5).1; M.1;
K<u> := GF(2^3); M := ext<K | 2>; K := 0; u := 0; GF(2^3).1; Eltseq(M.1^5);
K<z> := GF(17^2); for x in K do K := 0; z := 0; GF(17^2).1; break; end for;
function fu() K<q> := GF(19^2); return q; end function;
x6 := fu(); x6; 1; 2; 3; GF(19^2).1; x6 := 0; 1; 2; 3; GF(19^2).1;
function fv() K<w> := GF(23^2); K := 0; return GF(23^2).1; end function; fv();
K<w1> := GF(29^2); K := 0; w1 := 0; K<w2> := GF(29^2); GF(29^2).1;
F<l> := GF(2^21); F<l> := GF(2^22); GF(2^21).1;
F<l> := GF(3^13); x7 := l; F := 0; l := 0; GF(3^13).1; x7 := 0; 1; 2; 3; GF(3^13).1;
