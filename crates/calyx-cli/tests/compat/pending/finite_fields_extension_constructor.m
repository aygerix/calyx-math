// ExtensionField< F, x | P >: x names the variable of the polynomial ring
// over F in P only (#33).
F := GF(5);
K<w> := ExtensionField< F, x | x^2 + 2 >;
K; w^2; DefiningPolynomial(K);
x;
K2, m := ExtensionField< F, y | y^3 + y + 1 >; m;
L := ExtensionField< GF(2), z | z^4 + z + 1 >; L; L.1^4;
Parent(DefiningPolynomial(L));
P<t> := PolynomialRing(GF(7));
M := ExtensionField< GF(7), u | u^2 - 3 >;
DefiningPolynomial(M);
Parent(DefiningPolynomial(M)) eq P;
u := 5;
N := ExtensionField< GF(7), u | u^2 + 1 >;
u;
N;
f := function(p)
  a := 2;
  K := ExtensionField< GF(p), x | x^2 - a >;
  g := func< | x >;
  return K, a;
end function;
f(5);
h := func< q | ExtensionField< GF(q), v | v^3 - q - 1 > >;
h(3);
for p in [3, 7] do ExtensionField< GF(p), x | x^2 + 1 >; end for;
