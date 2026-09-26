// Maps given by rules print as mappings, even from hom< > and iso< > (#51).
f := hom< Integers() -> Integers() | x :-> 2*x >; f;
g := hom< GF(5) -> GF(5) | x :-> x^5 >; g;
h := hom< Integers() -> Integers() | x :-> 2*x, y :-> y div 2 >; h;
i := iso< Integers() -> Integers() | x :-> -x, y :-> -y >; i;
j := iso< GF(5) -> GF(5) | x :-> x^5 >; j;
P<t> := PolynomialRing(Rationals());
k := hom< P -> P | t :-> t + 1 >; k; k(t^2);
m := map< Integers() -> Integers() | x :-> x + 1 >; m;
// The natural map from a prime field.
F := GF(7); G := GF(49);
h := hom< F -> G | >;
h;
h(3);
