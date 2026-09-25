// How rings print at each level, and how assignment names rings and
// their generators.
Q := Rationals();
for R in [* Integers(), Q, RealField(), RealField(20), ComplexField(),
    ComplexField(20), Integers(6), GF(7), GF(9), GF(2^30), PolynomialRing(Q),
    PolynomialRing(Integers(6)), PolynomialRing(GF(9)), PolynomialRing(GF(7)),
    PolynomialRing(RealField()), PolynomialRing(ComplexField()),
    PolynomialRing(PolynomialRing(Q)), PolynomialRing(Integers(), 2),
    PolynomialRing(Q, 3, "grevlex"), PolynomialRing(Q, 3, "glex"),
    PolynomialRing(GF(9), 2), PolynomialRing(PolynomialRing(Q), 2),
    PolynomialRing(PolynomialRing(Q, 2), 2) *] do
    print R;
    print R : Minimal;
    print R : Magma;
end for;
[PolynomialRing(Integers(6))];
[PolynomialRing(Q, 2), PolynomialRing(Q, 2)];
<PolynomialRing(GF(5), 2), 1>;
PolynomialRing(GF(5), 2), 1;

// Generators print with the name the structure was first assigned to,
// unless they have names of their own.
F := GF(9); F.1; F.1^2 + 1;
K := F; K.1;
GF(9).1;
G := GF(2^30); G.1;
P := PolynomialRing(Q); P.1; P.1^2 + 1;
PolynomialRing(Q).1;
P;
M := PolynomialRing(Q, 2); M.1; M;
PolynomialRing(GF(9)).1;
H<z> := GF(9); F.1;
L := GF(9); L.1;
AssignNames(~L, ["r"]); L.1; F.1;
S := PolynomialRing(Integers(6)); S; S.1^2 + 1;

// Maps name their domain and codomain.
map<Integers() -> Integers() | x :-> x>;
Z := Integers();
map<Integers() -> Integers() | x :-> x>;
Y := Integers();
map<Y -> Y | x :-> x>;
map<Q -> Q | x :-> x>;
R := RealField(); map<R -> R | x :-> x>;
R2 := RealField(20); map<R2 -> R2 | x :-> x>;
B := Booleans(); map<B -> B | x :-> x>;
St := Strings(); map<St -> St | x :-> x>;
PS := PowerSet(Z); map<PS -> PS | x :-> x>;
Z6 := Integers(6); map<Z6 -> Z6 | x :-> x>;
map<F -> F | x :-> x>;
C := ComplexField(); map<C -> C | x :-> x>;
map<M -> M | x :-> x>;
map<P -> P | x :-> x>;
map<GF(7) -> GF(7) | x :-> x>;
map<PolynomialRing(Q, 2) -> Q | x :-> 1>;
