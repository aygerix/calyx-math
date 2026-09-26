// x @ f for values that are not maps: '@' is named only in a statement of its own; extended types of polynomial sequences.
P<x> := PolynomialRing(Integers());
f := x^2 + 1;
2 @ f;
f(2);
P2<a,b> := PolynomialRing(Integers(), 2);
h := a*b + a;
[1, 2] @ h;
y := 2 @ f;
ExtendedType([x]); ExtendedType({x}); ExtendedType([P|]); ExtendedType(x);
Q<y> := PolynomialRing(GF(5)); ExtendedType([y]); ExtendedType([[y]]);
R<a, b> := PolynomialRing(Integers(), 2); ExtendedType([a]);
