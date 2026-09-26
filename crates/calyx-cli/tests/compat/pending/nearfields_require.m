// Failed requirements of the nearfield intrinsics name the intrinsic unless
// the call is a statement of its own.
DicksonPairs(4, 1, 2, 1, 2);
x := DicksonPairs(4, 1, 2, 1, 2);
DicksonTriples(4, 2, 2);
x := DicksonTriples(4, 2, 2);
NumberOfVariants(5, 3);
x := NumberOfVariants(5, 3);
VariantRepresentatives(5, 3);
x := VariantRepresentatives(5, 3);
DicksonNearfield(5, 3);
x := DicksonNearfield(5, 3);
DicksonNearfield(9, 2 : Variant := 2);
x := DicksonNearfield(9, 2 : Variant := 2);
ZassenhausNearfield(8);
x := ZassenhausNearfield(8);
N := DicksonNearfield(9, 2);
Element(N, GF(25).1);
x := Element(N, GF(25).1);
Inverse(Zero(N));
x := Inverse(Zero(N));
Order(Zero(N));
x := Order(Zero(N));
[Order(Zero(N))];
