// Errors raised in the nearfield package code show the hidden package
// traceback: with the intrinsic's frame when the error is its own, without
// it when it comes from deeper, where another intrinsic's error keeps its
// name.
DicksonNearfield(3, -2);
x := DicksonNearfield(3, -2);
DicksonNearfield(1, 2);
x := DicksonNearfield(9, 0);
DicksonNearfield(9, 2 : LargeMatrices := 1);
NumberOfVariants(3, -2);
x := NumberOfVariants(1, 2);
VariantRepresentatives(3, -2);
x := VariantRepresentatives(9, 0);
DicksonPairs(2, -1, 1, 1, 1);
x := DicksonPairs(2, 1, 1, 0, 1);
DicksonPairs(4, 2, 2);
x := DicksonPairs(4, 2, 2);
N := DicksonNearfield(9, 2);
N ! GF(25).1;
x := N ! GF(25).1;
f := function(a, b) return NumberOfVariants(a, b); end function;
f(3, -2);
g := function(n) return DicksonNearfield(9, 2 : LargeMatrices := n); end function;
g(1);
try x := VariantRepresentatives(3, -2); catch e print e; end try;
try x := DicksonNearfield(1, 2); catch e print e; end try;
// Elements of different nearfields: / fails a requirement and ^ fails
// deeper in the package. Across kinds of nearfields every operator fails
// deeper, but ^ shows its own frame.
N2 := DicksonNearfield(25, 2);
Z := ZassenhausNearfield(1);
a := Identity(N); b := Identity(N2); c := Identity(Z);
a + b;
a / b;
x := a / b;
x := a ^ b;
a eq c;
x := c * a;
a ^ c;
x := c ^ a;
