// Aggregates, like structures, are known by the first name they are
// assigned to, which maps print; a loop variable names one only while the
// loop runs.
map<{1, 2} -> {1, 2} | x :-> x>;
T := {1, 2}; map<T -> T | x :-> x>;
U := T; map<U -> U | x :-> x>;
map<{1, 2} -> {1, 2} | x :-> x>;
S := [1, 2]; map<S -> S | x :-> x>;
I := {@ 1, 2 @}; map<I -> I | x :-> x>;
V := T; Include(~V, 3); map<V -> V | x :-> x>;
map<T -> Integers() | x :-> x>;
f := map<T -> T | x :-> x>; f;
for W in [ {5, 6} ] do map<W -> W | x :-> x>; end for;
for R in [* RealField(), GF(9), Integers(6) *] do print R : Minimal; end for;
RealField() : Minimal;
GF(9).1;
map<Integers(6) -> Integers(6) | x :-> x>;
for X in [* RealField(30) *] do map<X -> X | x :-> x>; end for;
Y := RealField(); Y : Minimal;
RealField() : Minimal;
RealField(25) : Minimal;
W := RealField(25); W : Minimal;
PolynomialRing(RealField(25));
ComplexField() : Minimal;
CC := ComplexField(); ComplexField() : Minimal;
