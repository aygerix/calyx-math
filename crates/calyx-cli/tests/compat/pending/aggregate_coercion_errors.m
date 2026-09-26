// Elements outside a universe: associative array keys, Include, Append, and CoveringStructure without a cover.
P<x> := PolynomialRing(Integers());
A := AssociativeArray(); A[x] := 1; A[1.5] := 2; Universe(A);
S := {1, 2}; Include(~S, "a");
S := {1, 2}; T := Include(S, "a");
Q := [1, 2]; Append(~Q, "a");
Q := [1, 2]; R := Append(Q, "a");
CoveringStructure(Integers(), GF(5));
b, C := ExistsCoveringStructure(Integers(), GF(5)); b;
CoveringStructure(GF(5), GF(7));
b := ExistsCoveringStructure(GF(5), GF(7)); b;
