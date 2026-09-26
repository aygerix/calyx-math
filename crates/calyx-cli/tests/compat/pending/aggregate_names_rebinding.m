// A structure is named by the first global it is assigned to that still
// holds it; when that is rebound, the next global assigned it takes over.
// Assignments to locals name nothing (#55).
C := ComplexField(30); x := C.1; x;
C := ComplexField(20); x;
D := ComplexField(30); x;
F := GF(9); y := F.1; y;
F := GF(25); y;
P := PolynomialRing(Rationals()); t := P.1; t;
P := PolynomialRing(GF(7)); t;
E := ComplexField(40); z := E.1; E2 := E; z;
delete E; z;
h := function() S := {1, 2}; return map< S -> S | x :-> x >; end function;
h();
k := function() R := Integers(); return map< R -> R | x :-> x >; end function;
k();
E := GF(3^5); z := E.1; E2 := E; z;
delete E; z;
E3 := E2; delete E2; z;
F := GF(7^3); a := F.1; G := F; F := 1; a;
L := [GF(11^3)]; b := L[1].1; b;
M := L[1]; b;
N := GF(13^3); c := N.1; P := N; N := 2; c;
Q := GF(17^3); d := Q.1; Q := 3; d;
R := Parent(d); d;
S := GF(19^3); e := S.1; T := S; S := 4; U := T; T := 5; e;
f := function() V := GF(23^3); return V.1; end function;
g := f(); g;
W := Parent(g); g;
