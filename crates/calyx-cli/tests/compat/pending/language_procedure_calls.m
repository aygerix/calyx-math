// Procedures called as functions: intrinsics whose only matching signature is a procedure, and user procedures.
_ := Embed(GF(4), GF(16));
_ := Embed(1, 2);
x := SetSeed(1);
x := SetVerbose("Classgroup", 1);
print SetSeed(1);
SetSeed(1) + 1;
[ SetSeed(1) ];
procedure P(x) end procedure;
x := P(1);
P(1) + 1;
x := Factorization(1.5);
Embed(1, 2);
