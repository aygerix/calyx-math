// Assigning into, or mutating, an identifier that was never assigned: the
// error names it as undeclared, with the caret at the first operation on
// it; a failed assignment does not declare it.
zz`foo := 1;
zz[1] := 2;
zz[1]`a := 3;
zz +:= 1;
zz[1] +:= 1;
zz;
zz := 5; zz;
