// Failed requirements name the intrinsic unless the call is a statement of
// its own.
RandomExtension(GF(3), 0);
x := RandomExtension(GF(3), 0);
RandomIrreduciblePolynomial(GF(3), -1);
x := RandomIrreduciblePolynomial(GF(3), 0);
CommonOverfield(GF(2), GF(3));
x := CommonOverfield(GF(2), GF(3));
try x := RandomIrreduciblePolynomial(GF(3), 0); catch e print e; end try;
