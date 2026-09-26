// Factorization sequences with a negative exponent, or one of 2^64 or more,
// are errors in calyx (#10): Magma 2.22 gives meaningless answers for them
// (a negative number of divisors, say) or stops with an internal error.
// So are products and powers whose exponents overflow a word.
x := Factorization(12); x[1] := <2, -3>;
Facint(x);
NumberOfDivisors(x);
EulerPhi(x);
x * x;
x ^ 2;
Gcd(x, x);
IsSquarefree(x);
x := Factorization(12); x[1] := <2, 2^64>;
EulerPhi(x);
Facint(x);
(Factorization(2)^(2^62))^4;
F := Factorization(2)^(2^62); F*F*F*F;
