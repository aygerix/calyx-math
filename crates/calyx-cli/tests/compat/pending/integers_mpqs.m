// MPQS: the quadratic sieve, on integers above the handbook's bound of
// 5*10^24. Magma 2.22 crashes on some inputs (1, some products of three
// primes, and often a second sieve run in one session), and after taking
// out a small factor it leaves the cofactor unfactored (MPQS(2*p*q) returns
// [<2, 1>] and [p*q]); calyx splits every part until it is prime. So this
// runs the sieve once, besides primes and prime powers.
p := 1234567000000000000000169; q := 8765432000000000000000329;
f, c := MPQS(p*q : Proof := false); f; c; Type(f), Type(c);
MPQS(p^2 : Proof := false);
MPQS(NextPrime(10^30 : Proof := false) : Proof := false);
MPQS(3^60 : Proof := false);
