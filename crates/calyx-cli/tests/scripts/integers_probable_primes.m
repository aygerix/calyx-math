// A copy of compat/pending/integers_probable_primes.m, so that calyx's output, checked
// against Magma 2.22, is kept until #24 records the output of 2.29.
// Probable primes: IsProbablePrime's Bases (exact below the
// Sorenson-Webster bound, random bases above it) and the Proof parameter
// of the functions that find primes.
n := NextPrime(10^30 : Proof := false); c := n * NextPrime(10^31 : Proof := false);
IsProbablePrime(n); IsProbablePrime(n : Bases := 1); IsProbablePrime(c : Bases := 1); IsProbablePrime(-n : Bases := 3); IsProbablePrime(2*n : Bases := 3);
IsProbablePrime(3215031751 : Bases := 1); IsProbablePrime(25326001 : Bases := 1); IsProbablePrime(3317044064679887385961813 : Bases := 1);
IsProbablePrime(4 : Bases := 2^30 - 1); IsProbablePrime(97 : Bases := 1); IsProbablePrime(1 : Bases := 1); IsProbablePrime(0 : Bases := 1);
IsProbablePrime(n : Bases := 0);
IsProbablePrime(97 : Bases := -1);
IsProbablePrime(4 : Bases := 2^30);
IsProbablePrime(n : Bases := 10^30);
IsProbablePrime(n : Bases := 1.5);
IsProbablePrime(1 : Bases := "x");
IsPrime(n : Proof := false); IsPrime(c : Proof := false); IsPrime(3317044064679887385961981 : Proof := false); IsPrime(3317044064679887385961813 : Proof := false);
NextPrime(10^30 : Proof := false); NextPrime(3317044064679887385961813 : Proof := false); NextPrime(0 : Proof := false); NextPrime(2 : Proof := false);
PreviousPrime(10^30 : Proof := false); PreviousPrime(3317044064679887385962123 : Proof := false); PreviousPrime(4 : Proof := false); PreviousPrime(3 : Proof := false);
PreviousPrime(2 : Proof := false);
q := RandomPrime(100 : Proof := false); IsPrime(q) and q lt 2^100;
ok, q := RandomPrime(100, 3, 4, 1000 : Proof := false); ok, q mod 4, IsPrime(q), q lt 2^100;
IsPrime(97 : Proof := 1);
NextPrime(97 : Proof := 1);
PreviousPrime(97 : Proof := "x");
RandomPrime(10 : Proof := 1);
RandomPrime(10, 1, 4, 10 : Proof := 1);
