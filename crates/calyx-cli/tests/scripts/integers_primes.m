// A copy of compat/pending/integers_primes.m, so that calyx's output, checked against
// Magma 2.22, is kept until #24 records the output of 2.29.
// Primality (proven and probable), prime powers, next and previous primes,
// primes in ranges and the n-th prime.
IsPrime(97); IsPrime(97: Proof := false); IsPrime(1000000007); IsPrime(2^61-1); IsPrime(2^64+13);
IsPrime(3317044064679887385961981); IsPrime(3317044064679887385961981: Proof := false);
IsPrime(2^89-1: Proof := false); IsPrime(2^89+1: Proof := false);
IsProbablePrime(97); IsProbablePrime(91); IsProbablePrime(2^89-1); IsProbablePrime(2^89-1: Bases := 5); IsProbablyPrime(7); IsProbablePrime(1); IsProbablePrime(0); IsProbablePrime(-7); IsProbablePrime(2);
IsProbablePrime(3215031751); IsProbablePrime(3215031751: Bases := 1);
IsPrimePower(8); IsPrimePower(12); IsPrimePower(1); IsPrimePower(7); IsPrimePower(-8); IsPrimePower(0); IsPrimePower(3^40);
NextPrPPRepunit := function(nn) n := nn; repeat n := NextPrime(n); until IsProbablePrime((10^n-1) div 9 : Bases := 5); return n; end function; NextPrPPRepunit(1); NextPrPPRepunit(2); NextPrPPRepunit(19);
NextPrime(0); NextPrime(1); NextPrime(2); NextPrime(100); NextPrime(-5); NextPrime(10^20); NextPrime(10^30: Proof := false);
PreviousPrime(3); PreviousPrime(100); PreviousPrime(10^20);
PreviousPrime(2);
PreviousPrime(-5);
PrimesUpTo(30); PrimesUpTo(2); PrimesUpTo(1); PrimesUpTo(0); #PrimesUpTo(10000);
PrimesUpTo(-5);
PrimesInInterval(10, 30); PrimesInInterval(2, 2); PrimesInInterval(30, 10); PrimesInInterval(-10, 10); PrimesInInterval(10^12, 10^12+100);
NthPrime(1); NthPrime(10); NthPrime(1000); NthPrime(100000);
NthPrime(0);
NthPrime(-1);
PrimeBasis(360); PrimeBasis(-360); PrimeBasis(1); PrimeDivisors(97); PrimeDivisors(2^32+1);
PrimeBasis(0);
// The limits of the prime listing functions (2.22 lists primes up to at
// least 2^30; the handbook limits PrimesUpTo to 2^30 - 1).
PrimesUpTo(2^30);
PrimesInInterval(2, 2^30 + 1);
PrimesInInterval(2^57 - 100, 2^57);
PrimesInInterval(-10, -5);
PrimesInInterval(2^57 - 100, 2^57 - 1); PrimesInInterval(2^40, 2^40 + 100); PrimesInInterval(1, 1);
NthPrime(5761455); NthPrime(5761456); NthPrime(455052511);
NthPrime(455052512);
