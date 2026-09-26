// Random integers and primes: only properties of the random values are
// printed, plus the errors for bad arguments. RandomPrime(0) and
// RandomPrime(1) return 0, and RandomPrime(n, a, b, x) wants n >= 1, as the
// handbook of 2.29 says; 2.22 wants n >= 2 in both.
x := Random(1, 6); x ge 1 and x le 6; Type(x);
Random(5, 5); Random(0);
Random(6, 1);
Random(-1);
Random(0, 2^200) lt 2^200;
RandomBits(0); b := RandomBits(10); b ge 0 and b lt 2^10;
RandomBits(-1);
RandomPrime(0); RandomPrime(1); p := RandomPrime(10); IsPrime(p) and p lt 2^10; RandomPrime(2) in {2, 3};
RandomPrime(-1);
q := RandomPrime(64: Proof := false); IsProbablePrime(q) and q lt 2^64;
ok, p := RandomPrime(20, 1, 4, 100); ok, p mod 4, IsPrime(p), p lt 2^20;
RandomPrime(20, 0, 4, 100);
RandomPrime(3, 1, 4, 100);
RandomPrime(0, 1, 4, 100);
RandomPrime(10, 5, 4, 100);
RandomPrime(10, 1, 0, 100);
RandomPrime(10, 1, 4, 0);
r := RandomConsecutiveBits(20, 1, 3); r ge 0 and r lt 2^20;
RandomConsecutiveBits(0, 1, 3);
RandomConsecutiveBits(10, 3, 1);
r := RandomConsecutiveBits(10, 0, 1); r ge 0 and r lt 2^10;
RandomPrime(2^30);
