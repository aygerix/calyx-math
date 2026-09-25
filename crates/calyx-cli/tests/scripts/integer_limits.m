// The limits of the prime listing functions, small-integer arguments,
// RandomPrime for n = 0 and 1, and norm equations where d and m share
// square factors or that need every square root modulo a prime power.
PrimesUpTo(1); PrimesUpTo(30); #PrimesUpTo(10^6);
PrimesUpTo(0);
PrimesUpTo(2^30);
PrimesInInterval(1, 1); PrimesInInterval(1, 30); PrimesInInterval(10^6, 10^6 + 100);
PrimesInInterval(2^40, 2^40 + 100); PrimesInInterval(2^57 - 100, 2^57 - 1); #PrimesInInterval(2^31, 2^31 + 10^6);
PrimesInInterval(10, 5);
PrimesInInterval(-10, -5);
PrimesInInterval(0, 10);
PrimesInInterval(2^57 - 100, 2^57);
PrimesInInterval(2, 2^30 + 1);
NthPrime(0); NthPrime(1); NthPrime(10); NthPrime(5761455); NthPrime(5761456); NthPrime(455052511);
NthPrime(455052512);
NthPrime(-1);
Fibonacci(-11); Fibonacci(-10); Lucas(-11); Lucas(-10);
GeneralizedFibonacciNumber(2, 5, -40); [ GeneralizedFibonacciNumber(3, -7, n) : n in [-6..6] ];
Fibonacci(2^30);
Fibonacci(-2^63);
Lucas(-2^30);
GeneralizedFibonacciNumber(1, 1, 2^30);
RandomPrime(0); RandomPrime(1); RandomPrime(2) in {2, 3};
RandomPrime(-1);
RandomPrime(2^30);
RandomPrime(0, 1, 4, 100);
NormEquation(6875, 1953125); NormEquation(28561, 371293); NormEquation(25, 3125); NormEquation(16, 16000); NormEquation(18, 3011499);
