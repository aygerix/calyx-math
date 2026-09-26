// A copy of compat/pending/integers_gcd.m, so that calyx's output, checked against
// Magma 2.22, is kept until #24 records the output of 2.29.
// Greatest common divisors, extended gcds (of pairs and of sequences) and
// least common multiples.
GreatestCommonDivisor(12, 18); Gcd(-12, 18); GCD(0, -5); Gcd(0, 0); Gcd(2^100, 2^80*3);
GreatestCommonDivisor([12, 18, 27]); Gcd([0, 0]); GCD([-4]); Gcd([6]);
Gcd([]);
Gcd({12, 18});
ExtendedGreatestCommonDivisor(12, 18); Xgcd(-12, 18); XGCD(0, -5); Xgcd(0, 0); Xgcd(5, 0); Xgcd(240, 46); Xgcd(-240, -46);
g, X := Xgcd([12, 18, 27]); g, X; &+[X[i]*[12,18,27][i] : i in [1..3]];
g, X := Xgcd([0, 0]); g, X;
g, X := Xgcd([-6, 4]); g, X;
Xgcd([]);
LeastCommonMultiple(4, 6); Lcm(-4, 6); LCM(0, 5); Lcm(0, 0);
LeastCommonMultiple([4, 6, 10]); Lcm([-4, 6]); LCM([0, 5]); Lcm([7]);
Lcm([]);
Lcm({4, 6});
