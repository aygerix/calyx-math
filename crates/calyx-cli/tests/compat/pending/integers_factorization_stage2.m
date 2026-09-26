// pMinus1, pPlus1 and ECM: stage 2 by default and with B2 given, x0 and
// Sigma, the checks of the arguments and parameters in their order, and
// ECMSteps. Magma's stage 2 reaches past B2 by an amount that depends on
// its choice of polynomials, so the primes found here lie well inside B2
// and those missed well outside it.
n := 1000003*1000033;
// 1000033 - 1 = 2^5*3*11*947, and 1000003 - 1 = 2*3*166667.
pMinus1(n, 100 : x0 := 3, B2 := 1000);
pMinus1(n, 100 : x0 := 3, B2 := 1000, k := 5);
pMinus1(n, 100 : x0 := 3, B2 := 10);
pMinus1(n, 100 : x0 := 3, B2 := 0);
pMinus1(n, 2 : x0 := 3, B2 := 10^6);
pMinus1(n, 100 : x0 := 3);
pMinus1(15, 10 : x0 := 2, B2 := 100);
pMinus1(9, 10 : x0 := 2);
pMinus1(7, 10);
pMinus1(2^10, 10 : x0 := 5); pMinus1(4, 1000 : x0 := 3);
// An x0 that shares a factor with n.
pMinus1(n, 1000 : x0 := 1000003);
// A negative x0 gains 2^64 (as a machine word would), so -1 is not -1; a
// larger x0 counts in full.
pMinus1(n, 1000 : x0 := 1); pMinus1(n, 1000 : x0 := -1); pMinus1(n, 1000 : x0 := -5);
pMinus1(n, 1000 : x0 := -2^64 + 1); pMinus1(n, 1000 : x0 := -2^64 - 1); pMinus1(n, 1000 : x0 := n + 1);
pMinus1(n, 1000 : x0 := 2^64 + 1); pPlus1(n, 1000 : x0 := -2, B2 := 1000);
// p + 1 goes by x0: 30029 + 1 = 2*3*5*7*11*13, and 4^2 - 4 is not a square
// modulo 30029 while 3^2 - 4 is.
m := 30029*NextPrime(10^30);
pPlus1(m, 100 : x0 := 4, B2 := 100);
pPlus1(m, 100 : x0 := 3, B2 := 100);
pPlus1(n, 1000 : x0 := 4, B2 := 1000);
pPlus1(n, 1000 : x0 := 1000003, B2 := 10^5);
pPlus1(15, 10 : x0 := 3);
pPlus1(n, 1000 : x0 := 2);
// A curve whose order modulo p is 1000-smooth but for 34037779.
p := NextPrime(10^15); N := p*NextPrime(10^30);
ECM(N, 1000 : Sigma := 187, B2 := 4*10^7) eq <p, 187>;
f, s := ECM(N, 1000 : Sigma := 187, B2 := 4*10^7); f eq p, s;
ECM(N, 1000 : Sigma := 187, B2 := 3*10^6);
ECM(n, 1000 : Sigma := 7);
ECM(n, 10 : Sigma := 7);
ECM(n, 1000 : Sigma := 1000003);
ECM(n, 1000 : Sigma := 7, x0 := 1000003);
ECM(n, 1000 : Sigma := 2^64 + 13);
ECM(15, 10 : Sigma := 7);
ECM(4, 1000 : Sigma := 7);
ECM(n, 1000 : Sigma := 7, B2 := 10^6, k := 1000);
// Without a factor only 0 comes back.
a, b := pPlus1(n, 100 : x0 := 3, B2 := 100); a;
b;
a, b := ECM(n, 10 : Sigma := 7); a;
b;
x := ECMSteps(n, 100, 10); x;
ECMSteps(n, 100, 10);
// The checks: the parameters' types, k, Sigma, then the arguments.
pMinus1(n, 0);
pMinus1(n, -5);
pPlus1(n, 1);
ECM(n, 1);
pMinus1(1, 10);
pMinus1(-15, 10 : x0 := 2);
ECM(0, 100 : Sigma := 7);
pMinus1(n, 1000 : k := 0);
ECM(n, 1000 : k := -3);
ECM(n, 1 : k := 0);
ECM(n, 1000 : Sigma := 0);
ECM(n, 1000 : Sigma := -7);
ECM(1, 1000 : Sigma := 0);
pMinus1(n, 1000 : Sigma := 0);
pMinus1(n, 1000 : x0 := 3, Sigma := 7);
pPlus1(n, 1000 : Sigma := 7);
pMinus1(4, 1000 : Sigma := 7);
pMinus1(n, 1000 : k := 0, Sigma := 0);
pMinus1(n, 1000 : x0 := "a");
pMinus1(n, 1000 : B2 := 1/2);
ECMSteps(n, 1, 10);
ECMSteps(1, 10, 100);
