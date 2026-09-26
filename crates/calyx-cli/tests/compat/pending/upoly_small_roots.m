// Univariate polynomials: small roots modulo an integer by Coppersmith's
// method (handbook, Univariate Polynomial Rings, Roots, SmallRoots).
SetSeed(1);
F<x> := PolynomialRing (Integers());
length := 1024;
p:=NextPrime (2^(Round(length/2)): Proof:=false);
pi:=Pi(RealField());
q:=NextPrime (Round (pi*p): Proof:=false);
N := p*q;
hidden:=220;
approxq := q+Random(2^hidden-1);
A:=x-approxq;
perturb:=SmallRoots (A, N, hidden : Bits, Beta:=0.5)[1];
q eq approxq-perturb;

// Roots modulo N itself, in increasing order.
N := 1000003 * 1000033;
r := 12345;
SmallRoots(x^2 + 7*x + ((-r^2 - 7*r) mod N), N, 20000);
SmallRoots(x^2 + 7*x + ((-r^2 - 7*r) mod N), N, 15 : Bits);
SmallRoots(x^2 - 43*x - 5700, N, 200);
SmallRoots(x^2 - 43*x - 5700, N, 200 : Exponent := 1);
SmallRoots(x^2 - 43*x - 5700, N, 200 : Exponent := 0, Direct);
SmallRoots(x^2 - 43*x - 5700, -N, 200);
SmallRoots(x^2 + 1, N, 1000);
g := (x - 3)*(x + 5)*(x - 11) + N*(x^2 + 1);
SmallRoots(g, N, 50);
SmallRoots(g, N, 50 : Exponent := 2);
SmallRoots(x + 5, N, 10), SmallRoots(x - N + 5, N, 10);
SmallRoots(x - 10, N, 10), SmallRoots(x - 10, N, 9), SmallRoots(x + 10, N, 10);
SmallRoots((x - 3)^2, N, 10);
SmallRoots(x^2 - 1, 9, 1), SmallRoots(x^2 - 1, 100, 4);

// Roots modulo a large divisor of N.
p := NextPrime(2^100); q := NextPrime(3*2^100 + 12345); M := p*q;
SmallRoots(x - q - 123456789, M, 30 : Bits, Beta := 0.5);
SmallRoots(x - 5 + N, N, 250 : Beta := 0.5);

// The bound X < N^(Beta^2/d) / 2.
SmallRoots(x^2 - 43*x - 5700, N, 250000);
SmallRoots(x^2 - 43*x - 5700, N, 500009);
SmallRoots(x^2 - 43*x - 5700, N, 17 : Bits);
SmallRoots(x^2 - 43*x - 5700, N, 19 : Bits);
SmallRoots(x - 5 + N, N, 501 : Beta := 0.5);
SmallRoots(x^3 - 7, N, 2000);
SmallRoots(x^3 - 7, N, 5001);
SmallRoots(x - 17, 101, 101);
SmallRoots(x - 1, 2, 1);
SmallRoots(x + 5, 1, 10);

// Errors.
SmallRoots(F!0, N, 10);
SmallRoots(2*x + 1, N, 10);
SmallRoots(x + 5, N, -3);
SmallRoots(x + 5, N, -1 : Bits);
SmallRoots(x + 5, N, 10 : Beta := 0.0);
SmallRoots(x + 5, N, 10 : Beta := 2.0);
SmallRoots(x + 5, N, 10 : Beta := 1);
SmallRoots(x^2 - 43*x - 5700, N, 200 : Exponent := -1);
SmallRoots(x + 5, N, 10/3);
SmallRoots(x + 5, N*1.0, 10);
SmallRoots(PolynomialRing(Rationals())!(x + 5), N, 10);
SmallRoots(PolynomialRing(GF(7))!(x + 5), 7, 10);
