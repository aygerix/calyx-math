// Parameters an intrinsic does not take. Kernel intrinsics list the argument types; package intrinsics
// (ContinuedFraction of an integer, DirichletGroup, ECMSteps) fail as user functions do, without them.
ContinuedFraction(3 : Bound := 1);
ContinuedFraction(3/2 : Foo := 1);
DirichletGroup(5 : Foo := 1);
DirichletGroup(5, Integers(7) : Foo := 1);
ECMSteps(10, 100, 1000 : Foo := 1);
Gcd(4, 6 : Foo := 1);
EulerPhi(10 : Foo := 1);
IsPrime(7 : Bar := 1);
Sqrt(4 : Foo := 1);
f := func<x | x>; f(1 : A := 1);
g := func<x : A := 1 | x>; g(1 : B := 1);
