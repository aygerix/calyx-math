// The functions that factorize store the primes that ECM and MPQS split
// off, as Factorization does: the factor found and, once its powers are
// divided out, the cofactor left if it is prime (#60).
p := 223672931272088033; q := 254165319531347639; r := 460074858985283987;
ClearStoredFactors(); x := Factorization(p*q*r^3); Sort(GetStoredFactors());
ClearStoredFactors(); x := EulerPhi(p*q*r^3); Sort(GetStoredFactors());
ClearStoredFactors(); x := #Divisors(p*q*r^3); Sort(GetStoredFactors());
ClearStoredFactors(); x := IsSquarefree(p*q*r^3); Sort(GetStoredFactors());
ClearStoredFactors(); x := SumOfDivisors(p*r^2); Sort(GetStoredFactors());
ClearStoredFactors(); x := PrimeDivisors(q*r); Sort(GetStoredFactors());
ClearStoredFactors(); x := #UnitGroup(Integers(p*q)); Sort(GetStoredFactors());
// The stored primes then split later numbers at once.
x := Factorization(p^2*q*1000003); x;
ClearStoredFactors(); GetStoredFactors();
