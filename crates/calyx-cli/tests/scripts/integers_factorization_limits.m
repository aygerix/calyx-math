// A copy of compat/pending/integers_factorization_limits.m, so that calyx's output, checked against
// Magma 2.22, is kept until #24 records the output of 2.29.
// Factorization with its stages bounded: composites stay unfactored (the
// third value, with multiplicities) only when both ECMLimit and MPQSLimit
// are given. SQUFOF works on composites of at most SQUFOFLimit digits, MPQS
// on those of 26 to MPQSLimit digits.
p := NextPrime(10^14 : Proof := false); q := NextPrime(3*10^14 : Proof := false); r := NextPrime(7*10^14 : Proof := false);
f, s, u := Factorization(p*q : ECMLimit := 0, MPQSLimit := 0); f; s; u;
f, s, u := Factorization(-2^3*1000003*p*q : ECMLimit := 0, MPQSLimit := 0); f; s; u;
f, s, u := Factorization(p*q*r : ECMLimit := 0, MPQSLimit := 0); f; s; u;
f, s, u := Factorization((p*q)^2 : ECMLimit := 0, MPQSLimit := 0); f; s; u;
f, s, u := Factorization(p^2*q : ECMLimit := 0, MPQSLimit := 0); f; s; u;
f, s, u := Factorization(p*q*1000003*1000033 : ECMLimit := 0, MPQSLimit := 0, PollardRhoLimit := 10); f; s; u;
f, s, u := Factorization(p*q : MPQSLimit := 0); f; s; assigned u;
f, s, u := Factorization(p*q : ECMLimit := 0); f; s; assigned u;
// The primes split off by ECM and MPQS are stored, and later calls try them
// before ECM.
Sort(GetStoredFactors());
f, s, u := Factorization(p*q : ECMLimit := 0, MPQSLimit := 28); f; s; assigned u;
ClearStoredFactors();
f, s, u := Factorization(p*q : ECMLimit := 0, MPQSLimit := 28); f; s; u;
f := Factorization(1009*p*q : MPQSLimit := 0, Proof := false, TrialDivisionLimit := 100, PollardRhoLimit := 0); f; Sort(GetStoredFactors());
ClearStoredFactors();
f, s, u := Factorization(1000003*1000033 : ECMLimit := 0, MPQSLimit := 0, PollardRhoLimit := 0, SQUFOFLimit := 0); f; s; u;
f, s, u := Factorization(1000003*1000033 : ECMLimit := 0, MPQSLimit := 0, PollardRhoLimit := 0, SQUFOFLimit := 0, TrialDivisionLimit := 2000000); f; s; assigned u;
for d in [8..13] do
  p := NextPrime(10^(d-1)*3 : Proof := false); q := NextPrime(10^(d-1)*7 : Proof := false);
  f, s, u := Factorization(p*q : ECMLimit := 0, MPQSLimit := 0, PollardRhoLimit := 0);
  #Sprint(p*q), f, assigned u select u else "-";
end for;
p := NextPrime(3*10^11 : Proof := false); q := NextPrime(7*10^11 : Proof := false);
f, s, u := Factorization(p*q : ECMLimit := 0, MPQSLimit := 0, PollardRhoLimit := 0, SQUFOFLimit := 23); f, assigned u select u else "-";
f, s, u := Factorization(p*q : ECMLimit := 0, MPQSLimit := 0, PollardRhoLimit := 0, SQUFOFLimit := 24); f, assigned u select u else "-";
// Negative limits count as not given.
n := 7*1000003*1000033;
for td in [-5, 0, 1, 7] do f, s, u := Factorization(n : TrialDivisionLimit := td, ECMLimit := 0, MPQSLimit := 0, PollardRhoLimit := 0, SQUFOFLimit := 0); td, f, u; end for;
f, s, u := Factorization(n : ECMLimit := -1, MPQSLimit := -1, PollardRhoLimit := -1, SQUFOFLimit := -1); f, assigned u;
f, s, u := Factorization(1000003*1000033 : ECMLimit := 0, MPQSLimit := 0, PollardRhoLimit := -1, SQUFOFLimit := 0); f, assigned u;
f, s, u := Factorization(1000003*1000033 : ECMLimit := 0, MPQSLimit := 0, PollardRhoLimit := 0, SQUFOFLimit := -1); f, assigned u;
