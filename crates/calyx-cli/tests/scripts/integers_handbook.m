// A copy of compat/pending/integers_handbook.m, so that calyx's output, checked against
// Magma 2.22, is kept until #24 records the output of 2.29.
// The examples of the Ring of Integers chapter of the handbook (H19E2 to
// H19E9). H19E1 needs matrix rings, the quadratic field line of H19E2 needs
// number fields, H19E9 runs without `time`, and the NFS examples (H19E10 on)
// are not implemented.
Z := IntegerRing();
n := 1234567890;
n in Z;
m := elt< Z | 1234567890 >;
m eq n;
k := elt< Z | 0x499602D2 >;
k;
n := 1234567890;
n;
n:Hex;
{ p : p in [10^10+3..10^10+1000 by 4] |
       IsPrime(p) and IsPrime((p-1) div 2) };
d := func< m | DivisorSigma(1, m)-m >;
z := func< m | d(d(m)) eq m >;
for m := 2 to 10000 do
    if z(m) then
        m, d(m);
    end if;
end for;
NextPPRepunit := function(nn)
   n := nn;
   repeat
      n := NextPrime(n);
   until IsProbablePrime( (10^n-1) div 9 : Bases := 5);
   return n;
end function;
NextPPRepunit(1);
NextPPRepunit(2);
NextPPRepunit(19);
NextPPRepunit(23);
{ x : x in [2..1000] | &+Divisors(x) eq 2*x };
f := Factorization(496);
f;
Divisors(f);
PartialFactorization([1380, 675, 3408, 654]);
d := 957440000095744000002277749760;
m := 5102197760510219776012138128480644;
NormEquation(d, m);
f := Factorization(m);
f;
NormEquation(d, m: Factorization := f);
