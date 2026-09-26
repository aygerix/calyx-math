// A copy of compat/pending/integers_primality_certificates.m, so that calyx's output is
// kept until #24 records the output of 2.29.
// Primality certificates: small primes by the deterministic test, ECPP
// certificates checked step by step (their steps depend on the prover, so
// only their shape is printed), fixed and altered certificates, the old
// format and the errors.
c := PrimalityCertificate(1000003); c; Type(c); #c; CheckCertificate(c);
PrimalityCertificate(2); PrimalityCertificate(3317044064679887385961813);
CheckCertificate(PrimalityCertificate(2)); CheckCertificate(PrimalityCertificate(97) : Full := false);
// The steps chain from n down to a number below the Sorenson-Webster bound.
Chains := function(c, n)
  if c[1][2] ne n or c[#c][1] ne "Det" or c[#c][2] ge 3317044064679887385961981 then return false; end if;
  for i in [1..#c-1] do
    s := c[i];
    if s[1] eq "E" then
      p := s[5];
      if s[3] ge 0 or s[4] mod p ne 0 or (s[2] + 1 - s[4])^2 gt 4*s[2] then return false; end if;
    elif s[1] eq "N-1" then
      p := s[3];
      if (s[2] - 1) mod p ne 0 or Modexp(s[4], p, s[2]) ne 1 then return false; end if;
    else
      return false;
    end if;
    if c[i+1][2] ne p or not IsProbablePrime(p) then return false; end if;
  end for;
  return true;
end function;
for n in [10^25 + 13, NextPrime(10^30), 2^127 - 1, NextPrime(10^60), NextPrime(10^100)] do
  c := PrimalityCertificate(n);
  CheckCertificate(c), Chains(c, n);
end for;
// A curve step (y^2 = x^3 + 1 has 999999999999998058691781125968 points
// modulo n), which may give the curve and the point in longer forms.
c := [ [* "E", 1000000000000000000000000000057, -3, 999999999999998058691781125968, 623786892692306107, [0, 1],
  [946760654256043643941398750617, 870117905989289906146832602557] *], [* "Det", 623786892692306107 *] ];
CheckCertificate(c); OldCertificate(c)[1];
c[1][6] := [0, 0, 0, 0, 1]; c[1][7] := [946760654256043643941398750617, 870117905989289906146832602557, 1]; CheckCertificate(c);
d := c; d[1][7][1] := d[1][7][1] + 1; CheckCertificate(d);
d := c; d[1][6] := [0, 0, 0, 1, 1]; CheckCertificate(d);
d := c; d[1][5] := 623786892692306109; d[2][2] := 623786892692306109; CheckCertificate(d);
CheckCertificate([c[1], [* "Det", 13 *]]); CheckCertificate([c[1]]); CheckCertificate([c[2], c[1]]);
// An N-1 step: g has order p modulo n.
c := [ [* "N-1", 10000000000000000000000013, 9881422924901185770751, 7075732216821963961146399 *], [* "Det", 9881422924901185770751 *] ];
CheckCertificate(c);
d := c; d[1][4] := 2; CheckCertificate(d);
d := c; d[1][4] := 1; CheckCertificate(d);
CheckCertificate([ [* "N-1", 1000003, 166667, 64 *], [* "Det", 166667 *] ]);
CheckCertificate([ [* "N-1", 1000003, 3, 2 *], [* "Det", 3 *] ]);
CheckCertificate([ [* "Det", 13 *] ]); CheckCertificate([ [* "Det", 15 *] ]); CheckCertificate([ [* "Det", 3317044064679887385961981 *] ]);
OldCertificate([ [* "Det", 13 *] ]); OldCertificate(PrimalityCertificate(2));
PrimalityCertificate(0);
PrimalityCertificate(-7);
PrimalityCertificate(1);
PrimalityCertificate(15);
PrimalityCertificate(3317044064679887385961981);
PrimalityCertificate(2^89 + 1);
PrimalityCertificate(7 : Foo := 1);
CheckCertificate(PrimalityCertificate(7) : Foo := 1);
OldCertificate(PrimalityCertificate(7) : Foo := 1);
