// The proofs that CheckCertificate prints, in calyx's own words (those of
// Magma 2.29 are not known).
CheckCertificate(PrimalityCertificate(1000003) : Print := true);
c := [ [* "E", 1000000000000000000000000000057, -3, 999999999999998058691781125968, 623786892692306107, [0, 1],
  [946760654256043643941398750617, 870117905989289906146832602557] *], [* "Det", 623786892692306107 *] ];
CheckCertificate(c : Print := true);
c[1][7][2] := 1; CheckCertificate(c : Print := true);
c := [ [* "N-1", 10000000000000000000000013, 9881422924901185770751, 7075732216821963961146399 *], [* "Det", 9881422924901185770751 *] ];
CheckCertificate(c : Print := true);
CheckCertificate([c[1]] : Print := true);
CheckCertificate([c[2], c[1]] : Print := true);
CheckCertificate([ [* "Det", 15 *] ] : Print := true);
CheckCertificate([ [* "Det", 3317044064679887385962123 *] ] : Print := true);
CheckCertificate([1, 2] : Print := true);
CheckCertificate([] : Print := true);
CheckCertificate(PrimalityCertificate(NextPrime(10^40)) : Print := true);
