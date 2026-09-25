// Partial factorizations: which square factors are found and how the
// cofactors are split depends on the order of the input, so this runs
// every order of a few sequences and every pair from a list of integers
// with square factors (one line per pair: F | G for each integer).
PartialFactorization([4]); PartialFactorization([8]); PartialFactorization([16]); PartialFactorization([4, 2]); PartialFactorization([2, 4]);
PartialFactorization([36, 6]); PartialFactorization([6, 36]); PartialFactorization([72, 12]); PartialFactorization([12, 72]);
PartialFactorization([45, 75]); PartialFactorization([10, 15, 6]); PartialFactorization([100, 10]); PartialFactorization([2^10, 2^3]); PartialFactorization([2^7, 3^5, 6^4]);
PartialFactorization([30, 42, 70]); PartialFactorization([12, 18, 27]); PartialFactorization([50, 20]); PartialFactorization([20, 50]);
PartialFactorization([30, 105, 385]); PartialFactorization([675, 3, 115]); PartialFactorization([115, 3, 675]);
SetColumns(0);
show := procedure(P)
  for t in P do
    for f in t[1] do printf " %o^%o", f[1], f[2]; end for;
    printf " |";
    for f in t[2] do printf " %o^%o", f[1], f[2]; end for;
    printf " ;";
  end for;
  printf "\n";
end procedure;
orders := function(s)
  if #s le 1 then return [s]; end if;
  return [ [x] cat p : p in $$(Exclude(s, x)), x in s ];
end function;
for S in [[1380, 675, 3408, 654], [30, 42, 70], [1380, 675, 3408]] do
  for T in orders(S) do
    printf "%o:", T; show(PartialFactorization(T));
  end for;
end for;
N := [2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 27, 32, 36, 45, 48, 54, 64, 72, 75, 90, 100, 108, 144, 180, 216, 225, 288, 360, 675];
for x in N do for y in N do
  printf "%o %o:", x, y; show(PartialFactorization([x, y]));
end for; end for;
// seven or more integers, where the order of the singleton subsets differs
// from 1..n, including sizes past each resize of the table.
for S in [[1, 1, 1, 1, 125, 20, 4], [27, 1, 1, 1, 24, 1, 8], [1, 5, 9, 1, 1, 1, 1, 675], [1, 1, 1, 1, 1, 1, 1, 1, 1, 125, 20, 4],
          [53900, 121000, 38416, 1715, 8575, 1100, 3969], [100, 1, 1, 10, 2, 1, 45, 72, 675]] do
  printf "%o:", S; show(PartialFactorization(S));
end for;
for n in [7, 8, 12, 13, 14, 15, 24, 25, 30, 44] do
  S := [ (i mod 6 + 2)^(i mod 3 + 1) * (i mod 4 + 2) * (i mod 5 + 1)^2 : i in [1..n] ];
  printf "%o:", n; show(PartialFactorization(S));
  printf "%o:", -n; show(PartialFactorization(Reverse(S)));
end for;
