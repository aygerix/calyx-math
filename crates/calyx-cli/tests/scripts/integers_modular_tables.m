// A copy of compat/pending/integers_modular_tables.m, so that calyx's output, checked against
// Magma 2.22, is kept until #24 records the output of 2.29.
// Tables of modular square roots and norm equation solutions, to check
// which root and which solution is chosen.
SetColumns(0);
for p in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 73, 89, 97, 101, 113, 193, 257, 641] do
  printf "%o:", p;
  for n in [1..p-1] do
    if LegendreSymbol(n, p) eq 1 then printf " %o", Modsqrt(n, p); end if;
  end for;
  printf "\n";
end for;
for m in [4, 8, 9, 15, 16, 21, 25, 27, 32, 45, 49, 60, 64, 100, 121, 125, 128] do
  printf "%o:", m;
  for n in [0..m-1] do
    ok := exists{b : b in [0..m-1] | b^2 mod m eq n};
    if ok then printf " %o=%o", n, Modsqrt(n, m); end if;
  end for;
  printf "\n";
end for;
for k in [3..10] do
  m := 2^k;
  printf "%o:", m;
  for n in [0..m-1] do
    ok := exists{b : b in [0..m-1] | b^2 mod m eq n};
    if ok then printf " %o=%o", n, Modsqrt(n, m); end if;
  end for;
  printf "\n";
end for;
for m in [27, 81, 243, 125, 12, 24, 36, 48, 72, 96, 200, 1000] do
  printf "%o:", m;
  for n in [0..m-1] do
    ok := exists{b : b in [0..m-1] | b^2 mod m eq n};
    if ok then printf " %o=%o", n, Modsqrt(n, m); end if;
  end for;
  printf "\n";
end for;
for d in [1, 2, 3, 5, 7] do
  for m in [0..80] do
    ok, x, y := NormEquation(d, m);
    if ok then printf "%o %o %o %o\n", d, m, x, y; end if;
  end for;
end for;
