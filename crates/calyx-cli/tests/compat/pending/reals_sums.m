// Summation of infinite series: InfiniteSum, PositiveSum and AlternatingSum
// of a map from the integers to a real field (or a complex one for
// InfiniteSum). The sums are computed in 128 bits and returned in the field
// of the terms.

Z := Integers(); Q := Rationals(); R := RealField(20); C<i> := ComplexField(20);

// InfiniteSum adds terms until three in a row are negligible.
InfiniteSum(map< Z -> RealField() | n :-> 1/3^n >, 1), InfiniteSum(map< Z -> RealField() | n :-> 1/Factorial(n) >, 1);
InfiniteSum(map< Z -> RealField() | n :-> 1/2^n >, 5), InfiniteSum(map< Z -> RealField() | n :-> -1/3^n >, 0);
InfiniteSum(map< Z -> RealField() | n :-> 10/3^n >, 0), InfiniteSum(map< Z -> RealField() | n :-> R!0 >, 1);
x := InfiniteSum(map< Z -> R | n :-> 1/3^n >, 1); x, MantissaExponent(x), Parent(x);
x := InfiniteSum(map< Z -> R | n :-> n le 3 select 0 else 1/3^n >, 1); x, Parent(x);
// The terms it evaluates. (In Magma 2.22, an InfiniteSum of terms that are
// not reals after a PositiveSum or AlternatingSum is 2 less than the sum.)
h := function(n) printf "."; return 1/3^n; end function;
x := InfiniteSum(map< Z -> R | n :-> h(n) >, 1); print ""; x;

// PositiveSum transforms a series of positive terms into an alternating one.
x := PositiveSum(map< Z -> RealField() | n :-> 1/n^2 >, 1); x, MantissaExponent(x), Parent(x);
x := PositiveSum(map< Z -> R | n :-> 1/n^2 >, 1); x, MantissaExponent(x), Parent(x);
PositiveSum(map< Z -> R | n :-> 1/n^3 >, 1), PositiveSum(map< Z -> R | n :-> 1/2^n >, 0), PositiveSum(map< Z -> R | n :-> 1/(n^2 + 1) >, -3);
PositiveSum(map< Z -> R | n :-> n eq 3 select 0 else 1/n^2 >, 1), PositiveSum(map< Z -> R | n :-> n eq 12 select -1 else 1/n^2 >, 1);
// The terms it evaluates: here the series stops at n = 39.
f := function(n) printf "%o ", n; return n lt 40 select 1/n^2 else 0; end function;
x := PositiveSum(map< Z -> R | n :-> f(n) >, 1); print ""; x;

// AlternatingSum by the Cohen-Villegas-Zagier acceleration (the default),
// or by Euler's transformation in van Wijngaarden's form.
m := map< Z -> RealField() | n :-> (-1)^n/n >;
x := AlternatingSum(m, 1); x, MantissaExponent(x), Parent(x);
x := AlternatingSum(m, 1 : Al := "Villegas"); x, MantissaExponent(x);
x := AlternatingSum(m, 1 : Al := "EulerVanWijngaarden"); x, MantissaExponent(x);
m := map< Z -> R | n :-> (-1)^n/n^2 >;
AlternatingSum(m, 1), Parent(AlternatingSum(m, 1));
m := map< Z -> RealField() | n :-> (-1)^n/n^2 >;
AlternatingSum(m, 1), AlternatingSum(m, 1 : Al := "EulerVanWijngaarden");
m := map< Z -> RealField() | n :-> (-1)^n*Exp(-n/10) >;
AlternatingSum(m, 0), AlternatingSum(m, 0 : Al := "EulerVanWijngaarden");
m := map< Z -> R | n :-> (-1)^n*Exp(-R!n/10) >;
AlternatingSum(m, 1 : Al := "EulerVanWijngaarden");
m := map< Z -> R | n :-> (-1)^n >;
AlternatingSum(m, 1), AlternatingSum(m, 1 : Al := "EulerVanWijngaarden");
// Zero terms: alternation is only checked between consecutive terms.
AlternatingSum(map< Z -> R | n :-> n le 3 select 0 else (-1)^n/n >, 1), AlternatingSum(map< Z -> R | n :-> n eq 2 select 0 else (-1)^n/n >, 1);
AlternatingSum(map< Z -> R | n :-> n eq 4 select 0 else (-1)^(n + (n gt 4 select 1 else 0))/n >, 1);
AlternatingSum(map< Z -> R | n :-> n ge 5 select 0 else (-1)^n/n^2 >, 1 : Al := "EulerVanWijngaarden");
// The terms each algorithm evaluates: ten to check the signs, then the sum.
g := function(n) printf "."; return (-1)^n/n^2; end function;
x := AlternatingSum(map< Z -> R | n :-> g(n) >, 1); print ""; x;
x := AlternatingSum(map< Z -> RealField() | n :-> g(n) >, 1 : Al := "EulerVanWijngaarden"); print ""; x;

// Errors.
InfiniteSum(map< Z -> Q | n :-> 1/2^n >, 1);
InfiniteSum(map< Z -> Z | n :-> 0 >, 1);
InfiniteSum(map< Q -> R | n :-> 1/2^n >, 1);
PositiveSum(map< Q -> Q | n :-> 1 >, 1);
AlternatingSum(map< Z -> Q | n :-> (-1)^n/n >, 1);
AlternatingSum(map< Z -> C | n :-> (-1)^n/C![n, 1] >, 1);
PositiveSum(map< Z -> C | n :-> C![1, 1]/n^2 >, 1);
AlternatingSum(map< Z -> R | n :-> (-1)^n/n >, 1 : Al := "Foo");
AlternatingSum(map< Z -> R | n :-> (-1)^n/n >, 1 : Al := "villegas");
AlternatingSum(map< Z -> R | n :-> (-1)^n/n >, 1 : Al := 1);
AlternatingSum(map< Q -> R | n :-> 1 >, 1 : Al := "Foo");
PositiveSum(map< Z -> R | n :-> -1/n^2 >, 1);
AlternatingSum(map< Z -> R | n :-> 1/2^n >, 1);
AlternatingSum(map< Z -> R | n :-> 1/2^n >, 1 : Al := "EulerVanWijngaarden");
try AlternatingSum(map< Z -> R | n :-> (-1)^n/n >, -3); catch e print e`Object; end try;
PositiveSum(map< Z -> R | n :-> 1 >, 1/2);
InfiniteSum(func< n | 1/2^n >, 1);
// Euler's transformation gives up after 10000 terms.
AlternatingSum(map< Z -> R | n :-> (-1)^n/n >, 1 : Al := "EulerVanWijngaarden");

// Complex terms. (Magma 2.22 crashes on these; they follow the handbook.)
x := InfiniteSum(map< Z -> C | n :-> C![1, 2]/3^n >, 1); x, Parent(x);
D<j> := ComplexField(); x := InfiniteSum(map< Z -> D | n :-> D![1, -1]/3^n + D![0, 1]/Factorial(n) >, 1); x, Parent(x);
