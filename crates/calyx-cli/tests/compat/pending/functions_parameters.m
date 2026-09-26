// Unknown parameters to intrinsics, functions and procedures.
Gcd(4, 6 : Foo := 1);
x := Gcd(4, 6 : Foo := 1);
PolynomialRing(Rationals(), 2, "lex" : Global := true);
P := PolynomialRing(Rationals(), 2 : Foo := 1);
Factorization(12 : Foo := 1, Bar := 2);
Factorization(12 : ECMLimit := 10, Bar := 2);
Gcd("a", 6 : Foo := 1);
f := func< x : B := 1 | x + B >;
f(1 : C := 2);
g := func< x | x >;
g(1 : C := 2);
procedure p(x) end procedure;
p(1 : C := 2);
procedure q(x : D := 1) end procedure;
q(1 : C := 2);
Sort([3, 1, 2] : Foo := 1);
// Intrinsics without arguments.
Cputime(: Foo := 1);
Integers(: Foo := 1);
IsSquare();
Gcd(: Foo := 1);
h := func< | 1 >;
h(: Foo := 1);
print "done";
