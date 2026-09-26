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

// A bad call is an error "in procedure call" only as a statement; inside
// an expression it is a plain runtime error. A variadic parameter takes at
// least one argument.
function F(a, b) return a + b; end function;
x := F(1);
F(1, 2, 3);
y := [F(1)];
print F(1);
procedure Q(a) end procedure;
Q(1, 2);
z := 1 + F(1, 2, 3);
g := func< a | a >;
w := g(1, 2);
g(1, 2);
h := function(a : p := 1) return a; end function;
v := h(1 : q := 2);
h(1 : q := 2);
k := function(a) return a; end function;
v := k(1 : q := 2);
procedure R(~a) a := 1; end procedure;
b := 0; R(b);
function V(x, ...) return x; end function;
v := V();
V();
function V2(x, ...) return x; end function;
V2(5); V2(5, 6); V2(5, 6, 7);
function W(a, x, ...) return <a, x>; end function;
W(1, 2); W(1, 2, 3);
W(1);
v := W(1);
