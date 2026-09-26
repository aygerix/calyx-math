// Call frames of error reports print their arguments minimally, on one
// line, cut after 60 characters.
f := function(K, x) return K ! x; end function;
try f(GF(4), [1, 2, 3]); catch e print e; end try;
try f(Integers(), [1, 2]); catch e print e; end try;
try f(RationalField(), "a"); catch e print e; end try;
P<t> := PolynomialRing(GF(3));
try f(P, {1, 2}); catch e print e; end try;
try f(ResidueClassRing(12), GF(7) ! 3); catch e print e; end try;
g := func< a | 1 div a >;
try g(GF(2)); catch e print e; end try;
try g(quo<Integers() | 6>); catch e print e; end try;
try g(ext<GF(2) | 3>); catch e print e; end try;
try g(PolynomialRing(Integers(), 2)); catch e print e; end try;
try g([GF(2) | 1, 0]); catch e print e; end try;
try g(map< Integers() -> Integers() | x :-> x + 1 >); catch e print e; end try;
try g(map< Integers() -> Integers() | x :-> x + 1, y :-> y - 1 >); catch e print e; end try;
try g([1..40]); catch e print e; end try;
try g("abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefgh"); catch e print e; end try;
try g("abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghi"); catch e print e; end try;
try g("ab\ncd"); catch e print e; end try;
try g(["ab", "c"]); catch e print e; end try;
try g(<1, "x", [2]>); catch e print e; end try;
try g([1..30] cat [1..30]); catch e print e; end try;
try g(rec< recformat< a, b > | a := 1, b := 2 >); catch e print e; end try;
try g(10^80); catch e print e; end try;
try g(Integers()); catch e print e; end try;
try g(true); catch e print e; end try;
print <1, "x", [2]>: Minimal;
print ["ab", "c"]: Minimal;
print rec< recformat< a, b > | a := 1, b := 2 >: Minimal;

// S ! x for sequences and sets.
try [1] ! 2; catch e print e; end try;
try {1, 2} ! 3; catch e print e; end try;
try {@ 1, 2 @} ! 3; catch e print e; end try;
try {* 1, 2 *} ! 3; catch e print e; end try;
try [1] ! "a"; catch e print e; end try;
try [GF(5) | 1] ! 7; catch e print e; end try;
[GF(5) | 1] ! 6;
IsCoercible([1], 2);
IsCoercible({1}, 1);
try [] ! 1; catch e print e; end try;
try {} ! 1; catch e print e; end try;
x := [1, 2] ! 2; x;
[1] ! 2;
{1, 2} ! 3;

// A function is named after the first identifier it is assigned to; one
// never assigned shows where it is defined.
m := map< Integers() -> Rationals() | n :-> 1/n >;
try m(0); catch e print e; end try;
try 0 @ m; catch e print e; end try;
try (func< x | 1/x >)(0); catch e print e; end try;
h := [func< x | 1/x >];
try h[1](0); catch e print e; end try;
k := function(f) return f(0); end function;
try k(func< x | 1/x >); catch e print e; end try;
try k(func< y |
  1 div y >); catch e print e; end try;
try [func< x | 1/x >(0)]; catch e print e; end try;
g := func< a | 1 div a >;
f := g;
try f(0); catch e print e; end try;
r := function(x) return 1 div x; end function;
s := r;
try s(0); catch e print e; end try;
t := [g];
try t[1](0); catch e print e; end try;
l := func< x | func< y | 1 div y > >;
try l(1)(0); catch e print e; end try;
u := l(1);
try u(0); catch e print e; end try;
procedure pr(x) y := 1 div x; end procedure;
try pr(0); catch e print e; end try;
v := procedure(x) y := 1 div x; end procedure;
try v(0); catch e print e; end try;
w := function(x)
  z := func< y |
    1 div y >;
  return z(x);
end function;
try w(0); catch e print e; end try;
q := 1;
q := func< a | 1 div a >;
try q(0); catch e print e; end try;
m(0);
