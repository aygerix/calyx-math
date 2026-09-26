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
