// The object of a caught error is its report line; it ends with a newline
// when the report ends with a blank line.
procedure show(e) print "[" cat e`Object cat "]"; end procedure;
try x := Gcd(1, "a"); catch err show(err); end try;
try x := Sqrt(Integers(7)!3); catch err show(err); end try;
try x := IsSquare(); catch err show(err); end try;
try x := Gcd(1, 2 : Foo := 1); catch err show(err); end try;
function f1() b, r := IsSquare(3); return r; end function;
try x := f1(); catch err show(err); end try;
function f2() b, r := IsSquare(3); s := r; return 1; end function;
try x := f2(); catch err show(err); end try;
try assert 1 eq 2; catch err show(err); end try;
try error "custom"; catch err show(err); end try;
try error Error("object"); catch err show(err); end try;
