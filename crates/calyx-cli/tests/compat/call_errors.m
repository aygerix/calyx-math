f := function(x : Opt := 1) return x + Opt; end function;
f(1 : Bad := 2);
procedure p(~a, b) a := b; end procedure;
z := 0;
p(~z, 2); z;
p(z, 2);
Gcd(~z, 2);
g := function(x) return x; end function;
g(1, 2);
