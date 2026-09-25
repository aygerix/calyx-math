// Handbook Part I, "Functions, Procedures and Packages".
fibonacci := function(n)
   if n le 2 then
      return 1;
   else
      return $$(n-1) + $$(n-2);
   end if;
end function;
fibonacci(10) + fibonacci(12);
function Lucas(n)
   if n eq 1 then
      return 1;
   elif n eq 2 then
      return 3;
   else
      return Lucas(n-1) + Lucas(n-2);
   end if;
end function;
Lucas(11);
fibo := func< n | n le 2 select 1 else $$(n-1) + $$(n-2) >;
fibo(10) + fibo(12);
// Parameters
f := function(x, y: Proof := true, Al := "Simple")
   return <x, y, Proof, Al>;
end function;
f(1, 2);
f(1, 2: Proof := false);
f(1, 2: Al := "abc", Proof := false);
f(1, 2: Bad := 1);
g := function(n : Scale := n^2) return Scale; end function;
g(3);
g(3 : Scale := 1);
// Undefined return values
f := function(x)
   if IsOdd(x) then
       return true, x;
   else
       return false, _;
   end if;
end function;
f(1);
f(2);
a, b := f(1);
b;
a, b := f(2);
b;
// Variadic functions
f := function(x, y, ...)
    print "x: ", x;
    print "y: ", y;
    return [x + z : z in y];
end function;
f(1, 2);
f(1, 2, 3, 4);
// Procedures and reference arguments
procedure CheckPythagoras(x, y, z, ~h)
    if x^2+y^2 eq z^2 then
        h := true;
    else
        h := false;
    end if;
end procedure;
for x, y, z in { 1..15 } do
    CheckPythagoras(x, y, z, ~h);
    if h then
      "Yes, Pythagorean triple!", x, y, z;
    end if;
end for;
p := procedure(x, ~y) y := x; end procedure;
a := 5; b := 6;
p(a, ~b);
a, b;
AddOne := proc< ~x | Append(~x, 1) >;
L := [ 0 ];
AddOne(~L);
L;
p(a, b);
x := p(1, ~b);
// Closures capture values when they are created
a := 1;
bf := func< n | a >;
a := 2;
bf(0);
f := func< n | n + 1 >;
g := func< m | m + f(m) >;
g(6);
f := func< n | n + 2 >;
g(6);
make := function(n) return func< x | x + n >; end function;
add3 := make(3);
add3(10);
// forward declarations and mutual recursion
forward isOdd;
isEven := func< n | n eq 0 select true else isOdd(n - 1) >;
isOdd := func< n | n eq 0 select false else isEven(n - 1) >;
isEven(10), isOdd(7);
function usesUndefined(n) return undefinedThing(n); end function;
// local declarations
temp := 7;
f := function(a, b)
   local temp;
   temp := a * b;
   return temp^2;
end function;
f(3, 4), temp;
// Packages
Attach("pkgs/myrat.m");
r := MyRational(3, -9);
r;
s := MyRational(4, 7);
r + s;
r * s;
Type(r);
MyRational(1, 0);
Attach("pkgs/dirprod.m");
Z := IntegerRing();
Q := RationalField();
D := DirectProduct(<Z, Q>);
x := D!<1, 2/3>;
y := D!<2, 3/4>;
x;
Parent(x);
x + y;
D!<1>;
S := [x, y];
S;
&+S;
Attach("pkgs/uses_defs.m");
BelowLimit(5), BelowLimit(10^6);
Fred(4);
Overloaded(1, 2), Overloaded(1/2, 2), Overloaded("a", 1);
MyBinomial(5, 2);
MyBinomial(5, 7);
MyBinomial(-1, 0);
Q := [ 1 ];
AppendTwice(~Q, 9);
Q;
Func(3);
c := Func(5);
a, b := Func(4);
a, b;
SumAll(1, 2, 3, 4);
?MyBinomial
// Attributes on user types
declare_ok := true;
AddAttribute(RngInt, "Nickname");
Z := Integers();
Z`Nickname := "zed";
Z`Nickname;
assigned Z`Nickname;
GetAttributes(RngInt);
Z`Unknown := 1;
// Verbose flags
SetVerbose("User1", 2);
GetVerbose("User1");
vprint User1: "level one";
vprint User1, 3: "level three";
vprintf User1, 2: "value %o\n", 42;
IsVerbose("User1", 3);
