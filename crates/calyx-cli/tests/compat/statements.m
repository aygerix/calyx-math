// Handbook Part I, "Statements and Expressions".
// Assignment
x := 13;
y := x^2-2;
x, y;
f := PreviousPrime;
f(y);
Plus := '+';
Plus(1/2, 2);
d, x, y := Xgcd(12, 15);
d, x, y;
_, x, y := Xgcd(12, 15);
x, y;
assigned x;
assigned zzz;
assigned Gcd;
// Indexed assignment
s := [ [1], [1, 2], [1, 2, 3] ];
s;
s[2, 2] := -1;
s;
s[2][1] := 5;
s;
// Mutation assignment
x := 1;
S := { };
for i := 1 to 10 do
   S join:= { x };
   x *:= 2;
end for;
S;
n := 17; n div:= 5; n;
n := 17; n mod:= 5; n;
n := 2; n ^:= 10; n;
str := "ab"; str cat:= "cd"; str;
b := true; b and:= false; b;
// Deletion
z := 5;
delete z;
z;
// Booleans
P := Booleans();
#P;
for x, y in P do
     (x ne y) eq (x xor y);
end for;
false and (4/0 eq 6);
true or (4/0 eq 6);
// Equality
1 eq 2/2;
1 cmpeq 2/2;
1 eq "x";
1 cmpeq "x";
[1] eq ["x"];
[1] cmpeq ["x"];
1 ne 2;
"a" cmpne 1;
// Coercion
Integers() ! (6/3);
Integers() ! (1/2);
IsCoercible(Integers(), 6/3);
IsCoercible(Integers(), 1/2);
Rationals() ! 5;
Type($1);
// where
x := 1;
x where x is 10;
x;
y := 2;
x + y where x is 5 where y is 6;
(x + y where x is 5) where y is 6;
x + y where x is (5 where y is 6);
x + y where x is y where y is 6;
(x + y where x is y) where y is 6;
x + y where x is (y where y is 6);
{ a : i in [1 .. 10] | IsPrime(a) where a is 3*i + 1 };
[ <x, y> : i in [1 .. 10] | IsPrime(x) and IsPrime(y) where x is y + 2 where y is 2 * i + 1 ];
[a, a where a is 1];
[a, (a where a is 1)] where a is 2;
[ <a, b>, <b, a> where a is 1 where b is 2 ];
[ a, a where a is 2, a where a is 3 ];
// Conditionals
m := 1111;
if IsPrime(m) then
    m, "is prime";
else
    Factorization(m);
end if;
y := -3;
s := (y gt 0) select 1 else (y eq 0 select 0 else -1);
s;
f := [ i gt 2 select Self(i-1)+Self(i-2) else 1 : i in [1..20] ];
f;
x := 73;
case Sign(x):
   when 1:
      x, "is positive";
   when 0:
      x, "is zero";
   when -1:
      x, "is negative";
end case;
case 5:
   when 1, 2, 3: "small";
   else "large";
end case;
case< x | 1 : "one", 73 : "seventy-three", default : "other" >;
case< 2 | 1 : "one", default : "other" >;
// Iteration
for i := 1 to 150 by 33 do i; end for;
for i := 10 to 1 by -3 do i; end for;
for i := 5 to 1 do i; end for;
x := 27;
steps := 0;
while x gt 1 do
    x := IsEven(x) select x div 2 else 3*x + 1;
    steps +:= 1;
end while;
steps;
i := 0;
repeat
    i +:= 1;
    if i eq 3 then continue; end if;
    if i eq 6 then break; end if;
until i ge 10;
i;
p := 10037;
for x in [1 .. 100] do
   for y in [1 .. 100] do
      if x^2 + y^2 eq p then
         x, y;
         break x;
      end if;
   end for;
end for;
for x in [1 .. 100] do
   for y in [1 .. 100] do
      if x^2 + y^2 eq p then
         x, y;
         break;
      end if;
   end for;
end for;
for i -> v in ["a", "b", "c"] do i, v; end for;
// eval
x := eval "1+1";
x;
eval "1+1;";
eval "return 1+1;";
eval "x + 1";
eval "x := x + 1; return x";
// Comments and continuation
/* a multi-line
   comment */
x := 12\
34;
x;
// Types
Type(3);
t := MakeType("RngIntElt");
t;
Type(3) eq t;
Z := IntegerRing();
Type(Z);
ElementType(Z);
ISA(RngIntElt, RngElt);
ISA(RngIntElt, GrpElt);
ISA(FldRat, Fld);
Q := RationalField();
CoveringStructure(Z, Q);
ExistsCoveringStructure(Z, Q);
ExtendedType([1, 2]);
ExtendedType([[1/2]]);
tS := ExtendedType([[1]]);
BaseType(tS);
#tS;
tS[1];
tS[1][1];
Type(tS);
// Random
SetSeed(1);
GetSeed();
a := [Random(1, 100) : i in [1..10]];
SetSeed(1);
b := [Random(1, 100) : i in [1..10]];
a eq b;
Random({1}), Random([7]), Random(0);
// Miscellaneous
IsIntrinsic("ABCD");
l, a := IsIntrinsic("Abs");
l;
a(-3);
