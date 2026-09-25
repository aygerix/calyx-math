// Handbook Part II, "Introduction to Aggregates" and "Sets".
i := { IntegerRing() | 1, 2, 3 };
s := { RationalField() | 1, 2, 3 };
Universe(i), Universe(s);
T := { 1, 2, 1/3 };
T;
Universe(T);
{ Integers() | 1, 2, 1/3 };
{ 1, "a" };
S := [ [ 1..10 ] | x^2+x+1 : x in { -3 .. 2 by 1 } ];
S;
S := [ [ 1..10 ] | x^2+x+1 : x in { -3 .. 3 by 1 } ];
Z := Integers();
T := [ Z | 1, 2, 3/3 ];
T[2] := 3/4;
I := { 1, 2 };
P := PowerSet( RationalField() );
J := P ! I;
Parent(J);
T := { 1, 2 } join { 1/3 };
T;
S := { { 1..100 } | x^3 : x in [ 1..3 ] };
T := { x : x in [ 1..99 ] | IsOdd(x) };
W := S meet T;
W;
a := [ [ 1 ], [ 1, 2, 3 ] ];
b := [ [ 2/3 ] ];
c := a cat b;
c;
Universe(c);
S := [ [1, 2], [2, 3] ];
S[2,5] := 7;
S;
S[4] := [7];
S;
S[6, 1] := 7;
S := [ 5, 13, 17, 29 ];
S[ [2, 3] ];
S[ [2, 3] ][2];
S[ [2, 3][2] ];
// Creating sets
S := { (7^2+1)/5, (8^2+1)/5, (9^2-1)/5 };
S;
Parent(S);
T := { Integers() | (7^2+1)/5, (8^2+1)/5, (9^2-1)/5 };
Parent(T);
{ U | } where U is Integers();
{ };
IsNull({ }), IsNull({ Integers() | }), IsEmpty({ Integers() | });
cubes := {@ Integers() | z^3 : z in [1..25] @};
plus := { <x, y, z> : x in [-10..10], y in [-10..10], z in [1..25] |
   y ge x and Abs(x) gt 1 and Abs(y) gt 1 and (x^3+y^3-1) in cubes
   and (x^3+y^3-1) eq cubes[z] };
plus;
M := {* 1, 1, 1, 3, 5 *};
M;
M := {* 1^^4, 2^^5, 1/2^^3 *};
M;
#M;
{* x mod 3 : x in [1..10] *};
{* x^^2 : x in [1..3] *};
{ 1..10 };
{ 1..10 by 3 };
{ 10..1 by -4 };
{ 5..1 };
{ Integers() | 1..5 };
// Power sets
S := { 1 .. 10 };
P := PowerSet(S);
P;
F := { 6/3, 12/4 };
F in P;
G := P ! F;
Parent(F);
Parent(G);
PowerIndexedSet(Integers());
PowerMultiset(Rationals());
// Accessing sets
B := {@ { i : i in [1..k] } : k in [1..5] @};
B;
#B;
Universe(B);
Parent(B);
Category(B);
Index(B, { 2, 1 });
#B[2];
Universe(B[2]);
B[ [1, 3] ];
Rep({ 5, 7 }), Representative({@ 9, 8 @});
S := { 3, 1, 2 };
ExtractRep(~S, ~r);
S, r;
Minimum({ 4, 2, 9 }), Maximum({ 4, 2, 9 });
Minimum({@ 4, 2, 9 @});
Max({* 3^^2, 7 *});
Hash(3) eq Hash(3/1);
// Modifying sets
R := { 218, 271, 511 };
x := 0;
cubes := { 0 };
while not IsEmpty(R) do
   x +:= 1;
   c := x^3;
   Include(~cubes, c);
   Include(~cubes, -c);
   for z in cubes do
       Exclude(~R, z+c);
       Exclude(~R, z-c);
   end for;
end while;
R := { 218, 271, 511 };
{ { x, y } : x, y in cubes | x+y in R };
Include({ 1 }, 1/1), Exclude({ 1, 2 }, 2);
Include({@ 3, 1 @}, 2);
Include({* 1 *}, 1), Exclude({* 1, 1 *}, 1);
ChangeUniverse({ 1, 2 }, Rationals());
Universe($1);
CanChangeUniverse({ 1/2 }, Integers());
CanChangeUniverse({ 4/2 }, Integers());
SetToIndexedSet({ 3, 1, 2 });
IndexedSetToSet({@ 3, 1, 2 @});
IndexedSetToSequence({@ 3, 1, 2 @});
MultisetToSet({* 1, 1, 2 *});
SetToMultiset({ 1, 2 });
SequenceToMultiset([ 1, 1, 2 ]);
// Operations on sets
R := { 1, 2, 3 };
S := { 1, 1/2, 1/3 };
R join S;
R meet S;
R diff S;
S diff R;
R sdiff S;
2 in R, 5 notin R, { 1, 2 } subset R, R subset { 1 }, R notsubset { 1 };
IsDisjoint({ 1, 2 }, { 3 }), IsDisjoint({ 1, 2 }, { 2 });
{ 1, 2 } eq { 2, 1 }, { 1 } ne { 1/1 };
{@ 1, 2 @} join {@ 2, 3 @};
{* 1, 1, 2 *} join {* 1, 3 *};
{* 1, 1, 2 *} meet {* 1, 3 *};
{* 1, 1, 2 *} diff {* 1, 3 *};
Multiplicity({* 1^^3, 2 *}, 1), Multiplicity({* 1 *}, 5);
Multiplicities({* 5^^3, 2 *});
Subsets({ 1, 2, 3 });
Subsets({ 1, 2, 3 }, 2);
#Subsets({ 1..10 });
Multisets({ 1, 2 }, 2);
Subsequences({ 0, 1 }, 2);
Permutations({ 1, 2, 3 });
Permutations({ 1, 2, 3 }, 2);
#RandomSubset({ 1..20 }, 5);
// Quantifiers
exists(t){ <x, y> : x, y in [ t^3 : t in [-10..10] ] | x + y eq 218 };
t;
exists(t){ <x, y> : x, y in [ t^3 : t in [1..10] ] | x + y eq 218 };
exists{ x : x in [1..10] | x gt 9 };
exists(a, b){ <x, x^2> : x in [1..10] | x^2 gt 50 };
a, b;
forall(u){ m : m in [5..1000 by 4] |
      exists{ <x, y, z> : x, y in [0..30], z in [-1, 0, 1] |
         x^2+y^2+z eq m } };
u;
forall{ x : x in { 2, 4 } | IsEven(x) };
rep{ x : x in [10..20] | IsPrime(x) };
rep{ x : x in [10..13] | x gt 100 };
x := random{ x : x in [1..100] | IsPrime(x) };
IsPrime(x);
// Reduction
function choose(S, k)
   if k eq 0 then
      return { { } };
   else
      return &join{ { s join { x } : s in choose(S diff { x }, k-1) } : x in S };
   end if;
end function;
choose({ 1, 2, 3, 4 }, 2);
&+{ 1, 2, 3 }, &*{ 1, 2, 3, 4 };
&+{ Integers() | }, &*{ Rationals() | };
&and{ true, false }, &or{ Booleans() | };
&join{ { 1 }, { 2 } };
&meet{ { 1, 2 }, { 2, 3 } };
&+{ };
// Iteration
M := Multiset(Eltseq("hello"));
for letter -> count in M do letter, count; end for;
for letter in {* "a", "a", "b" *} do letter; end for;
for i -> x in {@ "p", "q" @} do i, x; end for;
