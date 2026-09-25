// Handbook Part II, "Sequences".
[ ];
[ Integers() | ];
IsNull([]), IsNull([ Integers() | ]);
[ 1, 2, 3 ];
[ Rationals() | 1, 2 ];
Universe($1);
[ x^2 : x in [1..6] | IsEven(x) ];
[ Integers() | x/2 : x in [2, 4] ];
[ 1^^3, 2 ];
[ 1..10 ];
[ 1..10 by 3 ];
[ 10..1 by -3 ];
[ 5..1 ];
[ Integers() | 1..3 ];
\[ 1, 2, 3 ];
S := [ 1 .. 10 ];
P := PowerSequence(S);
P;
F := [ 6/3, 12/4 ];
F in P;
G := P ! F;
Parent(F);
Parent(G);
// Access
S := [ 5, 13, 17, 29 ];
#S, S[2];
S[5];
S[0];
S[ [4, 1] ];
Parent(S), Universe(S);
Minimum([ 3, 1, 4, 1, 5 ]), Maximum([ 3, 1, 4, 1, 5 ]);
Index([ 3, 1, 4, 1 ], 1), Index([ 3, 1, 4, 1 ], 1, 3), Position([ 3 ], 7);
Rep([ 8, 9 ]);
a, b, c := Explode([ 1, 2, 3 ]);
c, b, a;
Eltseq([ 1, 2 ]);
// Modification (procedures and functions)
S := [ 1, 2 ];
Append(~S, 3); S;
Append(S, 4), S;
Exclude(~S, 2); S;
Include(~S, 1); Include(~S, 9); S;
Insert(~S, 2, 7); S;
Insert(~S, 7, 0); S;
Insert([ 1, 2, 3, 4, 5 ], 2, 4, [ 0, 0 ]);
Insert([ 1, 2, 3 ], 2, 1, [ 9 ]);
Prune(~S); S;
Remove(~S, 1); S;
Remove([ 1 ], 3);
Reverse([ 1, 2, 3 ]);
Rotate([ 1, 2, 3, 4 ], 1), Rotate([ 1, 2, 3, 4 ], -1);
T := [ 3, 1, 2 ];
Sort(~T); T;
Sort([ 3, 1, 2 ]);
Sort([ "pear", "apple", "fig" ], func< x, y | #x - #y >);
T := [ 5, 2, 8 ];
Sort(~T, func< x, y | y - x >); T;
A := [ 3, 1, 2 ];
B := [ "c", "a", "b" ];
ParallelSort(~A, ~B);
A, B;
U := [ 1, 2, 3 ];
Undefine(~U, 2); U;
IsComplete(U), IsDefined(U, 2), IsDefined(U, 3), IsDefined(U, 9);
ChangeUniverse([ 1, 2 ], Rationals());
CanChangeUniverse([ 1/2 ], Integers());
// Farey series
D := Denominator;
N := Numerator;
farey := function(n)
   f := [ RationalField() | 0, 1/n ];
   p := 0;
   q := 1;
   while p/q lt 1 do
      p := ( D(f[#f-1]) + n) div D(f[#f]) * N(f[#f])  - N(f[#f-1]);
      q := ( D(f[#f-1]) + n) div D(f[#f]) * D(f[#f])  - D(f[#f-1]);
      Append(~f, p/q);
   end while;
   return f;
end function;
farey(6);
function farey2(n)
   if n eq 1 then
      return [RationalField() | 0, 1 ];
   else
      f := farey2(n-1);
      i := 0;
      while i lt #f-1 do
         i +:= 1;
         if D(f[i]) + D(f[i+1]) eq n then
            Insert( ~f, i+1, (N(f[i]) + N(f[i+1]))/(D(f[i]) + D(f[i+1])));
         end if;
      end while;
      return f;
   end if;
end function;
farey2(6);
farey3 := func< n | Sort(Setseq({ a/b : a in { 0..n }, b in { 1..n } | a le b }))>;
farey3(6);
// New sequences from old
[ 1, 2 ] cat [ 3 ];
[ 1 ] cat [ 1/2 ];
[ 1 ] cat [ "a" ];
S := [ 1 ]; S cat:= [ 2, 3 ]; S;
Partition([ 1..6 ], 2);
Partition([ 1..6 ], [ 1, 2, 3 ]);
Partition([ 1..5 ], 2);
Setseq({ 3, 1, 2 }), Seqset([ 3, 1, 3 ]);
egyptian := function(r)
      n := Numerator(r);
      d := Denominator(r);
      s := [d : i in [1..n]];
      t := { d };
      i := 2;
      while i le #s do
             c := s[i];
             if c in t then
                    Remove(~s, i);
                    s cat:= [c+1, c*(c+1)];
             else
                    t join:= { c };
                    i := i+1;
             end if;
      end while;
      return s;
end function;
e := egyptian(11/13);
&+[1/d : d in e];
#e;
#IntegerToString(Maximum(e));
// Sequences of booleans
And([ true, false ], [ true, true ]), Or([ false, false ], [ true, false ]);
Xor([ true, true ], [ true, false ]), Not([ true, false ]);
B := [ true, false ]; Not(~B); B;
// Predicates
2 in [ 1, 2 ], 3 notin [ 1, 2 ], 1/1 in [ 1 ];
IsSubsequence([ 2, 3 ], [ 1, 2, 3 ]), IsSubsequence([ 1, 3 ], [ 1, 2, 3 ]);
IsSubsequence([ 1, 3 ], [ 1, 2, 3 ] : Kind := "Sequential");
IsSubsequence([ 3, 1 ], [ 1, 2, 3 ] : Kind := "Setwise");
[ 1, 2 ] eq [ 1, 2 ], [ 1, 2 ] ne [ 1/1, 2 ];
[ 1, 2 ] lt [ 1, 3 ], [ 1, 2 ] lt [ 1, 2, 0 ], [ 2 ] gt [ 1, 9 ], [ 1 ] le [ 1 ], [ 1 ] ge [ 2 ];
// Recursion, reduction, iteration
s := [ i gt 2 select Self(i-2)+Self(i-1) else 1 : i in [1..100] ];
&+s;
[ #Self() : i in [1..4] ];
&+[ Integers() | ], &*[ Rationals() | ], &cat[ [ 1 ], [ 2 ] ], &cat[ PowerSequence(Integers()) | ];
&cat [ "ab", "cd" ];
&+[ ];
[ <number, letter> : number in [1..5], letter in ["a", "b", "c"]];
r := [];
for letter in ["a", "b", "c"] do
    for number in [1..5] do
        Append(~r, <number, letter>);
    end for;
end for;
r;
[ <x, y> : x in [0..5], y in [0..x] | x^2+y^2 lt 16 ];
[ <x, y> : x in [0..y], y in [0..5] | x^2+y^2 lt 16 ];
x := 1000;
#[ <x, y> : x in [0..5], y in [0..x] | x^2+y^2 lt 100 ];
letters := Eltseq("abc");
[ <i, x> : i -> x in letters ];
for i -> x in letters do
    printf "letters[%o] is %o\n", i, x;
end for;
S := [ 7, 3 ];
S[5] := 2;
S;
[ i : i -> _ in S ];
[ s : s in S ];
// Formal sequences
F := [! x in Integers() | IsEven(x) !];
4 in F, 5 in F, 1/2 in F;
