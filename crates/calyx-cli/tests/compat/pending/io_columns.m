// With SetColumns(0) nothing wraps and no line is indented, not even
// by IndentPush.
SetColumns(0);
[[1,2],[3,4]];
[[[1], [2]], [[3]]];
[* [1], [2] *];
< [1], 2 >;
x := [[1,2],[3,4]]; x;
print [[1,2]], 7;
rec<recformat<a,b> | a := 1, b := [[1]]>;
[ 10^100 ];
[ <1, [2]>, <3, [4]> ];
[ [ <1, 2> ] ];
Sprint([[1,2],[3,4]]);
f := func< | [[1],[2]] >; f();
if true then [[5]]; end if;
U := UnitGroup(Integers(20)); U;
S := [ rec<recformat<a> | a := [1]> ]; S;
IndentPush(); [[1]]; IndentPop();
print [ [1] ] : Magma;
X := [ PolynomialRing(Integers()) | 1 ]; X;
SetColumns(40);
[[1,2],[3,4]];
SetColumns(80);
[[1,2],[3,4]];
U;
