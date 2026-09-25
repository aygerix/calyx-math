// Aggregates whose elements have no common universe. A sequence of
// literal constants is rejected as soon as it is read.
[1, "a"];
{1, "a"};
x := 1; y := "a"; [x, y];
[x, y, 3];
{x, y};
[* 1, "a" *];
[1, 2, "a", 4];
[1/2, true];
[-1, 2.5, "b"];
{@ 1, "a" @};
{* 1, "a" *};
