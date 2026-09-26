// &+ adds the sum of the first half (rounded down) to that of the rest,
// and &* multiplies neighbours level by level, carrying an odd last term;
// the grouping shows when reals round or cancel (#70).
R := RealField(20);
&+[R | 1, 2^80, -2^80, 1];
&+[R | 1, 1, 2^80, -2^80, 1];
&+[R | 2^80, 1, -2^80];
&+[R | 1, 2^80, -2^80];
S := [R | 1/3, 3, 1/7, 7, 1/11, 11, 1/13];
[MantissaExponent(&*(S[i..7] cat S[1..i-1])) : i in [1..7]];
[MantissaExponent(&+(S[i..7] cat S[1..i-1])) : i in [1..7]];
&*[R | 2^60, 1 + 2^-60, 2^-60, 1 - 2^-60, 3];
// Exact rings are unaffected.
&*[1..25]; &+[1..100]; &*[GF(7) | x : x in [1..6]]; &+[x/7 : x in [1..10]];
&+[R | 1]; &*[R | 5];
// Lists cannot be reduced, and tuples only by &*; ranges need the integers
// as the universe and are not allowed in indexed sets and multisets.
&+[* 1, 2 *];
&*[* 2, 3/4 *];
&cat[* [1], [2] *];
&+<1, 2>;
&and<true, false>;
&*<2, 3/4, 5>; &*<2>;
[GF(7) | 1..6];
[Rationals() | 1..3 by 2];
{RealField(5) | 1..3};
{Integers() | 1..6};
{@ 1..6 @};
{* Integers() | 1..6 *};
