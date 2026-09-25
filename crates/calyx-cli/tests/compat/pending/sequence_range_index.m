// Indexing by a range, s[i..j] and s[i..j by k], picks out a subsequence
// like s[[i..j]]; assigning through one fails. The extended type of an
// empty aggregate has element type Any.
s := [4,5,6,7]; s[2..3];
s[[1,3]];
s[3..2];
s[2..2];
s[1..5];
s[0..1];
s[1..4 by 2];
Type(s[2..3]);
t := "hello"; t[2..4];
t[[1, 5]];
s[2..3] := [9, 9];
s[[2, 3]] := [9, 9];
s[2 .. 3];
ExtendedType([]);
ExtendedType({});
ExtendedType({@ @});
ExtendedType({* *});
ExtendedType([[]]);
Isqrt([]);
Isqrt({@ @});
Isqrt({* *});
Isqrt([[]]);
1 + [];
