// The rational field: creating Q and its elements (Rational Field chapter,
// "Creation Functions").
Q := Rationals();
Q; RationalField(); Q eq RationalField();
MaximalOrder(Q); IntegerRing(Q); Integers(Q); RingOfIntegers(Q); IntegerRing(); Integers();
MaximalOrder(Q) eq Integers();
FieldOfFractions(Q); FieldOfFractions(Integers()); FieldOfFractions(Q) eq Q;
One(Q), Identity(Q), Zero(Q), Representative(Q);
Parent(One(Q)), Parent(Identity(Q)), Parent(Zero(Q)), Parent(Representative(Q));
Q.1; Parent(Q.1);
Q.2;
Q.0;

// elements
6/4; -6/4; 6/-4; -6/-4; 0/5; 5/1; Parent(5/1); Parent(6/3);
Q!5; Q!(5/1); Q!-3; Parent(Q!5);
Q![3]; Q![1/2]; Q![[1, 2]];
Q![3, 6]; Q![-4, 6]; Q![4, -6]; Q![0, 5]; Q![2/1, 3]; Q![2^100, 2^101];
Q![Integers() | 4, 6]; Q![Q | 4, 6];
Q![Integers(7) | 3, 2]; Q![GF(5) | 2, 2];
Q![1, 0];
Q![1/2, 1];
Q![1/2, 1/3];
Q![1, 2, 3];
Q![];
Q![GF(5)!2];
Q![true];
Q![1.5];
Q![[1, 0]];
Q!<1, 2>;
Q!{1, 2};
Q!true;
Q!"1/2";
Q!1.5;
Q!(GF(5)!2);
Q!(Integers(5)!2);
IsCoercible(Q, [1, 2]); IsCoercible(Q, [1, 0]); IsCoercible(Q, [1, 2, 3]); IsCoercible(Q, [GF(5)!2]);
elt< Q | 3, 6 >; elt< Q | -3, -6 >; elt< Q | 3, -6 >; Parent(elt< Q | 4, 2 >);
elt< Q | 1, 0 >;
elt< Q | 1/2, 3 >;
elt< Q | "a", 2 >;
elt< Q | 2, "a" >;
elt< Q | 3 >;
elt< Q | 1/2 >;
elt< Q | 1, 2, 3 >;

// roots of unity
RootOfUnity(1, Q); RootOfUnity(2, Q); Parent(RootOfUnity(2, Q));
RootOfUnity(3, Q);
RootOfUnity(4, Q);
RootOfUnity(2^30 - 1, Q);
RootOfUnity(2^30, Q);
RootOfUnity(2^100, Q);
RootOfUnity(0, Q);
RootOfUnity(-2, Q);
RootOfUnity(1/2, Q);
RootOfUnity(1, Integers());

// random rationals: numerator in [-u..u], denominator in [1..u]
S := [Random(Q, 10) : i in [1..200]];
forall{q : q in S | Parent(q) eq Q and Abs(Numerator(q)) le 10 and Denominator(q) le 10};
S := [Random(Q, -10) : i in [1..200]];
forall{q : q in S | Abs(Numerator(q)) le 10 and Denominator(q) le 10};
{Random(Q, 0) : i in [1..20]};
{Random(Q, 1) : i in [1..100]};
{Random(Q, -1) : i in [1..100]};
q := Random(Q, 10^30); Abs(Numerator(q)) le 10^30 and Denominator(q) le 10^30;
Random(Q);
Random(Q, 1/2);
