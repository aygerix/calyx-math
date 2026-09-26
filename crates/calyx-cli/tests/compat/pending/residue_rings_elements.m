// Residue class rings: creation, invariants and the functions of their
// elements.
R := Integers(12);
One(R), Identity(R), Zero(R), Representative(R), elt<R | 29>;
Characteristic(R), #R, Modulus(R);
FactoredModulus(R);
Category(R); Parent(R); PrimeRing(R); Center(R);
#Set(R);
S := Integers(Factorization(360)); S; FactoredModulus(S);
ResidueClassRing(Factorization(10));
IntegerRing(Factorization(2^10));
print R: Magma;

// square roots
R := Integers(1000);
IsSquare(R!9), IsSquare(R!489), IsSquare(R!3);
Sqrt(R!9); Sqrt(R!489); SquareRoot(R!401);
Sqrt(R!3);
AllSquareRoots(R!0);
AllSquareRoots(R!1);
AllSquareRoots(R!489);
AllSqrts(Integers(64)!36);
AllSquareRoots(Integers(243)!9);
AllSquareRoots(Integers(1600)!100);
R := Integers(55); [<a, Sqrt(R!a)> : a in [0..54] | IsSquare(R!a)];
R := Integers(121); [<a, Sqrt(R!a)> : a in [0..120] | IsSquare(R!a)];
R := Integers(3087); [<a, Sqrt(R!a)> : a in [1..300] | IsSquare(R!a) and not IsSquare(a)];
for k in [5..8] do R := Integers(2^k); [<a, Sqrt(R!a)> : a in [1..2^k-1] | IsSquare(R!a) and not IsSquare(a)]; end for;
IsSquare(Integers(10^30+57)!2);
R := Integers(15);
IsSquare(R!4 : Factorization := [<3, 1>, <5, 1>]);
AllSquareRoots(R!4 : Factorization := Factorization(15));

// linear congruences
R := Integers(12);
Solution(R!4, R!8), Solution(R!5, R!3), Solution(R!0, R!0);
Solution(R!4, R!6);
Solution(R!4, Integers(24)!8);
Gcd(R!4, Integers(24)!8);

// gcds, lcms and normal forms
Gcd(R!8, R!6), GCD(R!9, R!0), GreatestCommonDivisor(R!5, R!7), Gcd(R!0, R!0);
Lcm(R!8, R!6), LCM(R!4, R!3), LeastCommonMultiple(R!0, R!5);
Gcd([R | 8, 6, 9]), Lcm([R | 2, 3, 8]);
[<x, y, u> where y, u := Normalize(R!x) : x in [0..11]];
[<x, y, u> where y, u := Normalise(Integers(20)!x) : x in [0..19]];
[x : x in [0..11] | IsRegular(R!x)];
[x : x in [0..49] | IsPrimitive(Integers(50)!x)];
PrimitiveElement(Integers(50)), PrimitiveRoot(Integers(49)), PrimitiveElement(Integers(15));
[Order(Integers(50)!x) : x in [1..12]];
Order(Integers(50)!0);

// div
R := Integers(12);
[[Integers() | x div y : x in R] : y in R | y ne 0];
R!7 div R!0;
R!7 div 5, R!7 div 4, 7 div R!5;
R!7 mod R!5;
R := Integers(1000);
[Integers() | R!x div R!y : x in [37, 123, 999], y in [6, 8, 12, 15, 250, 375, 400]];
