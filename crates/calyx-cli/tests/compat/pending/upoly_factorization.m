// Univariate polynomials: factorization, irreducibility, resultants,
// discriminants and Hensel lifting (handbook, Univariate Polynomial Rings,
// Factorization).
P<x> := PolynomialRing(Integers());
S<y> := PolynomialRing(Rationals());
T<t> := PolynomialRing(GF(7));
F<w> := GF(9);
U<u> := PolynomialRing(F);

// Factorization over the integers and rationals.
f := -12*x^5 + 12*x^4 + 30*x^3 - 30*x^2 - 18*x + 18;
Factorization(f);
L, c := Factorization(f); c;
Factorization((x - 3)*(x + 5)*(2*x + 1)^2*(x^2 + 1));
Factorization(x^4 + 4), Factorisation(P!-6), Factorization(P!1), Factorization(P!-1);
Factorization(P!0);
Factorization(4*x), Factorization(-8*x^2 + 8), Factorization(P!-12);
L, c := Factorization(-4*x); c;
Factorization(12*(x^2 + 1)^2*(x + 1)*(3*x - 2));
Factorization(S!f);
L, c := Factorization(y^3/2 - 1/2); L, c;
Factorization(S!3), Factorization(3*y + 2);

// Over finite fields.
Factorization(t^7 - t);
Factorization(3*t^4 + 2*t + 5);
Factorization((t + 1)^2*(t + 6)^3*(t^2 + 1));
L, c := Factorization(T!3); L, c;
L, c := Factorization(3*t^4 + 2*t + 5);
Factorization((t + 1)^2*(t + 6)^3*(t^2 + 1));
L, c := Factorization(T!3); L, c; c;
Factorization(u^9 - u);
Factorization(w*u^3 + u);
Factorization(PolynomialRing(Integers(7))![1, 0, 0, 1]);
Factorization(PolynomialRing(GF(2))![1, 1, 0, 0, 1, 1]);
Factorization(PolynomialRing(GF(1000003))![-4, 0, 1]);
Factorization(PolynomialRing(Integers(6))![1, 1]);

// H24E7 (the timings are left out).
SwinnertonDyerPolynomial(1);
SwinnertonDyerPolynomial(2);
SwinnertonDyerPolynomial(3);
SwinnertonDyerPolynomial(4);
IsIrreducible($1);
for i := 1 to 6 do
   f := SwinnertonDyerPolynomial(i);
   printf "%o:", i;
   for p in [3, 23, 503] do
        L := Factorization(PolynomialRing(GF(p)) ! f);
        printf " %o", {* Degree(t[1])^^t[2]: t in L *};
    end for;
    "";
end for;
sd6 := SwinnertonDyerPolynomial(6);
Degree(sd6);
Max([Abs(x): x in Coefficients(sd6)]);
L := Factorization(sd6);
#L;
p := sd6*SwinnertonDyerPolynomial(5);
L := Factorization(p);
#L;
L[1,1] eq SwinnertonDyerPolynomial(5);
L[2,1] eq sd6;

// Irreducibility.
[IsIrreducible(g) : g in [x^2 + 1, x^2 - 1, 2*x + 2, x + 2, P!2, P!1, P!-1, x^4 + 4]];
[IsPrime(g) : g in [x^2 + 1, x^2 - 1, 2*x + 2, x + 2, P!2]];
[IsIrreducible(g) : g in [y^2 + 1, y^2 - 1, 2*y + 2, S!2]];
[IsIrreducible(g) : g in [t^2 + 1, t^2 + 3, t^7 - t + 1, T!3]];
IsIrreducible(u^2 + w), IsIrreducible(u^2 - w^2);
IsIrreducible(P!0);
IsPrime(T!0);
IsIrreducible(PolynomialRing(Integers(6))![1, 1]);

// Squarefree, distinct-degree and equal-degree factorization.
SquarefreeFactorization(-2*x^5 + 2*x^3);
SquarefreeFactorization((x + 1)^2*(x - 1)^2*(x^2 + 1)^3*6);
SquarefreeFactorization(P!5), SquarefreeFactorization(P!1);
SquarefreeFactorization(P!0);
SquarefreeFactorization(4*x), SquarefreeFactorization(8*x^2), SquarefreeFactorization(12*x^2*(x + 1));
SquarefreeFactorization(P!-1), SquarefreeFactorization(P!12);
SquarefreeFactorization((x^2 - 2)*(x^2 + 1)^2*(x - 3)^2*(x + 5)^3);
SquarefreeFactorization(S!3), SquarefreeFactorization(T!3), SquarefreeFactorization(t^14 + 1);
SquarefreeFactorization((y/2 + 1)^2*(y - 1));
SquarefreeFactorization(t^7*(t + 1)^2*(t^2 + 1));
SquarefreeFactorization((u^3 + w)^3*(u + 1));
g := (t^2 + 1)*(t + 1)*(t + 2)*(t^3 + t + 1);
DistinctDegreeFactorization(g);
DistinctDegreeFactorization(g : Degree := 1);
DistinctDegreeFactorization(T!1);
DistinctDegreeFactorization(y^2 + 1);
// Without Degree the pairs come in the order of the products, with it by
// increasing degree.
DistinctDegreeFactorization((t + 1)*(t + 2)*(t + 3)*(t^2 + 1));
DistinctDegreeFactorization((t + 1)*(t + 6)*(t^2 + 2)*(t^3 + t + 1));
DistinctDegreeFactorization(g : Degree := 2);
DistinctDegreeFactorization(g : Degree := 100);
DistinctDegreeFactorization(3*(t + 1)*(t^2 + 1)), DistinctDegreeFactorization(3*t), DistinctDegreeFactorization(T!3);
DistinctDegreeFactorization(g : Degree := -1);
DistinctDegreeFactorization((t + 1)^2*(t^2 + 1));
DistinctDegreeFactorization(T!0);
DistinctDegreeFactorization((u + w)*(u^2 + w)*(u^3 + u + w));
h := (t + 1)*(t + 2)*(t + 4);
EqualDegreeFactorization(h, 1, Modexp(t, 7, h));
h := (t^2 + 1)*(t^2 + t + 3);
EqualDegreeFactorization(h, 2, Modexp(t, 7, h));
IsSeparable(t^7 - t), IsSeparable(t^7 - 1), IsSeparable(y^2 + 1), IsSeparable((y + 1)^2);
IsSeparable(x^2 + 1);
IsSeparable(T!1);

// Resultants and discriminants.
Resultant(x^2 + 1, x^3 - 2), Resultant(2*x + 1, 3*x - 1), Resultant(x^2 - 1, x - 1);
Resultant(y^2/2 + 1, y - 1/3), Resultant(t^3 + 2, t^2 + 3*t + 1), Resultant(u^2 + w, u + 1);
Resultant(P!0, x + 1), Resultant(P!3, x^2 + 1), Resultant(P!3, P!2);
Resultant(PolynomialRing(Integers(6))![1, 2, 3], PolynomialRing(Integers(6))![5, 1]);
Discriminant(x^2 + x + 1), Discriminant(3*x^2 + 2*x + 1), Discriminant(x^3 - 2), Discriminant(x - 5);
Discriminant(y^3/2 + y), Discriminant(t^3 + t + 1), Discriminant(u^2 + w);
Discriminant(x^4 + x^2), Discriminant(2*x^3 + 5);
Discriminant(P!3);
Discriminant(P!0);

// H24E8
R<x> := PolynomialRing(Integers());
b := x^5 - x^3 + 2*x^2 - 2;
F<f> := PolynomialRing(GF(5));
s := [ w[1] : w in Factorization( F ! b ) ];
s;
T<t> := PolynomialRing(Integers(5^3));
h := HenselLift(b, s, T);
h;
&*h;
HenselLift(b, s, PolynomialRing(Integers(5)));
HenselLift(b, s, PolynomialRing(Integers(25)));
HenselLift(3*b, s, PolynomialRing(Integers(125)));
HenselLift(b, [F ! b], PolynomialRing(Integers(125)));
HenselLift(2*x^2 + 3*x + 1, [f + 1, f + 3], PolynomialRing(Integers(125)));
HenselLift(b, s, PolynomialRing(Integers(10)));
HenselLift(b, s, PolynomialRing(Integers(7^2)));
HenselLift(b, s, PolynomialRing(GF(5)));
HenselLift(b, s, PolynomialRing(Integers()));
HenselLift(b, s[1..3], PolynomialRing(Integers(125)));
HenselLift(b, [f + 1, f + 1], PolynomialRing(Integers(125)));
HenselLift(b, [F!1], PolynomialRing(Integers(125)));
HenselLift(b, [2*s[1], s[2], s[3], s[4]], PolynomialRing(Integers(125)));
HenselLift(b, [PolynomialRing(GF(5)) | ], PolynomialRing(Integers(125)));
HenselLift(PolynomialRing(Rationals())!b, s, PolynomialRing(Integers(125)));

// The ring predicate and products of factorizations.
[HasPolynomialFactorization(R) : R in [* Integers(), Rationals(), GF(7), GF(9), Integers(12), Integers(7), RealField(), P *]];
[HasPolynomialFactorization(R) : R in [* Integers(9), ComplexField(), PolynomialRing(RealField()), PolynomialRing(GF(9)), PolynomialRing(Integers(), 3), PolynomialRing(Integers(6)), GF(1000003), Integers(1000003) *]];
L := Factorization(x^4 - 1);
FactorisationToPolynomial(L), Facpol(L), Facpol([<x - 1, 3>, <x^2 + 1, 2>]);
Facpol([<t + 1, 2>]);
Facpol([<P!2, 3>]), Facpol([<x + 1, 0>]);
Facpol([<2, 3>, <3, 1>]);
Facpol([<GF(7)!2, 3>]);
Facpol([<x + 1, 2, 3>]);
SwinnertonDyerPolynomial(0);
SwinnertonDyerPolynomial(-1);
Parent(SwinnertonDyerPolynomial(1));

// The verbose flag of factorization.
SetVerbose("PolyFact", 2); GetVerbose("PolyFact"); SetVerbose("PolyFact", 0);
