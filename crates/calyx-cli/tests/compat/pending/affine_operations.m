// Affine algebras (handbook, Affine Algebras: Operations on Affine
// Algebras, for the algebras themselves), and the arithmetic of their
// elements, which are kept reduced modulo the relations.

P<x, y, z> := PolynomialRing(RationalField(), 3);
I := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
Q := quo<P | I>;
Rank(Q), Ngens(Q);
BaseRing(Q), CoefficientRing(Q);
PreimageRing(Q);
OriginalRing(Q) eq P;
DivisorIdeal(Q);
PreimageIdeal(Q);
PreimageIdeal(Q) eq I, PreimageIdeal(Q) eq ideal<P | 1>;
DivisorIdeal(Q) eq I, DivisorIdeal(Q) cmpeq I;
Characteristic(Q);

// An algebra is its own unit ideal, comparable only with the ideals of the
// same algebra.
Q2 := quo<P | I>;
Q eq Q2, Q eq Q, Q ne Q2;
Q eq quo<P | x*z - 1, y^2 - z, x^2 - y>;
Q eq quo<P | x^2 - y, y^2 - z, x*z - 1, x^4 - z>;
Q subset Q2;
Q cmpeq Q2, Q cmpeq quo<P | x - 1>;
Q eq quo<P | x - 1>;
Q ne quo<P | x - 1>;
Q subset quo<P | x - 1>;
b := Q eq quo<P | x - 1>;
R<u, v, w> := PolynomialRing(RationalField(), 3);
Q eq quo<R | u^2 - v, v^2 - w, u*w - 1>;
Q eq P;
P eq Q;
Q eq I;
Q eq 1;
C := quo<P | x*y>;
C eq quo<P | y*x>;
C eq quo<P | x*y, x^2*y>;
C eq quo<P | x^2*y>;
Q.4;
Q.0;

// Elements.
Q<a, b, c> := quo<P | I>;
a; b; c;
Type(a), Category(a);
Parent(a);
a + b;
-a, 2*a, a + 1/2, a - a;
a * c;
a eq a^8;
Q!1, Q!(1/2), Q!0;
IsZero(Q!0);
Q!(1/3) * a;
Parent(Q!x) eq Q;
[a, b];
Q!(a^2);
f := a + b^2 + 3;
f;
LeadingTerm(f), LeadingMonomial(f), LeadingCoefficient(f);
Monomials(f);
Coefficients(f);
Terms(f);
TotalDegree(f);
Degree(f);
Degree(f, 3);
Length(f);
Evaluate(f, [1, 1, 1]);
IsZero(f), IsOne(f), IsMinusOne(-Q!1), IsUnit(f);
f eq f, f ne f, f eq 0, f eq 3;
f lt f;
IsField(Q), IsDomain(Q), IsFinite(Q);

// Coercion: P coerces by force only, and different algebras do not mix.
x + a;
a eq x;
a + x;
f div a;
f mod a;
Q!"a";
Q![1,2];
MonomialsOfDegree(Q, 2);
MonomialOrder(Q);
C := quo<P | x*y>;
D := quo<P | x^2 - y>;
D!C.1;
C!D.1;
C.1 eq D.1;
C.1 + D.1;
Integers()!(C!3);
Rationals()!(C!(1/2));
Rationals()!C.1;
S<s, t> := PolynomialRing(RationalField(), 2);
D!s;
ideal<P | C.1>;
C!"x";
