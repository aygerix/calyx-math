// Ideals of affine algebras (handbook, Affine Algebras: Operations on Affine
// Algebras). An ideal of an algebra has the type of the algebra, which is
// its own unit ideal. Sums of ideals are left out where they have several
// generators: Magma lists those in the hash order of its set of them.

P<x, y, z> := PolynomialRing(RationalField(), 3);
Q<a, b, c> := quo<P | x^2 - y + 1, y^3 + z - 1>;
I := ideal<Q | a^3*b*c^2>;
I;
Type(I), Category(I);
Parent(I);
Generic(I);
Generic(I) eq Q;
PreimageIdeal(I);
DivisorIdeal(I);
Rank(I), Ngens(I);
BaseRing(I), CoefficientRing(I);
I.1;
OriginalRing(I) eq P;
PreimageRing(I);
J := ideal<Q | a, b>;
J;
I * J;
J^2;
I subset J, J subset I;
I eq J, I eq I, I ne J;
IsProper(I), IsZero(I), IsProper(J);
a^3*b*c^2 in I, a in I, a in J;
a*b in J;
x in J;
K := ideal<Q | 1>;
K;
IsProper(K), IsZero(K);
K eq Q, Q eq K;
Z := ideal<Q | 0>;
Z;
IsZero(Z), IsProper(Z);
ideal<Q | >;
ideal<Q | [a, b]>;
ideal<Q | {a}>;
ideal<Q | x>;
ideal<Q | 2*a, 3*b>;
ideal<Q | a, 2*a, -a>;
ideal<Q | 0, a, 0>;
ideal<Q | 1/2>;
ideal<Q | 3>;
ideal<Q | a> + ideal<Q | a>;
ideal<Q | a> * ideal<Q | b, c>;
ideal<Q | b, c> * ideal<Q | a>;
ideal<Q | a, b> * ideal<Q | b, c>;
ideal<Q | a, b, c>^2;
ideal<Q | a + c, b>^2;
ideal<Q | a>^3;
ideal<Q | a> meet ideal<Q | b>;
ideal<Q | a, c> meet ideal<Q | b>;
Q / J;

// Products and powers are those of the representatives in P, normalized
// and reduced; zeros drop out.
R<u, v> := PolynomialRing(RationalField(), 2);
A<s, t> := quo<R | u^2, v^2>;
ideal<A | s> * ideal<A | s>;
ideal<A | s, t> * ideal<A | s>;
ideal<A | s>^2;
ideal<A | s, t>^3;
ideal<A | s> meet ideal<A | t>;
ideal<A | 2*s> * ideal<A | 3*t>;
ideal<A | 2*s + 1>^2;
ideal<A | s + t>^2;
ideal<A | 2*s, 3*t>^2;
ideal<A | s, s>^2;
ideal<A | s*t> eq ideal<A | 0>;
ideal<A | s, t> eq ideal<A | s + t, s - t>;
ideal<A | s*t> subset ideal<A | s>;
IsProper(ideal<A | 1 + s>), IsZero(ideal<A | s*t*0>), IsZero(ideal<A | s^2>);
ideal<A | A>;
ideal<A | ideal<A | s>, t>;
ideal<A | s> eq ideal<A | s>;
Parent(ideal<A | s>.1) eq A;

// The algebra as an ideal.
A + A;
A * A;
A meet A;
A^0;
A^1;
A^2;
IsZero(A), IsProper(A);
I := ideal<A | s>;
I * A;
A * I;
I meet A;
A meet I;
I subset A, A subset I, A eq I, I eq A, I ne A;
I^0;
I^1;
ideal<A | 1> eq A;

// An ideal answers for its algebra, and has names of its own.
Rank(I), Ngens(I);
Characteristic(I);
HasFiniteDimension(I);
Dimension(I);
MonomialBasis(I);
IsFinite(I);
#I;
IsField(I), IsDomain(I);
AssignNames(~I, ["e", "f"]);
I;
A;
Sprint(I, "Magma");
Sprint(I, "Minimal");
// Generators gives the variables of the algebra, as a set (one here, so
// that hash order doesn't matter).
P1<w> := PolynomialRing(RationalField(), 1);
A1<e> := quo<P1 | w^3>;
Generators(A1);
Generators(ideal<A1 | e^2>);
Type(Generators(A1));

// Membership, and ideals of another algebra.
B<p, q> := quo<R | u^2, v^3>;
J := ideal<B | p>;
I eq J;
I subset J;
b := I subset J;
U := ideal<A | 1 + s>;
q in I;
2 in I;
s in J;
(1/2)*s in I;
R.1 in I;
1/2 in I;
1/2 in U;
0 in U;
"x" in U;
R.1 in U;
p in U;
0 in I;
s in U;
1 notin U;
1 notin I;
s notin I;

// Quotients of an algebra, with the names of the polynomial ring, and the
// quotient map.
Q<a, b, c> := quo<P | x^2 - y + 1, y^3 + z - 1>;
R1 := quo<Q | a>;
R1;
Type(R1);
PreimageRing(R1) eq P;
R1.1, R1.2, R1.3;
// (Magma makes the map from the images of the generators, which needs the
// Groebner basis: X then prints it.)
X, f := quo<A | s*t>;
X.1, X.2;
X;
f(s + t);
f(s*t);
Parent(f(s)) eq X;
f;
Domain(f) eq A, Codomain(f) eq X;
s @ f;
X!s;
A!X.1;
A2<s2, t2> := quo<R | u^2, v^2>;
A2!s;
A!s2;
X2 := quo<R | u^2, v^2, u*v>;
X2!s;
X!X2.1;
X eq X2;
s in X;
X.1 in A;
X.1 + s;
Y := quo<A | ideal<A | s>>;
Y;
Z := quo<R | u^2>;
Z2 := quo<Z | Z.2^3 - 1>;
Z2;
