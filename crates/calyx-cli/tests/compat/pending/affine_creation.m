// Affine algebras (handbook, Affine Algebras: Creation of Affine Algebras),
// made with quo< P | J >, quo< P | a1, ..., ar > and P / J.

P<x, y, z> := PolynomialRing(RationalField(), 3);
I := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
Q := quo<P | I>;
Q;
Q.1, Q.2, Q.3;
Type(Q), Category(Q);
Q.1^2;
Q.1^5;
Q!(x^5);
a := Q.1; a^7 + a;
Q2<a, b, c> := quo<P | I>;
Q2;
a^2, a*b, a^5;
Q3, f := quo<P | x^2 - y, y^2 - z>;
Q3;
f;
f(x^3);
Parent(f(x)) eq Q3;
quo<P | x^2 - y, y^2 - z>;
Q4 := P / I;
Q4;
Type(P / I);
R := quo<P | ideal<P | x^2 + 1>>;
R;
R.1^2;
Sprint(R, "Magma");
Sprint(R);

// The relations print as the reduced Groebner basis once it is known, which
// is as soon as the algebra has an element.
Q5 := quo<P | I>;
Q6 := quo<P | I>;
_ := Q5.1;
Q6;
I;
Q7 := quo<P | I>;
Q7;
J := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
Q8 := quo<P | J>;
Q8;
Q9 := quo<P | x^2 - y, y^2 - z, x*z - 1>;
Q9!x;
Q9;
Q10 := quo<P | x^2 - y, y^2 - z, x*z - 1>;
Q10!1;
Q10;
Q11 := quo<P | x^2 - y, y^2 - z, x*z - 1>;
Q11.1 + Q11.2;
Q11;

// Names.
Q12<a, b, c> := quo<P | x^2 - y, y^2 - z, x*z - 1>;
Q12;
Q13 := quo<P | x^2 - y, y^2 - z, x*z - 1>;
AssignNames(~Q13, ["u", "v", "w"]);
Q13;
Q14 := quo<P | x^2 - y, y^2 - z, x*z - 1>;
Q14.3;
Q14;
Q15<d> := quo<P | x^2 - y, y^2 - z, x*z - 1>;
Q15;
Q15.1 eq x;
P!Q15.1;
Q15.1 in P, x in Q15;
Q16 := quo<P | x^2 - y>;
AssignNames(~Q16, ["u"]);
Q16;
Q16.1;
Name(Q16, 2), Ngens(Q16);

// The relations may be given as elements, ideals, sets and sequences.
quo<P | 0>;
quo<P | >;
Z := quo<P | 1>;
Z;
Z.1, Z!5;
quo<P | [x, y]>;
quo<P | {x}>;
quo<P | x, ideal<P | y>>;
quo<P | P>;

// Other coefficient rings and orders.
R<a, b> := PolynomialRing(GF(5), 2, "grevlex");
A := quo<R | a^3 - b, b^2 - 1>;
A;
A.1^4;
Characteristic(A), Rank(A);
S<c, d> := PolynomialRing(RationalField(), 2, "grevlexw", [2, 3]);
quo<S | c^3 - d^2>;
G<g, h> := PolynomialRing(RationalField(), [1, 2]);
H := quo<G | g^2 - h>;
H;
H.2;

// Relations from another ring.
quo<P | a>;
