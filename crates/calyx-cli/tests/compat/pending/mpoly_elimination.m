// Elimination in ideals of multivariate polynomial rings (handbook,
// Polynomial Ring Ideal Operations: Elimination): elimination ideals,
// univariate elimination ideal generators and relation ideals.

// H116E6.
P<x, y, z> := PolynomialRing(RationalField(), 3);
I := ideal<P |
    1 - x + x*y^2 - x*z^2,
    1 - y + y*x^2 + y*z^2,
    1 - z - z*x^2 + z*y^2 >;
UnivariateEliminationIdealGenerator(I, 1);
UnivariateEliminationIdealGenerator(I, 2);
E :=  EliminationIdeal(I, {y, z});
E;
I;

// H116E7.
function ZRadical(I)
    // Find radical of zero dimensional ideal I
    P := Generic(I);
    n := Rank(P);
    G := UnivariateEliminationIdealGenerators(I);
    N := {};

    for i := 1 to n do
        // Set FF to square-free part of the i-th univariate
        // elimination ideal generator
        F := G[i];
        FF := F;
        while true do
            D := GCD(FF, Derivative(FF, 1, i));
            if D eq 1 then
                break;
            end if;
            FF := FF div D;
        end while;
        // Include FF in N if FF is a proper divisor of F
        if FF ne F then
            Include(~N, FF);
        end if;
    end for;

    // Return the sum of I and N
    if #N eq 0 then
      return I;
    else
      return ideal<P | I, N>;
    end if;
end function;
P<x, y, z> := PolynomialRing(RationalField(), 3);
I := ideal<P | (x+1)^3*y^4, x*(y-z)^2+1, z^3-z^2>;
R := ZRadical(I);
Groebner(I);
Groebner(R);
I;
R;
I subset R;
R subset I;
IsInRadical(x + 1, I);

// H116E8.
P<x, y, z> := PolynomialRing(GF(2), 3, "grevlex");
S := [(x + y + z)^2, (x^2 + y^2 + z^2)^3 + x + y + z + 1];
I := ideal<P | S>;
Groebner(I);
I;
Q<a, b> := PolynomialRing(GF(2), 2);
U := RelationIdeal(S, Q);
U;
S[1]^6 + S[1] + S[2]^2;

// EliminationIdeal(I, k) leaves I as it was. Its basis comes from the
// Groebner basis for grevlex on the first k variables and then on the
// others: sorted and reduced in the ring's order, it need not be a
// Groebner basis there. With k = n it is [1] or empty, and I gets its
// easy basis; with k = 0 it is I itself.
P<x, y, z> := PolynomialRing(RationalField(), 3);
I := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
E := EliminationIdeal(I, 1); E;
I;
E := EliminationIdeal(I, 2); E;
I;
E := EliminationIdeal(I, 3); E;
I;
E := EliminationIdeal(I, 0); E;
J := ideal<P | x^2 + y^2 - 1, x - z^2>;
E := EliminationIdeal(J, 1); E;
E := EliminationIdeal(J, 3); E;
J;
K := ideal<P | x*y, y*z>;
EliminationIdeal(K, 1);
EliminationIdeal(ideal<P | 1>, 1);
EliminationIdeal(ideal<P | 1>, 3);
EliminationIdeal(ideal<P | 0>, 1);
EliminationIdeal(P, 1);
L := [
  [x - y, y^3 - z, z^2 - y],
  [x - y, y^3 - z],
  [x*y - 1, y^2 - z^3],
  [x - y*z, y^2 - z, z^3 - 2],
  [x^2 - y, y^2 - z],
  [x - z, y^2 - z^3, y*z - 1],
  [x*z - y, y^2 - z, x^2 - 1],
  [x - y^2, y - z^2],
  [x^2 + y, x*y - z],
  [x - 1, y^2 - z, y*z^2 - 1],
  [x - z, y^2 - z^3, y*z - 1, z^5 - 1],
  [x^2 - z, y^2 - z^3, y*z - 1],
  [x - z, y^2 - z^3 + z, y*z - 1],
  [x*y - z, y^2 - z^3, y*z - 1],
  [x*y - z, x^2 - z^3]
];
for G in L do
  I := ideal<P | G>;
  print Basis(EliminationIdeal(I, 1)), Dimension(ideal<P | G>);
end for;
P<a, b, c, d> := PolynomialRing(RationalField(), 4);
I := ideal<P | a - b, b - c*d^3, c^2 - d>;
EliminationIdeal(I, 1);
I := ideal<P | a - b*c + d^2, b^2 - c*d - 1, a*c - d^3 + b>;
EliminationIdeal(I, 1);
P<t, x, y, z, w> := PolynomialRing(RationalField(), 5);
I := ideal<P | x - t, y - t^2, z - t^3, w - t^4>;
Basis(EliminationIdeal(I, 1));
Basis(EliminationIdeal(I, 2));
Basis(EliminationIdeal(I, 3));
P<x, y, z, w> := PolynomialRing(RationalField(), 4);
I := ideal<P | x^2 + y^2 + z^2 + w^2 - 1, x - y*z, y - z*w + 1>;
Basis(EliminationIdeal(I, 1));
Basis(EliminationIdeal(I, 2));
Basis(EliminationIdeal(I, 3));
I := ideal<P | x*y - z*w, x^2 - y*w + z, y^2 - x*z + w>;
Basis(EliminationIdeal(I, 1));
Basis(EliminationIdeal(I, 2));
I := ideal<P | x*y - z, y*z - w, z*w - x, x*w - y>;
Basis(EliminationIdeal(I, 1));
Basis(EliminationIdeal(I, 2));
P<x, y, z, w> := PolynomialRing(GF(7), 4);
I := ideal<P | x - y*z, y - z*w, x^2 - w^3>;
EliminationIdeal(I, 1);
EliminationIdeal(I, 2);
I := ideal<P | x - y*z, y - z*w + z^2, x^2 - w^3>;
Basis(EliminationIdeal(I, 1));
P<a, b, c, d> := PolynomialRing(GF(11), 4);
I := ideal<P | a - b*c + d^2, b^2 - c*d - 1, a*c - d^3 + b>;
EliminationIdeal(I, 1);
EliminationIdeal(I, 2);
for al in ["Default", "Direct", "Walk"] do
  al; Basis(EliminationIdeal(I, 1: Al := al));
end for;

// A lexicographical Groebner basis, once known, gives the elimination
// ideals.
P<x, y, z> := PolynomialRing(RationalField(), 3);
I := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
Groebner(I);
Basis(EliminationIdeal(I, 1));
I := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
J := ideal<P | x - z^4, y - z^3, z^5 - 1>;
_ := I eq J;
I;
EliminationIdeal(I, 1);
I := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
_ := x in I;
EliminationIdeal(I, 1);
I;
P<a, b, c, d> := PolynomialRing(RationalField(), 4);
I := ideal<P | a - b*c + d^2, b^2 - c*d - 1, a*c - d^3 + b>;
Groebner(I);
Basis(EliminationIdeal(I, 1));
P<t, x, y, z, w> := PolynomialRing(RationalField(), 5);
I := ideal<P | x - t, y - t^2, z - t^3, w - t^4>;
Groebner(I);
Basis(EliminationIdeal(I, 1));

// In other orders.
P<x, y, z> := PolynomialRing(RationalField(), 3, "grevlex");
I := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
E := EliminationIdeal(I, 1); E;
E := EliminationIdeal(I, 2); E;
I;
P<x, y, z> := PolynomialRing(RationalField(), 3, "glex");
I := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
E := EliminationIdeal(I, 1); E;
I;
Q := RationalField();
P<t, x, y, z, w> := PolynomialRing(Q, 5, "grevlex");
I := ideal<P | x - t, y - t^2, z - t^3, w - t^4>;
EliminationIdeal(I, 1);
EliminationIdeal(I, 2);
P<t, x, y, z, w> := PolynomialRing(Q, 5, "glex");
I := ideal<P | x - t, y - t^2, z - t^3, w - t^4>;
EliminationIdeal(I, 1);
P<t, x, y, z, w> := PolynomialRing(Q, 5, "elim", 1);
I := ideal<P | x - t, y - t^2, z - t^3, w - t^4>;
EliminationIdeal(I, 1);
P<t, x, y, z, w> := PolynomialRing(Q, 5, "elim", 2);
I := ideal<P | x - t, y - t^2, z - t^3, w - t^4>;
EliminationIdeal(I, 1);
P<t, x, y, z, w> := PolynomialRing(Q, 5, "grevlexw", [1, 1, 2, 3, 4]);
I := ideal<P | x - t, y - t^2, z - t^3, w - t^4>;
EliminationIdeal(I, 1);
P<t, x, y, z, w> := PolynomialRing(Q, 5, "grevlex");
I := ideal<P | x^2 - t*y, y^2 - x*z + t, z^2 - w*t, t^3 - x*w>;
EliminationIdeal(I, 1);
P<a, b, c, d> := PolynomialRing(Q, 4, "glex");
I := ideal<P | a - b*c + d^2, b^2 - c*d - 1, a*c - d^3 + b>;
EliminationIdeal(I, 1);
P<a, b, c, d> := PolynomialRing(Q, 4, "grevlexw", [1, 1, 3, 1]);
I := ideal<P | a - b^2, b*c - d^5, c^2 - d, a*d - 1>;
EliminationIdeal(I, 1);
P<x, y, z, w> := PolynomialRing(Q, 4, "glex");
I := ideal<P | x^2 + y^2 + z^2 + w^2 - 1, x - y*z, y - z*w + 1>;
Basis(EliminationIdeal(I, 1));
Basis(EliminationIdeal(I, 2));
I := ideal<P | x*y - z*w, x^2 - y*w + z, y^2 - x*z + w>;
Basis(EliminationIdeal(I, 1));
P<x, y, z, w> := PolynomialRing(Q, 4, "grevlexw", [2, 1, 3, 1]);
I := ideal<P | x^2 + y^2 + z^2 + w^2 - 1, x - y*z, y - z*w + 1>;
Basis(EliminationIdeal(I, 1));
Basis(EliminationIdeal(I, 2));
P<x, y, z, w> := PolynomialRing(Q, 4, "elim", 2);
I := ideal<P | x^2 + y^2 + z^2 + w^2 - 1, x - y*z, y - z*w + 1>;
Basis(EliminationIdeal(I, 1));
Basis(EliminationIdeal(I, 3));

// EliminationIdeal(I, S) keeps the easy basis of I and gives the reduced
// Groebner basis in grevlex of the elimination ideal, monic in grevlex.
// With every variable in S it is I itself.
P<x, y, z> := PolynomialRing(RationalField(), 3);
I := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
E := EliminationIdeal(I, {2, 3}); E;
E := EliminationIdeal(I, {x, z}); E;
E := EliminationIdeal(I, {z}); E;
E := EliminationIdeal(I, {}); E;
E := EliminationIdeal(I, {Integers()|}); E;
I;
J := ideal<P | x^2 + y^2 - 1, x - z^2>;
E := EliminationIdeal(J, {y}); E;
J;
K := ideal<P | x*y, y*z>;
EliminationIdeal(K, {1, 3});
EliminationIdeal(ideal<P | 1>, {});
EliminationIdeal(ideal<P | 1>, {1});
I := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
E0 := EliminationIdeal(I, {1, 2, 3});
_ := x in E0;
I;
P<x, y, z> := PolynomialRing(RationalField(), 3, "grevlex");
I := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
E := EliminationIdeal(I, {2, 3}); E;
I;
E := EliminationIdeal(I, {1, 3}); E;
P<t, x, y, z, w> := PolynomialRing(RationalField(), 5);
I := ideal<P | x - t, y - t^2, z - t^3, w - t^4>;
EliminationIdeal(I, {2, 3, 4, 5});
P<x, y, z, w> := PolynomialRing(GF(7), 4);
I := ideal<P | x - y*z, y - z*w, x^2 - w^3>;
EliminationIdeal(I, {3, 4});
EliminationIdeal(I, {1, 4});
EliminationIdeal(I, {2, 4});
I;
P<a, b, c, d> := PolynomialRing(GF(11), 4);
I := ideal<P | a - b*c + d^2, b^2 - c*d - 1, a*c - d^3 + b>;
EliminationIdeal(I, {2, 3, 4});
EliminationIdeal(I, {1, 3});

// Errors.
P<x, y, z> := PolynomialRing(RationalField(), 3);
I := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
EliminationIdeal(I, 4);
EliminationIdeal(I, -1);
EliminationIdeal(I, {4});
EliminationIdeal(I, {0});
EliminationIdeal(I, {x + y});
EliminationIdeal(I, {x^2});
EliminationIdeal(I, {y}: Al := "Direct");

// UnivariateEliminationIdealGenerator(s) keep the easy basis of I, which
// must be zero-dimensional.
P<x, y, z> := PolynomialRing(RationalField(), 3);
I := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
UnivariateEliminationIdealGenerator(I, 1);
I;
UnivariateEliminationIdealGenerator(I, 3);
UnivariateEliminationIdealGenerators(I);
I;
K := ideal<P | x^2, y^2 - z, z^3 - 1>;
UnivariateEliminationIdealGenerator(K, 2);
UnivariateEliminationIdealGenerator(K, 1);
K;
J := ideal<P | x + 1, y^2 - 2*y*z + z - 1, z^2 - z>;
UnivariateEliminationIdealGenerators(J);
J;
I := ideal<P | (x+1)^3*y^4, x*(y-z)^2+1, z^3-z^2>;
UnivariateEliminationIdealGenerators(I);
I;
P<x, y> := PolynomialRing(GF(5), 2, "grevlex");
I := ideal<P | x^3 - y^2 + 1, x*y - 2>;
UnivariateEliminationIdealGenerators(I);
I;
P<x, y> := PolynomialRing(GF(3), 2);
K := ideal<P | x^3 - y, y^3 - 1>;
UnivariateEliminationIdealGenerators(K);
K;
P<x, y, z> := PolynomialRing(RationalField(), 3);
I := ideal<P | x^2 - y, y^2 - z, x*z - 1>;
J := ideal<P | x^2 + y^2 - 1, x - z>;
UnivariateEliminationIdealGenerator(J, 1);
UnivariateEliminationIdealGenerators(J);
UnivariateEliminationIdealGenerator(I, 4);
UnivariateEliminationIdealGenerator(I, 0);
UnivariateEliminationIdealGenerators(ideal<P | 1>);
UnivariateEliminationIdealGenerator(ideal<P | 1>, 2);

// RelationIdeal: the reduced Groebner basis in grevlex of the relations,
// each polynomial monic in the order of the ring of the ideal, which is
// grevlex by default.
P<x, y, z> := PolynomialRing(GF(2), 3, "grevlex");
S := [(x + y + z)^2, (x^2 + y^2 + z^2)^3 + x + y + z + 1];
U2 := RelationIdeal(S);
U2;
Generic(U2);
P<x, y> := PolynomialRing(RationalField(), 2);
R := RelationIdeal([x^2, x*y, y^2]);
R;
R2 := RelationIdeal([x^2, x*y, y^2], PolynomialRing(RationalField(), 3, "grevlex"));
R2;
R3 := RelationIdeal([x + y, x*y, x^2 + y^2]);
R3;
R4 := RelationIdeal([x, y]);
R4;
R6 := RelationIdeal([x^2 + 1, x^3 - x]);
R6;
R := RelationIdeal([x^3, x^2*y, x*y^2, y^3]); R;
T<a, b, c, d> := PolynomialRing(RationalField(), 4);
R := RelationIdeal([x^3, x^2*y, x*y^2, y^3], T); R;
T<a, b, c, d> := PolynomialRing(RationalField(), 4, "glex");
R := RelationIdeal([x^3, x^2*y, x*y^2, y^3], T); R;
R := RelationIdeal([x + 1, x^2*y, x*y^2 - x, y^3 + y]); R;
T<a, b, c, d> := PolynomialRing(RationalField(), 4);
R := RelationIdeal([x + 1, x^2*y, x*y^2 - x, y^3 + y], T); R;
_ := a in R;
R;
R := RelationIdeal([x, x^2, x^3]); R;
T<a, b, c> := PolynomialRing(RationalField(), 3);
R := RelationIdeal([x, x^2, x^3], T); R;
R := RelationIdeal([x^2 - y, x^3 - y^2, x*y]); R;
RelationIdeal([P | ]);
RelationIdeal([x^2, y], PolynomialRing(RationalField(), 3));
RelationIdeal([x^2, y], PolynomialRing(GF(3), 2));
RelationIdeal([x^2, y^3, x*y], PolynomialRing(RationalField(), 3, "glex"));
