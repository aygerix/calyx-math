// Changing the monomial order (handbook, Gröbner Bases: Changing the
// Monomial Order).

// The handbook's example: the univariate elimination ideal generators, by a
// change to the univ order.
function univgen(I, i)
   // Make sure I has a Groebner basis so that
   // the conversion algorithm will be used when
   // constructing a Groebner basis of J
   Groebner(I);
   J := ChangeOrder(I, "univ", i);
   Groebner(J);
   return rep{f: f in Basis(J) | IsUnivariate(f, i)};
end function;

P<x, y, z> := PolynomialRing(RationalField(), 3, "grevlex");
I := ideal<P |
    1 - x + x*y^2 - x*z^2,
    1 - y + y*x^2 + y*z^2,
    1 - z - z*x^2 + z*y^2 >;

univgen(I, 1);
univgen(I, 2);
univgen(I, 3);

// Bases of zero-dimensional ideals in lex come from those in grevlex, over
// any field.
Q<a,b,c> := PolynomialRing(RationalField(), 3);
J := ideal<Q | a^2 + b^2 + c^2 - 1, a*b - c, b^2 - a*c + 2>;
GroebnerBasis(J);
J;
M := ideal<Q | a^2 - b*c, b^2 - a*c>;
GroebnerBasis(M);
F<w> := GF(9);
R<u,v> := PolynomialRing(F, 2);
K := ideal<R | u^3 + w*v - 1, v^2 - w^2*u>;
GroebnerBasis(K);
S<s,t> := PolynomialRing(GF(NextPrime(2^40)), 2);
L := ideal<S | s^3 - 2*t + 1, t^2 - 3*s*t + 5>;
GroebnerBasis(L);
