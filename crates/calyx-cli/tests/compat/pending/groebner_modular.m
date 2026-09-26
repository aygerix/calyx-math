// Gröbner bases over the rationals: by default Magma lifts them from bases
// modulo primes (Monte Carlo); GlobalModular := false computes them without
// that shortcut. The two agree.

// A zero-dimensional ideal with denominators, in grevlex, glex and lex.
S := func< P | [P.1^2 + P.2*P.3/3 - 2, P.1*P.2 - P.3^2/5 + 1/7, P.2^2 - P.1*P.3 + 3/2] >;
for o in ["grevlex", "glex", "lex"] do
    P<x,y,z> := PolynomialRing(RationalField(), 3, o);
    G := GroebnerBasis(S(P));
    G eq GroebnerBasis(S(P) : GlobalModular := false), #G, [LeadingMonomial(g) : g in G];
end for;
P<x,y,z> := PolynomialRing(RationalField(), 3);
GroebnerBasis(S(P));

// Elimination and weighted orders.
P<x,y,z> := PolynomialRing(RationalField(), 3, "elim", 1);
G := GroebnerBasis(S(P));
G eq GroebnerBasis(S(P) : GlobalModular := false), [LeadingMonomial(g) : g in G];
P<x,y,z> := PolynomialRing(RationalField(), 3, "grevlexw", [1, 2, 3]);
G := GroebnerBasis(S(P));
G eq GroebnerBasis(S(P) : GlobalModular := false), [LeadingMonomial(g) : g in G];

// Ideals, also once membership has needed a basis in grevlex (which is then
// kept).
P<x,y,z> := PolynomialRing(RationalField(), 3, "lex");
I := ideal<P | S(P)>;
Groebner(I : GlobalModular := false);
GroebnerBasis(I) eq GroebnerBasis(S(P));
J := ideal<P | S(P)>;
x in J, x^2 + y*z/3 - 2 in J;
GroebnerBasis(J : GlobalModular := false) eq GroebnerBasis(S(P));

// Ideals of positive dimension.
P<x,y,z> := PolynomialRing(RationalField(), 3, "lex");
T := [x*z - y^2/2, x^3 - y*z/3];
GroebnerBasis(T);
GroebnerBasis(T) eq GroebnerBasis(T : GlobalModular := false);
Q<x,y,z> := PolynomialRing(RationalField(), 3);
T := [x^2*y - z^3/4, x*y^2 - 2*z/5];
GroebnerBasis(T);
GroebnerBasis(T) eq GroebnerBasis(T : GlobalModular := false);

// The unit ideal and the zero ideal.
GroebnerBasis([x*y - 1/3, x - 1/2, y]);
GroebnerBasis([Q | 0]);

// Primes dividing a denominator or a leading coefficient give no basis;
// the first prime below 2^31 is unlucky for the second ideal.
P<x,y> := PolynomialRing(RationalField(), 2, "lex");
GroebnerBasis([2147483647*x - 1, y^2 - 1/2147483629]);
GroebnerBasis([x*y - 2147483647, x^2 - 1]);
Q<x,y> := PolynomialRing(RationalField(), 2);
GroebnerBasis([x*y - 2147483647, x^2 - 1]);

// Lex bases in shape position, x - g(y) and f(y) with f squarefree, and
// others. Here some points have y-coordinates congruent modulo the first
// prime below 2^31 or the second.
P<x,y> := PolynomialRing(RationalField(), 2, "lex");
for T in [[x - y^2 + 1/3, y^3 - 2*y + 5/7], [x^2 - 1, y^2 - 1], [x - y, y^2],
          [x - y, y^2 - 2147483647*y], [x - y, y^2 - 2147483629*y],
          [x^3 - 3*x^2 + 2*x, 4294967257*x^2 - 8589934515*x + 2*y]] do
    G := GroebnerBasis(T);
    G, G eq GroebnerBasis(T : GlobalModular := false);
end for;
P<x,y,z> := PolynomialRing(RationalField(), 3, "lex");
GroebnerBasis([x*z - 1, y - z^2 + 3, z^4 - 2/3*z - 1]);

// Katsura-4, whose basis in lex takes some hundred primes.
P<u0,u1,u2,u3,u4> := PolynomialRing(RationalField(), 5, "lex");
K := [u0 + 2*u1 + 2*u2 + 2*u3 + 2*u4 - 1,
      u0^2 + 2*u1^2 + 2*u2^2 + 2*u3^2 + 2*u4^2 - u0,
      2*u0*u1 + 2*u1*u2 + 2*u2*u3 + 2*u3*u4 - u1,
      u1^2 + 2*u0*u2 + 2*u1*u3 + 2*u2*u4 - u2,
      2*u1*u2 + 2*u0*u3 + 2*u1*u4 - u3];
G := GroebnerBasis(K);
G eq GroebnerBasis(K : GlobalModular := false), #G, [LeadingMonomial(g) : g in G];
G eq GroebnerBasis(ideal<P | K>);
// The largest numerator and denominator.
a := Max([Abs(Numerator(c)) : c in Coefficients(g), g in G]);
d := Max([Denominator(c) : c in Coefficients(g), g in G]);
a, d;
