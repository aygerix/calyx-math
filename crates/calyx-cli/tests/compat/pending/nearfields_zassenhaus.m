// Zassenhaus nearfields: construction, printing, attributes, equality and
// the arithmetic of their elements.

// H23E4
for n := 1 to 7 do ZassenhausNearfield(n); end for;

// Names, attributes and structure
Z1 := ZassenhausNearfield(1);
Z1;
[Z1];
<Z1, 1>;
[ZassenhausNearfield(3)];
<ZassenhausNearfield(3), 1>;
for n in [1..7] do
    Z := ZassenhausNearfield(n);
    n, Z`ndx, Z`p, Z`q, Z`sz, #Z, Cardinality(Z), Z`prim eq PrimitiveElement(Z`gf), Z`gf eq GF(Z`p^2);
end for;
F<w> := Z1`gf;
Z1`prim, Z1`gf, Kernel(Z1), PrimeField(Z1), Type(Z1), Identity(Z1), Zero(Z1);
GetAttributes(NfdZss);
[assigned Z1``a : a in ["gf", "ndx", "p", "prim", "q", "sz"]];
NumberOfVariants(Z1);

// Equality: the same Zassenhaus number
Z1b := ZassenhausNearfield(1); Z2 := ZassenhausNearfield(2); Z5 := ZassenhausNearfield(5);
D := DicksonNearfield(5, 2);
Z1 eq Z1b, Z1 ne Z1b, Z1 eq Z1, Z2 eq Z5, Z1 cmpeq Z1b, #{Z1, Z1b}, Z1 cmpeq D;
Z1 eq D;
D ne Z1;

// Elements of the nearfield of order 25, whose units form SL(2, 3)
u := Z1!w; ub := Z1b!w; d := D!w;
u, Parent(u), Type(u), Eltseq(u), Z1![1, 2], Z1!(1/2), Z1!3, Z1!GF(5)!3, Z1!(GF(625)!w), Element(Z1, w^2);
u*u, u^-1, Inverse(u), Order(u), u^5, u/u, u^ub, IsUnit(u), IsIdentity(u^Order(u)), -u;
[Order(Z1!e) : e in F | e ne 0];
[Z1!e * u : e in [F!1, w, w^2, w^3, w + 1]];
[u * Z1!e : e in [F!1, w, w^2, w^3, w + 1]];
E := [Z1!e : e in F];
&and[(e*f)*g eq e*(f*g) : e, f, g in E];
&and[(e + f)*g eq e*g + f*g : e, f, g in E];
&and[e*(f + g) eq e*f + e*g : e, f, g in E];
&and[e*Inverse(e) eq Identity(Z1) : e in E | e ne Zero(Z1)];
#{e*f : e, f in E};

// An integer is a scalar on either side: u*2 is u + u, not u*(Z1!2).
v := Z1!(w^5 + 2);
u*2, u*Z1!2, Z1!2*u, u + u, 2*u, u*3, u*Z1!3, u*0, u*(-1), u*Z1!(-1), u*7, v*2, v*Z1!2, 2*v;
u^(Z1!w^6), u^Z1!2, u^(2^70), u^(-2^70);

// The other nearfields
H<t> := GF(121);
x2 := Z2!t; x5 := Z5!t;
[Order(Z2!e) : e in [t, t^2, t + 1, t^5, t^60]], [Order(Z5!e) : e in [t, t^2, t + 1, t^5, t^60]];
[x2 * Z2!e : e in [t, t^2, t + 1, t^5, t^60]];
[x5 * Z5!e : e in [t, t^2, t + 1, t^5, t^60]];
Z := ZassenhausNearfield(4);
K<k> := Z`gf;
a := Z!(k^100); b := Z!(k + 3); c := Z!(k^7 - 2);
a*b, b*a, (a*b)*c eq a*(b*c), (a + b)*c eq a*c + b*c, a*(b + c) eq a*b + a*c, a^b, Order(a), Order(b), a^-1, a^1000, Inverse(b)*b;
Z := ZassenhausNearfield(7);
K<k> := Z`gf;
x := Z!(k^5); y := Z!(k^1234 + 7);
x*3, x*Z!3, 3*x, y*5, y*Z!5, x*y, y*x, x^y, Order(x), Order(y), Order(x*y);
for n in [3, 6] do
    Z := ZassenhausNearfield(n);
    K<k> := Z`gf;
    [Z!(k^i) * Z!(k^j) : i, j in [1, 5, 17]], [Order(Z!(k^i)) : i in [1..12]];
end for;

// Equal nearfields share their elements; other nearfields do not, and
// nearfields of the other kind do not even compare. (Errors raised inside
// Magma's package code are caught, since Magma reports them with a
// traceback.)
u eq ub, u*ub, u + ub, Z1!ub, ub in Z1, d in Z1, u in D, IsCoercible(Z1, d), IsCoercible(Z1, 1/3);
try u + d; catch e print e`Object; end try;
try u - d; catch e print e`Object; end try;
try u / d; catch e print e`Object; end try;
try u ^ d; catch e print e`Object; end try;
try d ^ u; catch e print e`Object; end try;
try u / (D!0); catch e print e`Object; end try;
try u ^ (D!0); catch e print e`Object; end try;
try (D!0) ^ u; catch e print e`Object; end try;
try u ne d; catch e print e`Object; end try;
try d * u; catch e print e`Object; end try;
try d eq u; catch e print e`Object; end try;
try x2 eq x5; catch e print e`Object; end try;
try x2 * x5; catch e print e`Object; end try;
try x2 + x5; catch e print e`Object; end try;
try Z1!d; catch e print e`Object; end try;
try D!u; catch e print e`Object; end try;
try Z2!x5; catch e print e`Object; end try;
x5 in Z2;
[u, ub];
[u, d];
u lt d;
u lt ub;
u lt u;
u ge 1;
Z1 eq 1;

// Errors
ZassenhausNearfield(1/2);
try ZassenhausNearfield(0); catch e print e`Object; end try;
try ZassenhausNearfield(8); catch e print e`Object; end try;
try ZassenhausNearfield(-1); catch e print e`Object; end try;
try ZassenhausNearfield(2^100); catch e print e`Object; end try;
try Inverse(Z1!0); catch e print e`Object; end try;
try (Z1!0)^-1; catch e print e`Object; end try;
try u/(Z1!0); catch e print e`Object; end try;
try Order(Z1!0); catch e print e`Object; end try;
try Z1!GF(125).1; catch e print e`Object; end try;
try Element(Z1, GF(125).1); catch e print e`Object; end try;
try [e : e in Z1]; catch e print e`Object; end try;
try u*(1/2); catch e print e`Object; end try;
try u*F!2; catch e print e`Object; end try;
try u^(1/2); catch e print e`Object; end try;
Random(Z1) in Z1, IsZero(Z1!0), IsUnit(Z1!0), IsIdentity(Z1!1), Z1!1 eq Identity(Z1);
