// Elements of Dickson nearfields: arithmetic, predicates, orders, and
// what they do not mix with.

// H23E5, taking the field element D`gf.1 directly
D := DicksonNearfield(3^2,2);
x := Element(D,D`gf.1);
x;
Parent(x);
x^2;
Identity(D);
assert x ne Identity(D);
assert x eq x;
Zero(D);
Parent(Zero(D));
assert not IsZero(D!1);
assert not IsZero(x);
assert IsZero(Zero(D));
K<z> := GF(3,4);
x := Element(D,z^61);
y := Element(D,z^54);
assert x + y eq Element(D,z^61+z^54);
assert x - y eq Element(D,z^61-z^54);
x*y;
x/y;
x^y;

// H23E6
N := DicksonNearfield(3^2,4);
F<a> := N`gf;
x := Element(N,a^5215);
y := Element(N,a^5140);
z := Element(N,a^5819);
x*y eq y*x;
x*(y+z) eq x*y+x*z;
(y+z)*x eq y*x+z*x;

// The nearfield of order 9: its units form the quaternion group
N := DicksonNearfield(3, 2);
G<w> := GF(9);
u := N!w;
[Order(N!e) : e in G | e ne 0];
Inverse(u), u^-1, u^0, u^5, u^-3, (N!0)^3;
u*Inverse(u) eq Identity(N), Inverse(u)*u eq Identity(N), u^4 eq Identity(N);
IsIdentity(u^4), IsIdentity(Identity(N)), IsUnit(Zero(N)), IsUnit(u), IsZero(u - u);
-u, 2*u, u*2, u - N!(w^2), u/u, (N!w)^2, N!(w^2), N!1, N!(-1), N!(1/2), N![1, 2];
x := u; x +:= u; x; x *:= u; x;
Eltseq(u), ElementToSequence(N!(w^3));
u in N, Parent(u) eq N, Type(u);
E := [N!e : e in G];
#Set(E), #{e*f : e, f in E};
&and[(e*f)*g eq e*(f*g) : e, f, g in E];
&and[(e + f)*g eq e*g + f*g : e, f, g in E];
&and[e*(f + g) eq e*f + e*g : e, f, g in E];
&and[e*f eq f*e : e, f in E];

// Integers meet nearfield elements only as scalars and exponents, and
// field elements not at all; there is no iteration over a nearfield.
// (Errors raised inside Magma's package code are caught, since Magma
// reports them with a traceback.)
Inverse(N!0);
Order(N!0);
1 in N, w in N;
try u + 1; catch e print e`Object; end try;
try 1 - u; catch e print e`Object; end try;
try u/2; catch e print e`Object; end try;
try u eq 1; catch e print e`Object; end try;
try u ne 0; catch e print e`Object; end try;
try u eq w; catch e print e`Object; end try;
try u*w; catch e print e`Object; end try;
try u^w; catch e print e`Object; end try;
try u lt u; catch e print e`Object; end try;
try u gt 1; catch e print e`Object; end try;
try [e : e in N]; catch e print e`Object; end try;
try Set(N); catch e print e`Object; end try;
try (N!0)^-1; catch e print e`Object; end try;
try u/(N!0); catch e print e`Object; end try;
try u^(N!0); catch e print e`Object; end try;
try N!GF(27).1; catch e print e`Object; end try;
try Element(N, GF(27).1); catch e print e`Object; end try;
N!(GF(81)!w), N!GF(3)!2, Element(N, GF(3)!2);
try N!(1/3); catch e print e`Object; end try;
try N!"w"; catch e print e`Object; end try;
try Element(N, 2); catch e print e`Object; end try;

// Equal nearfields share their elements; others do not
N2 := DicksonNearfield(3, 2);
u2 := N2!w;
u eq u2, u + u2, u*u2, u2 in N, N2!u;
A := DicksonNearfield(5, 4); B := DicksonNearfield(5, 4 : Variant := 3); C := DicksonNearfield(5, 4 : Variant := 7);
K<k> := GF(625);
a := A!k; b := B!k; c := C!k;
a*a, b*b, b*c, b*c eq c*b, b in C, a in B;
try a eq b; catch e print e`Object; end try;
try a + b; catch e print e`Object; end try;
try a*b; catch e print e`Object; end try;
try a^b; catch e print e`Object; end try;
try B!a; catch e print e`Object; end try;
try Element(B, a); catch e print e`Object; end try;

// In aggregates, elements of two nearfield objects share no universe, even
// when the nearfields are equal; coercion into a given nearfield takes them.
[u, u2];
{u, u2};
{@ u, u2 @};
{* u, u2 *};
&+[u, u2];
[u] cat [u2];
[N | ] cat [u2];
[u] eq [u2];
[u] cmpeq [u2], [N | u, u2], {N | u2}, <u, u2>, ChangeUniverse([u], N2), [N2 | x : x in [u]];
S := [u, u^2, u]; T := {u, u^2};
S, Universe(S), #Set(S), T, Universe(T);
Append(S, u2), Append(S, 1), Include(T, u2), Exclude(T, u2);
u2 in S, u2 in T, u2 in {@ u @}, u2 in {* u *}, Index(S, u2), Position(S, u2);
S[2] := u2; S;
S[1] := GF(27).1;
{N | GF(27).1};
&*[u, u], &+[N | ], &*[N | ], Seqset(S), SequenceToSet([N | u, u2]), Multiset([u, u]), {u, u^2} eq {u^2, u};
#{N, N2}, #{N, A}, #[N, N2], N2 in [N], N2 in {N}, Index([N, A], N2), [N] eq [N2], {N} eq {N2};

// Nearfield elements have no order, and IsCoercible gives its reason.
Sort([u]);
Max([u]);
Min([u, u^2]);
Max({u, u^2});
Min({@ u, u^2 @});
Sort([u, u^2], func<a, b | 0>);
Sort([N | ]);
Max([N | ]);
IsCoercible(N, 1);
IsCoercible(N, w);
IsCoercible(N, u2);
IsCoercible(N, 1/3);
IsCoercible(N, GF(27).1);
IsCoercible(A, u);
IsCoercible(N, "w");
IsCoercible(N, [1, 2]);
IsCoercible(G, u), IsCoercible(Integers(), u);
l, v := IsCoercible(N, 1/3); Type(v);

// A nearfield on a field without logarithm tables
M := DicksonNearfield(13, 6);
H<t> := M`gf;
m := M!t;
m*m, m^2, M!(t^2)*m;
Order(m), Order(m^6), Order(M!(t^6)), Order(M!(t + 1));
(m*M!(t + 1))*M!(t^3) eq m*(M!(t + 1)*M!(t^3));
Inverse(m)*m eq Identity(M), m^-1 eq Inverse(m);
m^(M!(t + 2)) eq Inverse(M!(t + 2))*m*M!(t + 2);
