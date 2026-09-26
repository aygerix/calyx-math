// Elements of Dickson nearfields: arithmetic, predicates and orders.
// (Not yet checked against Magma: Magma 2.22 on the reference VM predates
// nearfields.)

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
[Order(e) : e in N | IsUnit(e)];
Inverse(u), u^-1, u^0, u^5, u^-3, (N!0)^3;
u*Inverse(u) eq Identity(N), Inverse(u)*u eq Identity(N), u^4 eq Identity(N);
IsIdentity(u^4), IsIdentity(Identity(N)), IsUnit(Zero(N)), IsUnit(u), IsZero(u - u);
-u, u + 1, 2*u, u*2, u - N!(w^2), u/u, (N!w)^2, N!(w^2);
Eltseq(u), ElementToSequence(N!(w^3));
u in N, Parent(u) eq N, Type(u);
#{e : e in N}, #{e*f : e, f in N};
&and[(e*f)*g eq e*(f*g) : e, f, g in N];
&and[(e + f)*g eq e*g + f*g : e, f, g in N];
&and[e*(f + g) eq e*f + e*g : e, f, g in N];
&and[e*f eq f*e : e, f in N];

// A nearfield on a field without logarithm tables
M := DicksonNearfield(13, 6);
H<t> := M`gf;
m := M!t;
m*m, m^2, M!(t^2)*m;
Order(m), Order(m^6), Order(M!(t^6)), Order(M!(t + 1));
(m*M!(t + 1))*M!(t^3) eq m*(M!(t + 1)*M!(t^3));
Inverse(m)*m eq Identity(M), m^-1 eq Inverse(m);
m^(M!(t + 2)) eq Inverse(M!(t + 2))*m*M!(t + 2);
