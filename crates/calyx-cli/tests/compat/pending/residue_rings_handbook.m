// The examples of the Residue Class Rings chapter (H20E1-H20E6). The
// ideal division is assigned before printing (as a statement Magma also
// prints a second value), and the set of powers in H20E6 is compared
// rather than printed (it prints in hash order).
Z := Integers();
I := ideal<Z|1>; // ideal of Z
D := Z/I; D; // interpreted as ideal division
quo<Z|I>; // quotient of ring by ideal

Z := IntegerRing();
I13 := ideal< Z | 13 >;
I13;
1 in I13;
0 in I13;
-13 in I13;
I0 := ideal< Z | 0 >;
0 in I0;
1 in I0;
I1 := ideal< Z | 1 >;
I1 eq Z;

p := PreviousPrime(2^16);
p;
R := ResidueClassRing(p);
exists(t){x : x in R | x^3 eq 23};
t;

r := ResidueClassRing(3) ! 5;
r;
ResidueClassRing(6) ! r;

R := ResidueClassRing(2340);
x := R!1404;
sqrts := AllSquareRoots(x);
sqrts;
[ y^2 : y in sqrts ];

m := 735;
R := ResidueClassRing(m);
U, psi := UnitGroup(R);
U;
#U;
EulerPhi(735);
gens := [ psi(U.i) : i in [1..3] ]; gens;
[ Order(x) : x in gens ];

R := IntegerRing(50);
U, psi := UnitGroup(R);
w := PrimitiveElement(R);
w;
Order(w);
powers := { w^i : i in [0..19] };
#powers;
powers eq { psi(u) : u in U };
