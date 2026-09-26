// Univariate polynomials: functional decomposition (handbook, Univariate
// Polynomial Rings, Decomposition).
k:=GF(3^2);
P<x>:=PolynomialRing(k);
f:=x^9-x;
Decomposition(f);
Decomposition(f : All := false);
Evaluate($1[1][2], $1[1][1]) eq f;

// The number of decompositions, whether each composes back to f, and the
// decompositions as sorted lines.
composed := function(d)
    c := d[1];
    for i in [2..#d] do c := Evaluate(d[i], c); end for;
    return c;
end function;
show := procedure(f)
    D := Decomposition(f);
    print #D, forall{d : d in D | composed(d) eq f};
    for s in Sort([&cat[Sprint(c) cat "; " : c in d] : d in D]) do print s; end for;
end procedure;

// Over the rationals.
Q<x> := PolynomialRing(Rationals());
Decomposition(x^6);
Decomposition(x^12);
Decomposition(x^12 : All := false);
Decomposition(Q!ChebyshevT(6));
show(Q!ChebyshevT(12));
show(x^60);
show(x^30);
show(x^4 + x^2 + 1);
show(2*x^4 + 4*x^2 + 3);
show(3*(2*x^2 + 3*x + 1)^3 - 5*(2*x^2 + 3*x + 1) + 7);
show(-x^6/2 + x^3 - 7);
show(x^2*(x^2 + 1)^2);
show((x^3 + x)^3);
show((x^3 + 2*x)^2 + 5*(x^3 + 2*x));
show(Evaluate(x^3 + x + 1, Evaluate(x^4 - 7*x^3 + x, x^5 + 3*x^2 - x)));
Decomposition(x^5 + x + 1);
Decomposition(x^2 + 1);
Decomposition(3*x + 1);

// Over finite fields, with inseparable polynomials and additive ones.
F3<y> := PolynomialRing(GF(3));
show(y^9 - y);
Decomposition(y^6);
show(y^6 + y^3);
show(y^18 + 2*y^9 + y^3);
show(y^4 + y^2);
show(y^27);
show(y^81 - y);
F2<w> := PolynomialRing(GF(2));
show(w^4 + w);
show(w^8 + w);
show(w^4 + w^2 + w);
show(w^64 + w);
F4<u> := PolynomialRing(GF(4));
show(u^4 + u);
show(u^16 + u);
F9<v> := PolynomialRing(k);
show(v^6 + k.1*v^3);
show(v^9 + k.1*v^3);
show(v^27 - v);
F7<t> := PolynomialRing(GF(7));
show(t^6);
show(F7!ChebyshevT(6));
show(F7!ChebyshevT(14));
F27<s> := PolynomialRing(GF(27));
show(s^27 - s);
F5<r> := PolynomialRing(GF(5));
show(Evaluate(r^5 + 2*r^2 + r, r^5 + r^3 + 3*r));

// Constant polynomials and other coefficient rings.
Decomposition(Q!5);
Decomposition(Q!0);
Z<z> := PolynomialRing(Integers());
Decomposition(z^4 + z^2 + 1);
R<a> := PolynomialRing(RealField());
Decomposition(a^4 + a^2);
Decomposition(PolynomialRing(Integers(6)).1^4);
Decomposition(x^4 : All := 1);
