// The confluent hypergeometric function U(a, b, x). (HypergeometricSeries
// returns a power series, which calyx does not have yet.)

R := RealField(20);
C<i> := ComplexField(20);
D := RealField(10); E := RealField(30);
x := R!2/3; w := R!5/2;

for t in [<x, w, R!1/3>, <R!1, R!2, R!3>, <R!-1, R!2, w>, <R!0, x, w>, <x, w, R!10^6>, <x, w, R!1/10^10>, <R!-3, R!-5/2, w>] do
  r := HypergeometricU(t[1], t[2], t[3]);
  t, r, MantissaExponent(r);
end for;

// Integers and rationals are in the default field, and so is the value
// unless the arguments are reals of the same precision.
HypergeometricU(1, 2, 3), HypergeometricU(1, 2, w), HypergeometricU(1/3, 1/2, 5/2);
HypergeometricU(2/3, 5/2, R!1/3), HypergeometricU(x, w, 5), HypergeometricU(x, w, 1/3);
HypergeometricU(D!2/3, D!5/2, D!1/3), HypergeometricU(E!2/3, E!5/2, E!1/3);
HypergeometricU(D!2/3, w, R!1/3), HypergeometricU(x, D!5/2, R!1/3), HypergeometricU(x, E!5/2, D!1/3);
// Reals a and b of the same precision need x in their field.
HypergeometricU(x, w, D!1/3);
HypergeometricU(x, w, E!1/3);
HypergeometricU(C![1, 1], w, w);
