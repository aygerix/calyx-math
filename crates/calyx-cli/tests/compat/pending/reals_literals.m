// Real literals with a precision (1.2345p10), the elt constructor of real
// and complex fields, and the coercion homomorphisms from them. These
// need the lexer to read the p suffix and the evaluator to pass elt< >
// arguments and build hom< R -> S | > for real and complex fields (#54).

// H26E4
x := 1.2345;
x, Parent(x);
SetDefaultRealField(RealField(20));
x1 := 1.2345;
x1, Parent(x1);
x2 := 12345e-4;
x2, Parent(x2);
x3 := 1.2345p10;
x3, Parent(x3);
x4 := 12345e-4p8;
x4, Parent(x4);
x5 := RealField(12) ! 1.2345;
x5, Parent(x5);
SetDefaultRealField(RealField(30));
1.5p5; 1.5P5; 2e3p4; -1.5p40; 1e-400p10; 1p10;

// elt< >: m*2^n in a real field, x + y*i in a complex field.
elt<RealField(10) | 3, 4>;
elt<RealField(10) | 3/2, -4>;
elt<RealField(10) | 1.5, 1000>;
elt<ComplexField(10) | 1, 2>;
elt<ComplexField(10) | 1/3, RealField(20)!2/3>;

// H26E2
Re := RealField(20);
PC<x, y> := PolynomialRing(ComplexField(8), 2);
f := hom< Re -> PC | >;
bangf := Bang(Re, PC);
f(Pi(Re));
f(Pi(Re)) eq bangf(Pi(Re));
