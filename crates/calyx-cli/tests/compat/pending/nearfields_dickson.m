// Dickson nearfields: Dickson pairs and triples, variants, construction
// and printing.

// H23E1
DicksonPairs(5,3,4,4,5);
DicksonPairs(5,4,5);
DicksonTriples(5,4,5);

// H23E2
NumberOfVariants(625,4);
VariantRepresentatives(625,4);

// H23E3
D := DicksonNearfield(625,4);
D3 := DicksonNearfield(625,4 : Variant := 3);
D5 := DicksonNearfield(625,4 : Variant := 5);
D eq D3;
D3 eq D5;
D eq D5;
D;

// More pairs and variants
DicksonPairs(2, 6, 7);
DicksonTriples(7, 2, 8);
NumberOfVariants(3^3, 13), VariantRepresentatives(3^3, 13);
NumberOfVariants(7, 2), VariantRepresentatives(7, 2), NumberOfVariants(5^2, 1), VariantRepresentatives(5^2, 1);
NumberOfVariants(D3), NumberOfVariants(DicksonNearfield(13, 6));
N := DicksonNearfield(3^3, 13 : Variant := 2);
N;
N eq DicksonNearfield(3^3, 13 : Variant := 6), N eq DicksonNearfield(3^3, 13 : Variant := 4);
N eq DicksonNearfield(3^3, 13 : Variant := 15), N eq DicksonNearfield(3^3, 13 : Variant := -11), D eq DicksonNearfield(625, 4 : Variant := 1);

// Magma's order of variants and its choice of primitive element
for qv in [<13, 12>, <31, 15>, <49, 16>, <61, 60>, <73, 72>, <37, 72>, <64, 63>, <19, 27>, <121, 20>, <81, 16>] do
    NumberOfVariants(qv[1], qv[2]), VariantRepresentatives(qv[1], qv[2]);
end for;
for t in [<5, 4, 3>, <5, 4, 7>, <5, 4, -1>, <25, 8, 3>, <25, 8, 5>, <7, 9, 2>, <7, 9, 5>, <13, 12, 5>, <49, 4, 3>, <17, 16, 5>, <16, 15, 11>, <31, 5, 3>, <13, 3, 5>, <3, 1, 3>, <5, 2, 3>] do
    E := DicksonNearfield(t[1], t[2] : Variant := t[3]);
    t, Log(PrimitiveElement(E`gf), E`prim);
end for;
N`prim, D3`prim, DicksonNearfield(7, 9 : Variant := 5)`prim;

// Attributes
E := DicksonNearfield(7, 9 : Variant := 2);
E`p, E`h, E`q, E`v, E`sz, E`twist, E`rho;
D`twist, D`rho, N`twist;
GetAttributes(NfdDck), GetAttributes(NfdZss), GetAttributes(Nfd), GetAttributes(NfdElt);
assigned E`matgrp, assigned E`prim;
Type(D), #D, Cardinality(N);
Kernel(D), PrimeField(D), Kernel(N), PrimeField(N);
D`gf, N`gf;
F := DicksonNearfield(7^2, 1);
F;
#F, Kernel(F);

// Printing without a name
DicksonNearfield(3, 2);
[DicksonNearfield(3, 2)];
<DicksonNearfield(3, 2), 1>;

// Errors, and negative v. (Errors raised inside Magma's package code are
// caught, since Magma reports them with a traceback.)
DicksonNearfield(6, 2);
DicksonNearfield(3, 4);
DicksonNearfield(3, -4);
DicksonNearfield(625, 4 : Variant := 2);
NumberOfVariants(6, 2);
VariantRepresentatives(3, 4);
try DicksonNearfield(1, 2); catch e print e`Object; end try;
try DicksonNearfield(3, 0); catch e print e`Object; end try;
try DicksonNearfield(3, -2); catch e print e`Object; end try;
try DicksonNearfield(625, 4 : Variant := 1/2); catch e print e`Object; end try;
try DicksonNearfield(625, 4 : LargeMatrices := 1); catch e print e`Object; end try;
try NumberOfVariants(0, 2); catch e print e`Object; end try;
try NumberOfVariants(3, -2); catch e print e`Object; end try;
try VariantRepresentatives(3, -2); catch e print e`Object; end try;
try DicksonPairs(4, 2, 2); catch e print e`Object; end try;
try DicksonPairs(-5, 1, 3); catch e print e`Object; end try;
try DicksonPairs(6, 1, 2, 1, 2); catch e print e`Object; end try;
try DicksonPairs(5, 0, 1, 0, 2); catch e print e`Object; end try;
try DicksonPairs(5, -1, 1, -2, 2); catch e print e`Object; end try;
try DicksonPairs(5, 1, 1, 0, 2); catch e print e`Object; end try;
try DicksonTriples(4, 2, 2); catch e print e`Object; end try;
try DicksonTriples(-5, 1, 3); catch e print e`Object; end try;
DicksonPairs(5, 1, 1, -2, -1), DicksonPairs(5, 2, 1, 0, 2), DicksonPairs(5, 1, 0), DicksonPairs(5, 0, 2);
DicksonTriples(5, 0, 2), DicksonTriples(5, 2, 0), DicksonTriples(5, -1, 2);
DicksonPairs(2^61 - 1, 1, 2);
