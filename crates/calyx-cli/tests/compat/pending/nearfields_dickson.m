// Dickson nearfields: Dickson pairs and triples, variants, construction
// and printing. (Not yet checked against Magma: Magma 2.22 on the
// reference VM predates nearfields.)

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
Type(D), #D, Cardinality(N);
Kernel(D), PrimeField(D), Kernel(N), PrimeField(N);
D`gf, N`gf;
F := DicksonNearfield(7^2, 1);
F;
#F, Kernel(F);
