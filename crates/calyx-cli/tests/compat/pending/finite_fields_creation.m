// Creation of finite fields: GF, FiniteField and GaloisField, extensions
// by a degree and by a polynomial, subfields, ground and prime fields,
// meets and common overfields.
F7 := FiniteField(7);
F7;
F<z> := FiniteField(7^4);
F;
F<z> := ext< F7 | 4 >;
F;
P<x> := PolynomialRing(F7);
p := x^4+4*x^3+2*x+3;
F<z> := ext< F7 | p >;
F;
F49<w> := ext< F7 | 2 >;
F<z> := ext< F49 | 2 >;
F;

GF(2); GF(4); GF(2^20); GF(3, 5); GaloisField(5, 3); FiniteField(9); GaloisField(11); FiniteField(2, 8);
GF(2, 100); GF(1009); GF(1000003, 2); GF(2^127 - 1); GF(2^61 - 1, 2);
GF(7) eq FiniteField(7), GF(7^2) eq GF(49), GF(7, 2) eq GaloisField(49), GF(7^2) eq GF(7^3), GF(2, 3: Optimize := false) eq GF(8);
Type(GF(7)), Type(GF(7^2)), Type(GF(2^100)), Type(GF(2^127 - 1));
K<a> := GF(2^100); a^101; a^100 + a^99 + 1;
L<b> := GF(3, 40); b^41 - b^40;
M<c> := GF(1000003, 2); c^3; c + 1000002;
G<u> := GF(2^16); u^65534, u^65535, u^32768;

// Extensions by a degree and by polynomials
E := ext< F7 | 1 >; E eq F7;
E, m := ext< F7 | 3 >; E; m; m(F7!3); E eq GF(7^3);
E6<e6> := ext< F49 | 3 >; E6; e6; IsDefault(E6), Degree(E6), Degree(E6, F49), GroundField(E6) eq F49;
E<e> := ext< F7 | x^2 + 1 >; E; e^2; IsDefault(E), IsConway(E);
E<e> := ext< F7 | x - 3 >; E; e;
Q<y> := PolynomialRing(F49);
H<h> := ext< F49 | y^2 + y + 6*w + 4 >; H; h^2; GroundField(H) eq F49; Degree(H), Degree(H, F49);
H<h> := ext< F49 | 3 >; H; IsDefault(H);
R<r> := ext< E | 2 >; R; GroundField(R) eq E; Degree(R, E);
K2 := ext< GF(2^100) | 2 >; K2; IsDefault(K2);

// Random extensions and splitting fields
Degree(RandomExtension(F7, 5)), IsDefault(RandomExtension(F7, 5)), Degree(RandomExtension(F49, 3), F49);
S := SplittingField(x^6 - 2); S; Degree(S);
S := SplittingField((x^2 + 1)*(x^3 + x + 1)); Degree(S);
S := SplittingField({x^2 + 1, x^3 + x + 1, x - 2}); Degree(S);
Degree(SplittingField(y^3 - w)), Degree(SplittingField(y^2 - w), F49);

// Subfields
F<z> := GF(7^6);
S, m := sub< F | 2 >; S; Domain(m) eq S, Codomain(m) eq F; S eq GF(49); m(S.1) eq z^((7^6 - 1) div 48);
S := sub< F | 3 >; S eq GF(7^3);
S := sub< F | 6 >; S eq F;
S := sub< F | 1 >; S eq F7;
S, m := sub< F | z^(7^3 + 1) >; S eq GF(7^3); m(S.1) eq z^(7^3 + 1);
S := sub< F | z^((7^6 - 1) div 6) >; S eq F7;
G<u> := ext< F7 | x^4 + x + 1 >;
S, m := sub< G | 2 >; Degree(S); m(S.1)^49 eq m(S.1); DefiningPolynomial(S) eq ConwayPolynomial(7, 2);
S := sub< G | u^400 >; Degree(S);
S := sub< G | u >; S eq G;

// Ground fields, prime fields, meets and common overfields
GroundField(F), BaseField(F), PrimeField(F), GroundField(F7), PrimeField(E);
GroundField(H) eq F49, PrimeField(H), BaseField(R) eq E;
IsPrimeField(F7), IsPrimeField(F), IsPrimeField(GF(2^100)), IsPrimeField(E);
GF(7^6) meet GF(7^4); GF(7^6) meet GF(7^6); GF(7^12) meet GF(7^8); GF(7^5) meet GF(7^3);
GF(7^6) meet sub< GF(7^6) | 3 >;
CommonOverfield(GF(7^2), GF(7^3)); CommonOverfield(GF(7^4), GF(7^6)); CommonOverfield(F7, GF(7^5));
CommonOverfield(GF(7^6), sub< GF(7^6) | 2 >);
CommonOverfield(sub< G | 2 >, GF(7^3));

// errors
GF(6);
GF(1);
GF(0);
GF(-7);
GF(7, 0);
GF(7, -1);
GF(6, 2);
FiniteField(2^127);
ext< F7 | 0 >;
ext< F7 | -2 >;
ext< F7 | x^2 - 1 >;
ext< F7 | 2*x^2 + 1 >;
ext< F7 | P!3 >;
ext< F49 | x^2 + 1 >;
sub< F | 4 >;
sub< F | 0 >;
sub< F | -2 >;
sub< F | GF(5)!2 >;
GF(7) meet GF(5);
GF(7^2) meet ext< F7 | x^2 + 1 >;
CommonOverfield(GF(5), GF(7));
CommonOverfield(ext< F7 | x^2 + 1 >, ext< F7 | x^2 + 1 >);
SplittingField(P!0);
SplittingField(P!3);
RandomExtension(F7, 0);
