// Factorization and the individual factoring methods (trial division,
// Pollard rho, p-1, p+1, SQUFOF, ECM with a fixed curve, MPQS), stored
// factors, ECM group orders, divisors, coprime bases, partial
// factorizations and Cunningham numbers.
// TrialDivision follows the handbook of 2.29: since V2.29-9 it keeps to the
// bound exactly and returns the residue as an integer, where 2.22 returns a
// sequence and always divides out 2, 3, 5 and 7. StoreFactor takes a set,
// as the handbook says; 2.22 accepts one but stores nothing. SQUFOF(360) is
// complete here, where 2.22 returns [<2, 1>] and [10, 18]; that needs 2.29.
Factorization(360); Factorisation(-360); Factorization(1); Factorization(-1); Factorization(2^64+1); Factorization(10^20+1);
Factorization(0);
f, s := Factorization(-12); f, s;
f, s, r := Factorization(12); f, s; assigned r;
Factorization(1000001 : TrialDivisionLimit := 10); Factorization(2^67-1 : PollardRhoLimit := 10); Factorization(1000003*1000033 : SQUFOFLimit := 0);
Factorization(2^89-1: Proof := false); Factorization(2^89-1: Bases := 3, Proof := false);
StoreFactor(1000003); StoreFactor([1000033, 1000037]); GetStoredFactors(); ClearStoredFactors(); GetStoredFactors();
StoreFactor(10);
StoreFactor({101, 103}); GetStoredFactors(); ClearStoredFactors();
StoreFactor(-7);
TrialDivision(360); TrialDivision(2^10*1000003); TrialDivision(2^10*1000003, 10^7); TrialDivision(97, 5); TrialDivision(97*101, 100); TrialDivision(-360); TrialDivision(1); TrialDivision(15, 2);
TrialDivision(0);
TrialDivision(360, 1);
TrialDivision(360, 0);
TrialDivision(360, -1);
a, b := TrialDivision(2^3*3*1000003*1000033); a; b;
TrialDivision(360, 3); TrialDivision(360, 2); TrialDivision(2^3*7^2*11, 7);
PollardRho(1000003*1000033); PollardRho(360); PollardRho(97); PollardRho(1000003*1000033, 1, 1, 10);
PollardRho(1);
PollardRho(0);
pMinus1(1000003*2^89, 1000) gt 1;
pMinus1(1000003*1000033, 100, 1000);
pMinus1(1000003*1000033, 100: x0 := 3);
pMinus1(15, 10: x0 := 2);
pMinus1(1, 10);
pPlus1(1000003*1000033, 100: x0 := 3);
SQUFOF(1000003*1000033); SQUFOF(360); SQUFOF(97); SQUFOF(1000003*1000033, 10);
SQUFOF(1);
SQUFOF(2^200+1);
ECM(1000003*1000033, 1000: Sigma := 7);
ECM(1000003*1000033, 10: Sigma := 7);
ECM(1, 1000);
MPQS(1000003*1000033*1000037*1000039*1000081);
MPQS(10^30 + 57);
ECMOrder(1000003, 7); ECMFactoredOrder(1000003, 7); ECMOrder(1000033, 7); ECMOrder(10007, 123456);
ECMOrder(15, 7);
PrimeBasis(360); Divisors(28); Divisors(Factorization(496)); Divisors(1); Divisors(-12);
Divisors(0);
Divisors([<2, 3>]);
Divisors(Factorization(12)); PrimeBasis(Factorization(12));
CoprimeBasis([12, 18]); CoprimeBasis({6, 10, 15}); CoprimeBasis([]); CoprimeBasis([1]); CoprimeBasis([4, 8]); CoprimeBasis([12, 18, 1000]); CoprimeBasis([6, 15, 35]);
CoprimeBasis([0, 5]);
CoprimeBasis([-4, 6]);
Type(CoprimeBasis([12, 18]));
PartialFactorization([12]); PartialFactorization([]); PartialFactorization([1]); PartialFactorization([-12, 18]); PartialFactorization([7, 49, 343]); PartialFactorization([2^5*3^2, 6^3]);
PartialFactorization([0]);
Type(PartialFactorization([12])[1][1]);
Cunningham(2, 67, -1); Cunningham(2, 64, 1); Cunningham(10, 5, 1);
Cunningham(2, 10, 1); Cunningham(3, 5, -1); Cunningham(10, 1, 1); Cunningham(2, 1, -1); Cunningham(2, 0, 1); Cunningham(1, 5, 1);
Cunningham(12, 7, 1); Cunningham(6, 15, -1); Cunningham(2, 60, -1);
Cunningham(2, 67, 0);
Cunningham(2, 10, 2);
Cunningham(-2, 10, 1);
Cunningham(2, -3, 1);
HasAttribute(RngInt, "CunninghamStorageLimit");
RngInt`CunninghamStorageLimit;
AssertAttribute(RngInt, "CunninghamStorageLimit", 10^6); RngInt`CunninghamStorageLimit;
AssertAttribute(RngInt, "CunninghamStorageLimit", 0); HasAttribute(RngInt, "CunninghamStorageLimit");
AssertAttribute(RngInt, "CunninghamStorageLimit", 2^30-1); RngInt`CunninghamStorageLimit;
AssertAttribute(RngInt, "CunninghamStorageLimit", 2^30);
AssertAttribute(RngInt, "CunninghamStorageLimit", -1);
AssertAttribute(RngInt, "CunninghamStorageLimit", "x");
AssertAttribute(RngInt, "CunninghamStorageLimit", 1/2);
AssertAttribute(RngInt, "Foo", 1);
AssertAttribute(FldRat, "CunninghamStorageLimit", 1);
HasAttribute(RngInt, "Foo");
RngInt`Foo;
AssertAttribute(RngInt, "CunninghamStorageLimit", 50);
