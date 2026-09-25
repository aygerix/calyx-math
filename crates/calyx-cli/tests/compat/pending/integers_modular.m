// Modular arithmetic: powers, inverses, square roots, orders, primitive
// roots, linear congruences, the Chinese remainder theorem and norm
// equations.
Modexp(3, 4, 7); Modexp(3, -1, 7); Modexp(3, 0, 7); Modexp(-3, 3, 7); Modexp(2, 100, 2^61-1); Modexp(3, 4, 1);
Modexp(2, -1, 4);
Modexp(3, 4, 0);
Modexp(3, 4, -7);
17 mod 5; -17 mod 5; 17 mod -5;
Modinv(3, 7); InverseMod(3, 7); Modinv(-3, 7); Modinv(10, 7); Modinv(3, 1);
Modinv(2, 4);
Modinv(3, 0);
Modinv(3, -7);
Modsqrt(2, 7); Modsqrt(4, 7); Modsqrt(0, 7); Modsqrt(4, 15); Modsqrt(1, 2); Modsqrt(9, 16); Modsqrt(-1, 5); Modsqrt(2, 49);
Modsqrt(3, 7);
Modsqrt(2, 1);
Modsqrt(2, 0);
Modorder(2, 7); Modorder(3, 7); Modorder(2, 4); Modorder(1, 7); Modorder(6, 7); Modorder(-1, 7); Modorder(10, 7);
Modorder(2, 1);
Modorder(2, 0);
IsPrimitive(3, 7); IsPrimitive(2, 7); IsPrimitive(2, 4); IsPrimitive(3, 4); IsPrimitive(10, 7); IsPrimitive(0, 7);
IsPrimitive(3, 1);
PrimitiveRoot(7); PrimitiveRoot(2); PrimitiveRoot(4); PrimitiveRoot(8); PrimitiveRoot(9); PrimitiveRoot(18); PrimitiveRoot(1000003); PrimitiveRoot(2*3^5);
PrimitiveRoot(1);
PrimitiveRoot(0);
PrimitiveRoot(-7);
Solution(3, 4, 7); Solution(6, 4, 10); Solution(6, 3, 10); Solution(0, 0, 5); Solution(5, 0, 5); Solution(-3, 4, 7); Solution(3, 11, 7);
Solution(3, 4, 1);
Solution(3, 4, 0);
ChineseRemainderTheorem([2, 3], [3, 5]); CRT([2, 3, 2], [3, 5, 7]); CRT([1, 2], [4, 6]); CRT([1, 3], [4, 6]); CRT([], []); CRT([5], [7]); CRT([-1], [7]);
CRT([1], [1]);
CRT([1, 2], [3]);
CRT([1, 2], [0, 5]);
Solution([3, 2], [4, 1], [7, 5]); Solution([2], [1], [4]); Solution([1, 1], [1, 2], [4, 6]); Solution([1, 1], [1, 3], [4, 6]);
Solution([1], [1], [1]);
Solution([1, 2], [1], [3, 5]);
NormEquation(1, 25); NormEquation(1, 3); NormEquation(2, 9); NormEquation(3, 7); NormEquation(5, 0); NormEquation(1, 1); NormEquation(957440000095744000002277749760, 5102197760510219776012138128480644);
NormEquation(1, 25: Factorization := [<5, 2>]);
NormEquation(0, 4);
NormEquation(1, -4);
// Norm equations where d and m share square factors, or whose solutions
// need every square root modulo p^k.
NormEquation(6875, 1953125); NormEquation(28561, 371293); NormEquation(25, 3125); NormEquation(16, 16000); NormEquation(18, 3011499);
