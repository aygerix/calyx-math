// List comprehensions [* e : x in S | P *], pairs a -> b in aggregates, and Self outside a sequence constructor.
S := [1, 2, 3];
[* a : a in S *];
[* a^2 : a in S | a gt 1 *];
L := [* a : a in S *]; Type(L); #L;
[* <i, j> : i in [1..2], j in [1..i] *];
[* <i, j> : j in [1..i], i in [1..2] *];
[* x : x in [] *];
[* [* a : a in [1..b] *] : b in [1..3] *];
f := func< n | [* k : k in [1..n] | IsPrime(k) *] >; f(10);
[* a : a in S | a gt 5 *];
[* 1, 2 *]; [* *]; [* 1 *];
// a -> b is the pair <a, b>
[* i -> j : i in [1..3], j in {5} *];
[ i -> i^2 : i in [1..3] ];
#{ i -> i^2 : i in [1..3] }; <2, 4> in { i -> i^2 : i in [1..3] };
[ 1 -> 2, 3 -> 4 ];
[* 1 -> 2, 3 -> 4 *];
[ Integers() | 1, 2 ]; [ Parent(<1, 2>) | 1 -> 2 ];
m := map< {1, 2, 3} -> Integers() | [ x -> x^2 : x in [1..3] ] >; m(2);
// Self outside a sequence constructor
[* Self(1) : x in [1..3] *];
< Self(1) : x in [1..3] >;
{ Self(1) : x in [1..3] };
[ Self(1) : x in [1..3] ];
[ x gt 1 select Self(x - 1) + 1 else 1 : x in [1..4] ];
