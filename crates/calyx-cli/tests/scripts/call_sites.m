// A call site remembers the signature it chose for the argument types it
// saw; the same site called with other types must choose again.
f := func< x | Abs(x) >;
for x in [* -2, -1/2, -1.5, -2 *] do f(x); end for;
for g in [* Abs, Floor, Ceiling *] do g(-3/2); end for;
h := func< a, b | Gcd(a, b) >; h(12, 18), h(12/1, 18), h(-4, 6);
s := []; for x in [1, 2, 3] do Append(~s, x); end for; s;
t := [1/2]; for x in [1, 2] do Append(~t, x); end for; t;
k := func< x | IsEven(x) >; k(4), k(3);
try k(1/2); catch e print e`Object; end try;
k(4);
m := func< x | Sprint(x) >; m(1), m([1]), m("a"), m(1);
