// Iterating over a ring makes its elements one at a time, so a loop that
// stops early never builds them all, even past 2^26 elements.
n := 0; for x in GF(2^27) do n +:= 1; if n eq 6 then print x; break; end if; end for; n;
K<k> := GF(3^13); for x in K do if x ne 0 and x ne 1 and x ne 2 then print x; break; end if; end for;
exists{x : x in GF(5^9) | x ne 0 and IsPrimitive(x)};
exists(t){x : x in GF(11^7) | x ne 0}; t;
exists(t){x : x in GF(1000003^2) | x ne 0}; t;
for x in GF(1000003) do if x ne 0 then print x; break; end if; end for;
for x in Integers(10^20) do if x ne 0 then print x; break; end if; end for;
&+[x : x in GF(7^3)], #[x : x in GF(3^4)], {x^2 : x in GF(9)};
