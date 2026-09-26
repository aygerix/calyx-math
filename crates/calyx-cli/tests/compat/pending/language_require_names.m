// A failed requirement in a package intrinsic names the intrinsic unless
// the call is a statement of its own.
ECMOrder(10, 7);
x := ECMOrder(10, 7);
print ECMOrder(10, 7);
ECMOrder(10, 7), 1;
EulerPhiInverse(0);
x := EulerPhiInverse(0);
[ECMOrder(10, 7)];
f := func< | ECMOrder(10, 7)>; f();
procedure p() x := ECMOrder(10, 7); end procedure; p();
function g() return ECMOrder(10, 7); end function; g();
z := g();
try x := ECMOrder(10, 7); catch e print e`Object; end try;
try ECMOrder(10, 7); catch e print e`Object; end try;
