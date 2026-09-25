// Error handling, assertions and runtime errors.
procedure always_fails(x)
    error Error(x);
end procedure;
try
    always_fails(1);
    always_fails(2);
catch e
    print "In catch handler";
    e`Object, e`Type;
end try;
try
    x := 1/0;
catch err
    err`Type;
    err`Object;
end try;
try
    error "custom", 42;
catch err
    err`Object;
end try;
error "Error calling procedure with parameter: ", 1;
error if 1 eq 1, "condition", "held";
error if 1 eq 2, "not raised";
"after";
assert 1 eq 1;
assert 1 eq 2;
SetAssertions(0);
assert 1 eq 2;
SetAssertions(1);
assert2 false;
SetAssertions(2);
assert2 false;
1/0;
7 div 0;
[1, 2][3];
Gcd("a", 1);
Gcd(1);
UnknownFunction(3);
unknownIdentifier;
"a" + 1;
f := func< x | x + "s" >;
f(1);
function deep(n) if n eq 0 then return 1/0; end if; return deep(n - 1); end function;
deep(3);
if 1 then "yes"; end if;
x := ;
for i := 1 to 3 do i;
end for;
try
  try
    error "inner";
  catch e
    error "outer from " cat e`Object;
  end try;
catch e2
  e2`Object;
end try;
