error "top level message";
"next";
function f(x)
  error "inside f", x;
end function;
f(3);
"next2";
function g(x)
  return h(x);
end function;
function h(x)
  return x + "a";
end function;
g(1);
"next3";
procedure pr(x)
  require x gt 0: "x must be positive";
  print x;
end procedure;
pr(-1);
"next4";
function k(x)
  assert x gt 0;
  return x;
end function;
k(-1);
error Error("object");
e := Error("obj2"); error e;
Gcd(1, "a");
1/0;
a := 0; 1/a;
