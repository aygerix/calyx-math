function h(x, y)
  return x + y;
end function;
function g(a)
  return h(a, "s") * 2;
end function;
g(1);
"--";
procedure pp(~v, w)
  v := v + w;
end procedure;
z := 1;
pp(~z, "q");
"--";
f := func< n | [1,2][n] >;
f(5);
"--";
[ g(i) : i in [1..2] ];
"--";
k := function(x) if x eq 0 then return 1/x; end if; return k(x-1); end function;
k(2);
