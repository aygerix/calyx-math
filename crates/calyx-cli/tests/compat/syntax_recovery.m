x := 1 +; y := 2; "same line";
y;
z := 3 + ; "a"; "b";
"next";
for i in [1..2] do
  i;
  q := 1/0; "c";
  "d";
end for;
"after";
try
  1 + ;
catch e
  "caught";
end try;
