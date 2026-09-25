// After a runtime error the rest of the line still runs. After a syntax
// error, the statements before it have run and the rest of the input up to
// the end of that line is dropped.
1 div 0; "after";
x := 1; y := 1 div 0; x + 1;
[1][3]; "still here";
1 div 0; 2 div 0; "third";
"a" + 1; "b";
"runs"; 1 +; "dropped";
"next1";
"c"; if true then
  "d";
  1 +;
end if; "e";
"next2";
1 +; "i";
"next3";
"f"; x := ; "g";
"next4";
"j"; "k" "l";
"next5";
"m"; for i in [1..2] do i; end fo; "n";
"next6";
