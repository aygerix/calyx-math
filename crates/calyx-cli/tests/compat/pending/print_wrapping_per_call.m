// Each print or printf wraps its own output at the line width as if it
// started a line: the column is not carried over from earlier output on
// the same line.
printf "aaaaaaaaaa bbbbbbbbbb cccccccccc dddddddddd eeeeeeeeee ffffffffff gggggggggg hhhhhhhhhh\n";
printf "%o\n", "aaaaaaaaaa bbbbbbbbbb cccccccccc dddddddddd eeeeeeeeee ffffffffff gggggggggg hhhhhhhhhh";
printf "%o\n", [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31];
printf "%o %o\n", [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20], [21,22,23,24,25,26,27,28,29,30,31];
printf "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx %o\n", [1,2,3,4,5,6];
printf "%o", 2^300; printf "\n";
for i in [1..30] do printf "%o ", 10^i; end for; printf "\n";
for i in [1..40] do printf " %o", i; end for; printf "\n";
print "aaaaaaaaaa", "bbbbbbbbbb cccccccccc dddddddddd eeeeeeeeee ffffffffff gggggggggg hhhhhhhhhh iiii";
printf "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"; printf "%o\n", [1,2,3,4,5,6,7,8,9,10];
printf "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"; printf "%o\n", [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26];
printf "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"; print [1,2,3,4,5,6,7,8,9,10];
printf "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"; print "aaaaaaaaaa bbbbbbbbbb cccccccccc";
printf "abc\ndef %o\n", [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26];
printf "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n";
