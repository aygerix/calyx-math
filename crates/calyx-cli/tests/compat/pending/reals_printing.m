// Printing of real and complex numbers: significant digits, positional
// and exponent forms, zeros, the Magma print level, printf's %.No and
// aggregates.
R := RealField();
R; Precision(R);
x := 1/3; R!x; R!2/3;
10.0^40; 10.0^29; 10.0^30; 10.0^31; 1.0e-5; 0.0001; 0.001; 1.5e-10; -1.5e-10;
R!0; -R!0;
123456789012345678901234567890123.0;
RealField(5)!123456; RealField(5)!12345; RealField(5)!1234.5; RealField(5)!0.000012345;
Sqrt(R!2); Sqrt(RealField(10)!2);
x := RealField(10)!2; y := RealField(20)!3; x*y; Parent(x*y);
1.0 + RealField(10)!1;
R5 := RealField(5);
R5!99999.5; R5!99999.4; R5!99994.9; R5!9.99996; R5!0.000099999; R5!0.00009999951;
R5!(-99999.7);

// Low precisions print at least two digits.
R0 := RealField(2 : Bits := true); R0!1; R0!3; R0!0.5; R0!123; Sprint(R0!3, "Magma");
R1 := RealField(4 : Bits := true); R1!1/3; R1!7; R1!123;
Pi(RealField(1)); Pi(RealField(2));
RealField(2 : Bits := true)!0; RealField(4 : Bits := true)!0; -RealField(2 : Bits := true)!0;

// Print levels.
x := RealField(20)!1.5;
Sprint(x); Sprintf("%o", x); Sprintf("%m", x); Sprint(x, "Magma"); Sprint(x, "Minimal"); Sprint(x, "Default");
print x : Magma;
print x : Minimal;
[x, x+1]; {x}; <x, 2>;
y := RealField(10)!2/3; y; Sprint(y, "Magma");
z := R5!123456; Sprint(z, "Magma");
w := RealField(10)!(-0.0); w;
Sprint(-RealField(10)!0, "Magma");
Sprint(Sqrt(-2.0), "Magma"); Sprint(0.0/1, "Magma");
e := 10.0^1000000000; Sprint(e, "Magma"); Sprint(e*0, "Magma");
"a" cat Sprint(1.5);

// printf with a number of decimals.
x := 123.456;
Sprintf("%.3o", x); Sprintf("%.1o", x); Sprintf("%.0o", x); Sprintf("%.10o", x); Sprintf("%.40o", x);
Sprintf("%.3o", 1.0e-10); Sprintf("%.3o", 1.0e40); Sprintf("%.3o", -0.0005); Sprintf("%.3o", 0.0005); Sprintf("%.3o", 0.0015); Sprintf("%.3o", 2.5);
Sprintf("%.2o", 0.125); Sprintf("%.2o", 0.135);
Sprintf("%.3o", 7); Sprintf("%.3o", 7/2);
Sprintf("%.3m", x);
Sprintf("%10o|", x);
Sprintf("%-40o|", x);
Sprintf("%.3o", [x, x]);
for e in [-8..-1] cat [0,1,2,5,10,20,28,29,30,31,35] do
  x := 1.23456789 * 10.0^e;
  printf "%o: %.0o | %.1o | %.2o | %.3o | %.5o | %.8o\n", e, x, x, x, x, x, x;
end for;
y := RealField(10)!1.23456789;
for e in [-6, -5, -4, -3, 5, 8, 9, 10, 11, 12] do
  x := y * 10^e;
  printf "R10 %o: %.0o | %.2o | %.5o | %.12o\n", e, x, x, x, x;
end for;
printf "%.3o|%.3o|%.3o|%.3o\n", RealField(10)!0, -RealField(10)!0, 10.0^1000000000, (10.0^1000000000)*0;
printf "%.3o\n", RealField(5)!99999.9;
printf "%.3o\n", 0.9999999;
printf "%.3o\n", 0.00099999999;
printf "%.1o\n", 9.96;
printf "%.1o\n", 0.00996;
printf "%.1o\n", 0.0996;
printf "%.3o %.3o %.3o %.3o %.3o\n", 0.000951, 0.00095, 0.000949, 0.00099, 0.0009;
printf "%.1o %.1o %.1o %.1o\n", 0.0951, 0.095, 0.0949, 0.05;
printf "%.0o %.0o %.0o %.0o %.0o\n", 0.951, 0.5, 0.49, 9.5, 99.5;
printf "%.2o %.2o %.2o\n", 0.00951, 0.00499, 0.005;
R := RealField(10);
printf "%.2o %.2o %.2o %.2o\n", R!9999999999.7, R!99999999999, R!9.9999999999e9, R!123;
printf "%.0o|%.0o|%.1o\n", R!0, -R!0, R!0;
printf "%o|%.3o|%.3o\n", R!1/3, [R!1/3], <R!1/3, 2>;
printf "%.3o\n", ComplexField(10)![1/3, 2/3];
printf "%.0o|%.0o|%.0o|%.0o|%.0o|%.0o\n", R!-0.4, R!-0.5, R!-0.6, R!-0.04, R!-1.4, R!-0.0004;
printf "%.1o|%.1o|%.1o|%.1o\n", R!-0.04, R!-0.05, R!-0.004, -R!0;
printf "%.2o|%.0o|%.0o\n", -R!0, -R!0, R!0;

// Complex numbers.
C<i> := ComplexField(10);
z := 1.5 + 2*i; z; Sprint(z, "Magma"); Sprintf("%.3o", z);
1.5 - 2*i; -2*i; 2*i; i; -i; C!0; -C!0; C!1; -C!1; 1 + 0*i; 1e-10*i; 1e40 + 1e40*i;
Sprint(i, "Magma"); Sprint(-C!1, "Magma"); Sprint(C!0, "Magma");
C2 := ComplexField(10); C2.1;
C3 := ComplexField(12); C3.1; C3!2; Sprint(C3.1, "Magma"); Sprint(C3!2 + C3.1, "Magma");
1.5 * (1 + i);

// Long numbers break across lines.
Pi(RealField(200));
x := Pi(RealField(100)); [x, x];
C<i> := ComplexField(40); z := Pi(C) + (Pi(C)/2)*i; z; [z, z, z];
<z, 1>;
[ComplexField(10) | 1, 2, 3];
[C | 1, 2+i, -i];
