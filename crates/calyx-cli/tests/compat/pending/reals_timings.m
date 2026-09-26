// Timings (Cputime and Realtime) lie in a real field of their own, of 52
// bits, that prints as of precision 15 with 3 decimals, and so do the
// results computed from them, unless a real of lower precision takes part.
// t - t is a timing whose value is known.
t := Cputime(); z := t - t; F := Parent(z);
F;
Parent(Realtime()), Parent(Cputime(t)), Parent(Realtime(Realtime()));
F eq RealField(15), F eq RealField(), Precision(F);
z; z + 1/3; z + 1.5; 1.5 + z; z + 2;
u := z + 1/3;
u, Sqrt(u), Max(u, u), Min(u, 2*u);
[u, 1.5]; Universe([u, 1.5]); [1.5, u]; [u, 1]; [u, 1/3];
[u, RealField(10)!1]; Universe([u, RealField(10)!1]); [u, RealField(16)!1];
u * 1.5, 1.5 * u, u/3, u^2, -u, Abs(-u);
Exp(u), Log(u + 1), Sin(u);
Floor(u), Round(u), Ceiling(u), Round(1000*u);
RealField(15)!u; RealField(30)!u;
u + RealField(30)!1.5, RealField(30)!1.5 + u, u + RealField(5)!1.5;
u + RealField(15)!1.5, u + RealField(16)!1.5, u + RealField(14)!1.5;
Parent(u + RealField(15)!1.5);
Parent(u + RealField(16)!1.5);
F!1.5, F!2, F!(1/3);
s := [u, u]; &+s, &*s;
u eq 1/3, u lt 1;
x := u; x +:= 1; x;
printf "%o %.5o\n", u, u;
Sprint(u);
MantissaExponent(u);
MantissaExponent(Sqrt(u));
MantissaExponent(u + RealField(30)!1/7);
C := ComplexField(10); C!u, u + C!1;
<u, 1.5>;
{@ u, 1.5 @};
ChangePrecision(u, 20); Parent(ChangePrecision(u, 20));
Precision(u);
