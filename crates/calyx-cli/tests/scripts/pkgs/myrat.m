// A user-defined type for rational numbers (handbook example Func_MyRat).
declare type MyRat;
declare attributes MyRat: Numer, Denom;

intrinsic MyRational(n::RngIntElt, d::RngIntElt) -> MyRat
{Create n/d}
    require d ne 0: "Denominator must be non-zero";
    r := New(MyRat);
    r`Numer := n;
    r`Denom := d;
    return r;
end intrinsic;

intrinsic Print(r::MyRat)
{Print r}
    n := r`Numer;
    d := r`Denom;
    g := GCD(n, d);
    if d lt 0 then g := -g; end if;
    printf "%o/%o", n div g, d div g;
end intrinsic;

intrinsic '+'(r::MyRat, s::MyRat) -> MyRat
{Return r + s}
    return MyRational(r`Numer*s`Denom + s`Numer*r`Denom, r`Denom*s`Denom);
end intrinsic;

intrinsic '*'(r::MyRat, s::MyRat) -> MyRat
{Return r * s}
    return MyRational(r`Numer*s`Numer, r`Denom*s`Denom);
end intrinsic;
