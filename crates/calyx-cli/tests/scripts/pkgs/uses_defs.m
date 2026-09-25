import "defs.m": MY_LIMIT, fred;

intrinsic BelowLimit(n::RngIntElt) -> BoolElt
{Whether n is below the limit}
    return n lt MY_LIMIT;
end intrinsic;

intrinsic Fred(x::RngIntElt) -> FldRatElt
{One over x}
    return fred(x);
end intrinsic;

intrinsic Overloaded(x::RngIntElt, y::RngIntElt) -> RngIntElt
{Overload for integers}
    return 1;
end intrinsic;

intrinsic Overloaded(x::RngElt, y::RngElt) -> RngIntElt
{Overload for ring elements}
    return 2;
end intrinsic;

intrinsic Overloaded(x::., y::.) -> RngIntElt
{Overload for anything}
    return 3;
end intrinsic;

intrinsic MyBinomial(n::RngIntElt, k::RngIntElt) -> RngIntElt
{n choose k}
    requirege n, 0;
    requirerange k, 0, n;
    return Factorial(n) div Factorial(n - k) div Factorial(k);
end intrinsic;

intrinsic AppendTwice(~Q::SeqEnum, x::.)
{Append x to Q twice}
    Append(~Q, x);
    Append(~Q, x);
end intrinsic;

intrinsic Func(x::RngIntElt) -> ., .
{Report how many results were requested}
    n := Nresults();
    printf "[Nresults: %o]\n", n;
    if n eq 1 then
        return x;
    else
        return x, x^2;
    end if;
end intrinsic;

intrinsic SumAll(x::RngIntElt, rest::., ...) -> RngIntElt
{The sum of x and the other arguments}
    return x + &+[ Integers() | y : y in rest ];
end intrinsic;
