// Direct products of rings as a user type with an element type
// (handbook example Func_UserTypes2, with our own code).
declare type DirProd[DirProdElt];
declare attributes DirProd: Rings;
declare attributes DirProdElt: Elements, Parent;

intrinsic DirectProduct(Rings::Tup) -> DirProd
{The direct product of the rings in the tuple}
    require forall{R : R in Rings | ISA(Type(R), Rng)}: "Tuple entries are not all rings";
    D := New(DirProd);
    D`Rings := Rings;
    return D;
end intrinsic;

intrinsic Print(D::DirProd)
{Print D}
    printf "Direct product of %o", D`Rings;
end intrinsic;

function CreateElement(D, Elements)
    x := New(DirProdElt);
    x`Elements := Elements;
    x`Parent := D;
    return x;
end function;

intrinsic IsCoercible(D::DirProd, x::.) -> BoolElt, .
{Whether x is coercible into D, and the result}
    Rings := D`Rings;
    n := #Rings;
    if Type(x) eq DirProdElt then
        if x`Parent cmpeq D then
            return true, x;
        end if;
        x := x`Elements;
    end if;
    if Type(x) ne Tup then
        return false, "Coercion RHS must be a tuple";
    end if;
    if #x ne n then
        return false, "Wrong length of tuple for coercion";
    end if;
    Elements := <>;
    for i := 1 to n do
        l, t := IsCoercible(Rings[i], x[i]);
        if not l then
            return false, Sprintf("Tuple entry %o not coercible", i);
        end if;
        Append(~Elements, t);
    end for;
    return true, CreateElement(D, Elements);
end intrinsic;

intrinsic Print(x::DirProdElt)
{Print x}
    printf "%o", x`Elements;
end intrinsic;

intrinsic Parent(x::DirProdElt) -> DirProd
{Parent of x}
    return x`Parent;
end intrinsic;

intrinsic '+'(x::DirProdElt, y::DirProdElt) -> DirProdElt
{Return x + y}
    D := Parent(x);
    require D cmpeq Parent(y): "Incompatible arguments";
    Ex := x`Elements;
    Ey := y`Elements;
    return CreateElement(D, <Ex[i] + Ey[i] : i in [1 .. #Ex]>);
end intrinsic;
