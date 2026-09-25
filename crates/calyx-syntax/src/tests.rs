use crate::ast::*;
use crate::{FileId, parse_expression, parse_program};

fn expr(src: &str) -> Expr {
    parse_expression(src, FileId(0)).unwrap_or_else(|e| panic!("{src}: {}", e.message))
}

/// Render an expression with explicit parentheses to check precedence.
fn sexp(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Int(s) | ExprKind::Real(s) => s.clone(),
        ExprKind::Ident(s) => s.clone(),
        ExprKind::Str(s) => format!("{s:?}"),
        ExprKind::Paren(e) => sexp(e),
        ExprKind::Unary(op, e) => format!("({op:?} {})", sexp(e)),
        ExprKind::Binary(op, a, b) => format!("({} {} {})", op.intrinsic_name(), sexp(a), sexp(b)),
        ExprKind::Select(c, a, b) => format!("(select {} {} {})", sexp(c), sexp(a), sexp(b)),
        ExprKind::Where(e, n, v) => format!("(where {} {n} {})", sexp(e), sexp(v)),
        ExprKind::Coerce(a, b, _) => format!("(! {} {})", sexp(a), sexp(b)),
        ExprKind::Image(a, b) => format!("(@ {} {})", sexp(a), sexp(b)),
        ExprKind::Call(f, args, _) => {
            let a: Vec<String> = args
                .iter()
                .map(|a| match a {
                    Arg::Value(e) => sexp(e),
                    Arg::Ref(lv, _) => format!("~{}", lv.root().cloned().unwrap_or_default()),
                })
                .collect();
            format!("{}({})", sexp(f), a.join(" "))
        }
        ExprKind::Index(f, i) => format!("{}[{}]", sexp(f), i.iter().map(sexp).collect::<Vec<_>>().join(" ")),
        ExprKind::Reduce(op, e) => format!("(&{} {})", op.intrinsic_name(), sexp(e)),
        ExprKind::Tuple(v) => format!("<{}>", v.iter().map(sexp).collect::<Vec<_>>().join(" ")),
        ExprKind::Aggregate(k, _, _) => format!("{k:?}"),
        other => format!("{other:?}"),
    }
}

#[test]
fn precedence() {
    let cases = [
        ("-2^2", "(Neg (^ 2 2))"),
        ("2^3^2", "(^ 2 (^ 3 2))"),
        ("2^-1*3", "(* (^ 2 (Neg 1)) 3)"),
        ("a + b * c", "(+ a (* b c))"),
        ("a - b - c", "(- (- a b) c)"),
        ("not a eq b and c", "(and (Not (eq a b)) c)"),
        ("x in S join T", "(in x (join S T))"),
        ("#S + 1", "(+ (Card S) 1)"),
        ("&+ S[1]", "(&+ S[1])"),
        ("R ! x ^ 2", "(^ (! R x) 2)"),
        ("c select 1 else d select 2 else 3", "(select c 1 (select d 2 3))"),
        ("x + y where x is 5 where y is 6", "(where (where (+ x y) x 5) y 6)"),
        ("x @ f @ g", "(@ (@ x f) g)"),
        ("a cat b * c", "(* (cat a b) c)"),
        ("f(x)(y)[1]", "f(x)(y)[1]"),
    ];
    for (src, want) in cases {
        assert_eq!(sexp(&expr(src)), want, "{src}");
    }
}

#[test]
fn aggregates_and_constructors() {
    let e = expr("[ Integers() | x^2 : x in [1..10], i -> y in S | IsOdd(x) ]");
    let ExprKind::Aggregate(AggKind::Seq, Some(_), AggBody::Compr(c)) = e.kind else { panic!() };
    assert_eq!(c.iters.len(), 2);
    assert_eq!(c.iters[1].index.as_deref(), Some("i"));
    assert!(c.pred.is_some());

    let e = expr("{* 1^^2, 3 *}");
    assert!(matches!(e.kind, ExprKind::Aggregate(AggKind::MSet, None, AggBody::Enum(_))));

    let e = expr("map< Integers() -> Integers() | x :-> x^2, y :-> Isqrt(y) >");
    assert!(matches!(e.kind, ExprKind::Map(MapKind::Map, _, _, MapBody::Rule(_, _, Some(_)))));

    let e = expr("func< x, y : P := 1 | x + y + P >");
    let ExprKind::Function(f) = e.kind else { panic!() };
    assert_eq!(f.params.len(), 2);
    assert_eq!(f.opt_params.len(), 1);

    let e = expr("exists(t){ x : x in S | x gt 3 }");
    assert!(matches!(e.kind, ExprKind::Quantifier(QuantKind::Exists, ref w, _) if w == &["t".to_string()]));

    let e = expr("case< x | 1 : \"one\", 2 : \"two\", default : \"many\" >");
    assert!(matches!(e.kind, ExprKind::Case(_, ref arms, _) if arms.len() == 2));

    let e = expr("<1, <2, 3>>");
    assert_eq!(sexp(&e), "<1 <2 3>>");
}

#[test]
fn statements() {
    let src = r#"
        x := 13; y := x^2 - 2;
        x, y;
        a, _, c := Xgcd(12, 15);
        s[2, 2] := -1;
        S join:= { x };
        x div:= 2;
        P<t> := PolynomialRing(Integers());
        Append(~Q, 1);
        for x, y in {1..3} do x, y; end for;
        for i := 1 to 10 by 2 do if i eq 3 then break; elif i eq 5 then continue; else i; end if; end for;
        function f(n) return n le 1 select 1 else n * f(n-1); end function;
        procedure p(~x, y : Q := 2) x := y; end procedure;
        case x: when 1, 2: "small"; else: "big"; end case;
        try error "bad", 1; catch e print e`Object; end try;
        repeat x +:= 1; until x gt 10;
        print x : Magma;
        printf "%o\n", x;
        vprint User1, 2: "hi";
        time x := 5;
        r`a := 3;
        delete x;
        declare verbose Foo, 3;
        forward g;
        1 : Magma;
    "#;
    let prog = parse_program(src, FileId(0)).unwrap_or_else(|e| panic!("{}", e.message));
    assert_eq!(prog.len(), 25);
    assert!(matches!(prog[3].kind, StmtKind::Assign(ref l, _, _) if l.len() == 3));
    assert!(matches!(prog[6].kind, StmtKind::OpAssign(_, BinOp::IntDiv, _)));
    assert!(matches!(prog[7].kind, StmtKind::GenAssign(..)));
    let StmtKind::For { body, .. } = &prog[9].kind else { panic!() };
    assert!(matches!(body[0].kind, StmtKind::For { .. }));
}

#[test]
fn intrinsic_definitions() {
    let src = r#"
intrinsic myGCD(x::RngIntElt, y::[RngIntElt], ~Q::SeqEnum, z::. : Al := "x") -> RngIntElt, .
{ Return the GCD of x's and y's; a \} brace }
    require x ge 0: "Argument 1 must be non-negative";
    return Gcd(x, y);
end intrinsic;
intrinsic '+'(a::MyRat, b::MyRat) -> MyRat
{Sum}
    return a;
end intrinsic;
"#;
    let prog = parse_program(src, FileId(0)).unwrap_or_else(|e| panic!("{}", e.message));
    let StmtKind::Intrinsic(d) = &prog[0].kind else { panic!() };
    assert_eq!(d.args.len(), 4);
    assert_eq!(d.args[1].ty, Some(TypeExpr::Seq(Some(Box::new(TypeExpr::Named("RngIntElt".into()))))));
    assert_eq!(d.doc, "Return the GCD of x's and y's; a } brace");
    assert_eq!(d.returns.as_ref().unwrap().len(), 2);
    let StmtKind::Intrinsic(d) = &prog[1].kind else { panic!() };
    assert_eq!(d.name, "+");
}

#[test]
fn incomplete_input_is_flagged() {
    for src in ["if x then", "x := [1, 2", "f := function(x)", "\"abc", "/* comment"] {
        let err = parse_program(src, FileId(0)).unwrap_err();
        assert!(err.incomplete, "{src}: {}", err.message);
    }
    let err = parse_program("x := ;", FileId(0)).unwrap_err();
    assert!(!err.incomplete);
}

#[test]
fn keyword_list_matches_lexer() {
    for w in crate::token::KEYWORDS {
        assert!(crate::token::Kw::from_word(w).is_some(), "{w} is not a keyword");
    }
    assert!(crate::token::Kw::from_word("func").is_none());
}
