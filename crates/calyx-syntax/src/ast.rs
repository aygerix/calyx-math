//! The abstract syntax tree for Magma programs.

use std::rc::Rc;

use crate::span::Span;

pub type Name = String;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    IntDiv,
    Mod,
    Pow,
    Cat,
    Join,
    Meet,
    Diff,
    Sdiff,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Cmpeq,
    Cmpne,
    In,
    Notin,
    Subset,
    Notsubset,
    Adj,
    Notadj,
    And,
    Or,
    Xor,
}

impl BinOp {
    /// The name of the intrinsic implementing this operator, e.g. `'+'`.
    pub fn intrinsic_name(self) -> &'static str {
        use BinOp::*;
        match self {
            Add => "+",
            Sub => "-",
            Mul => "*",
            Div => "/",
            IntDiv => "div",
            Mod => "mod",
            Pow => "^",
            Cat => "cat",
            Join => "join",
            Meet => "meet",
            Diff => "diff",
            Sdiff => "sdiff",
            Eq => "eq",
            Ne => "ne",
            Lt => "lt",
            Le => "le",
            Gt => "gt",
            Ge => "ge",
            Cmpeq => "cmpeq",
            Cmpne => "cmpne",
            In => "in",
            Notin => "notin",
            Subset => "subset",
            Notsubset => "notsubset",
            Adj => "adj",
            Notadj => "notadj",
            And => "and",
            Or => "or",
            Xor => "xor",
        }
    }

    pub fn from_name(s: &str) -> Option<BinOp> {
        use BinOp::*;
        Some(match s {
            "+" => Add,
            "-" => Sub,
            "*" => Mul,
            "/" => Div,
            "div" => IntDiv,
            "mod" => Mod,
            "^" => Pow,
            "cat" => Cat,
            "join" => Join,
            "meet" => Meet,
            "diff" => Diff,
            "sdiff" => Sdiff,
            "eq" => Eq,
            "ne" => Ne,
            "lt" => Lt,
            "le" => Le,
            "gt" => Gt,
            "ge" => Ge,
            "cmpeq" => Cmpeq,
            "cmpne" => Cmpne,
            "in" => In,
            "notin" => Notin,
            "subset" => Subset,
            "notsubset" => Notsubset,
            "adj" => Adj,
            "notadj" => Notadj,
            "and" => And,
            "or" => Or,
            "xor" => Xor,
            _ => return None,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Plus,
    Not,
    Card,
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
    /// Where errors in this expression are reported: the operator of a
    /// binary expression, the bracket of a call or index, otherwise the
    /// start of the expression.
    pub at: u32,
}

impl Expr {
    /// The span used for reporting errors in this expression.
    pub fn err_span(&self) -> Span {
        Span { file: self.span.file, lo: self.at, hi: self.span.hi }
    }
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Int(String),
    Real(String),
    Str(String),
    Bool(bool),
    Ident(Name),
    /// `$1`, `$2`, ...: previously printed values.
    Previous(u32),
    /// `$$`: the function currently being defined.
    SelfRef,
    /// `_`, the undefined value (in `return` lists).
    Underscore,
    Paren(Box<Expr>),
    Unary(UnOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    /// `cond select a else b`
    Select(Box<Expr>, Box<Expr>, Box<Expr>),
    Call(Box<Expr>, Vec<Arg>, Vec<ParamArg>),
    Index(Box<Expr>, Vec<Expr>),
    /// `S.i`
    Dot(Box<Expr>, Box<Expr>),
    /// ``x`name``
    Attr(Box<Expr>, Name),
    /// ``x``expr``
    AttrDyn(Box<Expr>, Box<Expr>),
    /// `S ! x` (or `S !! x` when the flag is set)
    Coerce(Box<Expr>, Box<Expr>, bool),
    /// `x @ f`
    Image(Box<Expr>, Box<Expr>),
    /// `y @@ f`
    Preimage(Box<Expr>, Box<Expr>),
    /// `&op S`
    Reduce(BinOp, Box<Expr>),
    Assigned(Box<Expr>),
    Eval(Box<Expr>),
    /// `e where x is v`, or `e where x, y := v` binding several values of
    /// a call (`_` skips one).
    Where(Box<Expr>, Vec<Name>, Box<Expr>),
    /// `x ^^ n` (multiplicity in multiset constructors)
    Multiplicity(Box<Expr>, Box<Expr>),
    Tuple(Vec<Expr>),
    /// `< e : x in S | P >`
    TupleCompr(Comprehension),
    /// `[ ... ]`, `{ ... }`, `{@ ... @}`, `{* ... *}`
    Aggregate(AggKind, Option<Box<Expr>>, AggBody),
    /// `[* ... *]`
    List(Vec<Expr>),
    /// `[* e : x in S | P *]`
    ListCompr(Comprehension),
    /// `{! x in S | P !}` / `[! x in S | P !]`
    Formal(FormalKind, Option<Box<Expr>>, Name, Box<Expr>, Option<Box<Expr>>),
    /// `exists(t){ ... }`, `forall(t){ ... }`, `random{ ... }`, `rep{ ... }`
    Quantifier(QuantKind, Vec<Name>, Comprehension),
    Function(Rc<FuncDef>),
    Map(MapKind, Box<Expr>, Box<Expr>, MapBody),
    Rec(Box<Expr>, Vec<(Name, Expr)>),
    RecFormat(Vec<(Name, Option<Expr>)>),
    Car(Vec<Expr>),
    Cop(Vec<Expr>),
    Elt(Box<Expr>, Vec<Expr>),
    /// `case< e | a : b, ..., default : d >`
    Case(Box<Expr>, Vec<(Expr, Expr)>, Box<Expr>),
    /// Any other `Name< ... | ... >` constructor, e.g. `sub<G | x>`.
    Constructor(Name, Vec<Expr>, Option<Vec<Expr>>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AggKind {
    Seq,
    Set,
    ISet,
    MSet,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FormalKind {
    Set,
    Seq,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QuantKind {
    Exists,
    Forall,
    Random,
    Rep,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MapKind {
    Map,
    PMap,
    Hom,
    Iso,
}

#[derive(Clone, Debug)]
pub enum AggBody {
    Empty,
    Enum(Vec<Expr>),
    Range(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
    Compr(Comprehension),
}

/// `e : x in S, i -> y in T | P`
#[derive(Clone, Debug)]
pub struct Comprehension {
    pub head: Box<Expr>,
    pub iters: Vec<Iter>,
    pub pred: Option<Box<Expr>>,
}

#[derive(Clone, Debug)]
pub struct Iter {
    /// For dual iteration `i -> x in S`, the index variable.
    pub index: Option<Name>,
    pub var: Name,
    pub domain: Expr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum MapBody {
    /// `x :-> e` with an optional inverse `y :-> e'`.
    Rule(Name, Box<Expr>, Option<(Name, Box<Expr>)>),
    /// A graph, generator images, or a function, depending on the kind.
    Exprs(Vec<Expr>),
}

#[derive(Clone, Debug)]
pub enum Arg {
    Value(Expr),
    /// `~x`, `~x[i]`, `~r`f`
    Ref(LValue, Span),
}

#[derive(Clone, Debug)]
pub struct ParamArg {
    pub name: Name,
    pub value: Expr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Param {
    pub name: Name,
    pub is_ref: bool,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum FuncBody {
    Block(Vec<Stmt>),
    Expr(Box<Expr>),
}

/// A user function or procedure.
#[derive(Clone, Debug)]
pub struct FuncDef {
    /// Set for the statement form `function f(...)`, allowing recursion by name.
    pub name: Option<Name>,
    pub params: Vec<Param>,
    pub variadic: bool,
    pub opt_params: Vec<(Name, Expr)>,
    pub body: FuncBody,
    pub is_procedure: bool,
    pub span: Span,
}

/// A type pattern in an intrinsic signature.
#[derive(Clone, Debug, PartialEq)]
pub enum TypeExpr {
    Any,
    Named(Name),
    /// `T[A, B]`
    Extended(Name, Vec<TypeExpr>),
    /// `[T]` / `[]`
    Seq(Option<Box<TypeExpr>>),
    /// `{T}` / `{}`
    Set(Option<Box<TypeExpr>>),
    /// `{[T]}` / `{[]}`
    SetOrSeq(Option<Box<TypeExpr>>),
    /// `{@T@}`
    ISet(Option<Box<TypeExpr>>),
    /// `{*T*}`
    MSet(Option<Box<TypeExpr>>),
    /// `<>`
    Tuple,
}

#[derive(Clone, Debug)]
pub struct IntrinsicArg {
    pub name: Name,
    pub is_ref: bool,
    pub ty: Option<TypeExpr>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct IntrinsicDef {
    pub name: Name,
    pub args: Vec<IntrinsicArg>,
    pub variadic: bool,
    pub opt_params: Vec<(Name, Expr)>,
    /// `None` for procedures.
    pub returns: Option<Vec<TypeExpr>>,
    pub doc: String,
    pub body: Vec<Stmt>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum LValue {
    Ident(Name, Span),
    Underscore(Span),
    Index(Box<LValue>, Vec<Expr>, Span),
    Attr(Box<LValue>, Name, Span),
    AttrDyn(Box<LValue>, Box<Expr>, Span),
}

impl LValue {
    pub fn span(&self) -> Span {
        match self {
            LValue::Ident(_, s) | LValue::Underscore(s) | LValue::Index(_, _, s) | LValue::Attr(_, _, s) | LValue::AttrDyn(_, _, s) => *s,
        }
    }

    /// The identifier at the root of this l-value, if any.
    pub fn root(&self) -> Option<&Name> {
        match self {
            LValue::Ident(n, _) => Some(n),
            LValue::Underscore(_) => None,
            LValue::Index(b, _, _) | LValue::Attr(b, _, _) | LValue::AttrDyn(b, _, _) => b.root(),
        }
    }
}

#[derive(Clone, Debug)]
pub enum GenNames {
    /// `E<x, y, z>`, with the span of `<`
    List(Vec<(Name, Span)>, Span),
    /// `E<[x]>`, with the span of `<`
    Seq(Name, Span, Span),
}

#[derive(Clone, Debug)]
pub enum ForKind {
    /// `for i := a to b by c`
    Range(Expr, Expr, Option<Expr>),
    /// `for x in S` (or `for i -> x in S`)
    In(Expr),
    /// `for random x in S`
    Random(Expr),
}

#[derive(Clone, Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum StmtKind {
    Empty,
    /// A lone expression list, printed (or a procedure call).
    Expr(Vec<Expr>, Option<Name>),
    Print(Vec<Expr>, Option<Name>),
    Printf(Vec<Expr>),
    Fprintf(Expr, Vec<Expr>),
    Vprint(Name, Option<Expr>, Vec<Expr>),
    Vprintf(Name, Option<Expr>, Vec<Expr>),
    /// The targets, the value, and the span of `:=`.
    Assign(Vec<LValue>, Expr, Span),
    /// `lv o:= e`, with the position of the operator.
    OpAssign(LValue, BinOp, Expr, Span),
    /// Targets of which some have generator names (`E<x, y> := e`,
    /// `a, R<t> := e`), the value, and the span of `:=`.
    GenAssign(Vec<(LValue, Option<GenNames>)>, Expr, Span),
    If(Vec<(Expr, Vec<Stmt>)>, Option<Vec<Stmt>>),
    Case(Expr, Vec<(Vec<Expr>, Vec<Stmt>)>, Option<Vec<Stmt>>),
    For { index: Option<(Name, Span)>, var: (Name, Span), kind: ForKind, body: Vec<Stmt> },
    While(Expr, Vec<Stmt>),
    Repeat(Vec<Stmt>, Expr),
    Break(Option<Name>),
    Continue(Option<Name>),
    Return(Vec<Expr>),
    FuncDef(Name, Rc<FuncDef>),
    Intrinsic(Rc<IntrinsicDef>),
    Forward(Vec<(Name, Span)>),
    Local(Vec<(Name, Span)>),
    Delete(LValue),
    Error(Option<Expr>, Vec<Expr>),
    Assert(u8, Expr),
    Require(Expr, Vec<Expr>),
    RequireRange(Name, Expr, Expr),
    RequireGe(Name, Expr),
    Try(Vec<Stmt>, Option<(Name, Span)>, Vec<Stmt>),
    Time(Box<Stmt>),
    Vtime(Name, Option<Expr>, Box<Stmt>),
    Load(Expr, bool),
    Import(Expr, Vec<(Name, Span)>),
    Freeze,
    DeclareType(Name, Option<Name>, Vec<Name>),
    DeclareAttributes(Name, Vec<Name>),
    DeclareVerbose(Name, Expr),
    Read(LValue, Option<Expr>, bool),
    Quit(Option<Expr>),
    Clear,
    Save(Expr),
    Restore(Expr),
}
