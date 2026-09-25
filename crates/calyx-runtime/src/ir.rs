//! The resolved intermediate representation executed by the interpreter.
//!
//! The compiler turns the syntax tree into this form, resolving every
//! identifier to a frame slot, a captured value, or a global name according
//! to Magma's scoping rules.

use std::rc::Rc;

use calyx_syntax::Span;
use calyx_syntax::ast::{AggKind, BinOp, MapKind, QuantKind};

use crate::sym::Sym;
use crate::value::Value;

pub type Slot = u32;

/// An expression with its source position.
pub struct E {
    pub kind: Ex,
    pub span: Span,
}

pub enum Ex {
    Const(Value),
    Local(Slot, Sym),
    Capture(u32, Sym),
    /// A top-level (or forward-declared) identifier, looked up at run time.
    Global(Sym),
    /// `$$` or the name of the function being defined.
    SelfFn,
    /// `$n`
    Previous(u32),
    /// `_` in a return list.
    Undef,
    Neg(Box<E>),
    Not(Box<E>),
    Card(Box<E>),
    Bin(BinOp, Box<E>, Box<E>),
    And(Box<E>, Box<E>),
    Or(Box<E>, Box<E>),
    Select(Box<E>, Box<E>, Box<E>),
    Call(Box<CallEx>),
    Index(Box<E>, Vec<E>),
    Dot(Box<E>, Box<E>),
    Attr(Box<E>, Sym),
    AttrDyn(Box<E>, Box<E>),
    Coerce(Box<E>, Box<E>, bool),
    Image(Box<E>, Box<E>),
    Preimage(Box<E>, Box<E>),
    Reduce(BinOp, Box<E>),
    Assigned(Box<AssignedEx>),
    Eval(Box<E>),
    /// Bind a slot (for `where`) and evaluate the body.
    Let(Slot, Box<E>, Box<E>),
    Multiplicity(Box<E>, Box<E>),
    Tuple(Vec<E>),
    TupleCompr(Box<ComprEx>),
    Agg(Box<AggEx>),
    List(Vec<E>),
    /// `{! x in S | P !}`: the domain and the predicate closure.
    Formal(bool, Box<E>, Option<Box<E>>),
    Quant(Box<QuantEx>),
    Closure(Rc<FuncCode>, Rc<[CapSrc]>),
    Map(Box<MapEx>),
    Rec(Box<E>, Vec<(Sym, E)>),
    RecFormat(Vec<(Sym, Option<E>)>),
    Car(Vec<E>),
    Cop(Vec<E>),
    Elt(Box<E>, Vec<E>),
    Case(Box<E>, Vec<(E, E)>, Box<E>),
    Constructor(Sym, Vec<E>, Option<Vec<E>>),
    /// `Self(i)` inside a sequence constructor.
    SelfSeq(Box<E>),
}

pub struct CallEx {
    pub func: E,
    pub args: Vec<CArg>,
    pub params: Vec<(Sym, E)>,
}

pub enum CArg {
    Val(E),
    Ref(LV, Span),
}

/// A variable that can be assigned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Place {
    Local(Slot, Sym),
    Global(Sym),
}

impl Place {
    pub fn name(&self) -> Sym {
        match self {
            Place::Local(_, s) | Place::Global(s) => *s,
        }
    }
}

pub enum AssignedEx {
    Var(E),
    Attr(E, Sym),
    AttrDyn(E, E),
    Index(E, Vec<E>),
}

/// An assignment target.
pub enum LV {
    Var(Place, Span),
    Discard,
    Index(Box<LV>, Vec<E>, Span),
    Attr(Box<LV>, Sym, Span),
    AttrDyn(Box<LV>, E, Span),
}

pub struct AggEx {
    pub kind: AggKind,
    pub universe: Option<E>,
    pub body: AggBodyEx,
}

pub enum AggBodyEx {
    Empty,
    Enum(Vec<E>),
    Range(E, E, Option<E>),
    Compr(ComprEx),
}

pub struct ComprEx {
    pub head: E,
    pub iters: Vec<IterEx>,
    /// `where` bindings from the predicate, visible in the head.
    pub lets: Vec<(Slot, E)>,
    pub pred: Option<E>,
}

pub struct IterEx {
    pub var: Slot,
    pub index: Option<Slot>,
    pub domain: DomainEx,
    pub span: Span,
}

/// What a loop or constructor iterates over. Literal ranges are iterated
/// without building the sequence.
pub enum DomainEx {
    Range(E, E, Option<E>),
    General(E),
}

pub struct QuantEx {
    pub kind: QuantKind,
    pub witnesses: Vec<LV>,
    pub compr: ComprEx,
}

pub struct MapEx {
    pub kind: MapKind,
    pub domain: E,
    pub codomain: E,
    pub body: MapBodyEx,
}

pub enum MapBodyEx {
    Rule(E, Option<E>),
    Exprs(Vec<E>),
}

/// How a closure obtains each captured value when it is created.
#[derive(Clone, Debug)]
pub enum CapSrc {
    Local(Slot),
    Capture(u32),
    SelfFn,
    /// A global identifier; an error if unassigned (unless it names an
    /// intrinsic or a type). The span is where it is used.
    Global(Sym, Span),
    /// Like `Global`, but an unassigned identifier becomes a late-bound
    /// intrinsic reference (package code).
    GlobalLate(Sym),
    /// The initial value of a local that shadows an outer identifier;
    /// undefined if that identifier is unassigned.
    GlobalInit(Sym),
}

#[derive(Clone)]
pub struct ParamSpec {
    pub slot: Slot,
    pub name: Sym,
    pub is_ref: bool,
}

pub enum Body {
    Block(Vec<S>),
    Expr(E),
}

/// A compiled function, procedure, intrinsic or top-level unit.
pub struct FuncCode {
    pub name: Option<Sym>,
    pub params: Vec<ParamSpec>,
    pub variadic: bool,
    pub opt_params: Vec<(Sym, Slot, E)>,
    pub body: Body,
    pub is_procedure: bool,
    pub n_slots: u32,
    /// Locals that start out with the value of the same identifier in the
    /// enclosing context (the capture index), if it had one.
    pub local_inits: Vec<(Slot, u32)>,
    pub capture_names: Vec<Sym>,
    /// The identifier bound to each slot (for `eval`).
    pub slot_names: Vec<Sym>,
    pub span: Span,
    /// Source text of the definition, for printing.
    pub source: Option<Rc<str>>,
}

/// A statement with its source position.
pub struct S {
    pub kind: St,
    pub span: Span,
}

pub enum PrintLevel {
    Minimal,
    Default,
    Maximal,
    Magma,
}

pub enum St {
    Nop,
    /// Print a list of expressions (auto-print or `print`).
    Print(Vec<E>, Option<Sym>),
    /// A lone call: a procedure call, or a function call whose results are printed.
    CallStmt(Box<CallEx>, Option<Sym>),
    Printf(Vec<E>),
    Fprintf(E, Vec<E>),
    Vprint(Sym, Option<E>, Vec<E>, bool),
    /// The targets, the value, and the span of `:=`.
    Assign(Vec<LV>, E, Span),
    OpAssign(LV, BinOp, E),
    GenAssign(LV, GenNamesEx, E),
    If(Vec<(E, Vec<S>)>, Option<Vec<S>>),
    Case(E, Vec<(Vec<E>, Vec<S>)>, Option<Vec<S>>),
    ForRange { var: Place, from: E, to: E, by: Option<E>, body: Vec<S> },
    ForIn { var: Place, index: Option<Place>, domain: DomainEx, random: bool, body: Vec<S> },
    While(E, Vec<S>),
    Repeat(Vec<S>, E),
    Break(Option<Sym>),
    Continue(Option<Sym>),
    Return(Vec<E>),
    Error(Option<E>, Vec<E>),
    Assert(u8, E),
    Require(E, Vec<E>),
    RequireRange(E, E, E, Sym),
    RequireGe(E, E, Sym),
    Try(Vec<S>, Option<Place>, Vec<S>),
    Time(Box<S>),
    Vtime(Sym, Option<E>, Box<S>),
    Load(E, bool),
    Import(E, Vec<(Sym, Place)>),
    Forward(Vec<Sym>),
    Delete(LV),
    DeclareType(Sym, Option<Sym>, Vec<Sym>),
    DeclareAttributes(Sym, Vec<Sym>),
    DeclareVerbose(Sym, E),
    Intrinsic(Rc<IntrinsicDefIR>),
    Read(LV, Option<E>, bool),
    Quit(Option<E>),
    Clear,
    Save(E),
    Restore(E),
    Freeze,
}

pub enum GenNamesEx {
    List(Vec<(Place, Span)>),
    Seq(Place, Span),
}

/// A user intrinsic, ready to be registered.
pub struct IntrinsicDefIR {
    pub name: Sym,
    pub arg_types: Vec<(Option<calyx_syntax::ast::TypeExpr>, bool)>,
    pub returns: Option<Vec<calyx_syntax::ast::TypeExpr>>,
    pub doc: Rc<str>,
    pub code: Rc<FuncCode>,
    pub captures: Rc<[CapSrc]>,
    pub span: Span,
}

pub use calyx_syntax::ast::AggKind as AggregateKind;
