//! A recursive-descent / Pratt parser for the Magma language.

use std::rc::Rc;

use crate::ast::*;
use crate::lexer::Lexer;
use crate::span::{FileId, Span};
use crate::token::{Kw, Tok, Token};

#[derive(Clone, Debug)]
pub struct ParseError {
    pub message: String,
    pub span: Span,
    /// The input ended before the construct was complete (useful for REPLs).
    pub incomplete: bool,
}

pub type PResult<T> = Result<T, ParseError>;

// Binding powers, from loosest to tightest (see the operator table in the
// handbook's "Magma Semantics" chapter).
const BP_WHERE: u8 = 2;
const BP_SELECT: u8 = 6;
const BP_CARETCARET: u8 = 8;
const BP_OR: u8 = 10;
const BP_AND: u8 = 12;
const BP_NOT: u8 = 14;
const BP_CMP: u8 = 16;
const BP_IN: u8 = 18;
const BP_JOIN: u8 = 20;
const BP_DIFF: u8 = 22;
const BP_SDIFF: u8 = 24;
const BP_MEET: u8 = 26;
const BP_ADD: u8 = 28;
const BP_MUL: u8 = 30;
const BP_CAT: u8 = 32;
const BP_NEG: u8 = 34;
const BP_POW: u8 = 36;
const BP_BANG: u8 = 38;
const BP_AT: u8 = 40;
const BP_DOT: u8 = 42;
const BP_HASH: u8 = 44;
const BP_ASSIGNED: u8 = 46;
const BP_POSTFIX: u8 = 50;

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    toks: Vec<Token>,
    pos: usize,
    file: FileId,
}

fn binop_of(tok: &Tok) -> Option<(BinOp, u8, u8)> {
    use BinOp::*;
    let r = match tok {
        Tok::Plus => (Add, BP_ADD, BP_ADD + 1),
        Tok::Minus => (Sub, BP_ADD, BP_ADD + 1),
        Tok::Star => (Mul, BP_MUL, BP_MUL + 1),
        Tok::Slash => (Div, BP_MUL, BP_MUL + 1),
        Tok::Caret => (Pow, BP_POW, BP_POW),
        Tok::Kw(k) => match k {
            Kw::Div => (IntDiv, BP_MUL, BP_MUL + 1),
            Kw::Mod => (Mod, BP_MUL, BP_MUL + 1),
            Kw::Cat => (Cat, BP_CAT, BP_CAT + 1),
            Kw::Join => (Join, BP_JOIN, BP_JOIN + 1),
            Kw::Meet => (Meet, BP_MEET, BP_MEET + 1),
            Kw::Diff => (Diff, BP_DIFF, BP_DIFF + 1),
            Kw::Sdiff => (Sdiff, BP_SDIFF, BP_SDIFF + 1),
            Kw::Eq => (Eq, BP_CMP, BP_CMP + 1),
            Kw::Ne => (Ne, BP_CMP, BP_CMP + 1),
            Kw::Lt => (Lt, BP_CMP, BP_CMP + 1),
            Kw::Le => (Le, BP_CMP, BP_CMP + 1),
            Kw::Gt => (Gt, BP_CMP, BP_CMP + 1),
            Kw::Ge => (Ge, BP_CMP, BP_CMP + 1),
            Kw::Cmpeq => (Cmpeq, BP_CMP, BP_CMP + 1),
            Kw::Cmpne => (Cmpne, BP_CMP, BP_CMP + 1),
            Kw::In => (In, BP_IN, BP_IN + 1),
            Kw::Notin => (Notin, BP_IN, BP_IN + 1),
            Kw::Subset => (Subset, BP_IN, BP_IN + 1),
            Kw::Notsubset => (Notsubset, BP_IN, BP_IN + 1),
            Kw::Adj => (Adj, BP_IN, BP_IN + 1),
            Kw::Notadj => (Notadj, BP_IN, BP_IN + 1),
            Kw::And => (And, BP_AND, BP_AND + 1),
            Kw::Or => (Or, BP_OR, BP_OR + 1),
            Kw::Xor => (Xor, BP_OR, BP_OR + 1),
            _ => return None,
        },
        _ => return None,
    };
    Some(r)
}

/// Operators that may follow `&` in a reduction.
fn reduction_op(tok: &Tok) -> Option<BinOp> {
    match tok {
        Tok::Plus => Some(BinOp::Add),
        Tok::Minus => Some(BinOp::Sub),
        Tok::Star => Some(BinOp::Mul),
        Tok::Slash => Some(BinOp::Div),
        Tok::Caret => Some(BinOp::Pow),
        _ => binop_of(tok).map(|b| b.0),
    }
}

impl<'a> Parser<'a> {
    pub fn new(src: &'a str, file: FileId) -> Parser<'a> {
        Parser { lexer: Lexer::new(src, file), toks: Vec::new(), pos: 0, file }
    }

    // ----- token plumbing -------------------------------------------------

    fn fill(&mut self, k: usize) {
        while self.toks.len() <= self.pos + k {
            if self.toks.last().is_some_and(|t| t.tok == Tok::Eof) {
                let t = self.toks.last().unwrap().clone();
                self.toks.push(t);
            } else {
                let t = self.lexer.next_token();
                self.toks.push(t);
            }
        }
    }

    fn peek(&mut self) -> &Tok {
        self.fill(0);
        &self.toks[self.pos].tok
    }

    fn peek_at(&mut self, k: usize) -> &Tok {
        self.fill(k);
        &self.toks[self.pos + k].tok
    }

    fn span(&mut self) -> Span {
        self.fill(0);
        self.toks[self.pos].span
    }

    fn prev_span(&self) -> Span {
        if self.pos == 0 { Span::new(self.file, 0, 0) } else { self.toks[self.pos - 1].span }
    }

    fn bump(&mut self) -> Token {
        self.fill(0);
        let t = self.toks[self.pos].clone();
        self.pos += 1;
        t
    }

    fn at(&mut self, t: &Tok) -> bool {
        self.peek() == t
    }

    fn at_kw(&mut self, k: Kw) -> bool {
        matches!(self.peek(), Tok::Kw(x) if *x == k)
    }

    fn eat(&mut self, t: &Tok) -> bool {
        if self.at(t) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, k: Kw) -> bool {
        if self.at_kw(k) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn error_here<T>(&mut self, msg: impl Into<String>) -> PResult<T> {
        self.fill(0);
        let t = &self.toks[self.pos];
        let incomplete = matches!(t.tok, Tok::Eof | Tok::Unterminated(_));
        let message = match &t.tok {
            Tok::Error(m) | Tok::Unterminated(m) => m.clone(),
            _ => msg.into(),
        };
        Err(ParseError { message, span: t.span, incomplete })
    }

    fn unexpected<T>(&mut self, expected: &str) -> PResult<T> {
        let found = self.peek().describe();
        self.error_here(format!("bad syntax: expected {expected}, found {found}"))
    }

    fn expect(&mut self, t: &Tok) -> PResult<Span> {
        if self.at(t) {
            Ok(self.bump().span)
        } else {
            let what = t.describe();
            self.unexpected(&what)
        }
    }

    fn expect_kw(&mut self, k: Kw) -> PResult<Span> {
        if self.at_kw(k) {
            Ok(self.bump().span)
        } else {
            self.unexpected(&format!("'{}'", crate::token::kw_text(k)))
        }
    }

    fn ident(&mut self) -> PResult<(Name, Span)> {
        match self.peek().clone() {
            Tok::Ident(s) => {
                let sp = self.bump().span;
                Ok((s, sp))
            }
            _ => self.unexpected("an identifier"),
        }
    }

    /// An identifier or `_` (for loop and iterator variables).
    fn binder(&mut self) -> PResult<(Name, Span)> {
        if self.at(&Tok::Underscore) {
            let sp = self.bump().span;
            return Ok(("_".to_string(), sp));
        }
        self.ident()
    }

    fn at_ident(&mut self) -> bool {
        matches!(self.peek(), Tok::Ident(_))
    }

    // ----- programs and statements ----------------------------------------

    /// Parse statements until end of input.
    pub fn parse_program(&mut self) -> PResult<Vec<Stmt>> {
        let mut out = Vec::new();
        while !self.at(&Tok::Eof) {
            out.push(self.stmt()?);
        }
        Ok(out)
    }

    /// Parse a single expression spanning the whole input
    /// (a trailing semicolon is not allowed).
    pub fn parse_expression(&mut self) -> PResult<Expr> {
        let e = self.expr()?;
        if !self.at(&Tok::Eof) {
            return self.unexpected("end of expression");
        }
        Ok(e)
    }

    fn block_ends(&mut self) -> bool {
        matches!(
            self.peek(),
            Tok::Eof | Tok::Kw(Kw::End | Kw::Else | Kw::Elif | Kw::Until | Kw::Catch | Kw::When)
        )
    }

    fn block(&mut self) -> PResult<Vec<Stmt>> {
        let mut out = Vec::new();
        while !self.block_ends() {
            out.push(self.stmt()?);
        }
        Ok(out)
    }

    fn end(&mut self, k: Kw) -> PResult<()> {
        self.expect_kw(Kw::End)?;
        self.expect_kw(k)?;
        Ok(())
    }

    fn semi(&mut self) -> PResult<Span> {
        self.expect(&Tok::Semi)
    }

    fn stmt(&mut self) -> PResult<Stmt> {
        let start = self.span();
        let kind = self.stmt_kind()?;
        let span = start.to(self.prev_span());
        Ok(Stmt { kind, span })
    }

    fn stmt_kind(&mut self) -> PResult<StmtKind> {
        let tok = self.peek().clone();
        match tok {
            Tok::Semi => {
                self.bump();
                Ok(StmtKind::Empty)
            }
            Tok::Kw(k) => match k {
                Kw::If => self.if_stmt(),
                Kw::For => self.for_stmt(),
                Kw::While => {
                    self.bump();
                    let c = self.expr()?;
                    self.expect_kw(Kw::Do)?;
                    let b = self.block()?;
                    self.end(Kw::While)?;
                    self.semi()?;
                    Ok(StmtKind::While(c, b))
                }
                Kw::Repeat => {
                    self.bump();
                    let b = self.block()?;
                    self.expect_kw(Kw::Until)?;
                    let c = self.expr()?;
                    self.semi()?;
                    Ok(StmtKind::Repeat(b, c))
                }
                Kw::Case if !matches!(self.peek_at(1), Tok::Lt) => self.case_stmt(),
                Kw::Function | Kw::Procedure if matches!(self.peek_at(1), Tok::Ident(_)) => {
                    let is_proc = k == Kw::Procedure;
                    let start = self.bump().span;
                    let (name, _) = self.ident()?;
                    let def = self.func_rest(start, Some(name.clone()), is_proc)?;
                    self.semi()?;
                    Ok(StmtKind::FuncDef(name, def))
                }
                Kw::Intrinsic => self.intrinsic(),
                Kw::Return => {
                    self.bump();
                    let es = if self.at(&Tok::Semi) { Vec::new() } else { self.expr_list()? };
                    self.semi()?;
                    Ok(StmtKind::Return(es))
                }
                Kw::Break | Kw::Continue => {
                    self.bump();
                    let label = if self.at_ident() { Some(self.ident()?.0) } else { None };
                    self.semi()?;
                    Ok(if k == Kw::Break { StmtKind::Break(label) } else { StmtKind::Continue(label) })
                }
                Kw::Print => {
                    self.bump();
                    let es = if self.at(&Tok::Semi) || self.at(&Tok::Colon) { Vec::new() } else { self.expr_list()? };
                    let level = self.print_level()?;
                    self.semi()?;
                    Ok(StmtKind::Print(es, level))
                }
                Kw::Printf => {
                    self.bump();
                    let es = self.expr_list()?;
                    self.semi()?;
                    Ok(StmtKind::Printf(es))
                }
                Kw::Fprintf => {
                    self.bump();
                    let f = self.expr()?;
                    self.expect(&Tok::Comma)?;
                    let es = self.expr_list()?;
                    self.semi()?;
                    Ok(StmtKind::Fprintf(f, es))
                }
                Kw::Vprint | Kw::Vprintf => {
                    self.bump();
                    let (flag, level) = self.verbose_flag()?;
                    self.expect(&Tok::Colon)?;
                    let es = self.expr_list()?;
                    self.semi()?;
                    Ok(if k == Kw::Vprint { StmtKind::Vprint(flag, level, es) } else { StmtKind::Vprintf(flag, level, es) })
                }
                Kw::Error => {
                    self.bump();
                    let cond = if self.eat_kw(Kw::If) {
                        let c = self.expr()?;
                        self.expect(&Tok::Comma)?;
                        Some(c)
                    } else {
                        None
                    };
                    let es = self.expr_list()?;
                    self.semi()?;
                    Ok(StmtKind::Error(cond, es))
                }
                Kw::Assert | Kw::Assert2 | Kw::Assert3 => {
                    self.bump();
                    let level = match k {
                        Kw::Assert => 1,
                        Kw::Assert2 => 2,
                        _ => 3,
                    };
                    let e = self.expr()?;
                    self.semi()?;
                    Ok(StmtKind::Assert(level, e))
                }
                Kw::Require => {
                    self.bump();
                    let c = self.expr()?;
                    self.expect(&Tok::Colon)?;
                    let es = self.expr_list()?;
                    self.semi()?;
                    Ok(StmtKind::Require(c, es))
                }
                Kw::Requirerange => {
                    self.bump();
                    let (v, _) = self.ident()?;
                    self.expect(&Tok::Comma)?;
                    let lo = self.expr()?;
                    self.expect(&Tok::Comma)?;
                    let hi = self.expr()?;
                    self.semi()?;
                    Ok(StmtKind::RequireRange(v, lo, hi))
                }
                Kw::Requirege => {
                    self.bump();
                    let (v, _) = self.ident()?;
                    self.expect(&Tok::Comma)?;
                    let lo = self.expr()?;
                    self.semi()?;
                    Ok(StmtKind::RequireGe(v, lo))
                }
                Kw::Try => {
                    self.bump();
                    let body = self.block()?;
                    self.expect_kw(Kw::Catch)?;
                    let var = if self.at_ident() { Some(self.ident()?) } else { None };
                    let handler = self.block()?;
                    self.end(Kw::Try)?;
                    self.semi()?;
                    Ok(StmtKind::Try(body, var, handler))
                }
                Kw::Time => {
                    self.bump();
                    let s = self.stmt()?;
                    Ok(StmtKind::Time(Box::new(s)))
                }
                Kw::Vtime => {
                    self.bump();
                    let (flag, level) = self.verbose_flag()?;
                    self.expect(&Tok::Colon)?;
                    let s = self.stmt()?;
                    Ok(StmtKind::Vtime(flag, level, Box::new(s)))
                }
                Kw::Load | Kw::Iload => {
                    self.bump();
                    let e = self.expr()?;
                    self.semi()?;
                    Ok(StmtKind::Load(e, k == Kw::Iload))
                }
                Kw::Import => {
                    self.bump();
                    let f = self.expr()?;
                    self.expect(&Tok::Colon)?;
                    let names = self.ident_list()?;
                    self.semi()?;
                    Ok(StmtKind::Import(f, names))
                }
                Kw::Freeze => {
                    self.bump();
                    self.semi()?;
                    Ok(StmtKind::Freeze)
                }
                Kw::Declare => self.declare(),
                Kw::Forward | Kw::Local => {
                    self.bump();
                    let names = self.ident_list()?;
                    self.semi()?;
                    Ok(if k == Kw::Forward { StmtKind::Forward(names) } else { StmtKind::Local(names) })
                }
                Kw::Delete => {
                    self.bump();
                    let lv = self.lvalue()?;
                    self.semi()?;
                    Ok(StmtKind::Delete(lv))
                }
                Kw::Read | Kw::Readi => {
                    self.bump();
                    let lv = self.lvalue()?;
                    let prompt = if self.eat(&Tok::Comma) { Some(self.expr()?) } else { None };
                    self.semi()?;
                    Ok(StmtKind::Read(lv, prompt, k == Kw::Readi))
                }
                Kw::Quit | Kw::Exit => {
                    self.bump();
                    let e = if self.at(&Tok::Semi) { None } else { Some(self.expr()?) };
                    self.semi()?;
                    Ok(StmtKind::Quit(e))
                }
                Kw::Clear => {
                    self.bump();
                    self.semi()?;
                    Ok(StmtKind::Clear)
                }
                Kw::Save | Kw::Restore => {
                    self.bump();
                    let e = self.expr()?;
                    self.semi()?;
                    Ok(if k == Kw::Save { StmtKind::Save(e) } else { StmtKind::Restore(e) })
                }
                Kw::MarkSweep => {
                    self.bump();
                    self.semi()?;
                    Ok(StmtKind::Empty)
                }
                _ => self.expr_or_assign(),
            },
            _ => self.expr_or_assign(),
        }
    }

    fn print_level(&mut self) -> PResult<Option<Name>> {
        if self.eat(&Tok::Colon) {
            let (lvl, _) = self.ident()?;
            Ok(Some(lvl))
        } else {
            Ok(None)
        }
    }

    fn verbose_flag(&mut self) -> PResult<(Name, Option<Expr>)> {
        let (flag, _) = self.ident()?;
        let level = if self.eat(&Tok::Comma) { Some(self.expr()?) } else { None };
        Ok((flag, level))
    }

    fn ident_list(&mut self) -> PResult<Vec<(Name, Span)>> {
        let mut v = vec![self.ident()?];
        while self.eat(&Tok::Comma) {
            v.push(self.ident()?);
        }
        Ok(v)
    }

    fn if_stmt(&mut self) -> PResult<StmtKind> {
        self.expect_kw(Kw::If)?;
        let mut branches = Vec::new();
        let c = self.expr()?;
        self.expect_kw(Kw::Then)?;
        let b = self.block()?;
        branches.push((c, b));
        let mut else_ = None;
        loop {
            if self.eat_kw(Kw::Elif) {
                let c = self.expr()?;
                self.expect_kw(Kw::Then)?;
                let b = self.block()?;
                branches.push((c, b));
            } else if self.eat_kw(Kw::Else) {
                else_ = Some(self.block()?);
                break;
            } else {
                break;
            }
        }
        self.end(Kw::If)?;
        self.semi()?;
        Ok(StmtKind::If(branches, else_))
    }

    fn case_stmt(&mut self) -> PResult<StmtKind> {
        self.expect_kw(Kw::Case)?;
        let scrut = self.expr()?;
        self.expect(&Tok::Colon)?;
        let mut arms = Vec::new();
        let mut else_ = None;
        loop {
            if self.eat_kw(Kw::When) {
                let vals = self.expr_list()?;
                self.expect(&Tok::Colon)?;
                let b = self.block()?;
                arms.push((vals, b));
            } else if self.eat_kw(Kw::Else) {
                self.eat(&Tok::Colon);
                else_ = Some(self.block()?);
                break;
            } else {
                break;
            }
        }
        self.end(Kw::Case)?;
        self.semi()?;
        Ok(StmtKind::Case(scrut, arms, else_))
    }

    fn for_stmt(&mut self) -> PResult<StmtKind> {
        self.expect_kw(Kw::For)?;
        let random = self.eat_kw(Kw::Random);
        let first = self.binder()?;
        // `for i := a to b by c do`
        if !random && self.eat(&Tok::Assign) {
            let a = self.expr()?;
            self.expect_kw(Kw::To)?;
            let b = self.expr()?;
            let c = if self.eat_kw(Kw::By) { Some(self.expr()?) } else { None };
            self.expect_kw(Kw::Do)?;
            let body = self.block()?;
            self.end(Kw::For)?;
            self.semi()?;
            return Ok(StmtKind::For { index: None, var: first, kind: ForKind::Range(a, b, c), body });
        }
        // `for i -> x in S do`
        let (index, vars) = if self.eat(&Tok::Arrow) {
            (Some(first), vec![self.binder()?])
        } else {
            let mut vars = vec![first];
            while self.eat(&Tok::Comma) {
                vars.push(self.binder()?);
            }
            (None, vars)
        };
        self.expect_kw(Kw::In)?;
        let dom = self.expr()?;
        self.expect_kw(Kw::Do)?;
        let body = self.block()?;
        self.end(Kw::For)?;
        self.semi()?;
        // `for x, y in S` is shorthand for nested loops over S.
        let mut body = body;
        let n = vars.len();
        for (i, var) in vars.into_iter().enumerate().rev() {
            let kind = if random { ForKind::Random(dom.clone()) } else { ForKind::In(dom.clone()) };
            let idx = if i == n - 1 { index.clone() } else { None };
            if i == 0 {
                return Ok(StmtKind::For { index: idx, var, kind, body });
            }
            let span = var.1;
            body = vec![Stmt { kind: StmtKind::For { index: idx, var, kind, body }, span }];
        }
        unreachable!()
    }

    fn declare(&mut self) -> PResult<StmtKind> {
        self.expect_kw(Kw::Declare)?;
        let (what, _) = self.ident()?;
        match what.as_str() {
            "type" => {
                let (name, _) = self.ident()?;
                let elt = if self.eat(&Tok::LBrack) {
                    let (e, _) = self.ident()?;
                    self.expect(&Tok::RBrack)?;
                    Some(e)
                } else {
                    None
                };
                let parents = if self.eat(&Tok::Colon) { self.ident_list()?.into_iter().map(|p| p.0).collect() } else { Vec::new() };
                self.semi()?;
                Ok(StmtKind::DeclareType(name, elt, parents))
            }
            "attributes" => {
                let (cat, _) = self.ident()?;
                self.expect(&Tok::Colon)?;
                let names = self.ident_list()?.into_iter().map(|p| p.0).collect();
                self.semi()?;
                Ok(StmtKind::DeclareAttributes(cat, names))
            }
            "verbose" => {
                let (name, _) = self.ident()?;
                self.expect(&Tok::Comma)?;
                let max = self.expr()?;
                self.semi()?;
                Ok(StmtKind::DeclareVerbose(name, max))
            }
            _ => self.error_here(format!("bad syntax: unknown declaration '{what}'")),
        }
    }

    /// Statements that start with an expression: assignments, procedure
    /// calls and auto-printed expression lists.
    fn expr_or_assign(&mut self) -> PResult<StmtKind> {
        // Try a list of l-values (each identifier maybe with generator
        // names, `E<x, y>` or `E<[x]>`) followed by := or o:=.
        let save = self.pos;
        if let Some(mut targets) = self.try_target_list() {
            let at = self.span();
            if self.eat(&Tok::Assign) {
                let value = self.expr()?;
                self.semi()?;
                if targets.iter().any(|t| t.1.is_some()) {
                    return Ok(StmtKind::GenAssign(targets, value, at));
                }
                return Ok(StmtKind::Assign(targets.into_iter().map(|t| t.0).collect(), value, at));
            }
            if let [(_, None)] = targets[..] {
                if let Tok::OpAssign(op) = self.peek().clone() {
                    self.bump();
                    let Some(op) = BinOp::from_name(&op) else {
                        return self.error_here("bad syntax: unknown mutation operator");
                    };
                    let value = self.expr()?;
                    self.semi()?;
                    return Ok(StmtKind::OpAssign(targets.pop().unwrap().0, op, value, at));
                }
            }
        }
        self.pos = save;

        let es = self.expr_list()?;
        let level = self.print_level()?;
        self.semi()?;
        Ok(StmtKind::Expr(es, level))
    }

    fn try_target_list(&mut self) -> Option<Vec<(LValue, Option<GenNames>)>> {
        let mut v = Vec::new();
        loop {
            let save = self.pos;
            match self.gen_target() {
                Some(t) => v.push(t),
                None => {
                    self.pos = save;
                    v.push((self.lvalue().ok()?, None));
                }
            }
            if !self.eat(&Tok::Comma) {
                return Some(v);
            }
        }
    }

    /// An identifier with generator names: `E<x, y>`, `E<[x]>` or `E<>`.
    fn gen_target(&mut self) -> Option<(LValue, Option<GenNames>)> {
        let (name, sp) = self.ident().ok()?;
        if !self.at(&Tok::Lt) {
            return None;
        }
        let lt = self.bump().span;
        let names = if self.eat(&Tok::LBrack) {
            let (n, s) = self.ident().ok()?;
            self.eat(&Tok::RBrack).then_some(())?;
            GenNames::Seq(n, s, lt)
        } else if self.at(&Tok::Gt) {
            GenNames::List(Vec::new(), lt)
        } else {
            GenNames::List(self.ident_list().ok()?, lt)
        };
        self.eat(&Tok::Gt).then_some(())?;
        Some((LValue::Ident(name, sp), Some(names)))
    }

    /// The indices inside `s[...]`. `s[i..j]` (and `s[i..j by k]`) indexes
    /// by the range sequence.
    fn index_list(&mut self) -> PResult<Vec<Expr>> {
        let save = self.pos;
        let first = self.expr()?;
        if !self.eat(&Tok::DotDot) {
            self.pos = save;
            return self.expr_list();
        }
        let hi = self.expr()?;
        let by = if self.eat_kw(Kw::By) { Some(Box::new(self.expr()?)) } else { None };
        let sp = first.span.to(by.as_ref().map_or(hi.span, |b| b.span));
        Ok(vec![Self::mk(ExprKind::Aggregate(AggKind::Seq, None, AggBody::Range(Box::new(first), Box::new(hi), by)), sp)])
    }

    fn lvalue(&mut self) -> PResult<LValue> {
        let mut lv = match self.peek().clone() {
            Tok::Underscore => return Ok(LValue::Underscore(self.bump().span)),
            Tok::Ident(n) => {
                let sp = self.bump().span;
                LValue::Ident(n, sp)
            }
            _ => return self.unexpected("an identifier"),
        };
        loop {
            match self.peek() {
                Tok::LBrack => {
                    self.bump();
                    let idx = self.index_list()?;
                    let end = self.expect(&Tok::RBrack)?;
                    let sp = lv.span().to(end);
                    lv = LValue::Index(Box::new(lv), idx, sp);
                }
                Tok::Backquote => {
                    self.bump();
                    let (n, s) = self.ident()?;
                    let sp = lv.span().to(s);
                    lv = LValue::Attr(Box::new(lv), n, sp);
                }
                Tok::DoubleBackquote => {
                    self.bump();
                    let e = self.expr_bp(BP_POSTFIX)?;
                    let sp = lv.span().to(e.span);
                    lv = LValue::AttrDyn(Box::new(lv), Box::new(e), sp);
                }
                _ => return Ok(lv),
            }
        }
    }

    // ----- functions and intrinsics ---------------------------------------

    /// After `function`/`procedure` [name]: `(params) body end function`.
    fn func_rest(&mut self, start: Span, name: Option<Name>, is_procedure: bool) -> PResult<Rc<FuncDef>> {
        self.expect(&Tok::LParen)?;
        let (params, variadic, opt_params) = self.param_list(&Tok::RParen)?;
        self.expect(&Tok::RParen)?;
        let body = self.block()?;
        self.end(if is_procedure { Kw::Procedure } else { Kw::Function })?;
        let span = start.to(self.prev_span());
        Ok(Rc::new(FuncDef { name, params, variadic, opt_params, body: FuncBody::Block(body), is_procedure, span }))
    }

    /// Formal parameters: `x, ~y, ... : P := v, Q := w` up to `close`.
    fn param_list(&mut self, close: &Tok) -> PResult<(Vec<Param>, bool, Vec<(Name, Expr)>)> {
        let mut params = Vec::new();
        let mut variadic = false;
        let mut opts = Vec::new();
        if !self.at(close) && !self.at(&Tok::Colon) {
            loop {
                if self.eat(&Tok::Ellipsis) {
                    variadic = true;
                    break;
                }
                let is_ref = self.eat(&Tok::Tilde);
                let (name, span) = self.ident()?;
                params.push(Param { name, is_ref, span });
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        if self.eat(&Tok::Colon) {
            opts = self.opt_param_defs()?;
        }
        Ok((params, variadic, opts))
    }

    fn opt_param_defs(&mut self) -> PResult<Vec<(Name, Expr)>> {
        let mut opts = Vec::new();
        loop {
            let (n, _) = self.ident()?;
            self.expect(&Tok::Assign)?;
            let v = self.expr()?;
            opts.push((n, v));
            if !self.eat(&Tok::Comma) {
                return Ok(opts);
            }
        }
    }

    fn intrinsic(&mut self) -> PResult<StmtKind> {
        let start = self.expect_kw(Kw::Intrinsic)?;
        let name = match self.peek().clone() {
            Tok::Ident(n) => {
                self.bump();
                n
            }
            _ => return self.unexpected("an intrinsic name"),
        };
        self.expect(&Tok::LParen)?;
        let mut args = Vec::new();
        let mut variadic = false;
        let mut opt_params = Vec::new();
        if !self.at(&Tok::RParen) && !self.at(&Tok::Colon) {
            loop {
                if self.eat(&Tok::Ellipsis) {
                    variadic = true;
                    break;
                }
                let is_ref = self.eat(&Tok::Tilde);
                let (n, span) = self.ident()?;
                // `::` is lexed as two colons.
                let ty = if self.at(&Tok::Colon) && matches!(self.peek_at(1), Tok::Colon) {
                    self.bump();
                    self.bump();
                    Some(self.type_expr()?)
                } else {
                    None
                };
                if ty.is_none() && !is_ref {
                    return self.unexpected("'::' and a type");
                }
                args.push(IntrinsicArg { name: n, is_ref, ty, span });
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        if self.eat(&Tok::Colon) {
            opt_params = self.opt_param_defs()?;
        }
        self.expect(&Tok::RParen)?;
        let returns = if self.eat(&Tok::Arrow) {
            let mut v = vec![self.type_expr()?];
            while self.eat(&Tok::Comma) {
                v.push(self.type_expr()?);
            }
            Some(v)
        } else {
            None
        };
        // The doc comment is raw text in braces.
        if !self.at(&Tok::LBrace) {
            return self.unexpected("'{' starting the intrinsic's description");
        }
        let brace = self.span();
        self.toks.truncate(self.pos);
        self.lexer.seek(brace.lo as usize + 1);
        let Some(doc) = self.lexer.raw_until('}') else {
            return Err(ParseError { message: "unterminated intrinsic description".into(), span: brace, incomplete: true });
        };
        let body = self.block()?;
        self.end(Kw::Intrinsic)?;
        let span = start.to(self.prev_span());
        self.semi()?;
        let doc = doc.trim().to_string();
        Ok(StmtKind::Intrinsic(Rc::new(IntrinsicDef { name, args, variadic, opt_params, returns, doc, body, span })))
    }

    fn type_expr(&mut self) -> PResult<TypeExpr> {
        let tok = self.peek().clone();
        match tok {
            Tok::Dot => {
                self.bump();
                Ok(TypeExpr::Any)
            }
            Tok::Ident(n) => {
                self.bump();
                if self.eat(&Tok::LBrack) {
                    let mut ps = vec![self.type_expr()?];
                    while self.eat(&Tok::Comma) {
                        ps.push(self.type_expr()?);
                    }
                    self.expect(&Tok::RBrack)?;
                    Ok(TypeExpr::Extended(n, ps))
                } else {
                    Ok(TypeExpr::Named(n))
                }
            }
            Tok::LBrack => {
                self.bump();
                let inner = if self.at(&Tok::RBrack) { None } else { Some(Box::new(self.type_expr()?)) };
                self.expect(&Tok::RBrack)?;
                Ok(TypeExpr::Seq(inner))
            }
            Tok::LBrace => {
                self.bump();
                if self.eat(&Tok::LBrack) {
                    let inner = if self.at(&Tok::RBrack) { None } else { Some(Box::new(self.type_expr()?)) };
                    self.expect(&Tok::RBrack)?;
                    self.expect(&Tok::RBrace)?;
                    return Ok(TypeExpr::SetOrSeq(inner));
                }
                let inner = if self.at(&Tok::RBrace) { None } else { Some(Box::new(self.type_expr()?)) };
                self.expect(&Tok::RBrace)?;
                Ok(TypeExpr::Set(inner))
            }
            Tok::LBraceAt => {
                self.bump();
                let inner = if self.at(&Tok::AtRBrace) { None } else { Some(Box::new(self.type_expr()?)) };
                self.expect(&Tok::AtRBrace)?;
                Ok(TypeExpr::ISet(inner))
            }
            Tok::LBraceStar => {
                self.bump();
                let inner = if self.at(&Tok::StarRBrace) { None } else { Some(Box::new(self.type_expr()?)) };
                self.expect(&Tok::StarRBrace)?;
                Ok(TypeExpr::MSet(inner))
            }
            Tok::Lt => {
                self.bump();
                self.expect(&Tok::Gt)?;
                Ok(TypeExpr::Tuple)
            }
            _ => self.unexpected("a type"),
        }
    }

    // ----- expressions ----------------------------------------------------

    pub fn expr(&mut self) -> PResult<Expr> {
        self.expr_bp(0)
    }

    fn expr_list(&mut self) -> PResult<Vec<Expr>> {
        let mut v = vec![self.expr()?];
        while self.eat(&Tok::Comma) {
            v.push(self.expr()?);
        }
        Ok(v)
    }

    fn mk(kind: ExprKind, span: Span) -> Expr {
        Expr { kind, span, at: span.lo }
    }

    fn mk_at(kind: ExprKind, span: Span, at: Span) -> Expr {
        Expr { kind, span, at: at.lo }
    }

    fn expr_bp(&mut self, min_bp: u8) -> PResult<Expr> {
        let mut lhs = self.prefix()?;
        loop {
            let tok = self.peek().clone();
            match tok {
                Tok::LParen if BP_POSTFIX >= min_bp => {
                    let open = self.bump().span;
                    let (args, params) = self.call_args()?;
                    let end = self.expect(&Tok::RParen)?;
                    let sp = lhs.span.to(end);
                    lhs = Self::mk_at(ExprKind::Call(Box::new(lhs), args, params), sp, open);
                }
                Tok::LBrack if BP_POSTFIX >= min_bp => {
                    let open = self.bump().span;
                    let idx = self.index_list()?;
                    let end = self.expect(&Tok::RBrack)?;
                    let sp = lhs.span.to(end);
                    lhs = Self::mk_at(ExprKind::Index(Box::new(lhs), idx), sp, open);
                }
                Tok::Backquote if BP_POSTFIX >= min_bp => {
                    let op = self.bump().span;
                    let (n, s) = self.ident()?;
                    let sp = lhs.span.to(s);
                    lhs = Self::mk_at(ExprKind::Attr(Box::new(lhs), n), sp, op);
                }
                Tok::DoubleBackquote if BP_POSTFIX >= min_bp => {
                    let op = self.bump().span;
                    let e = self.expr_bp(BP_POSTFIX)?;
                    let sp = lhs.span.to(e.span);
                    lhs = Self::mk_at(ExprKind::AttrDyn(Box::new(lhs), Box::new(e)), sp, op);
                }
                Tok::Dot if BP_DOT >= min_bp => {
                    let op = self.bump().span;
                    let rhs = self.expr_bp(BP_DOT + 1)?;
                    let sp = lhs.span.to(rhs.span);
                    lhs = Self::mk_at(ExprKind::Dot(Box::new(lhs), Box::new(rhs)), sp, op);
                }
                Tok::At | Tok::AtAt if BP_AT >= min_bp => {
                    let op = self.bump().span;
                    let rhs = self.expr_bp(BP_AT + 1)?;
                    let sp = lhs.span.to(rhs.span);
                    lhs = if tok == Tok::At {
                        Self::mk_at(ExprKind::Image(Box::new(lhs), Box::new(rhs)), sp, op)
                    } else {
                        Self::mk_at(ExprKind::Preimage(Box::new(lhs), Box::new(rhs)), sp, op)
                    };
                }
                Tok::Bang | Tok::BangBang if BP_BANG >= min_bp => {
                    let op = self.bump().span;
                    let rhs = self.expr_bp(BP_BANG)?;
                    let sp = lhs.span.to(rhs.span);
                    lhs = Self::mk_at(ExprKind::Coerce(Box::new(lhs), Box::new(rhs), tok == Tok::BangBang), sp, op);
                }
                Tok::CaretCaret if BP_CARETCARET >= min_bp => {
                    self.bump();
                    let rhs = self.expr_bp(BP_CARETCARET + 1)?;
                    let sp = lhs.span.to(rhs.span);
                    lhs = Self::mk(ExprKind::Multiplicity(Box::new(lhs), Box::new(rhs)), sp);
                }
                Tok::Kw(Kw::Select) if BP_SELECT >= min_bp => {
                    let op = self.bump().span;
                    let a = self.expr_bp(BP_SELECT)?;
                    self.expect_kw(Kw::Else)?;
                    let b = self.expr_bp(BP_SELECT)?;
                    let sp = lhs.span.to(b.span);
                    lhs = Self::mk_at(ExprKind::Select(Box::new(lhs), Box::new(a), Box::new(b)), sp, op);
                }
                Tok::Kw(Kw::Where) if BP_WHERE >= min_bp => {
                    self.bump();
                    let mut names = vec![self.binder()?.0];
                    while self.eat(&Tok::Comma) {
                        names.push(self.binder()?.0);
                    }
                    let bound = (names.len() == 1 && self.eat_kw(Kw::Is)) || self.eat(&Tok::Assign);
                    if !bound {
                        return self.unexpected(if names.len() == 1 { "'is' or ':='" } else { "':='" });
                    }
                    let v = self.expr_bp(BP_WHERE + 1)?;
                    let sp = lhs.span.to(v.span);
                    lhs = Self::mk(ExprKind::Where(Box::new(lhs), names, Box::new(v)), sp);
                }
                _ => {
                    let Some((op, lbp, rbp)) = binop_of(&tok) else { break };
                    if lbp < min_bp {
                        break;
                    }
                    let op_span = self.bump().span;
                    let rhs = self.expr_bp(rbp)?;
                    // A literal fraction with a zero denominator is rejected
                    // as it is read.
                    if op == BinOp::Div {
                        if let (ExprKind::Int(_), ExprKind::Int(d)) = (&lhs.kind, &rhs.kind) {
                            if d.trim_start_matches("0x").chars().all(|c| c == '0') {
                                return Err(ParseError { message: "Illegal zero denominator".into(), span: rhs.span, incomplete: false });
                            }
                        }
                    }
                    let sp = lhs.span.to(rhs.span);
                    lhs = Self::mk_at(ExprKind::Binary(op, Box::new(lhs), Box::new(rhs)), sp, op_span);
                }
            }
        }
        Ok(lhs)
    }

    fn call_args(&mut self) -> PResult<(Vec<Arg>, Vec<ParamArg>)> {
        let mut args = Vec::new();
        let mut params = Vec::new();
        if !self.at(&Tok::RParen) && !self.at(&Tok::Colon) {
            loop {
                if self.at(&Tok::Tilde) {
                    let t = self.bump().span;
                    let lv = self.lvalue()?;
                    let sp = t.to(lv.span());
                    args.push(Arg::Ref(lv, sp));
                } else {
                    args.push(Arg::Value(self.expr()?));
                }
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        if self.eat(&Tok::Colon) {
            loop {
                let (name, s) = self.ident()?;
                let value = if self.eat(&Tok::Assign) {
                    self.expr()?
                } else {
                    // A bare parameter name means `Name := true`.
                    Self::mk(ExprKind::Bool(true), s)
                };
                let span = s.to(value.span);
                params.push(ParamArg { name, value, span });
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        Ok((args, params))
    }

    fn prefix(&mut self) -> PResult<Expr> {
        let t = self.bump();
        let sp = t.span;
        let kind = match t.tok {
            Tok::Int(s) => ExprKind::Int(s),
            Tok::Real(s) => ExprKind::Real(s),
            Tok::Str(s) => ExprKind::Str(s),
            Tok::Kw(Kw::True) => ExprKind::Bool(true),
            Tok::Kw(Kw::False) => ExprKind::Bool(false),
            Tok::Dollar(n) => ExprKind::Previous(n),
            Tok::DollarDollar => ExprKind::SelfRef,
            Tok::Underscore => ExprKind::Underscore,
            Tok::Ident(name) => {
                if self.at(&Tok::Lt) {
                    return self.constructor(name, sp);
                }
                if name == "rep" && self.at(&Tok::LBrace) {
                    return self.quantifier(QuantKind::Rep, Vec::new(), sp);
                }
                ExprKind::Ident(name)
            }
            Tok::LParen => {
                let e = self.expr()?;
                let end = self.expect(&Tok::RParen)?;
                return Ok(Self::mk(ExprKind::Paren(Box::new(e)), sp.to(end)));
            }
            Tok::Minus | Tok::Plus => {
                let e = self.expr_bp(BP_NEG)?;
                let op = if t.tok == Tok::Minus { UnOp::Neg } else { UnOp::Plus };
                let span = sp.to(e.span);
                return Ok(Self::mk(ExprKind::Unary(op, Box::new(e)), span));
            }
            Tok::Kw(Kw::Not) => {
                let e = self.expr_bp(BP_NOT)?;
                let span = sp.to(e.span);
                return Ok(Self::mk(ExprKind::Unary(UnOp::Not, Box::new(e)), span));
            }
            Tok::Hash => {
                let e = self.expr_bp(BP_HASH)?;
                let span = sp.to(e.span);
                return Ok(Self::mk(ExprKind::Unary(UnOp::Card, Box::new(e)), span));
            }
            Tok::Amp => {
                let optok = self.peek().clone();
                let Some(op) = reduction_op(&optok) else {
                    return self.unexpected("an operator after '&'");
                };
                self.bump();
                let e = self.expr_bp(BP_HASH)?;
                let span = sp.to(e.span);
                return Ok(Self::mk(ExprKind::Reduce(op, Box::new(e)), span));
            }
            Tok::Kw(Kw::Assigned) => {
                let e = self.expr_bp(BP_ASSIGNED)?;
                let span = sp.to(e.span);
                return Ok(Self::mk(ExprKind::Assigned(Box::new(e)), span));
            }
            Tok::Kw(Kw::Eval) => {
                let e = self.expr_bp(BP_HASH)?;
                let span = sp.to(e.span);
                return Ok(Self::mk(ExprKind::Eval(Box::new(e)), span));
            }
            Tok::Kw(k @ (Kw::Function | Kw::Procedure)) => {
                let def = self.func_rest(sp, None, k == Kw::Procedure)?;
                let span = def.span;
                return Ok(Self::mk(ExprKind::Function(def), span));
            }
            Tok::Kw(k @ (Kw::Exists | Kw::Forall)) => {
                let mut wit = Vec::new();
                if self.eat(&Tok::LParen) {
                    wit = self.ident_list()?.into_iter().map(|w| w.0).collect();
                    self.expect(&Tok::RParen)?;
                }
                let q = if k == Kw::Exists { QuantKind::Exists } else { QuantKind::Forall };
                return self.quantifier(q, wit, sp);
            }
            Tok::Kw(Kw::Random) => return self.quantifier(QuantKind::Random, Vec::new(), sp),
            Tok::Kw(Kw::Case) => return self.case_expr(sp),
            Tok::LBrack => return self.aggregate(AggKind::Seq, sp, Tok::RBrack),
            Tok::LBrace => return self.aggregate(AggKind::Set, sp, Tok::RBrace),
            Tok::LBraceAt => return self.aggregate(AggKind::ISet, sp, Tok::AtRBrace),
            Tok::LBraceStar => return self.aggregate(AggKind::MSet, sp, Tok::StarRBrace),
            Tok::LBraceBang => return self.formal(FormalKind::Set, sp, Tok::BangRBrace),
            Tok::LBrackBang => return self.formal(FormalKind::Seq, sp, Tok::BangRBrack),
            Tok::LBrackStar => {
                let mut v = Vec::new();
                if !self.at(&Tok::StarRBrack) {
                    let first = self.arrow_pair()?;
                    if self.eat(&Tok::Colon) {
                        let c = self.comprehension_rest(first, &Tok::StarRBrack)?;
                        let end = self.expect(&Tok::StarRBrack)?;
                        return Ok(Self::mk(ExprKind::ListCompr(c), sp.to(end)));
                    }
                    v.push(first);
                    while self.eat(&Tok::Comma) {
                        v.push(self.arrow_pair()?);
                    }
                }
                let end = self.expect(&Tok::StarRBrack)?;
                return Ok(Self::mk(ExprKind::List(v), sp.to(end)));
            }
            Tok::Lt => {
                let mut v = Vec::new();
                if !self.at(&Tok::Gt) {
                    let first = self.expr()?;
                    if self.eat(&Tok::Colon) {
                        let c = self.comprehension_rest(first, &Tok::Gt)?;
                        let end = self.expect(&Tok::Gt)?;
                        return Ok(Self::mk(ExprKind::TupleCompr(c), sp.to(end)));
                    }
                    v.push(first);
                    while self.eat(&Tok::Comma) {
                        v.push(self.expr()?);
                    }
                }
                let end = self.expect(&Tok::Gt)?;
                return Ok(Self::mk(ExprKind::Tuple(v), sp.to(end)));
            }
            _ => {
                self.pos -= 1;
                return self.unexpected("an expression");
            }
        };
        Ok(Self::mk(kind, sp))
    }

    fn aggregate(&mut self, kind: AggKind, start: Span, close: Tok) -> PResult<Expr> {
        if self.at(&close) {
            let end = self.bump().span;
            return Ok(Self::mk(ExprKind::Aggregate(kind, None, AggBody::Empty), start.to(end)));
        }
        let mut universe = None;
        let mut first = self.arrow_pair()?;
        if self.eat(&Tok::Pipe) {
            universe = Some(Box::new(first));
            if self.at(&close) {
                let end = self.bump().span;
                return Ok(Self::mk(ExprKind::Aggregate(kind, universe, AggBody::Empty), start.to(end)));
            }
            first = self.arrow_pair()?;
        }
        // Indexed sets and multisets take no ranges, as in Magma.
        if self.at(&Tok::DotDot) && matches!(kind, AggKind::ISet | AggKind::MSet) {
            return self.error_here("bad syntax: a range in an indexed set or multiset");
        }
        let body = if self.eat(&Tok::Colon) {
            AggBody::Compr(self.comprehension_rest(first, &close)?)
        } else if self.eat(&Tok::DotDot) {
            let hi = self.expr()?;
            let by = if self.eat_kw(Kw::By) { Some(Box::new(self.expr()?)) } else { None };
            AggBody::Range(Box::new(first), Box::new(hi), by)
        } else {
            let mut v = vec![first];
            while self.eat(&Tok::Comma) {
                v.push(self.arrow_pair()?);
            }
            AggBody::Enum(v)
        };
        let end = self.expect(&close)?;
        Ok(Self::mk(ExprKind::Aggregate(kind, universe, body), start.to(end)))
    }

    /// After `head :` — iterators and an optional predicate, up to `close`.
    fn comprehension_rest(&mut self, head: Expr, close: &Tok) -> PResult<Comprehension> {
        let mut iters = Vec::new();
        loop {
            let (first, fs) = self.binder()?;
            if self.eat(&Tok::Arrow) {
                let (var, _) = self.binder()?;
                self.expect_kw(Kw::In)?;
                let domain = self.expr()?;
                iters.push(Iter { index: Some(first), var, span: fs.to(domain.span), domain });
            } else {
                let mut vars = vec![(first, fs)];
                while self.eat(&Tok::Comma) {
                    vars.push(self.binder()?);
                }
                self.expect_kw(Kw::In)?;
                let domain = self.expr()?;
                // In `x, y in S` the first variable is the outer loop, while
                // among separate iterators the first is the inner one.
                for (var, vs) in vars.into_iter().rev() {
                    iters.push(Iter { index: None, var, span: vs.to(domain.span), domain: domain.clone() });
                }
            }
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        let pred = if self.eat(&Tok::Pipe) { Some(Box::new(self.expr()?)) } else { None };
        let _ = close;
        Ok(Comprehension { head: Box::new(head), iters, pred })
    }

    fn formal(&mut self, kind: FormalKind, start: Span, close: Tok) -> PResult<Expr> {
        // {! x in S | P !}  or  {! U | x in S | P !}
        let mut universe = None;
        let save = self.pos;
        let is_simple = self.at_ident() && matches!(self.peek_at(1), Tok::Kw(Kw::In));
        if !is_simple {
            let u = self.expr()?;
            self.expect(&Tok::Pipe)?;
            universe = Some(Box::new(u));
        } else {
            self.pos = save;
        }
        let (var, _) = self.ident()?;
        self.expect_kw(Kw::In)?;
        let dom = self.expr()?;
        let pred = if self.eat(&Tok::Pipe) { Some(Box::new(self.expr()?)) } else { None };
        let end = self.expect(&close)?;
        Ok(Self::mk(ExprKind::Formal(kind, universe, var, Box::new(dom), pred), start.to(end)))
    }

    fn quantifier(&mut self, q: QuantKind, witnesses: Vec<Name>, start: Span) -> PResult<Expr> {
        self.expect(&Tok::LBrace)?;
        let head = self.expr()?;
        self.expect(&Tok::Colon)?;
        let c = self.comprehension_rest(head, &Tok::RBrace)?;
        let end = self.expect(&Tok::RBrace)?;
        Ok(Self::mk(ExprKind::Quantifier(q, witnesses, c), start.to(end)))
    }

    fn case_expr(&mut self, start: Span) -> PResult<Expr> {
        self.expect(&Tok::Lt)?;
        let scrut = self.expr()?;
        self.expect(&Tok::Pipe)?;
        let mut arms = Vec::new();
        loop {
            if self.eat_kw(Kw::Default) {
                self.expect(&Tok::Colon)?;
                let d = self.expr()?;
                let end = self.expect(&Tok::Gt)?;
                return Ok(Self::mk(ExprKind::Case(Box::new(scrut), arms, Box::new(d)), start.to(end)));
            }
            let l = self.expr()?;
            self.expect(&Tok::Colon)?;
            let r = self.expr()?;
            arms.push((l, r));
            if !self.eat(&Tok::Comma) {
                return self.unexpected("',' followed by a case or 'default'");
            }
        }
    }

    /// `name< ... >` constructors.
    fn constructor(&mut self, name: Name, start: Span) -> PResult<Expr> {
        let open = self.expect(&Tok::Lt)?;
        let kind = match name.as_str() {
            "func" | "proc" => {
                let is_procedure = name == "proc";
                let (params, variadic, opt_params) = self.param_list(&Tok::Pipe)?;
                self.expect(&Tok::Pipe)?;
                let mut es = vec![self.expr()?];
                // func< x | a, b >: a function with several return values.
                while !is_procedure && self.eat(&Tok::Comma) {
                    es.push(self.expr()?);
                }
                let body = if es.len() == 1 {
                    FuncBody::Expr(Box::new(es.pop().unwrap()))
                } else {
                    let sp = es[0].span.to(es[es.len() - 1].span);
                    FuncBody::Block(vec![Stmt { kind: StmtKind::Return(es), span: sp }])
                };
                let end = self.expect(&Tok::Gt)?;
                let span = start.to(end);
                let def = FuncDef { name: None, params, variadic, opt_params, body, is_procedure, span };
                return Ok(Self::mk(ExprKind::Function(Rc::new(def)), span));
            }
            "map" | "pmap" | "hom" | "iso" => {
                let mk = match name.as_str() {
                    "map" => MapKind::Map,
                    "pmap" => MapKind::PMap,
                    "hom" => MapKind::Hom,
                    _ => MapKind::Iso,
                };
                let dom = self.expr()?;
                self.expect(&Tok::Arrow)?;
                let cod = self.expr()?;
                self.expect(&Tok::Pipe)?;
                let body = if self.at(&Tok::Gt) {
                    // `hom< Z -> R | >`: the natural homomorphism.
                    MapBody::Exprs(Vec::new())
                } else if self.at_ident() && self.at_maps_to(1) {
                    let (x, _) = self.ident()?;
                    self.eat_maps_to()?;
                    let img = self.expr()?;
                    let inv = if self.at(&Tok::Comma) && matches!(self.peek_at(1), Tok::Ident(_)) && self.at_maps_to(2) {
                        self.bump();
                        let (y, _) = self.ident()?;
                        self.eat_maps_to()?;
                        Some((y, Box::new(self.expr()?)))
                    } else {
                        None
                    };
                    MapBody::Rule(x, Box::new(img), inv)
                } else {
                    MapBody::Exprs(self.arrow_pair_list()?)
                };
                ExprKind::Map(mk, Box::new(dom), Box::new(cod), body)
            }
            "rec" => {
                let fmt = self.expr()?;
                self.expect(&Tok::Pipe)?;
                let mut fields = Vec::new();
                if !self.at(&Tok::Gt) {
                    loop {
                        let (n, _) = self.ident()?;
                        self.expect(&Tok::Assign)?;
                        fields.push((n, self.expr()?));
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                }
                ExprKind::Rec(Box::new(fmt), fields)
            }
            "recformat" => {
                let mut fields = Vec::new();
                if !self.at(&Tok::Gt) {
                    loop {
                        let (n, _) = self.ident()?;
                        let ty = if self.eat(&Tok::Colon) { Some(self.expr()?) } else { None };
                        fields.push((n, ty));
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                }
                ExprKind::RecFormat(fields)
            }
            "car" | "cop" => {
                let v = self.expr_list()?;
                if name == "car" { ExprKind::Car(v) } else { ExprKind::Cop(v) }
            }
            "elt" => {
                let parent = self.expr()?;
                self.expect(&Tok::Pipe)?;
                let v = self.expr_list()?;
                ExprKind::Elt(Box::new(parent), v)
            }
            _ => {
                let left = if self.at(&Tok::Pipe) || self.at(&Tok::Gt) { Vec::new() } else { self.expr_list()? };
                let right = if self.eat(&Tok::Pipe) {
                    Some(if self.at(&Tok::Gt) { Vec::new() } else { self.expr_list()? })
                } else {
                    None
                };
                ExprKind::Constructor(name, left, right)
            }
        };
        let end = self.expect(&Tok::Gt)?;
        // Errors in a map constructor, or in constructors such as ideal< >
        // and quo< >, are reported at the bracket.
        if matches!(kind, ExprKind::Map(..) | ExprKind::Constructor(..) | ExprKind::Elt(..)) {
            return Ok(Self::mk_at(kind, start.to(end), open));
        }
        Ok(Self::mk(kind, start.to(end)))
    }

    /// Expressions in a map graph, where `a -> b` means the pair `<a, b>`.
    fn arrow_pair_list(&mut self) -> PResult<Vec<Expr>> {
        let mut v = vec![self.arrow_pair()?];
        while self.eat(&Tok::Comma) {
            v.push(self.arrow_pair()?);
        }
        Ok(v)
    }

    /// An element of an aggregate or a map graph, where `a -> b` means the pair `<a, b>`.
    fn arrow_pair(&mut self) -> PResult<Expr> {
        let a = self.expr()?;
        if !self.eat(&Tok::Arrow) {
            return Ok(a);
        }
        let b = self.expr()?;
        let sp = a.span.to(b.span);
        Ok(Self::mk(ExprKind::Tuple(vec![a, b]), sp))
    }

    fn at_maps_to(&mut self, k: usize) -> bool {
        match self.peek_at(k) {
            Tok::MapsTo => true,
            Tok::Colon => matches!(self.peek_at(k + 1), Tok::Arrow),
            _ => false,
        }
    }

    fn eat_maps_to(&mut self) -> PResult<()> {
        if self.eat(&Tok::MapsTo) {
            return Ok(());
        }
        self.expect(&Tok::Colon)?;
        self.expect(&Tok::Arrow)?;
        Ok(())
    }
}

/// Parse a complete program.
pub fn parse_program(src: &str, file: FileId) -> PResult<Vec<Stmt>> {
    Parser::new(src, file).parse_program()
}

/// The statements before the first syntax error of `src`, and that error.
pub fn parse_program_prefix(src: &str, file: FileId) -> (Vec<Stmt>, Option<ParseError>) {
    let mut p = Parser::new(src, file);
    let mut out = Vec::new();
    while !p.at(&Tok::Eof) {
        match p.stmt() {
            Ok(s) => out.push(s),
            Err(e) => return (out, Some(e)),
        }
    }
    (out, None)
}

/// Parse a lone expression (used by `eval`).
pub fn parse_expression(src: &str, file: FileId) -> PResult<Expr> {
    Parser::new(src, file).parse_expression()
}
