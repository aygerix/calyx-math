//! The table of intrinsics (built-in and user-defined functions with type
//! signatures) and the built-in libraries.

pub mod aggregates;
pub mod core;
pub mod env;
pub mod ints;
pub mod io;
pub mod maps;
pub mod reals;
pub mod rings;
pub mod strings;

use std::path::PathBuf;
use std::rc::Rc;

use calyx_flint::Integer;
use rustc_hash::FxHashMap;

use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::sym::Sym;
use crate::types::{TypePat, parse_type_pat};
use crate::value::*;

pub type NativeFn = fn(&mut Interp, &mut CallArgs) -> RResult<Vec<Value>>;

pub enum Imp {
    Native(NativeFn),
    User(Rc<Closure>),
}

pub struct ArgSig {
    pub name: Rc<str>,
    pub pat: TypePat,
    pub is_ref: bool,
    /// A reference argument without a type (may be unassigned).
    pub untyped: bool,
}

pub struct ParamSig {
    pub name: Sym,
    pub default: Value,
    pub default_text: Rc<str>,
}

pub struct Signature {
    pub args: Vec<ArgSig>,
    pub variadic: bool,
    /// `None` for procedures.
    pub returns: Option<Vec<TypePat>>,
    pub params: Vec<ParamSig>,
    pub doc: Rc<str>,
    pub imp: Imp,
    /// A catch-all operator signature implemented by the evaluator.
    pub generic: bool,
    pub order: u64,
    /// The package file that defined this signature, if any.
    pub source: Option<PathBuf>,
}

#[derive(Default)]
pub struct IntrinsicTable {
    map: FxHashMap<Sym, Vec<Rc<Signature>>>,
    counter: u64,
}

impl IntrinsicTable {
    pub fn new() -> IntrinsicTable {
        IntrinsicTable::default()
    }

    pub fn contains(&self, name: Sym) -> bool {
        self.map.get(&name).is_some_and(|v| !v.is_empty())
    }

    pub fn get(&self, name: Sym) -> Option<&Vec<Rc<Signature>>> {
        self.map.get(&name).filter(|v| !v.is_empty())
    }

    pub fn add(&mut self, name: Sym, mut sig: Signature) {
        self.counter += 1;
        sig.order = self.counter;
        self.map.entry(name).or_default().push(Rc::new(sig));
    }

    /// Remove all signatures defined by a package file.
    pub fn remove_source(&mut self, path: &PathBuf) {
        for sigs in self.map.values_mut() {
            sigs.retain(|s| s.source.as_ref() != Some(path));
        }
    }

    pub fn names(&self) -> impl Iterator<Item = Sym> + '_ {
        self.map.iter().filter(|(_, v)| !v.is_empty()).map(|(k, _)| *k)
    }
}

/// Parse `"x::RngIntElt, ~S::SeqEnum -> RngIntElt"`.
fn parse_sig(it: &Interp, s: &str) -> Result<(Vec<ArgSig>, bool, Option<Vec<TypePat>>), String> {
    let (lhs, rhs) = match s.rfind("->") {
        Some(i) => (&s[..i], Some(&s[i + 2..])),
        None => (s, None),
    };
    let mut args = Vec::new();
    let mut variadic = false;
    for part in split_top(lhs) {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        if part == "..." {
            variadic = true;
            continue;
        }
        let (is_ref, rest) = match part.strip_prefix('~') {
            Some(r) => (true, r),
            None => (false, part),
        };
        let (name, pat, untyped) = match rest.split_once("::") {
            Some((n, t)) => (n.trim(), parse_type_pat(t.trim(), &it.types)?, false),
            None => (rest.trim(), TypePat::Any, true),
        };
        args.push(ArgSig { name: Rc::from(name), pat, is_ref, untyped: untyped && is_ref });
    }
    let returns = match rhs {
        None => None,
        Some(r) => {
            let mut v = Vec::new();
            for t in split_top(r) {
                let t = t.trim();
                if !t.is_empty() {
                    v.push(parse_type_pat(t, &it.types)?);
                }
            }
            Some(v)
        }
    };
    Ok((args, variadic, returns))
}

fn split_top(s: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut depth = 0;
    let mut start = 0;
    for (i, c) in s.char_indices() {
        match c {
            '[' | '{' | '<' => depth += 1,
            ']' | '}' | '>' => depth -= 1,
            ',' if depth == 0 => {
                out.push(&s[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    out.push(&s[start..]);
    out
}

impl Interp {
    /// Register a native intrinsic.
    pub fn def(&mut self, name: &str, sig: &str, doc: &str, f: NativeFn) {
        self.def_params(name, sig, &[], doc, f);
    }

    /// Register a native intrinsic with named parameters and defaults.
    pub fn def_params(&mut self, name: &str, sig: &str, params: &[(&str, Value)], doc: &str, f: NativeFn) {
        let (args, variadic, returns) = parse_sig(self, sig).unwrap_or_else(|e| panic!("bad signature for {name}: {sig}: {e}"));
        let params = params
            .iter()
            .map(|(n, v)| ParamSig { name: Sym::new(n), default: v.clone(), default_text: Rc::from(self.format_flat(v, crate::print::Level::Magma).unwrap_or_default().as_str()) })
            .collect();
        let sig = Signature { args, variadic, returns, params, doc: Rc::from(doc), imp: Imp::Native(f), generic: false, order: 0, source: None };
        self.intrinsics.add(Sym::new(name), sig);
    }

    /// Register a catch-all operator signature.
    pub fn def_generic(&mut self, name: &str, sig: &str, doc: &str, f: NativeFn) {
        let (args, variadic, returns) = parse_sig(self, sig).unwrap();
        let sig = Signature { args, variadic, returns, params: Vec::new(), doc: Rc::from(doc), imp: Imp::Native(f), generic: true, order: 0, source: None };
        self.intrinsics.add(Sym::new(name), sig);
    }

    /// Text describing an intrinsic and its signatures.
    pub fn describe_intrinsic(&self, name: Sym) -> String {
        let mut out = format!("Intrinsic '{name}'\n\nSignatures:\n");
        if let Some(sigs) = self.intrinsics.get(name) {
            for s in sigs {
                out.push('\n');
                out.push_str("    ");
                out.push_str(&self.signature_line(s));
                out.push('\n');
                if !s.params.is_empty() {
                    for p in &s.params {
                        out.push_str(&format!("    [\n        {}: default {}\n    ]\n", p.name, p.default_text));
                    }
                }
                if !s.doc.is_empty() {
                    out.push('\n');
                    for line in wrap_text(&s.doc, 68) {
                        out.push_str("        ");
                        out.push_str(&line);
                        out.push('\n');
                    }
                }
            }
        }
        out.trim_end().to_string()
    }

    pub fn signature_line(&self, s: &Signature) -> String {
        let mut parts: Vec<String> = s
            .args
            .iter()
            .map(|a| {
                let t = a.pat.describe(&self.types);
                format!("{}<{}> {}", if a.is_ref { "~" } else { "" }, t, a.name)
            })
            .collect();
        if s.variadic {
            parts.push("...".into());
        }
        let mut line = format!("({})", parts.join(", "));
        if let Some(r) = &s.returns {
            let rs: Vec<String> = r.iter().map(|t| t.describe(&self.types)).collect();
            line.push_str(&format!(" -> {}", rs.join(", ")));
        }
        line
    }
}

fn wrap_text(s: &str, width: usize) -> Vec<String> {
    let mut lines = Vec::new();
    let mut cur = String::new();
    for w in s.split_whitespace() {
        if !cur.is_empty() && cur.len() + 1 + w.len() > width {
            lines.push(std::mem::take(&mut cur));
        }
        if !cur.is_empty() {
            cur.push(' ');
        }
        cur.push_str(w);
    }
    if !cur.is_empty() {
        lines.push(cur);
    }
    lines
}

// ----- helpers for native implementations ----------------------------------

pub fn one(v: Value) -> RResult<Vec<Value>> {
    Ok(vec![v])
}

pub fn none() -> RResult<Vec<Value>> {
    Ok(Vec::new())
}

pub fn boolv(b: bool) -> RResult<Vec<Value>> {
    Ok(vec![Value::Bool(b)])
}

pub fn intv(i: Integer) -> RResult<Vec<Value>> {
    Ok(vec![Value::Int(i)])
}

impl CallArgs {
    pub fn int(&self, i: usize) -> RResult<&Integer> {
        match &self.args[i] {
            Value::Int(n) => Ok(n),
            other => Err(RuntimeError::runtime(format!("Argument {} must be an integer (got {})", i + 1, crate::value_kind(other)))),
        }
    }

    pub fn i64(&self, i: usize) -> RResult<i64> {
        self.int(i)?.to_i64().ok_or_else(|| RuntimeError::runtime(format!("Argument {} is too large", i + 1)))
    }

    pub fn usize(&self, i: usize) -> RResult<usize> {
        let n = self.int(i)?;
        if n.sign() < 0 {
            return Err(RuntimeError::runtime(format!("Argument {} must be non-negative", i + 1)));
        }
        n.to_u64().map(|v| v as usize).ok_or_else(|| RuntimeError::runtime(format!("Argument {} is too large", i + 1)))
    }

    pub fn str(&self, i: usize) -> RResult<&str> {
        match &self.args[i] {
            Value::Str(s) => Ok(s),
            other => Err(RuntimeError::runtime(format!("Argument {} must be a string (got {})", i + 1, crate::value_kind(other)))),
        }
    }

    pub fn bool(&self, i: usize) -> RResult<bool> {
        match &self.args[i] {
            Value::Bool(b) => Ok(*b),
            other => Err(RuntimeError::runtime(format!("Argument {} must be a boolean (got {})", i + 1, crate::value_kind(other)))),
        }
    }

    pub fn seq(&self, i: usize) -> RResult<&Rc<SeqEnum>> {
        match &self.args[i] {
            Value::Seq(s) => Ok(s),
            other => Err(RuntimeError::runtime(format!("Argument {} must be a sequence (got {})", i + 1, crate::value_kind(other)))),
        }
    }

    pub fn param_bool(&self, name: &str) -> RResult<bool> {
        match self.param(name) {
            Some(Value::Bool(b)) => Ok(*b),
            Some(_) => Err(RuntimeError::runtime(format!("Parameter '{name}' must be a boolean"))),
            None => Ok(false),
        }
    }
}

/// Register every built-in library.
pub fn register_all(it: &mut Interp) {
    core::register(it);
    ints::register(it);
    reals::register(it);
    strings::register(it);
    aggregates::register(it);
    maps::register(it);
    rings::register(it);
    io::register(it);
    env::register(it);
}
