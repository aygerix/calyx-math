//! The tree-walking interpreter.

pub mod assign;
mod call;
mod eval;
mod iter;
mod stmt;

use std::collections::VecDeque;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

use calyx_syntax::{FileId, SourceFile, Span};
use rustc_hash::{FxHashMap, FxHashSet};

pub use assign::seq_index;
pub use call::CallArgs;
pub use iter::ValueIter;

use crate::error::{ErrKind, RResult, RuntimeError, TraceFrame};
use crate::intrinsics::IntrinsicTable;
use crate::ir::{FuncCode, Slot};
use crate::output::Output;
use crate::random::Rng;
use crate::sym::Sym;
use crate::types::TypeRegistry;
use crate::value::Value;

/// Control flow out of a statement.
pub enum Flow {
    Normal,
    Break(Option<Sym>),
    Continue(Option<Sym>),
    Return(Vec<Value>),
}

/// The activation record of a running function or top-level unit.
pub struct Frame {
    pub slots: Vec<Value>,
    pub captures: Rc<[Value]>,
    /// The closure being executed (for `$$`).
    pub self_fn: Option<Value>,
    pub code: Option<Rc<FuncCode>>,
    /// Number of results the caller asked for (for `Nresults`).
    pub nresults: usize,
}

impl Frame {
    pub fn new(n_slots: u32) -> Frame {
        Frame { slots: vec![Value::Undef; n_slots as usize], captures: Rc::from(Vec::new()), self_fn: None, code: None, nresults: 1 }
    }

    #[inline]
    pub fn get(&self, s: Slot) -> &Value {
        &self.slots[s as usize]
    }

    #[inline]
    pub fn set(&mut self, s: Slot, v: Value) {
        self.slots[s as usize] = v;
    }
}

/// A package file that has been attached (or imported).
pub struct Package {
    pub path: PathBuf,
    pub globals: FxHashMap<Sym, Value>,
    pub mtime: Option<std::time::SystemTime>,
}

/// The whole interpreter state.
pub struct Interp {
    pub types: TypeRegistry,
    pub globals: FxHashMap<Sym, Value>,
    pub forwards: FxHashSet<Sym>,
    pub intrinsics: IntrinsicTable,
    pub out: Output,
    pub previous: VecDeque<Vec<Value>>,
    pub previous_size: usize,
    pub rng: Rng,
    /// Primes given to `StoreFactor`, tried first by `Factorization`.
    pub stored_factors: Vec<calyx_flint::Integer>,
    /// `RngInt`CunninghamStorageLimit`.
    pub cunningham_storage_limit: i64,
    pub verbose: FxHashMap<Rc<str>, (i64, i64)>,
    pub assertions: i64,
    pub sources: Vec<Rc<SourceFile>>,
    pub trace: Vec<TraceFrame>,
    pub depth: usize,
    pub max_depth: usize,
    /// Results requested from each active user function (for `Nresults`).
    pub nresults_stack: Vec<usize>,
    /// Partial results of enclosing sequence constructors (for `Self`).
    pub self_seqs: Vec<Vec<Value>>,
    /// Variables visible to `eval` code, innermost last.
    pub eval_env: Vec<FxHashMap<Sym, Value>>,
    pub interrupt: Arc<AtomicBool>,
    pub start: Instant,
    pub packages: Vec<Package>,
    /// Globals of the package currently being loaded, if any.
    pub package_stack: Vec<FxHashMap<Sym, Value>>,
    pub quit: Option<i32>,
    pub show_real_time: bool,
    pub indent_level: usize,
    pub indent_width: usize,
    pub search_path: Vec<PathBuf>,
    pub echo_input: bool,
    pub quit_on_error: bool,
    pub script_args: Vec<String>,
    pub script_name: String,
    pub history: Vec<String>,
    pub prompt: String,
    pub file_stack: Vec<PathBuf>,
    pub profile: bool,
    pub warn_override: bool,
    /// Pending standard-input lines for `read` (used when not interactive).
    pub input_lines: VecDeque<String>,
    pub read_line_hook: Option<Box<dyn FnMut(&str) -> Option<String>>>,
    /// Canonical rings (residue class rings, finite fields, ...).
    pub rings: crate::rings::RingCache,
    /// The symmetric groups, one per degree.
    pub groups: crate::perms::GroupCache,
    /// The identifier a function is being called through.
    pub pending_call_name: Option<String>,
}

impl Interp {
    pub fn new() -> Interp {
        let types = TypeRegistry::new();
        let mut it = Interp {
            intrinsics: IntrinsicTable::new(),
            types,
            globals: FxHashMap::default(),
            forwards: FxHashSet::default(),
            out: Output::stdout(),
            previous: VecDeque::new(),
            previous_size: 3,
            rng: Rng::from_time(),
            stored_factors: Vec::new(),
            cunningham_storage_limit: 50,
            verbose: FxHashMap::default(),
            assertions: 1,
            sources: Vec::new(),
            trace: Vec::new(),
            depth: 0,
            max_depth: 20_000,
            nresults_stack: Vec::new(),
            self_seqs: Vec::new(),
            eval_env: Vec::new(),
            interrupt: Arc::new(AtomicBool::new(false)),
            start: Instant::now(),
            packages: Vec::new(),
            package_stack: Vec::new(),
            quit: None,
            show_real_time: false,
            indent_level: 0,
            indent_width: 4,
            search_path: Vec::new(),
            echo_input: false,
            quit_on_error: false,
            script_args: Vec::new(),
            script_name: String::new(),
            history: Vec::new(),
            prompt: "> ".to_string(),
            file_stack: Vec::new(),
            profile: false,
            warn_override: false,
            input_lines: VecDeque::new(),
            read_line_hook: None,
            rings: Default::default(),
            groups: Default::default(),
            pending_call_name: None,
        };
        crate::intrinsics::register_all(&mut it);
        it
    }

    /// Register a source text so spans into it can be reported.
    pub fn add_source(&mut self, name: &str, text: &str) -> FileId {
        let id = FileId(self.sources.len() as u32);
        self.sources.push(Rc::new(SourceFile::new(name, text)));
        id
    }

    pub fn source(&self, id: FileId) -> Option<Rc<SourceFile>> {
        self.sources.get(id.0 as usize).cloned()
    }

    #[inline]
    pub fn check_interrupt(&self) -> RResult<()> {
        if self.interrupt.load(Ordering::Relaxed) {
            self.interrupt.store(false, Ordering::Relaxed);
            return Err(RuntimeError::interrupt());
        }
        Ok(())
    }

    /// The global value of `name`, falling back to intrinsics and types.
    pub fn lookup_global(&self, name: Sym) -> Option<Value> {
        for env in self.eval_env.iter().rev() {
            if let Some(v) = env.get(&name) {
                return Some(v.clone());
            }
        }
        if let Some(pkg) = self.package_stack.last() {
            if let Some(v) = pkg.get(&name) {
                return Some(v.clone());
            }
        }
        if let Some(v) = self.globals.get(&name) {
            if !v.is_undef() {
                return Some(v.clone());
            }
        }
        self.builtin_value(name)
    }

    /// The value an unassigned identifier denotes: an intrinsic or a type.
    pub fn builtin_value(&self, name: Sym) -> Option<Value> {
        if self.intrinsics.contains(name) {
            return Some(Value::Intr(name));
        }
        let s = name.as_rc();
        self.types.lookup(&s).map(Value::Cat)
    }

    pub fn set_global(&mut self, name: Sym, v: Value) {
        if let Some(pkg) = self.package_stack.last_mut() {
            pkg.insert(name, v);
            return;
        }
        self.globals.insert(name, v);
    }

    pub fn unassigned_error(&self, name: Sym) -> RuntimeError {
        let declared = self.package_stack.last().map_or(false, |p| p.contains_key(&name)) || self.globals.contains_key(&name);
        if declared {
            RuntimeError::user(format!("Identifier '{name}' has not been assigned"))
        } else {
            RuntimeError::user(format!("Identifier '{name}' has not been declared or assigned"))
        }
    }

    /// Record a value list in the previous-value buffer (`$1`, ...).
    pub fn push_previous(&mut self, vals: Vec<Value>) {
        if self.previous_size == 0 {
            return;
        }
        self.previous.push_front(vals);
        while self.previous.len() > self.previous_size {
            self.previous.pop_back();
        }
    }

    /// Run a compiled top-level unit.
    pub fn run_unit(&mut self, code: &Rc<FuncCode>) -> RResult<Flow> {
        let mut frame = Frame::new(code.n_slots);
        frame.code = Some(code.clone());
        match &code.body {
            crate::ir::Body::Block(stmts) => self.exec_block(stmts, &mut frame),
            crate::ir::Body::Expr(e) => {
                let v = self.eval(e, &mut frame)?;
                Ok(Flow::Return(vec![v]))
            }
        }
    }

    /// Attach the error position and a trace frame to an error.
    pub fn locate(&self, mut e: RuntimeError, span: Span) -> RuntimeError {
        if e.span.is_none() && !e.at_caller {
            e.span = Some(span);
        }
        e
    }

    pub fn user_error(msg: impl Into<String>) -> RuntimeError {
        RuntimeError { kind: ErrKind::User, ..RuntimeError::runtime(msg) }
    }
}

impl Default for Interp {
    fn default() -> Self {
        Interp::new()
    }
}
