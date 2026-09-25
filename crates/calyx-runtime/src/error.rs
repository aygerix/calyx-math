//! Runtime errors.

use calyx_syntax::Span;

use crate::value::Value;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrKind {
    /// Raised by `error`, `require`, `assert`, or unassigned identifiers.
    User,
    /// Raised by the system (bad arguments, division by zero, ...).
    Runtime,
    /// A syntax error in code being compiled or loaded.
    Syntax,
    /// The computation was interrupted.
    Interrupt,
}

/// A frame of the call stack at the time an error was raised.
#[derive(Clone, Debug)]
pub struct TraceFrame {
    pub name: String,
    pub span: Option<Span>,
    /// Parameter names and their printed values.
    pub args: Vec<(String, String)>,
}

/// How an error is reported.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrStyle {
    /// `Runtime error in 'Gcd': ...`, from intrinsics and operators.
    Normal,
    /// `Runtime error in assert: ...`: raised by a statement.
    Statement,
    /// `Runtime error: ...` with no source position (the `error` statement).
    Bare,
    /// Just the printed error object (`error Error(x)`).
    Object,
    /// Like `Normal` but without the blank line after the report (failed
    /// coercions).
    Plain,
}

#[derive(Clone)]
pub struct RuntimeError {
    pub kind: ErrKind,
    /// The intrinsic or operator in which the error arose (`'Gcd'`, `'/'`).
    pub context: Option<String>,
    pub message: String,
    /// Where the error is reported.
    pub span: Option<Span>,
    /// Calls that were active, innermost first.
    pub trace: Vec<TraceFrame>,
    /// The user object passed to `error` (for `e`Object`).
    pub object: Option<Value>,
    /// Report the error at the call site of the current function
    /// (for `require` in intrinsics).
    pub at_caller: bool,
    pub style: ErrStyle,
    /// For errors in `eval` code: where the `eval` is, and whether the error
    /// arose while reading the code (rather than running it).
    pub eval_outer: Option<(Span, bool)>,
}

impl RuntimeError {
    pub fn runtime(message: impl Into<String>) -> RuntimeError {
        RuntimeError { kind: ErrKind::Runtime, context: None, message: message.into(), span: None, trace: Vec::new(), object: None, at_caller: false, style: ErrStyle::Normal, eval_outer: None }
    }

    pub fn user(message: impl Into<String>) -> RuntimeError {
        RuntimeError { kind: ErrKind::User, ..RuntimeError::runtime(message) }
    }

    pub fn interrupt() -> RuntimeError {
        RuntimeError { kind: ErrKind::Interrupt, ..RuntimeError::runtime("Interrupted") }
    }

    pub fn in_context(mut self, ctx: impl Into<String>) -> RuntimeError {
        if self.context.is_none() {
            self.context = Some(ctx.into());
        }
        self
    }

    pub fn at(mut self, span: Span) -> RuntimeError {
        if self.span.is_none() && !self.at_caller {
            self.span = Some(span);
        }
        self
    }

    /// An error raised by a statement such as `assert` (reported as
    /// `Runtime error in assert: ...`).
    pub fn statement(ctx: &str, message: impl Into<String>) -> RuntimeError {
        RuntimeError { context: Some(ctx.to_string()), style: ErrStyle::Statement, ..RuntimeError::runtime(message) }
    }

    /// Whether the report ends with an extra blank line (errors raised by
    /// intrinsics and operators).
    pub fn trailing_blank(&self) -> bool {
        self.kind == ErrKind::Runtime && self.style == ErrStyle::Normal && self.context.as_deref().is_none_or(|c| context_style(c).2)
    }

    /// The headline, e.g. `Runtime error in 'Gcd': Bad argument types`.
    pub fn headline(&self) -> String {
        let label = match self.kind {
            ErrKind::User => "User error",
            ErrKind::Runtime => "Runtime error",
            ErrKind::Syntax => "User error",
            ErrKind::Interrupt => "Interrupted",
        };
        if self.kind == ErrKind::Interrupt {
            return "[Interrupted]".to_string();
        }
        match self.style {
            ErrStyle::Bare => return format!("Runtime error: {}", self.message),
            ErrStyle::Object => return self.message.clone(),
            ErrStyle::Statement => {
                if let Some(c) = &self.context {
                    return format!("{label} in {c}: {}", self.message);
                }
            }
            ErrStyle::Normal | ErrStyle::Plain => {}
        }
        match &self.context {
            Some(c) => {
                let (name, quoted, _) = context_style(c);
                if quoted { format!("{label} in '{name}': {}", self.message) } else { format!("{label} in {name}: {}", self.message) }
            }
            None => format!("{label}: {}", self.message),
        }
    }
}

impl std::fmt::Debug for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.headline())
    }
}

pub type RResult<T> = Result<T, RuntimeError>;

/// Shorthand for returning a runtime error.
pub fn rt_err<T>(msg: impl Into<String>) -> RResult<T> {
    Err(RuntimeError::runtime(msg))
}

pub fn user_err<T>(msg: impl Into<String>) -> RResult<T> {
    Err(RuntimeError::user(msg))
}

/// How Magma names an error context: the name, whether it is quoted, and
/// whether a blank line follows the report. Intrinsics and operators are
/// quoted; constructions of the language are not.
pub fn context_style(ctx: &str) -> (&str, bool, bool) {
    match ctx {
        "@" => ("map application", false, true),
        "map< >" => ("map< ... >", false, true),
        "rec< >" => ("rec< ... >", false, true),
        "`" => ("`", false, true),
        "{ }" | "{ ... }" => ("{ ... }", false, true),
        "[ ]" | "[ ... ]" => ("[ ... ]", false, true),
        "{@ @}" => ("{@ ... @}", false, true),
        "{* *}" => ("{* ... *}", false, true),
        "sequence construction" => ("sequence construction", false, false),
        "[]:=" => (":=", false, false),
        _ => (ctx, true, true),
    }
}
