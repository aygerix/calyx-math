//! Line editing for the interactive session: syntax colouring, completion
//! of names, history hints, and multi-line input with automatic indentation.

use std::borrow::Cow::{self, Borrowed, Owned};
use std::cell::Cell;
use std::collections::HashSet;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use calyx_runtime::Interp;
use calyx_syntax::FileId;
use calyx_syntax::token::KEYWORDS;
use rustyline::completion::{Completer, FilenameCompleter, Pair};
use rustyline::highlight::{CmdKind, Highlighter};
use rustyline::hint::{Hinter, HistoryHinter};
use rustyline::validate::Validator;
use rustyline::{Cmd, ConditionalEventHandler, Context, Event, EventContext, Helper, KeyCode, KeyEvent, RepeatCount};

use crate::style;

/// A rewrite of the input asked for by a key handler: replace the text from
/// the given offset to the cursor. Key handlers can only return a single
/// command, so they request a completion and the completer performs the
/// rewrite, which leaves the cursor after the new text.
pub type Rewrite = Arc<Mutex<Option<(usize, String)>>>;

pub struct CalyxHelper {
    color: bool,
    rewrite: Rewrite,
    intrinsics: HashSet<String>,
    /// Intrinsic names and keywords, sorted, for completion.
    words: Vec<String>,
    /// Assigned global identifiers, refreshed before each prompt.
    globals: Vec<String>,
    hinter: HistoryHinter,
    files: FilenameCompleter,
    /// Whether the next redraw should emphasise matching brackets (not on
    /// the final redraw of an accepted line).
    brackets: Cell<bool>,
}

impl CalyxHelper {
    pub fn new(color: bool, rewrite: Rewrite) -> CalyxHelper {
        CalyxHelper {
            color,
            rewrite,
            intrinsics: HashSet::new(),
            words: Vec::new(),
            globals: Vec::new(),
            hinter: HistoryHinter::new(),
            files: FilenameCompleter::new(),
            brackets: Cell::new(false),
        }
    }

    /// Pick up intrinsics and identifiers defined since the last prompt.
    pub fn refresh(&mut self, it: &Interp) {
        if it.intrinsics.names().count() != self.intrinsics.len() {
            self.intrinsics = it.intrinsics.names().map(|s| s.as_str()).collect();
            self.words = self.intrinsics.iter().cloned().chain(KEYWORDS.iter().map(|k| k.to_string())).collect();
            self.words.sort_unstable();
            self.words.dedup();
        }
        self.globals = it.globals.iter().filter(|(_, v)| !v.is_undef()).map(|(k, _)| k.as_str()).collect();
    }
}

/// Is `pos` inside a string literal of `line`?
fn in_string(line: &str, pos: usize) -> bool {
    style::scan(line).iter().any(|p| {
        let closed = p.end - p.start >= 2 && line.as_bytes()[p.end - 1] == b'"';
        p.class == style::Class::Str && p.start < pos && (pos < p.end || !closed)
    })
}

impl Completer for CalyxHelper {
    type Candidate = Pair;

    fn complete(&self, line: &str, pos: usize, _ctx: &Context<'_>) -> rustyline::Result<(usize, Vec<Pair>)> {
        if let Some((start, text)) = self.rewrite.lock().unwrap().take() {
            return Ok((start, vec![Pair { display: text.clone(), replacement: text }]));
        }
        // File names inside strings, as in `load "..."` or `Attach("...")`.
        if in_string(line, pos) {
            return self.files.complete_path(line, pos);
        }
        let start = line[..pos].char_indices().rev().find(|&(_, c)| !(c.is_ascii_alphanumeric() || c == '_')).map_or(0, |(i, c)| i + c.len_utf8());
        let prefix = &line[start..pos];
        if prefix.is_empty() || prefix.starts_with(|c: char| c.is_ascii_digit()) {
            return Ok((pos, Vec::new()));
        }
        let mut names: Vec<&String> = self.words.iter().chain(&self.globals).filter(|w| w.starts_with(prefix)).collect();
        names.sort_unstable();
        names.dedup();
        Ok((start, names.into_iter().map(|n| Pair { display: n.clone(), replacement: n.clone() }).collect()))
    }
}

impl Hinter for CalyxHelper {
    type Hint = String;

    fn hint(&self, line: &str, pos: usize, ctx: &Context<'_>) -> Option<String> {
        self.hinter.hint(line, pos, ctx)
    }
}

impl Highlighter for CalyxHelper {
    fn highlight<'l>(&self, line: &'l str, pos: usize) -> Cow<'l, str> {
        if !self.color {
            return Borrowed(line);
        }
        let cursor = self.brackets.get().then_some(pos);
        Owned(style::code(line, cursor, &|w| self.intrinsics.contains(w)))
    }

    fn highlight_prompt<'b, 's: 'b, 'p: 'b>(&'s self, prompt: &'p str, default: bool) -> Cow<'b, str> {
        if self.color && default { Owned(format!("{}{prompt}{}", style::PROMPT, style::RESET)) } else { Borrowed(prompt) }
    }

    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        if self.color { Owned(format!("{}{hint}{}", style::DIM, style::RESET)) } else { Borrowed(hint) }
    }

    fn highlight_char(&self, _line: &str, _pos: usize, kind: CmdKind) -> bool {
        self.brackets.set(kind != CmdKind::ForcedRefresh);
        self.color
    }
}

impl Validator for CalyxHelper {}

impl Helper for CalyxHelper {}

/// Does `src` need more lines before it can run?
pub fn needs_more(src: &str) -> bool {
    let t = src.trim_start();
    if t.is_empty() || t.starts_with('?') {
        return false;
    }
    matches!(calyx_syntax::parse_program(src, FileId(0)), Err(e) if e.incomplete)
}

/// Enter runs the input when it is complete, and otherwise starts a new,
/// indented line in the same input so the whole statement can be edited
/// and recalled from history as one entry.
pub struct EnterHandler {
    pub prompt_width: Arc<AtomicUsize>,
}

impl ConditionalEventHandler for EnterHandler {
    fn handle(&self, _evt: &Event, _n: RepeatCount, _positive: bool, ctx: &EventContext) -> Option<Cmd> {
        let line = ctx.line();
        if !needs_more(line) {
            return None;
        }
        let indent = self.prompt_width.load(Ordering::Relaxed) + 4 * style::depth(&line[..ctx.pos()]);
        Some(Cmd::Insert(1, format!("\n{}", " ".repeat(indent))))
    }
}

/// Words that close or continue a block, and so line up with its opening.
const CLOSERS: &[&str] = &["end", "else", "elif", "until", "catch"];

/// The keys that complete a word of `CLOSERS`.
pub const CLOSER_KEYS: &[char] = &['d', 'e', 'f', 'l', 'h'];

/// Typing the last letter of `end`, `else`, ... at the start of a
/// continuation line moves the line back to the level of its block.
pub struct DedentHandler {
    pub prompt_width: Arc<AtomicUsize>,
    pub rewrite: Rewrite,
}

impl ConditionalEventHandler for DedentHandler {
    fn handle(&self, evt: &Event, n: RepeatCount, _positive: bool, ctx: &EventContext) -> Option<Cmd> {
        let Some(KeyEvent(KeyCode::Char(c), _)) = evt.get(0) else { return None };
        let line = ctx.line();
        if n != 1 || ctx.pos() != line.len() {
            return None;
        }
        let start = line.rfind('\n')? + 1;
        let current = format!("{}{c}", &line[start..]);
        let word = current.trim_start();
        if !CLOSERS.contains(&word) {
            return None;
        }
        let indent = self.prompt_width.load(Ordering::Relaxed) + 4 * style::depth(&line[..start]).saturating_sub(1);
        if current.len() - word.len() <= indent {
            return None;
        }
        *self.rewrite.lock().unwrap() = Some((start, format!("{}{word}", " ".repeat(indent))));
        Some(Cmd::Complete)
    }
}
