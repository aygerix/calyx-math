//! Output sinks: standard output, redirection to files, and capture.

use std::fs::File;
use std::io::Write;

pub enum SinkKind {
    Stdout,
    File(File),
    Capture(String),
}

pub struct Sink {
    pub kind: SinkKind,
    /// Column of the next character on the current line.
    pub col: usize,
}

pub struct Output {
    stack: Vec<Sink>,
    pub columns: usize,
    pub auto_columns: bool,
    pub log: Option<File>,
}

impl Output {
    pub fn stdout() -> Output {
        Output { stack: vec![Sink { kind: SinkKind::Stdout, col: 0 }], columns: 80, auto_columns: false, log: None }
    }

    /// Discard all output (useful for tests of side effects).
    pub fn capture_all() -> Output {
        Output { stack: vec![Sink { kind: SinkKind::Capture(String::new()), col: 0 }], columns: 80, auto_columns: false, log: None }
    }

    pub fn col(&self) -> usize {
        self.stack.last().map(|s| s.col).unwrap_or(0)
    }

    /// Whether lines have no width limit (`SetColumns(0)`).
    pub fn unlimited(&self) -> bool {
        self.columns > 1_000_000
    }

    pub fn write(&mut self, s: &str) {
        self.write_styled(s, None);
    }

    /// Write `s`, showing `styled` instead (the same text with terminal
    /// escape codes) when the output goes to standard output. Files, captures
    /// and the log always receive the plain text.
    pub fn write_styled(&mut self, s: &str, styled: Option<&str>) {
        if s.is_empty() {
            return;
        }
        let top = self.stack.last_mut().unwrap();
        match &mut top.kind {
            SinkKind::Stdout => {
                let mut out = std::io::stdout().lock();
                let _ = out.write_all(styled.unwrap_or(s).as_bytes());
            }
            SinkKind::File(f) => {
                let _ = f.write_all(s.as_bytes());
            }
            SinkKind::Capture(buf) => buf.push_str(s),
        }
        match s.rfind('\n') {
            Some(i) => top.col = s[i + 1..].chars().count(),
            None => top.col += s.chars().count(),
        }
        let is_primary = self.stack.len() == 1;
        if is_primary {
            if let Some(log) = &mut self.log {
                let _ = log.write_all(s.as_bytes());
            }
        }
    }

    pub fn flush(&mut self) {
        let _ = std::io::stdout().flush();
        if let Some(Sink { kind: SinkKind::File(f), .. }) = self.stack.last_mut() {
            let _ = f.flush();
        }
    }

    /// Start a new line if the current one is not empty.
    pub fn ensure_newline(&mut self) {
        if self.col() != 0 {
            self.write("\n");
        }
    }

    pub fn begin_capture(&mut self) {
        self.stack.push(Sink { kind: SinkKind::Capture(String::new()), col: 0 });
    }

    pub fn end_capture(&mut self) -> String {
        match self.stack.pop() {
            Some(Sink { kind: SinkKind::Capture(s), .. }) => s,
            Some(other) => {
                self.stack.push(other);
                String::new()
            }
            None => String::new(),
        }
    }

    /// Take everything captured by the base sink (for `capture_all`).
    pub fn take_captured(&mut self) -> String {
        match &mut self.stack[0].kind {
            SinkKind::Capture(s) => std::mem::take(s),
            _ => String::new(),
        }
    }

    pub fn redirect_to_file(&mut self, f: File) {
        // Replace an existing redirection rather than nesting.
        self.unredirect();
        self.stack.push(Sink { kind: SinkKind::File(f), col: 0 });
    }

    pub fn unredirect(&mut self) -> bool {
        if let Some(pos) = self.stack.iter().rposition(|s| matches!(s.kind, SinkKind::File(_))) {
            if pos > 0 {
                self.stack.remove(pos);
                return true;
            }
        }
        false
    }

    pub fn has_redirect(&self) -> bool {
        self.stack.iter().any(|s| matches!(s.kind, SinkKind::File(_)))
    }
}
