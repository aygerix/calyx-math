/// Identifies a source text (a file, a REPL input, an `eval` string, ...).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct FileId(pub u32);

/// A byte range in a source text.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct Span {
    pub file: FileId,
    pub lo: u32,
    pub hi: u32,
}

impl Span {
    pub fn new(file: FileId, lo: usize, hi: usize) -> Span {
        Span { file, lo: lo as u32, hi: hi as u32 }
    }

    /// The smallest span covering both `self` and `other`.
    pub fn to(self, other: Span) -> Span {
        Span { file: self.file, lo: self.lo.min(other.lo), hi: self.hi.max(other.hi) }
    }
}

/// A named source text with precomputed line starts for position lookup.
#[derive(Clone, Debug)]
pub struct SourceFile {
    pub name: String,
    pub text: String,
    line_starts: Vec<usize>,
}

impl SourceFile {
    pub fn new(name: impl Into<String>, text: impl Into<String>) -> SourceFile {
        let text = text.into();
        let mut line_starts = vec![0];
        line_starts.extend(text.match_indices('\n').map(|(i, _)| i + 1));
        SourceFile { name: name.into(), text, line_starts }
    }

    /// Zero-based line index and zero-based column (in characters) of `offset`.
    pub fn line_col(&self, offset: usize) -> (usize, usize) {
        let offset = offset.min(self.text.len());
        let line = match self.line_starts.binary_search(&offset) {
            Ok(i) => i,
            Err(i) => i - 1,
        };
        let start = self.line_starts[line];
        let col = self.text[start..offset].chars().count();
        (line, col)
    }

    /// The text of the zero-based line `line`, without its newline.
    pub fn line_text(&self, line: usize) -> &str {
        let start = self.line_starts.get(line).copied().unwrap_or(self.text.len());
        let end = self.line_starts.get(line + 1).map(|e| e - 1).unwrap_or(self.text.len());
        self.text[start..end.max(start)].trim_end_matches('\r')
    }
}
