use crate::span::{FileId, Span};
use crate::token::{Kw, Tok, Token};

/// An on-demand tokenizer for Magma source text.
///
/// A backslash immediately followed by a newline is a line continuation and
/// is removed before tokenization, so it may even split a token in two.
pub struct Lexer<'a> {
    src: &'a str,
    file: FileId,
    /// Characters with their byte offsets, continuations removed.
    chars: Vec<(usize, char)>,
    pos: usize,
}

const WORD_OPS: &[&str] = &["join", "meet", "diff", "sdiff", "cat", "div", "mod", "and", "or", "xor"];

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str, file: FileId) -> Lexer<'a> {
        let raw: Vec<(usize, char)> = src.char_indices().collect();
        let mut chars = Vec::with_capacity(raw.len());
        let mut i = 0;
        while i < raw.len() {
            if raw[i].1 == '\\' {
                if raw.get(i + 1).map(|c| c.1) == Some('\n') {
                    i += 2;
                    continue;
                }
                if raw.get(i + 1).map(|c| c.1) == Some('\r') && raw.get(i + 2).map(|c| c.1) == Some('\n') {
                    i += 3;
                    continue;
                }
            }
            chars.push(raw[i]);
            i += 1;
        }
        Lexer { src, file, chars, pos: 0 }
    }

    pub fn source(&self) -> &'a str {
        self.src
    }

    fn peek(&self, k: usize) -> Option<char> {
        self.chars.get(self.pos + k).map(|c| c.1)
    }

    fn offset(&self) -> usize {
        self.chars.get(self.pos).map(|c| c.0).unwrap_or(self.src.len())
    }

    fn span_from(&self, start: usize) -> Span {
        Span::new(self.file, start, self.offset())
    }

    /// Move the lexer to the given byte offset (used after raw scans).
    pub fn seek(&mut self, offset: usize) {
        self.pos = self.chars.partition_point(|c| c.0 < offset);
    }

    /// Read raw text from the current position up to (not including) an
    /// unescaped `close` character; `\close` yields a literal `close`.
    /// Returns `None` if the input ends first.
    pub fn raw_until(&mut self, close: char) -> Option<String> {
        let mut out = String::new();
        while let Some(c) = self.peek(0) {
            if c == '\\' && self.peek(1) == Some(close) {
                out.push(close);
                self.pos += 2;
                continue;
            }
            self.pos += 1;
            if c == close {
                return Some(out);
            }
            out.push(c);
        }
        None
    }

    fn skip_trivia(&mut self) -> Option<Token> {
        loop {
            match self.peek(0) {
                Some(c) if c.is_whitespace() => self.pos += 1,
                Some('/') if self.peek(1) == Some('/') => {
                    while let Some(c) = self.peek(0) {
                        if c == '\n' {
                            break;
                        }
                        self.pos += 1;
                    }
                }
                Some('/') if self.peek(1) == Some('*') => {
                    let start = self.offset();
                    self.pos += 2;
                    loop {
                        match self.peek(0) {
                            None => {
                                return Some(Token {
                                    tok: Tok::Unterminated("unterminated comment".into()),
                                    span: self.span_from(start),
                                });
                            }
                            Some('*') if self.peek(1) == Some('/') => {
                                self.pos += 2;
                                break;
                            }
                            _ => self.pos += 1,
                        }
                    }
                }
                _ => return None,
            }
        }
    }

    pub fn next_token(&mut self) -> Token {
        if let Some(t) = self.skip_trivia() {
            return t;
        }
        let start = self.offset();
        let Some(c) = self.peek(0) else {
            return Token { tok: Tok::Eof, span: Span::new(self.file, start, start) };
        };
        let tok = if c.is_ascii_digit() {
            self.number()
        } else if c.is_alphabetic() || c == '_' {
            self.word()
        } else if c == '"' {
            self.string()
        } else if c == '\'' {
            self.quoted_ident()
        } else {
            self.punct()
        };
        Token { tok, span: self.span_from(start) }
    }

    fn number(&mut self) -> Tok {
        let mut s = String::new();
        if self.peek(0) == Some('0') && self.peek(1) == Some('x') && self.peek(2).is_some_and(|c| c.is_ascii_hexdigit()) {
            self.pos += 2;
            s.push_str("0x");
            while let Some(c) = self.peek(0).filter(|c| c.is_ascii_hexdigit()) {
                s.push(c);
                self.pos += 1;
            }
            return Tok::Int(s);
        }
        while let Some(c) = self.peek(0).filter(|c| c.is_ascii_digit()) {
            s.push(c);
            self.pos += 1;
        }
        let mut real = false;
        if self.peek(0) == Some('.') && self.peek(1) != Some('.') && !self.peek(1).is_some_and(|c| c.is_alphabetic() || c == '_') {
            real = true;
            s.push('.');
            self.pos += 1;
            while let Some(c) = self.peek(0).filter(|c| c.is_ascii_digit()) {
                s.push(c);
                self.pos += 1;
            }
        }
        if matches!(self.peek(0), Some('e' | 'E')) {
            let sign = matches!(self.peek(1), Some('+' | '-'));
            let d = if sign { self.peek(2) } else { self.peek(1) };
            if d.is_some_and(|c| c.is_ascii_digit()) {
                real = true;
                s.push('e');
                self.pos += 1;
                if sign {
                    s.push(self.peek(0).unwrap());
                    self.pos += 1;
                }
                while let Some(c) = self.peek(0).filter(|c| c.is_ascii_digit()) {
                    s.push(c);
                    self.pos += 1;
                }
            }
        }
        // A precision suffix makes a real with that many decimal digits: 1.5p10, 1p10.
        if let Some(p @ ('p' | 'P')) = self.peek(0).filter(|_| self.peek(1).is_some_and(|c| c.is_ascii_digit())) {
            real = true;
            s.push(p);
            self.pos += 1;
            while let Some(c) = self.peek(0).filter(|c| c.is_ascii_digit()) {
                s.push(c);
                self.pos += 1;
            }
        }
        if real { Tok::Real(s) } else { Tok::Int(s) }
    }

    fn word(&mut self) -> Tok {
        let mut s = String::new();
        while let Some(c) = self.peek(0).filter(|c| c.is_alphanumeric() || *c == '_') {
            s.push(c);
            self.pos += 1;
        }
        if s == "_" {
            return Tok::Underscore;
        }
        if WORD_OPS.contains(&s.as_str()) && self.peek(0) == Some(':') && self.peek(1) == Some('=') {
            self.pos += 2;
            return Tok::OpAssign(s);
        }
        match Kw::from_word(&s) {
            Some(k) => Tok::Kw(k),
            None => Tok::Ident(s),
        }
    }

    fn string(&mut self) -> Tok {
        self.pos += 1;
        let mut s = String::new();
        loop {
            match self.peek(0) {
                None => return Tok::Unterminated("unterminated string".into()),
                Some('"') => {
                    self.pos += 1;
                    return Tok::Str(s);
                }
                Some('\\') => {
                    let e = self.peek(1);
                    self.pos += 2;
                    match e {
                        Some('n') => s.push('\n'),
                        Some('t') => s.push('\t'),
                        Some('r') => s.push('\r'),
                        Some('"') => s.push('"'),
                        Some('\\') => s.push('\\'),
                        Some(c) => {
                            s.push('\\');
                            s.push(c);
                        }
                        None => return Tok::Unterminated("unterminated string".into()),
                    }
                }
                Some(c) => {
                    s.push(c);
                    self.pos += 1;
                }
            }
        }
    }

    fn quoted_ident(&mut self) -> Tok {
        self.pos += 1;
        let mut s = String::new();
        loop {
            match self.peek(0) {
                None | Some('\n') => return Tok::Error("unterminated quoted name".into()),
                Some('\'') => {
                    self.pos += 1;
                    return if s.is_empty() { Tok::Error("empty quoted name".into()) } else { Tok::Ident(s) };
                }
                Some(c) => {
                    s.push(c);
                    self.pos += 1;
                }
            }
        }
    }

    fn punct(&mut self) -> Tok {
        let c = self.peek(0).unwrap();
        let n1 = self.peek(1);
        let n2 = self.peek(2);
        let (tok, len) = match c {
            ':' => match (n1, n2) {
                (Some('='), _) => (Tok::Assign, 2),
                (Some('-'), Some('>')) => (Tok::MapsTo, 3),
                _ => (Tok::Colon, 1),
            },
            '-' => match (n1, n2) {
                (Some('>'), _) => (Tok::Arrow, 2),
                (Some(':'), Some('=')) => (Tok::OpAssign("-".into()), 3),
                _ => (Tok::Minus, 1),
            },
            '+' => match (n1, n2) {
                (Some(':'), Some('=')) => (Tok::OpAssign("+".into()), 3),
                _ => (Tok::Plus, 1),
            },
            '*' => match (n1, n2) {
                (Some(':'), Some('=')) => (Tok::OpAssign("*".into()), 3),
                (Some('}'), _) => (Tok::StarRBrace, 2),
                (Some(']'), _) => (Tok::StarRBrack, 2),
                _ => (Tok::Star, 1),
            },
            '/' => match (n1, n2) {
                (Some(':'), Some('=')) => (Tok::OpAssign("/".into()), 3),
                _ => (Tok::Slash, 1),
            },
            '^' => match (n1, n2) {
                (Some(':'), Some('=')) => (Tok::OpAssign("^".into()), 3),
                (Some('^'), _) => (Tok::CaretCaret, 2),
                _ => (Tok::Caret, 1),
            },
            '!' => match n1 {
                Some('!') => (Tok::BangBang, 2),
                Some('}') => (Tok::BangRBrace, 2),
                Some(']') => (Tok::BangRBrack, 2),
                _ => (Tok::Bang, 1),
            },
            '@' => match n1 {
                Some('@') => (Tok::AtAt, 2),
                Some('}') => (Tok::AtRBrace, 2),
                _ => (Tok::At, 1),
            },
            '{' => match n1 {
                Some('@') => (Tok::LBraceAt, 2),
                Some('*') => (Tok::LBraceStar, 2),
                Some('!') => (Tok::LBraceBang, 2),
                _ => (Tok::LBrace, 1),
            },
            '[' => match n1 {
                Some('*') => (Tok::LBrackStar, 2),
                Some('!') => (Tok::LBrackBang, 2),
                _ => (Tok::LBrack, 1),
            },
            '.' => match (n1, n2) {
                (Some('.'), Some('.')) => (Tok::Ellipsis, 3),
                (Some('.'), _) => (Tok::DotDot, 2),
                _ => (Tok::Dot, 1),
            },
            '$' => {
                if n1 == Some('$') {
                    (Tok::DollarDollar, 2)
                } else if n1.is_some_and(|c| c.is_ascii_digit()) {
                    self.pos += 1;
                    let mut d = String::new();
                    while let Some(c) = self.peek(0).filter(|c| c.is_ascii_digit()) {
                        d.push(c);
                        self.pos += 1;
                    }
                    return match d.parse() {
                        Ok(n) => Tok::Dollar(n),
                        Err(_) => Tok::Error("bad $ reference".into()),
                    };
                } else {
                    // The structure of a constructor, as in quo< P | $.1 >.
                    (Tok::Ident("$".into()), 1)
                }
            }
            '`' => match n1 {
                Some('`') => (Tok::DoubleBackquote, 2),
                _ => (Tok::Backquote, 1),
            },
            '(' => (Tok::LParen, 1),
            ')' => (Tok::RParen, 1),
            ']' => (Tok::RBrack, 1),
            '}' => (Tok::RBrace, 1),
            '<' => (Tok::Lt, 1),
            '>' => (Tok::Gt, 1),
            ',' => (Tok::Comma, 1),
            ';' => (Tok::Semi, 1),
            '#' => (Tok::Hash, 1),
            '~' => (Tok::Tilde, 1),
            '|' => (Tok::Pipe, 1),
            '&' => (Tok::Amp, 1),
            '=' => (Tok::Equals, 1),
            '?' => (Tok::Question, 1),
            // `\[ 1, 2, 3 ]` is a literal integer sequence.
            '\\' if n1 == Some('[') => (Tok::LBrack, 2),
            other => (Tok::Error(format!("unexpected character '{other}'")), 1),
        };
        self.pos += len;
        tok
    }
}

/// Tokenize a whole string (mainly for tests and tooling).
pub fn tokenize(src: &str) -> Vec<Tok> {
    let mut lx = Lexer::new(src, FileId(0));
    let mut out = Vec::new();
    loop {
        let t = lx.next_token();
        let done = t.tok == Tok::Eof;
        out.push(t.tok);
        if done {
            break;
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_tokens() {
        let t = tokenize("x := [1..10 by 2]; y +:= 3.5e-2; S join:= {@ 1 @};");
        assert_eq!(
            t,
            vec![
                Tok::Ident("x".into()),
                Tok::Assign,
                Tok::LBrack,
                Tok::Int("1".into()),
                Tok::DotDot,
                Tok::Int("10".into()),
                Tok::Kw(Kw::By),
                Tok::Int("2".into()),
                Tok::RBrack,
                Tok::Semi,
                Tok::Ident("y".into()),
                Tok::OpAssign("+".into()),
                Tok::Real("3.5e-2".into()),
                Tok::Semi,
                Tok::Ident("S".into()),
                Tok::OpAssign("join".into()),
                Tok::LBraceAt,
                Tok::Int("1".into()),
                Tok::AtRBrace,
                Tok::Semi,
                Tok::Eof
            ]
        );
    }

    #[test]
    fn continuation_joins_tokens() {
        assert_eq!(tokenize("12\\\n34"), vec![Tok::Int("1234".into()), Tok::Eof]);
    }

    #[test]
    fn real_literals_with_a_precision() {
        let t = tokenize("1.5p10 1p10 12345e-4P8 2p x.p1");
        let real = |s: &str| Tok::Real(s.into());
        assert_eq!(t[..4], [real("1.5p10"), real("1p10"), real("12345e-4P8"), Tok::Int("2".into())]);
        assert_eq!(t[4], Tok::Ident("p".into()));
    }

    #[test]
    fn comments_strings_and_quoted_names() {
        let t = tokenize("/* c */ '+' // x\n \"a\\n\\\"b\" $1 $$ S.1 map<x :-> y>");
        assert_eq!(
            t,
            vec![
                Tok::Ident("+".into()),
                Tok::Str("a\n\"b".into()),
                Tok::Dollar(1),
                Tok::DollarDollar,
                Tok::Ident("S".into()),
                Tok::Dot,
                Tok::Int("1".into()),
                Tok::Ident("map".into()),
                Tok::Lt,
                Tok::Ident("x".into()),
                Tok::MapsTo,
                Tok::Ident("y".into()),
                Tok::Gt,
                Tok::Eof
            ]
        );
    }
}
