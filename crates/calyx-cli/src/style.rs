//! Terminal colours for the interactive session.
//!
//! Colour is only used when standard output is a terminal, and never for
//! the values a program prints: it is applied to the prompt, the input being
//! edited, error reports, help text and the banner. Redirected output, log
//! files and piped sessions always get plain text, identical to Magma's.

use std::sync::atomic::{AtomicBool, Ordering};

use calyx_syntax::token::Kw;

pub const RESET: &str = "\x1b[0m";
pub const BOLD: &str = "\x1b[1m";
pub const DIM: &str = "\x1b[2m";
pub const COMMENT: &str = "\x1b[2;3m";
pub const ERROR: &str = "\x1b[1;31m";
pub const PROMPT: &str = "\x1b[1;32m";
pub const STRING: &str = "\x1b[33m";
pub const INTRINSIC: &str = "\x1b[34m";
pub const KEYWORD: &str = "\x1b[35m";
pub const NUMBER: &str = "\x1b[36m";
pub const TYPE: &str = "\x1b[36m";
pub const BRACKET: &str = "\x1b[1;4m";
pub const UNMATCHED: &str = "\x1b[1;31m";

static ENABLED: AtomicBool = AtomicBool::new(false);

/// Decide whether to use colour: only on a terminal, and never when the
/// user asked for none (`--no-color`, `NO_COLOR`, or a dumb terminal).
pub fn init(allowed: bool) {
    use std::io::IsTerminal;
    let no_color = std::env::var_os("NO_COLOR").is_some_and(|v| !v.is_empty());
    let dumb = std::env::var("TERM").is_ok_and(|t| t == "dumb");
    ENABLED.store(allowed && !no_color && !dumb && std::io::stdout().is_terminal(), Ordering::Relaxed);
}

pub fn enabled() -> bool {
    ENABLED.load(Ordering::Relaxed)
}

fn paint(out: &mut String, style: &str, text: &str) {
    out.push_str(style);
    out.push_str(text);
    out.push_str(RESET);
}

pub fn dim(text: &str) -> String {
    if enabled() { format!("{DIM}{text}{RESET}") } else { text.to_string() }
}

/// The lexical class of a piece of source text, as far as colouring cares.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Class {
    Keyword,
    Ident,
    Number,
    Str,
    /// A quoted intrinsic name such as `'+'`.
    Quoted,
    Comment,
    Punct,
    Space,
}

#[derive(Clone, Copy, Debug)]
pub struct Piece {
    pub start: usize,
    pub end: usize,
    pub class: Class,
}

/// Words that act as keywords when they open a constructor, as in
/// `func< x | x^2 >` or `rec< RF | a := 1 >`.
const CONSTRUCTORS: &[&str] =
    &["func", "proc", "rec", "recformat", "map", "pmap", "hom", "iso", "sub", "quo", "ext", "ideal", "lideal", "rideal", "ncl", "elt"];

/// Split source text into pieces for colouring. Unlike the real lexer this
/// never fails: unterminated strings and comments run to the end.
pub fn scan(src: &str) -> Vec<Piece> {
    let b = src.as_bytes();
    let n = b.len();
    let mut out = Vec::new();
    let mut i = 0;
    while i < n {
        let start = i;
        let c = b[i];
        let class = if c.is_ascii_whitespace() {
            while i < n && b[i].is_ascii_whitespace() {
                i += 1;
            }
            Class::Space
        } else if src[i..].starts_with("//") {
            i = src[i..].find('\n').map_or(n, |k| i + k);
            Class::Comment
        } else if src[i..].starts_with("/*") {
            i = src[i + 2..].find("*/").map_or(n, |k| i + 2 + k + 2);
            Class::Comment
        } else if c == b'"' {
            i += 1;
            while i < n && b[i] != b'"' {
                i += if b[i] == b'\\' { 2 } else { 1 };
            }
            i = (i + 1).min(n);
            Class::Str
        } else if c == b'\'' {
            i += 1;
            while i < n && b[i] != b'\'' && b[i] != b'\n' {
                i += 1;
            }
            if i < n && b[i] == b'\'' {
                i += 1;
            }
            Class::Quoted
        } else if c.is_ascii_digit() {
            while i < n && b[i].is_ascii_digit() {
                i += 1;
            }
            // A fraction, but not the `..` of a range.
            if i + 1 < n && b[i] == b'.' && b[i + 1].is_ascii_digit() {
                i += 1;
                while i < n && b[i].is_ascii_digit() {
                    i += 1;
                }
            }
            if i < n && (b[i] == b'e' || b[i] == b'E') {
                let sign = usize::from(i + 1 < n && (b[i + 1] == b'+' || b[i + 1] == b'-'));
                if i + 1 + sign < n && b[i + 1 + sign].is_ascii_digit() {
                    i += 1 + sign;
                    while i < n && b[i].is_ascii_digit() {
                        i += 1;
                    }
                }
            }
            Class::Number
        } else if c.is_ascii_alphabetic() || c == b'_' {
            while i < n && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                i += 1;
            }
            let word = &src[start..i];
            let opens = src[i..].trim_start().starts_with('<');
            if Kw::from_word(word).is_some() || (opens && CONSTRUCTORS.contains(&word)) { Class::Keyword } else { Class::Ident }
        } else if c == b'$' {
            i += 1;
            if i < n && b[i] == b'$' {
                i += 1;
            }
            while i < n && b[i].is_ascii_digit() {
                i += 1;
            }
            Class::Ident
        } else {
            i += src[i..].chars().next().map_or(1, char::len_utf8);
            Class::Punct
        };
        out.push(Piece { start, end: i, class });
    }
    out
}

/// For each bracket in `pieces`, the index of its partner (or `None` when
/// it is unmatched).
fn bracket_partners(src: &str, pieces: &[Piece]) -> Vec<Option<usize>> {
    let mut partner = vec![None; pieces.len()];
    let mut stack: Vec<(usize, u8)> = Vec::new();
    for (k, p) in pieces.iter().enumerate() {
        if p.class != Class::Punct {
            continue;
        }
        let c = src.as_bytes()[p.start];
        match c {
            b'(' | b'[' | b'{' => stack.push((k, c)),
            b')' | b']' | b'}' => {
                let open = match c {
                    b')' => b'(',
                    b']' => b'[',
                    _ => b'{',
                };
                if let Some(&(j, o)) = stack.last() {
                    if o == open {
                        stack.pop();
                        partner[k] = Some(j);
                        partner[j] = Some(k);
                    }
                }
            }
            _ => {}
        }
    }
    partner
}

fn is_bracket(src: &str, p: &Piece) -> bool {
    p.class == Class::Punct && matches!(src.as_bytes()[p.start], b'(' | b'[' | b'{' | b')' | b']' | b'}')
}

/// Colour Magma source. When `cursor` is given, the bracket next to it and
/// its partner are emphasised.
pub fn code(src: &str, cursor: Option<usize>, is_intrinsic: &dyn Fn(&str) -> bool) -> String {
    let pieces = scan(src);
    let partner = bracket_partners(src, &pieces);
    let mut emphasised = [None, None];
    if let Some(pos) = cursor {
        let at = |q: usize| pieces.iter().position(|p| p.start == q && is_bracket(src, p));
        let here = pos.checked_sub(1).and_then(at).or_else(|| at(pos));
        if let Some(k) = here {
            if let Some(j) = partner[k] {
                emphasised = [Some(k), Some(j)];
            }
        }
    }
    let mut out = String::with_capacity(src.len() * 2);
    for (k, p) in pieces.iter().enumerate() {
        let text = &src[p.start..p.end];
        let style = match p.class {
            Class::Keyword if text == "true" || text == "false" => NUMBER,
            Class::Keyword => KEYWORD,
            Class::Ident if is_intrinsic(text) => INTRINSIC,
            Class::Number => NUMBER,
            Class::Str => STRING,
            Class::Quoted => INTRINSIC,
            Class::Comment => COMMENT,
            Class::Punct if emphasised.contains(&Some(k)) => BRACKET,
            Class::Punct if is_bracket(src, p) && partner[k].is_none() && matches!(text, ")" | "]" | "}") => UNMATCHED,
            _ => "",
        };
        if style.is_empty() {
            out.push_str(text);
        } else {
            paint(&mut out, style, text);
        }
    }
    out
}

/// How many blocks and brackets are open at the end of `src`, for
/// indenting continuation lines.
pub fn depth(src: &str) -> usize {
    let pieces: Vec<Piece> = scan(src).into_iter().filter(|p| !matches!(p.class, Class::Space | Class::Comment)).collect();
    let mut depth: i64 = 0;
    let mut after_end = false;
    for (k, p) in pieces.iter().enumerate() {
        let text = &src[p.start..p.end];
        // The keyword after `end` (as in `end if`) does not open a block.
        if std::mem::take(&mut after_end) && p.class == Class::Keyword {
            continue;
        }
        match (p.class, text) {
            (Class::Keyword, "function" | "procedure" | "intrinsic" | "if" | "for" | "while" | "try" | "repeat") => depth += 1,
            (Class::Keyword, "case") if pieces.get(k + 1).is_none_or(|q| &src[q.start..q.end] != "<") => depth += 1,
            (Class::Keyword, "end") => {
                depth -= 1;
                after_end = true;
            }
            (Class::Keyword, "until") => depth -= 1,
            (Class::Punct, "(" | "[" | "{") => depth += 1,
            (Class::Punct, ")" | "]" | "}") => depth -= 1,
            _ => {}
        }
    }
    depth.max(0) as usize
}

/// Colour an error report produced by `Interp::format_error`.
pub fn error(text: &str, is_intrinsic: &dyn Fn(&str) -> bool) -> String {
    let mut out = String::new();
    for line in text.split_inclusive('\n') {
        let (body, nl) = match line.strip_suffix('\n') {
            Some(b) => (b, "\n"),
            None => (line, ""),
        };
        if body.starts_with("In file ") {
            paint(&mut out, DIM, body);
        } else if let Some(src) = body.strip_prefix(">> ") {
            paint(&mut out, DIM, ">>");
            out.push(' ');
            out.push_str(&code(src, None, is_intrinsic));
        } else if body.ends_with('^') && body[..body.len() - 1].chars().all(char::is_whitespace) {
            out.push_str(&body[..body.len() - 1]);
            paint(&mut out, ERROR, "^");
        } else if body.starts_with("Runtime error") || body.starts_with("User error") {
            match body.split_once(": ") {
                Some((label, msg)) => {
                    paint(&mut out, ERROR, &format!("{label}:"));
                    out.push(' ');
                    out.push_str(msg);
                }
                None => paint(&mut out, ERROR, body),
            }
        } else if body == "[Interrupted]" {
            paint(&mut out, ERROR, body);
        } else {
            out.push_str(body);
        }
        out.push_str(nl);
    }
    out
}

/// Colour a signature line such as `(<RngIntElt> x, ~<SeqEnum> S) -> BoolElt`.
fn signature(line: &str, out: &mut String) {
    let mut depth = 0;
    let mut rest = line;
    while let Some(c) = rest.chars().next() {
        if depth == 0 && rest.starts_with("->") {
            paint(out, DIM, "->");
            paint(out, TYPE, &rest[2..]);
            return;
        }
        match c {
            '<' => {
                depth += 1;
                if depth == 1 {
                    paint(out, DIM, "<");
                    out.push_str(TYPE);
                } else {
                    out.push(c);
                }
            }
            '>' if depth > 0 => {
                depth -= 1;
                if depth == 0 {
                    out.push_str(RESET);
                    paint(out, DIM, ">");
                } else {
                    out.push(c);
                }
            }
            '~' if depth == 0 => paint(out, KEYWORD, "~"),
            _ => out.push(c),
        }
        rest = &rest[c.len_utf8()..];
    }
    if depth > 0 {
        out.push_str(RESET);
    }
}

/// Colour the output of `?Name`.
pub fn help(text: &str) -> String {
    let mut out = String::new();
    let mut similar = false;
    for line in text.split_inclusive('\n') {
        let (body, nl) = match line.strip_suffix('\n') {
            Some(b) => (b, "\n"),
            None => (line, ""),
        };
        if let Some(name) = body.strip_prefix("Intrinsic '").and_then(|s| s.strip_suffix('\'')) {
            paint(&mut out, DIM, "Intrinsic ");
            out.push('\'');
            paint(&mut out, &format!("{BOLD}{INTRINSIC}"), name);
            out.push('\'');
        } else if body == "Signatures:" {
            paint(&mut out, BOLD, body);
        } else if let Some(sig) = body.strip_prefix("    (") {
            out.push_str("    ");
            signature(&format!("({sig}"), &mut out);
        } else if body == "    [" || body == "    ]" {
            paint(&mut out, DIM, body);
        } else if body.ends_with("Similar names:") {
            similar = true;
            out.push_str(body);
        } else if similar && body.starts_with("  ") {
            out.push_str("  ");
            paint(&mut out, INTRINSIC, body.trim_start());
        } else {
            out.push_str(body);
        }
        out.push_str(nl);
    }
    out
}

/// The start-up banner.
pub fn banner(version: &str, seed: u64) -> String {
    if !enabled() {
        return format!("calyx {version} - free computer algebra, Magma language     [Seed = {seed}]\nType ? for help.  Type <Ctrl>-D to quit.\n");
    }
    let sep = format!(" {DIM}·{RESET} ");
    format!(
        "\n {PROMPT}✿{RESET} {BOLD}calyx{RESET} {DIM}{version}{RESET}{sep}free computer algebra{sep}Magma language\n   \
         {DIM}Seed = {seed}{RESET}{sep}{BOLD}?Name{RESET} help{sep}{BOLD}Tab{RESET} complete{sep}{BOLD}Ctrl-D{RESET} quit\n\n"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn classes(src: &str) -> Vec<(&str, Class)> {
        scan(src).into_iter().filter(|p| p.class != Class::Space).map(|p| (&src[p.start..p.end], p.class)).collect()
    }

    #[test]
    fn scans_magma_source() {
        use Class::*;
        assert_eq!(
            classes(r#"x := [1..10] cat "a\"b"; // done"#),
            vec![
                ("x", Ident),
                (":", Punct),
                ("=", Punct),
                ("[", Punct),
                ("1", Number),
                (".", Punct),
                (".", Punct),
                ("10", Number),
                ("]", Punct),
                ("cat", Keyword),
                (r#""a\"b""#, Str),
                (";", Punct),
                ("// done", Comment),
            ]
        );
        assert_eq!(classes("f := func< x | 2.5e-3 >;")[3..5], [("func", Keyword), ("<", Punct)]);
        assert_eq!(classes("func := 1;")[0], ("func", Ident));
        assert!(classes("2.5e-3").iter().all(|&(_, c)| c == Number));
        assert_eq!(classes("'+' $$ $1"), vec![("'+'", Quoted), ("$$", Ident), ("$1", Ident)]);
        assert_eq!(classes("\"open"), vec![("\"open", Str)]);
    }

    #[test]
    fn depth_counts_blocks_and_brackets() {
        assert_eq!(depth("function f(x)"), 1);
        assert_eq!(depth("function f(x)\n if x then"), 2);
        assert_eq!(depth("function f(x)\n if x then\n return 1;\n end if;"), 1);
        assert_eq!(depth("f := func< x | x >; S := [ 1,"), 1);
        assert_eq!(depth("case x:\n when 1: y := 2;"), 1);
        assert_eq!(depth("repeat x +:= 1; until x gt 3;"), 0);
        assert_eq!(depth("end if; end if;"), 0);
    }

    #[test]
    fn highlights_matching_brackets() {
        let plain = |_: &str| false;
        let s = code("f(g(x))", Some(7), &plain);
        assert_eq!(s.matches(BRACKET).count(), 2);
        assert!(s.starts_with("f\x1b[1;4m(\x1b[0m"));
        assert!(code("x)", None, &plain).contains(UNMATCHED));
    }
}
