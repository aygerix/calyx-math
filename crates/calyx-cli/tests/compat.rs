//! Compatibility tests: each `tests/compat/NAME.m` is run by `calyx` and its
//! output compared with `NAME.out`, which is the output of real Magma for
//! the same script (see `tests/compat/README.md`).
//!
//! Magma's web calculator strips trailing whitespace from lines, so lines
//! are compared without it, and trailing blank lines are ignored.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn run_script(dir: &Path, script: &Path) -> String {
    let input = std::fs::read(script).unwrap();
    let mut child = Command::new(env!("CARGO_BIN_EXE_calyx"))
        .args(["-b", "-S", "1"])
        .current_dir(dir)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to run calyx");
    child.stdin.take().unwrap().write_all(&input).unwrap();
    let out = child.wait_with_output().unwrap();
    let mut s = String::from_utf8_lossy(&out.stdout).to_string();
    s.push_str(&String::from_utf8_lossy(&out.stderr));
    s
}

fn normalize(text: &str) -> Vec<String> {
    let mut lines: Vec<String> = text.lines().map(|l| l.trim_end().to_string()).collect();
    while lines.last().is_some_and(|l| l.is_empty()) {
        lines.pop();
    }
    lines
}

#[test]
fn magma_compatibility() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/compat");
    let mut scripts: Vec<PathBuf> = std::fs::read_dir(&dir).unwrap().map(|e| e.unwrap().path()).filter(|p| p.extension().is_some_and(|e| e == "m")).collect();
    scripts.sort();
    assert!(!scripts.is_empty(), "no scripts found");
    let mut failures = Vec::new();
    for script in &scripts {
        let expected = std::fs::read_to_string(script.with_extension("out")).expect("missing expected output");
        let (e, g) = (normalize(&expected), normalize(&run_script(&dir, script)));
        if e != g {
            let i = (0..e.len().max(g.len())).find(|&i| e.get(i) != g.get(i)).unwrap();
            let name = script.file_name().unwrap().to_string_lossy();
            let show = |v: &Vec<String>| v.get(i).cloned().unwrap_or_else(|| "<eof>".into());
            failures.push(format!("{name}: line {}:\n  magma: {}\n  calyx: {}", i + 1, show(&e), show(&g)));
        }
    }
    assert!(failures.is_empty(), "differences from Magma:\n{}", failures.join("\n"));
}
