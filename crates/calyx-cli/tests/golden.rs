//! Golden tests: each `tests/scripts/NAME.m` is fed to `calyx` on standard
//! input and its output compared with `NAME.out`.
//!
//! Set `CALYX_BLESS=1` to (re)write the expected outputs.

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

#[test]
fn golden_scripts() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/scripts");
    let bless = std::env::var("CALYX_BLESS").is_ok();
    let mut scripts: Vec<PathBuf> = std::fs::read_dir(&dir).unwrap().map(|e| e.unwrap().path()).filter(|p| p.extension().is_some_and(|e| e == "m")).collect();
    scripts.sort();
    assert!(!scripts.is_empty(), "no scripts found");
    let mut failures = Vec::new();
    for script in &scripts {
        let got = run_script(&dir, script);
        let expected_path = script.with_extension("out");
        if bless {
            std::fs::write(&expected_path, &got).unwrap();
            continue;
        }
        let expected = std::fs::read_to_string(&expected_path).unwrap_or_default();
        if got != expected {
            let name = script.file_name().unwrap().to_string_lossy().to_string();
            let diff = first_difference(&expected, &got);
            failures.push(format!("{name}: {diff}"));
        }
    }
    assert!(failures.is_empty(), "golden output mismatches:\n{}", failures.join("\n"));
}

fn first_difference(expected: &str, got: &str) -> String {
    let e: Vec<&str> = expected.lines().collect();
    let g: Vec<&str> = got.lines().collect();
    for i in 0..e.len().max(g.len()) {
        let (a, b) = (e.get(i).copied().unwrap_or("<eof>"), g.get(i).copied().unwrap_or("<eof>"));
        if a != b {
            return format!("line {}:\n  expected: {a}\n  got:      {b}", i + 1);
        }
    }
    "outputs differ in trailing whitespace".to_string()
}
