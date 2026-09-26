# Working on calyx

calyx is a free, clean-room reimplementation of the Magma computer algebra
system in Rust (GPL-3.0-or-later), built on FLINT. It follows the Magma
handbook part by part: Parts I (the language) and II (sets, sequences and
mappings) are largely done, and Part III (Basic Rings) is in progress (see
`docs/ROADMAP.md`). Open work lives in the
GitHub issues of `aygerix/calyx-math`, labelled by area, kind and priority,
with one milestone per handbook part.

## Ground rules

- **Clean room.** Never read the Magma package sources (the `.m` files
  shipped with Magma). The handbook and black-box runs of Magma are fine,
  and handbook example code may be used verbatim in tests.
- **Current Magma is the reference.** Expected test output comes from Magma
  2.29 (the public calculator). Magma 2.22 on the reference VM is for
  exploration and benchmarks only; never record its output as expected
  output. Where the handbook's examples disagree with current Magma, follow
  current Magma.
- **Speed.** The aim is to beat Magma, not match it. Choose representations
  for speed from the start (elements on FLINT's native types, machine-word
  fast paths). Benchmark against Magma on the VM, where both run on the
  same machine; timings on a Mac are not comparable.
- **Evaluator boundary (#47).** Built-in intrinsics never touch `Frame` or
  the IR; they work through `CallArgs`, `Vals` and call-backs.
- **Bounded experiments.** Every loop in an exploratory script needs a hard
  bound. Run local probes that might run away under
  `~/calyx-tools/guard.py` (macOS enforces no memory limit; an unbounded
  script once brought the machine down).
- calyx reads standard input in file mode: run probes as
  `target/release/calyx -b < probe.m`, never with a file argument and an
  open terminal.

## Build, test, style

- `cargo build --release`; `cargo test --release` runs the unit tests,
  the compat tests and the golden tests.
- Never run `cargo fmt` on the tree. The code is formatted by hand in a
  compact style up to 160 columns; match the surrounding code, including
  its comment density.
- Commit messages: a short subject, then bullets saying what changed and
  why, wrapped at 72 columns.

## Tests

- `crates/calyx-cli/tests/compat/NAME.m` with `NAME.out` recorded from
  Magma 2.29; see the README there.
- `crates/calyx-cli/tests/compat/pending/`: scripts checked against 2.22
  that still need 2.29 output (#24). The coordinator records them when the
  calculator is available; only the coordinator uses the calculator.
- `crates/calyx-cli/tests/scripts/`: self-blessed golden tests (hash-order
  output, files and packages, calyx extensions).

## Reference tools (local, not in the repo)

`~/calyx-tools/` holds `mref.sh FILE` (run a script with Magma 2.22 on the
VM), `mdiff.sh FILE` (diff this worktree's release build against 2.22),
`mbench.sh FILE` (build this worktree on the VM and time it against 2.22,
best of three), `vtest.sh` (run this worktree's `cargo test --release` on
the VM) and `guard.py`. See `~/calyx-tools/README.md`. Magma runs share the
VM freely; a benchmark waits for sole use of it.

The Mac has 16 GB shared by every session: build locally for quick probes
and diffs, but run the full test suite with `vtest.sh`.

## Parallel lanes (Part III)

Several sessions work at once, each in its own worktree and branch:

| Lane | Branch | Issues, in order | Owns |
| --- | --- | --- | --- |
| Polynomials | `lane/polynomials` | #40, #34, then #41, #35 | `intrinsics/upoly.rs`, `intrinsics/mpoly.rs` |
| Finite fields | `lane/finite-fields` | #39, then #43 | `intrinsics/finite_fields.rs`, `intrinsics/nearfields.rs` |
| Reals | `lane/reals` | #42 | `intrinsics/reals.rs`, `intrinsics/complex.rs` |
| Rationals and integers | `lane/rationals` | #38, then #6, #5, #25 | `intrinsics/rationals.rs`, the integer modules |
| Coordinator | `rust` | merging, #26, #33, #49, #50, #24 | `docs/ROADMAP.md`, parser and evaluator |

- Commit and push only your lane branch; never push to `rust`. The
  coordinator merges lanes into `rust`.
- New intrinsics go in your lane's modules, which are already registered in
  `intrinsics/mod.rs`. New types go in your lane's block at the end of the
  two tables in `types.rs`.
- Keep edits to shared files (`value.rs`, `print.rs`, `ops.rs`,
  `coerce.rs`, `rings/`) small and self-contained, and ask for them to be
  merged early rather than carried for days. Parser and evaluator changes
  go through the coordinator.
- Don't edit `docs/ROADMAP.md`; the coordinator updates it on merge.
- Put your tests in your own files: `compat/pending/<chapter>_*.m`.
- To hand over work: rebase on `origin/rust`, make sure
  `cargo test --release` passes, push your branch, and tell the user what is
  ready to merge and which issues it closes.
