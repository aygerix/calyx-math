# Pending compatibility tests

Scripts here are waiting for their expected output from Magma 2.29 (the
public calculator). The compatibility test only reads the directory above,
so these are not run yet.

To promote one, record its output and move both files up. Run the
calculator client from the reference VM rather than a development machine:

```sh
python3 tools/magma-calc.py < crates/calyx-cli/tests/compat/pending/NAME.m > crates/calyx-cli/tests/compat/NAME.out
git mv crates/calyx-cli/tests/compat/pending/NAME.m crates/calyx-cli/tests/compat/
```
