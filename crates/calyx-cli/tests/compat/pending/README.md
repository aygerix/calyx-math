# Pending compatibility tests

Scripts here are waiting for their expected output from Magma 2.29 (the
public calculator). The compatibility test only reads the directory above,
so these are not run yet.

To promote one, record its output with the calculator client and move
both files up:

```sh
python3 tools/magma-calc.py < crates/calyx-cli/tests/compat/pending/NAME.m > crates/calyx-cli/tests/compat/NAME.out
git mv crates/calyx-cli/tests/compat/pending/NAME.m crates/calyx-cli/tests/compat/
```
