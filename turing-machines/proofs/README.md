# Collatz proof sources have moved

The [12-state evaluator](../collatz/evaluator12/README.md) and
[16-state cycle detector](../collatz/cycle16/README.md) now keep their
machine-specific proofs with their machine packages. Common proof infrastructure
is stored once in [the Collatz family](../collatz/shared/README.md).

All 22 Lean source files are byte-identical to the original audited release.
The new build recipe assembles their original module layout:

```sh
python3 turing-machines/collatz/scripts/prepare_proofs.py --build --audit --kernel
```

Run that command from the repository root. The generated Lake workspace is
`turing-machines/collatz/.build/lean/`. [Migration details](../collatz/MIGRATION.md).
