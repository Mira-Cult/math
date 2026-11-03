# Collatz machine family

Each machine has one package containing its writeup, exact table, proof material,
provenance, attribution, and verification instructions. The three statements are
different reductions; none asserts the Collatz conjecture.

| Machine | Exact scope | Proof status |
| --- | --- | --- |
| [12-state evaluator](evaluator12/README.md) | On an encoded positive input, halts exactly when its ordinary Collatz orbit reaches 1. | Lean-certified |
| [16-state cycle detector](cycle16/README.md) | From blank tape, halts exactly when a nontrivial positive ordinary Collatz cycle exists. It does not detect nonperiodic divergence. | Lean-certified |
| [17-state beeper](beeping17/README.md) | From blank tape, beeps infinitely often exactly when every positive orbit reaches 1. | Ordinary mathematical proof and finite checks; no Lean certificate |

## Verify locally

Install the pinned Lean toolchain `leanprover/lean4:v4.30.0` using
[elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
python3 turing-machines/collatz/scripts/check_release.py
python3 turing-machines/collatz/scripts/prepare_proofs.py --build --audit --kernel
```

The Lake package has no third-party dependencies. The imported standard
library comes with Lean 4.30.0. `leanchecker --fresh` replays the complete
imported environment through the same Lean kernel; it is not an external
proof assistant. No CI workflows are included.

`Audit.lean` prints exact theorem types and transitive axiom dependencies.
The final equivalences depend only on Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. There are no proof placeholders or new
axioms in their dependency closures. Both concrete machine specifications
are proved, so no macro-specification hypotheses remain in the final results.

The tape model is the complete function `Int → Bool`, with finite support
proved for canonical inputs and preserved through finite runs. `Reaches`
combines exact configuration equality with exclusion of every earlier halt.
`TableAudit.lean` reconstructs the exact strings from the actual transition
functions and proves that the unique halt transitions are L0 and O0.

Optional independent finite corroboration, from the repository root:

```sh
python3 turing-machines/collatz/scripts/verify_finite.py
```

This checks 65,535 evaluator inputs and 5,049 canonical cycle-detector inputs.
These finite checks do not replace the general proofs.


The assembler creates `turing-machines/collatz/.build/lean/`, which is ignored
by Git. It copies the 22 audited source files into their original module names,
plus the unchanged Lake configuration and import inventory. The machine-specific
sources live in their individual packages; the common modules and audit live in
[shared/proofs](shared/README.md). No proof source is generated or rewritten.

For separate commands after preparation:

```sh
cd turing-machines/collatz/.build/lean
lake build
lake env lean Audit.lean
lake env leanchecker --fresh CollatzTM
```

## Source identity and attribution

All 22 Lean source files retain the exact bytes and SHA-256 values recorded in
[PROVENANCE.json](PROVENANCE.json), from source snapshot
`b6c17e92bb9f0f4ba070190e17e17a24fe789ec6`. The snapshot is a
proof-development identifier, not an ancestor of this public repository.
The manifest maps original module names to canonical source paths. The check
script verifies this map, the import inventory, exact tables, and toolchain.
The 17-state package has its own [source manifest](beeping17/SOURCE.json).

See [family attribution](ATTRIBUTION.md) and each machine's local attribution.
[Migration notes](MIGRATION.md) explain the old paths and compatibility files.

[Back to all Turing-machine families](../README.md).
