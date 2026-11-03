# Shared certified Collatz proof infrastructure

The common arithmetic, whole-tape model, abstract evaluator/search specifications,
bridge lemmas and full-environment audit are stored once in [proofs](proofs/).
Machine-specific sources are owned by the [12-state](../evaluator12/proofs/README.md)
and [16-state](../cycle16/proofs/README.md) packages.

This is the same 22-file Lean environment as before the reorganization. The
[provenance map](../PROVENANCE.json) gives each original module name, canonical
source path, and unchanged SHA-256. The [import inventory](../proofs/IMPORTS.json)
records every import. [Arithmetic.lean](proofs/Arithmetic.lean) retains the
upstream proof attribution; see [family attribution](../ATTRIBUTION.md).

Use the [family verification recipe](../README.md#verify-locally). The assembler
copies exact sources into `.build/lean/` without changing declarations or imports.
The common aggregate audit intentionally covers both certified machines. It does
not certify the separate 17-state machine.
