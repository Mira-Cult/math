# Machine-specific Lean proof

These are the byte-identical source files for this machine from audited snapshot
`b6c17e92bb9f0f4ba070190e17e17a24fe789ec6`:

- [Machine16.lean](Machine16.lean)
- [Sixteen.lean](Sixteen.lean)
- [SixteenEntry.lean](SixteenEntry.lean)
- [SixteenEven.lean](SixteenEven.lean)
- [SixteenMain.lean](SixteenMain.lean)
- [SixteenOdd.lean](SixteenOdd.lean)
- [SixteenRebuild.lean](SixteenRebuild.lean)

Their original module names are recorded in [the local provenance](../PROVENANCE.json).
They depend on the [shared arithmetic and tape library](../../shared/README.md).
The common aggregate audit also imports the other certified machine so the
original 22-file environment can be replayed unchanged.

Run [the family build recipe](../../README.md#verify-locally). It assembles the
original module layout without modifying any Lean source. The all-input proof
is in the Lean sources; finite simulations are only corroboration.
