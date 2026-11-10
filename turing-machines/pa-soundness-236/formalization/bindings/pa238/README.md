# Retained finite Hilbert proof-generator input

[NumericHilbert238.v.txt](NumericHilbert238.v.txt) is an unchanged 65,420-byte
reference copy of `PA/m238/coq/logic/NumericHilbert238.v` from the recovered
local PA238 source snapshot. Its SHA-256 is
`fd577e5737cfa733c924bb832d2742ab7ead223c3837a27956c97d0076401223`.
The original header and provenance notices are preserved. Full snapshot,
historical revision and unavailable-object details are in
[source-baselines.md](../../source-baselines.md#required-pa238-dependency-closure).

This single file makes the [textual generator](../../code/generate_compact_hilbert_basis.py)
reproducible from the published checkout without requiring the wider archive.
The generator extracts a dependency closure of 97 explicit finite proof schemas.
Its [Lean output](../../lean/PASoundness/CompactHilbertBasis.lean) is checked
independently against the actual compact axiom and modus-ponens constructors.
The reference is not imported by Lean, and no Coq compilation or `coqchk` replay
is claimed. This is neither a delivery of the complete historical dependency
closure nor a change to the six original machine/source bindings.
