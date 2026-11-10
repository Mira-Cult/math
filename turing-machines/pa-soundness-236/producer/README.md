# Original M236 producer

The `problems/` subtree contains the 45 original source, input and license files
needed by the selected `FusedBeam` producer, copied unchanged from
Mira-Cult/math-wip commit `bad500e2d22c3f8b7c6420f5c5b1a504a6a57b30`.
Original relative paths are retained for imports and frozen grammar plans.
Their identities are in [../SOURCE-MANIFEST.json](../SOURCE-MANIFEST.json).

The selected machine is the full-blank-tape `boot/quotient` variant.
`FusedBeam` uses the repeated-address `CleanBoundaries` schedule and composes
paid grammar rebinding with output-event fusion. No grammar-search rerun is
needed: the two fixed plan inputs are included. Other builder outputs are not
interchangeable with this table.

## Reproduce the table and graph

Use Python 3.12. From the package directory (this directory's parent):

```sh
work=$(mktemp -d)
PYTHONDONTWRITEBYTECODE=1 python3 \
  producer/problems/pa-full-soundness/experiments/pa266-architecture-20261031/fused_beam.py \
  --out "$work/generated"
cmp machine.tm "$work/generated/boot/quotient/machine.tm"
cmp raw.tm "$work/generated/boot/raw/machine.tm"
PYTHONDONTWRITEBYTECODE=1 python3 \
  formalization/code/reproduce_m236_occurrence_graph.py \
  --producer-root producer --check
```

The output directory must not already exist. Generated variants, metadata,
caches and binaries belong in temporary storage, not in this source packet.
The selected quotient has 236 states and 472 rows; its raw parent has 237 states
and 474 rows. The occurrence graph has 760 rows and 1,036 edges.
See [../VERIFICATION.md](../VERIFICATION.md) for actual reproduction results.

These are conventional reproducibility checks. Lean separately checks the fixed
table, graph and semantic simulations, without a general Python compiler
correctness assumption. The retained vendor license applies to its vendor code;
this publication adds no project-wide license.
