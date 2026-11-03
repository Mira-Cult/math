# Layout-migration validation

Date: 2026-11-03. This report concerns the directory reorganization, not a new
proof of Collatz. The pre-migration public snapshot is
`334212df64a1d7c3d0f4b1227b882d15e9c85166`.

## Checks completed during preparation

- All 22 Lean source SHA-256 values match the existing provenance manifest.
  Every moved Lean file also reuses its original Git blob, so no Lean source
  bytes, declarations or imports changed.
- Original Lean import inventory and internal module closure match the new
  canonical-path map.
- All three `.tm` files are byte-identical to their previous public versions.
  Compatibility copies at the old raw-table paths remain byte-identical.
- The 17-state Python and C++ checker files retain their original Git blobs.
  Its ordinary proof text changes only in navigation links; its source manifest
  records the new navigation and local-attribution hashes.
- Relative Markdown file/directory targets and named heading anchors in the
  new or edited documentation were checked against the proposed repository tree.
- An independent JavaScript replay of the literal 12- and 16-state tables passed
  all 65,535 evaluator inputs (2,250,093 transitions) and 5,049 canonical
  cycle-detector inputs (6,745,714 transitions). The 16-state halt branch also
  checked its entire tape and exact head position. These are bounded checks,
  not substitutes for the unchanged all-input Lean proofs.
- The Collatz polygon attribution link was updated to the new machine package;
  its source manifest and SHA256SUMS were refreshed for that documentation edit.

## Runtime checks to reproduce

The new Python assembler and a fresh Lean build/audit/kernel replay were not
executed in the connector-only preparation environment. Byte identity is not
reported as a fresh Lean run. Run from the repository root:

```sh
python3 turing-machines/collatz/scripts/check_release.py
python3 turing-machines/collatz/scripts/prepare_proofs.py --build --audit --kernel
python3 turing-machines/collatz/scripts/verify_finite.py
python3 turing-machines/collatz/beeping17/machine.py
python3 -O turing-machines/collatz/beeping17/machine.py
python3 turing-machines/collatz/beeping17/independent_check.py
(cd tilings/collatz-30 && sha256sum -c SHA256SUMS)
```

The old 17-state C++ and Python release results remain historical results in
its [source manifest](beeping17/SOURCE.json); this migration does not label those
recorded runs as freshly executed.
