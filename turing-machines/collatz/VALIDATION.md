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
  At the time, compatibility copies at the old raw-table paths were also
  byte-identical; the later [migration note](MIGRATION.md#earlier-links-and-commands)
  records removal of the redundant 17-state copy.
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

## Independent checkout validation

A separate checkout of published commit
`a99d7fd47768a2566340faf54ca38aa0f24d2c3c` ran the following checks:

- `check_release.py`: PASS, including all canonical sources, provenance,
  compatibility tables and beeper hashes.
- `prepare_proofs.py`: PASS, materialized the exact 22-file original module layout.
- `verify_finite.py`: PASS, 65,535 evaluator and 5,049 cycle-detector cases.
- `beeping17/machine.py`: PASS, 2,079 macro cases in both normal and `-O` modes.
- `beeping17/independent_check.py`: PASS, 1,807 cases and 47,399,744 transitions.
- `tilings/collatz-30/SHA256SUMS`: every entry passed.

The fresh Lean build stopped before execution because `lake` was unavailable.
No new Lean build, axiom-audit execution or kernel replay is claimed. The
unchanged source-byte identities preserve the previously published audited
sources, but do not replace a fresh toolchain run.

## Reproduce the runtime checks

Run from the repository root with the pinned Lean toolchain available:

```sh
python3 turing-machines/collatz/scripts/check_release.py
python3 turing-machines/collatz/scripts/prepare_proofs.py --build --audit --kernel
python3 turing-machines/collatz/scripts/verify_finite.py
python3 turing-machines/collatz/beeping17/machine.py
python3 -O turing-machines/collatz/beeping17/machine.py
python3 turing-machines/collatz/beeping17/independent_check.py
(cd tilings/collatz-30 && sha256sum -c SHA256SUMS)
```

The 17-state C++ macro/blank-trace results remain historical results in its
[source manifest](beeping17/SOURCE.json); the C++ executable was not rerun for
this migration. The Python results above were independently rerun.
