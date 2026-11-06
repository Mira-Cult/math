# Machine-package layout migration

The 2026-11-03 reorganization groups [related Collatz machines](README.md) while
keeping each writeup, provenance, attribution, exact table and machine-specific
proof with its own machine. Shared Lean infrastructure is stored once.

## What did not change

- Every one of the 22 Lean source files has its original bytes and SHA-256.
- All three machine files have their original bytes.
- The 17-state machine's Python and C++ checker code is byte-identical.
- The mathematical claims and proof status are unchanged.
- Git history is retained; no history was rewritten and no license was changed.

## Build layout

The old monolithic Lean source directory is split into the individual machines'
`proofs/` directories and `shared/proofs/`. [PROVENANCE.json](PROVENANCE.json)
records the original module names, new canonical paths and original hashes.
The [assembler](scripts/prepare_proofs.py) copies the verified source bytes into
`.build/lean/`, preserving the original module paths, Lake project and audit.
There are no tracked symlinks, duplicate canonical proofs or generated build
products. Run the [new verification commands](README.md#verify-locally).

## Earlier links and commands

The 2026-11-03 migration retained the old machine catalogue headings, 17-state
README and all three old `.tm` URLs as compatibility pointers or copies. The
12- and 16-state compatibility tables and the two forwarding Python commands
remain. Direct old Lean-source and checker-file URLs moved; the complete
[path map](MIGRATION.json) records those moves. Pinned historical URLs remain
available in [the previous public snapshot](https://github.com/Mira-Cult/math/tree/334212df64a1d7c3d0f4b1227b882d15e9c85166/turing-machines).

On 2026-11-06, the redundant `collatz-beeping17/` directory was removed. It
contained only a navigation page and a table byte-identical to the canonical
[17-state table](beeping17/collatz_beeping17.tm); the complete machine package
remains in [beeping17/](beeping17/README.md). The old unpinned directory and
table URLs no longer resolve, but both remain available in the
[pre-consolidation snapshot](https://github.com/Mira-Cult/math/tree/b5e76264e419939d1c9ca48ac9dfe8ebf862cffb/turing-machines/collatz-beeping17).
No history was rewritten.

`cd turing-machines/proofs && lake build` is replaced by the assembler command;
the old proof directory contains a migration guide, not a second proof tree.

## Verification of this migration

Source hashes, original blob identities, import closure, machine table strings,
local provenance, document paths and compatibility-table equality are checked.
A fresh Lean build/kernel replay is separate from byte-identity checking; consult
[VALIDATION.md](VALIDATION.md) for what was actually rerun for this change.
