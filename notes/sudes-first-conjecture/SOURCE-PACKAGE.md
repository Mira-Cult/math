# Sude source package

This is a source export of commit 927a770a92c4fb135498d73e46d8978f27ec081a.
The package is prepared for release, not evidence that publication or a fresh full
Lean build has happened. The authoritative portable research narrative can be
added as research-writeup.md by the release editor.

## Contents and trust boundary

- formalization/: all 9,153 original Lean source modules, including committed
  generated certificate source; the original generators, lockfiles, import ledger,
  and selected technical diagnostics.
- finite-replay/: the exact seven-file strict finite certificate replay closure
  for all 1,000 positive odd orders below 2000. The gzip file is a mathematical
  certificate INPUT, not a compiler cache or log.
- regeneration-inputs/: the remaining original input/manuscript/source closure
  referenced by the certificate generators and input source-binding manifests.
- source-manifest.json: original paths, export paths, exact Git blobs, SHA-256,
  upstream tree identities, exclusions, and public dependency checks.
- prepare-regeneration.py: verify and reconstruct original relative paths in a
  new scratch directory without running any proof or generator.
- export-sude-sources.py: reproduce this source export from a local object-complete
  checkout at the pinned commit; it never publishes, fetches, or changes that repo.

The Lean all-odd theorem is conditional on the explicit FiniteWitness input and
15 published analytic propositions. The finite replay is separate executable
verification, not a Lean discharge of FiniteWitness. No stronger claim follows
from packaging or import-closure checks.

## Build from the exported project

With the separately installed pinned Lean toolchain available:

    cd formalization
    lake exe cache get
    lake build
    lake env lean Sude/Audit.lean

Toolchain: leanprover/lean4:v4.33.1. The exact mathlib and eight transitive pins
are in lake-manifest.json; all nine repositories and commit objects were checked
as public when this package was prepared. No dependency cache is bundled.
These commands were NOT executed during source packaging, and no resource,
time, or full-build-success claim is made. Run in an isolated directory.

## Finite replay

With Python 3.12.13 and a C++20 compiler installed:

    python3 -B finite-replay/code/cutoff2_finite_remainder_squares.py

The source bindings have been checked during packaging; the full replay was
not rerun for this export. Its input manifest records the intended checks and
scope. Do not substitute a direct verifier-only run for the strict wrapper.

## Original-layout regeneration

Choose a new path without symlink ancestors (on macOS use /private/tmp rather
than the /tmp symlink):

    python3 prepare-regeneration.py /absolute/new/sude-regeneration

This copies each manifest-listed file back to its original relative path,
including formalizations/sude, problems/prime-line-sums, and .python-version.
It preserves the original generator scripts byte for byte. Run any selected
generator only inside that scratch tree, using the original instructions.
Generators may write or refuse to overwrite their certificate-source outputs.
This preparation step neither runs nor guarantees the byte-for-byte result of
every historical generator. Recheck generated changes and build their modules.

## Historical material and licensing

Only RESEARCH_NOTES.md and handoff/HANDOFF.md are omitted from the original
formalization subtree: they are running commentary and an obsolete handoff, not
proof/build inputs. The original README and IMPORTS ledger are retained verbatim
for provenance. Some historical document links, old private commit provenance,
and repository-integrity commands refer to the original wider research checkout;
they are not needed by lake build or the source reconstruction recipe. The
portable research-writeup.md should be used as the release's current narrative.
The retained handoff/FWPhysicalFloorStock.lean.txt is an UNCHECKED historical draft,
not a Lean module in the exported build. Its preservation is not acceptance.

No source LICENSE exists in the original Sude subtree or repository root, so no
new license has been invented. Dependency license identifiers and public source
links are recorded in source-manifest.json; dependency code/licenses are obtained
from their pinned upstream packages, not vendored here. Bibliographic source
URLs and citations in import-map.json and IMPORTS.md are preserved. No published
paper PDF has been copied or relicensed.
