# Selected fixed construction

Run `python -B reproduce.py` from this directory, or the root-directory
commands in [VERIFICATION.md](../VERIFICATION.md). Python assertions must remain
enabled. There are no pip dependencies or network calls.

`source/` retains the producer-relative layout so imported generators and
proof references keep their mathematical context. This is a selected dependency
closure, not a copy of the research repository. The top-level wrapper deliberately
replaces the historical all-experiment entry point with a selected-only one.
It calls the retained `control_regions/fixed.py`, using the frozen grammar,
physical-sharing and completion plans, and compares every one of the 54 selected
and parent artifacts. It performs no optimization search.

The principal source is
[source/problems/np-conp-formulations/selector/continuation/compact/control_regions/sources/reuse_clock_roles.py](source/problems/np-conp-formulations/selector/continuation/compact/control_regions/sources/reuse_clock_roles.py).
The selected source proof is
[source/problems/np-conp-formulations/selector/continuation/compact/control_regions/PROOF.md](source/problems/np-conp-formulations/selector/continuation/compact/control_regions/PROOF.md).
Predecessor source, compiler, finite-control, storage, unary-bank, native-HALF,
completion and event arguments are retained alongside their relevant code.
Four directly cited predecessor source programs are included for comparison.

[The manifest](../SOURCE_MANIFEST.json) records original Git blob IDs, original
SHA-256 values, current SHA-256 values, exact origin revisions and adaptations.
The public adaptations affect ancillary attribution/provenance and verification
access, not the selected source, plans or 54 canonical output bytes. Original
vendor license notices remain included.

The two literal engines consume the root complete tables directly. They do not
invoke a compiler, source interpreter, macro-step engine or optimized simulator.
Their finite outputs are compared by `../verify.py --literal`.
