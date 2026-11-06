# Verification boundary

The complete selected artifacts are a **266-state marked machine** and its
**267-state exit-from-B companion**. This directory is a selected-construction
reproducibility package, not the full historical experiment archive.

## Reproduce and check

From this directory, with Python 3.11 or newer and assertions enabled:

```sh
python -B reproducibility/reproduce.py
python -B verify.py
python -B verify.py --literal
```

The first command uses a temporary directory, replays the frozen plans without
optimization search, and byte-compares all 54 construction artifacts. An explicit
fresh output directory can be retained with `--out path/to/new-directory`.
The second command verifies the source manifest, both complete tables and the
six selected source/control/physical check suites. The optional final command
also requires `cc` with C11 support and `c++` with C++17 support. It compiles two
small literal engines into a temporary directory and repeats the bounded blank
execution. No network access, private repository, Git history, model service or
third-party Python package is required. Do not run with `python -O`.

The checked receipts are [REPRODUCTION.json](REPRODUCTION.json) and
[VERIFICATION.json](VERIFICATION.json). Both commands accept `--receipt FILE`.
Tests were repeated with Python 3.12 in the preparation environment.

## Repeated evidence

- The export contains 223 explicitly hashed source, proof, plan, checker and
  canonical-artifact files. Each original file was checked against an immutable
  Git blob ID. [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json) records original and
  exported hashes and every adapted file.
- The frozen selected build reproduces **54 of 54 artifacts byte for byte**.
  The selected source, plans, complete transition tables and construction
  certificates retain their exact producer identities.
- The independent-written source checker compares 120 actual-clock and 416
  explicitly prepared-clock cases, 1,965 attempt traces per source, all four
  returned-bit pairs, 258 virtual-terminator fixtures and 1,024 even inputs.
  Seven deliberately damaged source mechanisms are rejected.
- Control checks verify the exact occurrence rewrites, postfixed masks and
  retained finite control graph. The selected pass removes nine individually
  proved-zero occurrences; a shared child with other nonzero callers is not
  globally erased. Nine control/certificate mutations are rejected.
- Region checks cover the actual clock/copy/seed entry premises, intermediate
  ownership and 134 orientation-swap fixtures. The shortened clock requires
  zero output at its actual entry; arbitrary stale output is not allowed.
- Storage/runtime/completion checks verify 19 allocated carriers, 15 projected
  carriers, twelve physical classes, 188 operations and 85 peer-zero sites.
  Twenty-nine deliberately damaged certificates or interfaces are rejected.
- Literal row checks cover 544 architectural raw equations, 540 completed-raw
  equations, 534 ingress equations and all 534 retained completion rows. All
  six completion holes and seven raw preimage occurrences are accounted for.
  Six deliberately damaged rows or maps are rejected. Exclusion reachability
  is a separate invariant obligation, not inferred from missing observations.
- Injected physical checks replay 1,126 operation/preparation fixtures over
  1,190,786 literal transitions, plus 511 full lexical fixtures over 150,355
  transitions. These are prepared configurations, not blank-start executions.

## Fresh blank prefix

Two independently implemented engines use different tape representations:
[C++ deque](reproducibility/literal_deque.cpp) and
[C bitset](reproducibility/literal_bitset.c). Both apply one literal transition
per step. For each complete table they agree on every event time, final state,
head and every nonzero tape cell through **112,620,826 transitions**.

- Marked table events: **89,844,341; 99,174,101; 112,620,825**.
- Companion exits from B: **89,844,342; 99,174,102; 112,620,826**.
- At the common stopping time both tables have state 49, head -3816 and 5,992
  one-cells. Each engine pair compares the complete finite-support tape, not
  just these summary counts. Full-configuration hashes are in the receipt.

This fresh public replay does not repeat the historical third-engine
source-boundary correspondence or separately identify the source-entry step.
Those older results must not be confused with the new two-engine prefix.
No finite trace determines whether events eventually stop, or proves that
all future physical comparisons terminate.

## Immutable origin and public adaptations

- Producer: `b6fb1987da70ac826fd8275e7726ee4e536af089`, tree
  `e02554432cb76871bfd2ac6e339c342bdc0e3726`.
- Separate original review delivery:
  `7a83222960fd1314668246fb5b4f549bea546059`, tree
  `4530a51482412198ce56dba39f212281920df944`.

The export is self-contained. These original object IDs establish provenance;
they are not instructions to fetch a private repository. The public wrapper
replays only `reuse_clock_roles_zero_geometry`. It does **not** claim to replay
the original 1,529-file producer inventory, all 30 experiments, or the
3,808-file historical physical-review export.

Twenty-nine ancillary files have disclosed public adaptations: neutral attribution
labels replace internal task paths; dependency digest constants follow those
attribution-only changes; one selected static check replaces two Git-history
lookups with explicit immutable content pins; proof links to omitted historical
comparison artifacts are identified as historical references.
The retained input pins are unchanged. The original input manifest retains its
source repository name as provenance, but no private access is required. No selected mathematical source,
optimization plan, transition row or construction certificate is changed.
Every original and exported hash is recorded. Fresh reproduction still matches
all 54 immutable canonical artifacts exactly. Historical `pending` fields in
frozen producer metadata are preserved rather than silently rewritten.

## What is not claimed

The theorem rests on the accompanying conventional mathematical and physical
arguments. The original producer received two scoped internal nonauthor model
reviews. Running their adapted checks here is a fresh replay, **not a new
independent review** or external human certification. This package makes no
266-table Lean or proof-kernel claim. The original producer and review-delivery
remote workflows were skipped, not passed. Their old repository-integrity
results and the public package's finite tests are distinct. This construction
does not decide NP = coNP, and no minimality claim is made.
