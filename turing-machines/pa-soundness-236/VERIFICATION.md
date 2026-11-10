# Verification and reproduction

Source identity, conventional finite checks, source review, and kernel proof
checking are distinct evidence. None of the finite checks decides ω-acceptance.

## Contents and pins

[SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) inventories **2,335 byte-identical
upstream files**:

- 2,289 files in the complete `lean/`, `code/` and `bindings/` trees from
  math-wip PR #89 at `f312d4eb53d92a2a49c941ea26d1ef91fad946d7`, including
  2,238 Lean modules, generators and frozen inputs;
- 45 files in the selected producer's source/input/license closure from
  `bad500e2d22c3f8b7c6420f5c5b1a504a6a57b30`;
- the historical [omega-semantics manuscript](history/omega-semantics.md) from
  `60c6f2c22ddd50d3ba40e2ca94a4a63a87e74a0c`. It is a historical source,
  not a replacement for this release's precise observer definition.

Entries give original path, commit, Git blob SHA, byte length and SHA-256.
Top-level machine tables exactly duplicate the bound inputs. Public prose and
small verification/runner scripts are release-specific. Proof sources are
unchanged. No `.olean`, native binary, cache, raw build log or credential is
included.

- Lean: `leanprover/lean4:v4.33.1`.
- mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- All nine direct/transitive Lake package revisions are fixed in
  [lake-manifest.json](formalization/lean/lake-manifest.json).
- Use Python 3.12 for conventional source tools.

Historical commit identifiers are provenance. Rebuilding the included formal
source or producer needs no private workbench access; public Lean dependency
downloads are still needed.

## Checks performed for this release

On 2026-11-10, using Python 3.12.14:

- All copied upstream bytes matched their exact Git blobs, lengths and SHA-256.
- `python3 verify.py` passed: all 2,335 source entries; ordered 472/474-row
  selected/raw tables; legal transitions and output marks; all 474
  output-preserving quotient equations; 2,238 Lean modules, 6,989 local imports
  and four literal includes; dependency pins and independent finite parser
  controls.
- `python3 regenerate.py` passed all **eight M236 generators** in a temporary
  copy. This includes the bootstrap certificate (77 chunks claiming 2,133,492
  raw steps), runtime certificate (333 chunks, 332,011 macro-operations claiming
  87,687,916 further steps), grammar/graph literals, and exact byte witnesses.
  These source inputs add to 89,821,408 steps. Reproducing them is not an
  independent literal replay or kernel check of their certificates.
- The original `FusedBeam` builder reproduced the 236-state selected and
  237-state raw tables byte for byte. The occurrence-graph reconstruction
  matched 760 rows and 1,036 edges, SHA-256
  `dbad7675ad75b28ff70f26387f0cb6cbeabe5dea586d681eefa47c11c422ae93`.
- The small literal runner executed 100,000 selected-machine transitions,
  ending at state 76, head −768, 621 nonzero cells and zero output events.
  This is only a finite smoke test.

On 2026-11-10, in an isolated clean checkout of public commit
`33c755adb8081b1eda611ca92cd8d1322747f1f2` on `x86_64-unknown-linux-gnu` using
pinned `leanprover/lean4:v4.33.1` (commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Lake `5.0.0-src+819816b`):

- Starting from zero project `.olean` files, `lake exe cache get Mathlib`
  unpacked 8,689 manifest-pinned `mathlib` cache files (`mathlib`
  `0df444a360eaa60ab8c11dca51a86af692955474` was not rebuilt from source).
  [lean-toolchain](formalization/lean/lean-toolchain) and
  [lake-manifest.json](formalization/lean/lake-manifest.json) remained
  byte-identical throughout.
- `lake build PASoundness PASoundness.Audit` passed across 5,275 jobs,
  compiling all 2,238 local Lean modules with zero `sorry` warnings.
- `PASoundness.Audit` verified 42,446 transitive theorem declarations using
  only `[propext, Classical.choice, Quot.sound]`, checked `#print axioms`
  across 13,521 declarations (11,466 using subsets of those three standard
  axioms and 2,055 axiom-free), and verified all 8,429 structural dependency
  roots independent of `Peano.soundness`, `Peano.formula_soundness`,
  `CompactSemantics.derivation_sound`, `CompactSemantics.proves_sound`,
  `CompactSemantics.axiom_sound`, and `CompactSemantics.finite_comprehension`.
- Direct `lake env lean` checks on
  [PAtoCompactEndToEndProofTranslation.lean](formalization/lean/PASoundness/PAtoCompactEndToEndProofTranslation.lean)
  and
  [M236HistoricalPASoundness.lean](formalization/lean/PASoundness/M236HistoricalPASoundness.lean)
  confirmed that all exported endpoint theorems depend only on
  `[propext, Classical.choice, Quot.sound]`.
- `lake env leanchecker --fresh PASoundness` (and `lake env leanchecker PASoundness.Audit`)
  passed, replaying all transitive declarations in a fresh environment using
  the **same Lean 4.33.1 kernel** (not an independent kernel implementation).
- `python3.12 -B formalization/code/check_m236_game.py` passed all 128 finite
  source-reference game cases in Lean (21 with rejection bit 1), and
  `python3.12 -B formalization/code/review_source.py --axioms` matched all 192
  matrix cases, 64 postfix certificates, and 144 axiom selector cases against
  the pinned PA926 source (`all_equal: true`).

No from-source rebuild of `mathlib`, independent third-party kernel check, or
independent literal 89,821,408-step replay outside the Lean chunk proofs is
claimed. The scoped publication review is recorded in [REVIEW.md](REVIEW.md).

## Upstream workbench records

The [PR #89 description](https://github.com/Mira-Cult/math-wip/pull/89) and
exact-source records report the following prior workbench runs. The original
workbench may require access; the required proof and input sources are included
in this public packet.

- At `7b551f1722cb62876c04195b6ad1059ac8116e0a`, two independent private
  **incremental** `lake build PASoundness PASoundness.Audit` runs passed,
  5,274 jobs each. Scoped end-to-end mathematical source review found no
  substantive mismatch, relying on imported contracts and separately reviewed
  modules rather than a transitive reproof of every import.
- At that revision, `lake env leanchecker --fresh PASoundness` passed in a
  fresh environment using the **same Lean kernel**, not an independent kernel
  implementation. The 128-case finite game regression and M236 generation
  check also passed.
- The historical-observer corollary and final code/doc-comment revision passed
  the aggregate build and audit at
  `60e9d76399dee09c01c3cecdb37c3830b3ce2612`, 5,275 jobs. The final source head
  `f312d4eb` differs only in `M236-CONTINUATION.md` and `OBSERVER-GUIDE.md`.
  The mathematical/code payload included here is unchanged from that build.
- The audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
  It roots both final PA-facing endpoints and the historical corollary. Its
  structural checks forbid dependencies on the specified project PA/K
  soundness and comprehension theorems: an independent metatheoretic soundness
  proof cannot silently replace the translations.
- An isolated Python 3.11 workbench integrity check passed 44 tests. Those are
  repository-integrity/tool tests, not mathematical proofs.

The 44-test workbench integrity suite above was not rerun here; the public
packet's own clean-project build, audit, and `leanchecker --fresh` replay are
recorded in the previous section. Exact-head lookup returned no PR-triggered
workflow runs. No remote CI pass is claimed; the source PR remained open and
draft at inspection.

## Trust boundary

Successful Lean checking validates the formal theorem relative to its kernel,
elaborated definitions and reported standard axioms. The source's correspondence
to the intended mathematics also needs review. Classical choice appears in
strategy arguments and proof-data construction. This package promises neither
a computable strategy finder nor an executable extractor from arbitrary
Prop-valued PA derivability.

The formal historical observer is equivalent to `TraceAccept` for physical
streams. Its match to manuscript prose remains a scoped review judgment.
Historical normalized-PA record coding is not identified record by record with
M236's compact game coding.

Hashes establish identity, not truth. Generator agreement establishes
reproducibility, not general compiler semantics. Finite runs establish finite
behavior, not coverage, infinitely many frames or all winning strategies.
The formal physical simulation supplies the all-time source correspondence and
guards; the game/calculus arguments establish the acceptance equivalence.

## Reproduce source and finite checks

From this package directory:

```sh
python3 verify.py
python3 regenerate.py
python3 run.py --steps 100000
```

`verify.py` uses only the standard library and does not execute project source.
`regenerate.py` checks the eight generators in a temporary copy, without Lean.
`run.py` interprets literal transitions with a finite budget. Events identify
zero-based transition indices and the state/read pair before the step; its
last line gives the final configuration summary. It is not an acceptance test.
The [producer recipe](producer/README.md) reproduces the machine and occurrence
graph in temporary output directories. Keep generated products out of Git.

## Rebuild the formal proof

Install Lean using its [official instructions](https://lean-lang.org/install/).
Preserve the toolchain and lockfile.

```sh
cd formalization/lean
lake env lean --version
# Optional pinned dependency cache:
lake exe cache get Mathlib
LEAN_NUM_THREADS=1 lake build PASoundness PASoundness.Audit
lake env lean PASoundness/PAtoCompactEndToEndProofTranslation.lean
lake env lean PASoundness/M236HistoricalPASoundness.lean
lake env leanchecker --fresh PASoundness
cd ../..
python3 formalization/code/check_m236_game.py
```

The endpoint files print transitive axiom dependencies. Inspect the aggregate
audit's actual output: it must reject unexpected axioms and forbidden soundness
dependencies. A smaller unrelated target passing is not the aggregate audit.

Use a clean project build after modifying any `include_str` input: Lake may
not detect the external file change. Dependency-cache use, an incremental
project build, a fresh-project build and a source-built dependency stack are
different receipts; state which was performed. `leanchecker`, if available in
the pinned toolchain, replays using the same kernel. A missing executable is a
missing optional replay check, never evidence of success.

Preserved workbench documentation and intermediate comments sometimes describe
historical obligations or paths outside this packet. Use the public README,
observer, proof guide and closed end-to-end modules for the current statement,
not an earlier conditional adapter.
