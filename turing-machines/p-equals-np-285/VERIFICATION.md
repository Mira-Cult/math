# Reproduction and verification status

This receipt separates source identity, finite execution, source review, and
Lean kernel checking. None decides P versus NP.

## Exact source and dependency pins

The scientific sources are pinned to
`d2352cd63de5840d05dcdc89e78dc9f7052ee32f` in Mira-Cult/math-wip, the reviewed
head of [PR #88](https://github.com/Mira-Cult/math-wip/pull/88) on 2026-11-04.
This packet contains **801 byte-identical upstream files**: the local Lean
import closure, selected audits and fixtures, certificate generators and frozen
inputs, axiom-gate script, Lake/toolchain files, and locked Nix shell.
[SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) records their original paths, Git
blob identities, byte lengths and SHA-256 digests. The small `Shared.lean`
umbrella and public prose/checkers are release-specific. Theorems are not edited.

- Lean: `leanprover/lean4:v4.33.1`.
- mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- Google DeepMind formal-conjectures: `5a2fb85045c86e4a184b15ce7531ba199a3c4580`.
- All ten direct/transitive package revisions are fixed in `lake-manifest.json`.
- The optional shell inputs are separately fixed in `flake.lock`.

The marked table is unchanged from producer
`db256d6ae59a47eb941a2f0c5cf3f37b3c4633c8`. Its SHA-256 is
`1aeafb43c7a9a8f599476ea23bbb5723506d33ca26e5186771fb942a88ad19d7`.
The companion SHA-256 is
`12fba54d7e9c51ca6e149ae4103a3753378a7cff7cfb3e66bcda19804bfeb880`.
The frozen source SHA-256 is
`6a546f803146da357997fd7a19f98b07d3b74f1f720202fbf9a8b3bbffbf9af8`.
No private repository access is needed to build this public copy. No `.olean`,
native binary, dependency cache or raw build log is shipped.

## Checks performed on this public copy

On 2026-11-04, with Python 3.12.14 and GCC 14.2.0:

- Reconciled all 801 upstream Git blobs against the exact source tree.
- `python3 verify.py` passed: ordered 570/572-row tables, legal transitions,
  unique mark, root/embedded literal identity, every source-manifest entry,
  resolved local imports and literal includes, and pinned dependencies.
- The same checker independently checked all 572 companion rows against the
  event-coloured quotient, with zero mismatches.
- `python3 regenerate.py` passed: all **23 generators plus the pre-control
  variant** reproduced the included Lean sources byte for byte in a temporary
  copy. The typed-source generator reproduced **146 lines and 4,961 bytes**.
- The independent literal interpreter in [replay.cpp](replay.cpp) reproduced
  the complete initialization configuration at 89,806,142 executed transitions:
  state 284, head −3818, the expected full finite nonblank tape, and zero events.
  It then reproduced the unique first marked event at zero-based transition
  index **89,844,409**, in state 121 reading 1. The interpreter uses ordinary
  literal steps, not the Lean certificate generators or macro-step machinery.

These are source/provenance and finite checks. They do not replace the all-time
proof. This publication environment has no Lean/Lake/Nix toolchain, so **no
independent Lean rebuild or independent reproduction of the axiom inventories
was performed here**.

## Upstream kernel and axiom evidence, reported by the owner

The upstream owner's PR #88 description was read on 2026-11-04 at 15:27 UTC.
It reports:

- At `d2352cd63de5840d05dcdc89e78dc9f7052ee32f` on aarch64-darwin,
  `python scripts/axiom_gate.py --self-test` passed after an **incremental
  2,888-job project build**, accepting 42,664 project declarations. The
  deliberately bad probe rejected local/imported custom axioms, `sorryAx`,
  native decision and `Lean.ofReduceBool`.
- At that same revision, direct execution of `PublicEndpoint.lean` passed,
  printing both public equivalences with only **`propext`, `Classical.choice`,
  and `Quot.sound`**. These are standard Lean axioms, not an axiom-free proof.
- At `1e0e638ad6e84a7b9e5e7f18cfce3ae1d0687b99`, the six-target build for the
  literal endpoint, controller totality, uniform coverage, typed progress,
  aligned-physical audit and public endpoint passed, reusing project/dependency
  artifacts (2,551 jobs). The d235 commit changes only display commands in the
  public file. The `related_control_word` audit reported only `propext`.
- At `32386aaf12350a7f16517d9b97b4541c27d49f2d`, the four-target project build
  started without project `.lake/build` and passed (2,541 jobs). It reused
  **1,216 manifest-pinned mathlib cache artifacts**; other dependencies were
  built as needed. This was a fresh project build, not a complete source rebuild
  of every upstream dependency.
- At the final head, 44 integrity/tool tests passed under Python 3.12.12,
  including the base-aware integrity variant. The syntax check also passed.
  Repository-integrity tests are not mathematical proofs.
- All four Nix shell derivations evaluated; only aarch64-darwin was exercised.
  Successful commands used the public Nix cache after a configured private
  cache timed out. Concurrent evaluation-cache warnings did not fail the runs.

These are **owner-reported upstream results**, not this release worker's own
kernel replay. The complete upstream gate includes more modules than this
focused public packet, so 42,664 is not a promised declaration count for the
public copy. Its axiom gate audits every included project module.

The exact-head upstream GitHub [integrity job](https://github.com/Mira-Cult/math-wip/actions/runs/41856435141/job/126666306150)
was **skipped**, not passed. No remote CI pass is claimed for this publication.

## Scoped nonauthor source review

Assistant-led nonauthor automated source reviews examined central interfaces
and selected supporting proofs at
`6aef75e8ffd5fd641968325e7bb7ee052b7102fc`, then the complete four-commit delta
through `d2352cd63de5840d05dcdc89e78dc9f7052ee32f`. The later reviews inspected
the full control-PC relation retained by `AlignedPhysical.Rel` and
`ProducerFullBoundary`, both public endpoints, the companion's one-step shift,
the canonical complexity definitions and dependency pins. They found no
blocking defect in the inspected correction/public-interface delta.

The earlier review had identified that the exported relation dropped control-PC
correspondence while keeping register equality. Commit
`cbb59ef1af1a2b1ceb6b0aa0936c1024e2f33957` preserves the already-proved full
`GrammarControlGraph.Related` witness and adds `related_control_word`; the later
review checked this correction. No new endpoint premise was introduced.

This was not review by Mira personally, an exhaustive review of all imported
proofs, an independent Lean rebuild, a formal GitHub PR approval, or external
human-expert certification. A separate presentation check reviewed this
release's proof/interface explanation and its observation/complexity boundaries.

## Historical receipt

The [previous public receipt](https://github.com/Mira-Cult/math/blob/572ea55a51714ab08d335f37f2b08444c940bddc/turing-machines/p-equals-np-285/VERIFICATION.md)
remains available in Git history. It pinned `576f0f2d`, recorded partial literal
and blank-start kernel checks, and described a full independent endpoint build
as pending. This update does **not** infer that run completed. The current
owner-reported build results above are different evidence at later revisions.

## Reproduce the finite checks

From this package directory, with Python 3.11+ and a C++17 compiler:

```sh
python3 verify.py
python3 regenerate.py
c++ -O3 -std=c++17 -Wall -Wextra -pedantic replay.cpp -o /tmp/pnp285-replay
/tmp/pnp285-replay events.tm
```

The generators write only a temporary copy. The bounded replay stops just after
the first event and fails if its explicitly bounded tape is exhausted. It cannot
establish eventual silence or infinitely many future events.

## Rebuild and inspect both public theorems

Install [Lean from its official instructions](https://lean-lang.org/install/).
Alternatively, use `nix develop` inside `formalization` with flakes enabled;
the included locked shell reads `lean-toolchain`. The Nix route has only the
upstream aarch64-darwin execution evidence described above.

```sh
cd formalization
lake env lean --version
LEAN_NUM_THREADS=1 lake build Shared.PNP.Record285.PublicEndpoint \
  Shared.PNP.Record285.LiteralEndpoint \
  Shared.PNP.Record285.SourceControllerTotal \
  Shared.PNP.Record285.PayloadUniversalCoverage \
  Shared.PNP.Record285.PythonControlProgressAudit \
  Shared.PNP.Record285.AlignedPhysicalAudit
lake env lean Shared/PNP/Record285/PublicEndpoint.lean
lake env lean Shared/PNP/Record285/LiteralEndpointAudit.lean
lake env lean Shared/PNP/Record285/AlignedPhysicalAudit.lean
lake env lean Shared/PNP/Record285/LiteralQuotientAudit.lean
lake env lean Shared/PNP/Record285/SourceControllerTotalAudit.lean
lake env lean Shared/PNP/Record285/PayloadUniversalCoverageAudit.lean
lake env lean Shared/PNP/Record285/PythonControlProgressAudit.lean
LEAN_NUM_THREADS=1 python3 scripts/axiom_gate.py --self-test
```

Keep the committed lockfile; do not run `lake update` to obtain newer revisions.
A fresh clone starts without project `.lake/build`. If upstream dependency
caches are reused, record that separately. Reusing project artifacts is an
incremental build and must not be described as a clean project rebuild.
The gate rejects axioms beyond the standard three and includes a temporary
negative self-test; it is separate from inspecting definition meaning.

The optional bounded source fixture is:

```sh
lake build Shared.PNP.Record285.Source
lake env python3 Shared/PNP/Record285/check_source_fixture.py
```

It compares 140 checkpoints. It is not the universal CPython correspondence,
which remains open and is not a premise of either literal-machine theorem.
