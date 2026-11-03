# Reproduction and verification status

## Source identity

The scientific source is pinned to revision
`576f0f2d69d37e4ba29d75ea712ddac6174832ca`. The public packet contains 743
unchanged upstream files: the transitive local Lean dependency closure,
selected audit and fixture modules, certificate generators and frozen inputs,
the axiom-gate script, and the three dependency/toolchain files.
[SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) records each original path, Git
blob, byte length, and SHA-256. `formalization/Shared.lean` is a new, narrow
public-release umbrella. Scientific theorem files are unchanged.

The marked literal is byte-identical to both the formalization's embedded
file and producer revision `db256d6ae59a47eb941a2f0c5cf3f37b3c4633c8`.
No generated `.olean`, native object, dependency cache, or build log is shipped.

## Checks performed for this public packet

On 2026-11-03:

- All 743 upstream Git blobs were reconstructed and checked against their
  exact fetched blob identities.
- `python3 verify.py` passed: complete ordered 570/572-row tables, valid
  destinations, the unique event, exact root/embedded literal equality,
  source manifest hashes, all 1,215 local import edges and literal includes,
  and the ten-package lockfile.
- `python3 regenerate.py` passed: all 22 certificate generators, plus the
  pre-control variant, reproduced the included Lean certificate sources
  byte for byte in a temporary copy. The generators are untrusted input
  producers, not proof oracles.
- An independent automated source/interface inspection checked the endpoint
  type, byte/event convention, actual blank start, positive cofinal full-tape
  refinement, source enumeration, canonical class definitions, and both paid
  complexity directions. See [INTERFACE.md](INTERFACE.md). This is not a
  full proof-corpus or independent human mathematical review.
- The independent rebuild has passed the literal certificate and blank-start
  layer. Fresh axiom printing for `literal_rows`, `literal_beep`,
  `literal_bootstrap`, `blank_start`, and `perpetual` reports only the three
  standard axioms `propext`, `Classical.choice`, and `Quot.sound`. This is a
  partial check; it is not the full endpoint build or its transitive audit.

The upstream author reported a cached local build of
`Shared.PNP.Record285.LiteralEndpoint` (2,483 jobs) and an axiom audit returning
only `propext`, `Classical.choice`, and `Quot.sound` for the closed endpoint
theorems and stated key dependencies. That is inherited evidence, not this
publication's fresh reproduction.

**An independent clean project-source rebuild and fresh axiom audit are in
progress. No successful result for that run, full from-source upstream
dependency rebuild, remote CI pass, or independent human nonauthor review is
claimed by this version of the receipt.** The independent run starts without
project `.olean` files; use of public upstream dependency caches must remain
distinct from rebuilding all dependencies from source.

## Reproduce the literal and generated-source checks

Python 3.11 or newer, standard library only, from the machine package directory:

```sh
python3 verify.py
python3 regenerate.py
```

The second command writes only a temporary copy. It does not regenerate the
whole historical machine producer. The frozen literal is the theorem's input;
the included generators reproduce its proof-certificate sources.

## Rebuild the formal endpoint

Install [Lean using its official installation instructions](https://lean-lang.org/install/).
The pinned toolchain is `leanprover/lean4:v4.33.1`.
From this package directory:

```sh
cd formalization
lake env lean --version
LEAN_NUM_THREADS=1 lake build Shared.PNP.Record285.LiteralEndpoint \
  Shared.PNP.Record285.LiteralQuotient \
  Shared.PNP.Record285.SourceCandidateClockTotal
lake env lean Shared/PNP/Record285/LiteralEndpointAudit.lean
lake env lean Shared/PNP/Record285/DirectEndpointAudit.lean
lake env lean Shared/PNP/Record285/AlignedPhysicalAudit.lean
lake env lean Shared/PNP/Record285/LiteralQuotientAudit.lean
lake env lean Shared/PNP/Record285/SourceCandidateClockTotalAudit.lean
```

The first build may be substantial. Do not run `lake update` to obtain newer
dependencies: keep the committed lockfile and pinned revisions. Lake obtains
only public GitHub dependencies. The principal pins are mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` and formal-conjectures
`5a2fb85045c86e4a184b15ce7531ba199a3c4580`; all transitive pins are in
`lake-manifest.json`.

For a clean project rebuild, use a fresh clone with no project `.lake/build`
directory. If an upstream dependency cache is used, disclose that separately.
Never reuse project artifacts from a different revision as clean-build evidence.

For the broader gate over every included project module, including a temporary
negative test that the gate rejects custom axioms, `sorryAx`, and native
reduction axioms:

```sh
LEAN_NUM_THREADS=1 python3 scripts/axiom_gate.py --self-test
```

This audits all shipped project modules, not the entire original research
repository.

The gate's temporary deliberately bad test module is not part of the theorem
source. A small axiom inventory supports the trust story but does not replace
checking the meanings of the definitions.

## Optional finite Python/source comparison

After building the source module, this compares 140 bounded checkpoints:

```sh
lake env python3 Shared/PNP/Record285/check_source_fixture.py
```

That is a finite regression, not a proof of the outstanding Python AST
translation. No long literal replay is needed to establish the all-time
theorems, and none is claimed as part of this publication's checks.
