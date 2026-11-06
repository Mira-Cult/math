# Reproduction and verification status

This receipt separates byte identity, finite execution, source review, and
Lean kernel checking. None of these checks decides NP versus coNP.

## Exact source and dependency pins

The mathematical source is frozen at
`6108c93565701e64775a3f1cbf9627d35c4c30e3`. This is the source revision
examined by the scoped nonauthor review, not a moving branch name.
[SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) records every unchanged upstream
file's original path, Git blob identity, length and SHA-256 digest.
[IMPORT-CLOSURE.json](IMPORT-CLOSURE.json) records the recursive local import
closure of `Shared.Beeping.NPcoNP.Bootstrap284AlignedFromBlank` and its external
imports. The public `Shared.lean` umbrella is release-specific and imports
only that endpoint. No proof is edited to make this package build.

- Lean: `leanprover/lean4:v4.33.1`.
- mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- Google DeepMind formal-conjectures: `5a2fb85045c86e4a184b15ce7531ba199a3c4580`.
- All ten direct and transitive packages have fixed Git revisions in
  `formalization/lake-manifest.json`.

The marked table has SHA-256
`0c924f63d3cdd89f97078aef409010fa868b189466ab186a17e105f81e9279aa`.
The 285-state companion has SHA-256
`5b2e39f9df0b872c0854273df7f2b7f050fdce525363538dea5c9dfabdcad868`.
The 3,131-byte preserved source listing has SHA-256
`4f1f6f317eb196b8d09a67439893622a759c43ef4e02e30adae4e04b0eb39515`.

No access to the private research repository is needed to read or build this
copy. Dependency downloads use the public upstream repositories fixed in the
lockfile. No `.olean`, native binary, dependency cache, credential, raw build
log, or private research conversation is shipped. No license is added or
changed; see [ATTRIBUTION.md](ATTRIBUTION.md).

## Checks on the prepared public copy

The preparation environment has Python 3.12.14 and GCC 14.2.0. It has no
Lean, Lake, or Nix executable. **No independent Lean rebuild, fresh kernel
replay, or reproduction of the axiom inventory was performed here.**

On 2026-11-06, the following preparation checks passed:

- Reconciled all **1,963 unchanged upstream file copies** against a freshly
  retrieved source tree at the exact mathematical revision. This includes
  **1,926 Lean modules** in the minimal recursive local endpoint closure,
  frozen inputs, 24 certificate-generator files, the original axiom gate,
  and the toolchain and dependency files. The copies total 13,883,337 bytes.
- `python3 verify.py` passed: all manifest hashes, the closed import graph,
  17 external import modules, literal includes, all ten dependency pins,
  all 568 marked-machine rows and their Lean numeric representation, and
  all 570 companion rows under the event-coloured quotient.
- Independently confirmed that all 16 external source modules exist at the
  two pinned upstream commits; [EXTERNAL-IMPORTS.json](EXTERNAL-IMPORTS.json)
  records their Git blob identities. The remaining external import, `Std`,
  belongs to the pinned Lean toolchain. This is a source-availability check,
  not a rebuild of those dependencies.
- `python3 regenerate.py` passed: **49 recipes reproduced 235 distinct
  released Lean sources byte for byte** in a temporary copy. Three additional
  diagnostic outputs fell outside the released import closure.
- The literal C++ interpreter compiled with the command below and passed:
  the first marked transition was at zero-based index **60,987,213**,
  state 99 and head −3817. This is the 60,987,214th executed transition
  when counted from 1.
- All 28 included Python sources passed syntax parsing. The package contained
  no symlinks, compiled build products or dependency caches.

These checks do not replace the all-time Lean proof or independent review.

## Reported upstream kernel evidence

The upstream verification report was read on 2026-11-06. Its
documentation revision is `18e55c671f5c570a49c076c5f29f3c8b40eae52d`;
the mathematical revision to which the following results are attributed is
`6108c93565701e64775a3f1cbf9627d35c4c30e3`:

- Lean v4.33.1 built `Bootstrap284AlignedFromBlank` in a 4,960-job run,
  reusing pinned dependency artifacts **and local project artifacts**.
  This is an incremental build, not a clean project rebuild.
- A targeted rejecting axiom gate covering the endpoint, literal parser and
  the 108-step bootstrap accepted 62,287 project declarations. The allowlist
  is exactly `propext`, `Classical.choice`, and `Quot.sound`.
- `leanchecker` replayed the endpoint module against its imported environment.
  `leanchecker --fresh` replayed it and all imported constants from an empty
  Lean environment. Both use Lean's kernel; neither is an external proof
  checker or a mathematical review.
- Python 3.11.14 `check.py` passed 52 repository-integrity and tooling tests,
  including the PR-base retention check. These are not mathematical proofs.
- The full-project axiom audit and a clean project rebuild using pinned
  dependency artifacts were reported as running. **Their completion and
  outcomes remain unconfirmed in this receipt.**
- No GitHub workflow pass or commit-status pass was reported for the then
  current head. No remote CI pass is claimed for this prepared release.

These are reported upstream results, not independently rerun results from the
publication environment. The targeted upstream gate included a different
module set from this minimal endpoint package; 62,287 is not a promised
declaration count for this copy's full included-source gate.

## Review scope

An assistant-led nonauthor automated interface and mathematical source review
examined the exact mathematical revision above. It found no blocking interface
mismatch within its stated scope, including the real blank start, preservation
of the infinite blank ray, root-to-beep boundary, cofinal matching argument,
literal parser binding, and connection to the canonical class theorem.

That review was not an exhaustive line-by-line audit of the full import
closure, an independent Lean rerun, human-expert review, or a formal pull-request
approval. A separate human review remains pending. Passing source or finite
checks must not be described as completing that review.

## Reproduce the finite checks

From this package directory, with Python 3.11+ and a C++17 compiler:

```sh
python3 verify.py
python3 regenerate.py
c++ -O3 -std=c++17 -Wall -Wextra -pedantic replay.cpp -o /tmp/npconp284-replay
/tmp/npconp284-replay events.tm
```

`verify.py` checks all source-manifest hashes, the exact local import closure,
literal includes, pinned dependencies, all 568 literal rows against the Lean
numeric table, and the 570-row companion quotient. The quotient check compares
the marked transition to **arrival** at companion state 1. Hence a marked
transition at zero-based time `t` corresponds to companion state 1 at time
`t+1`. It does not misidentify the marked machine's state 1 as a beep state.

`regenerate.py` runs the commands in
[GENERATOR-RECIPES.json](GENERATOR-RECIPES.json) in a fresh temporary copy,
without changing released files. It compares generated released source bytes
to the frozen originals. Some generators also emit diagnostic modules outside
the endpoint's import closure; these are not claimed as released or built.
Generated Lean certificates are mathematical source, not compiled build
products, and remain untrusted until Lean checks them.

The separately written literal interpreter checks the first marked transition
at zero-based index **60,987,213**, in state 99, reading 1, with head at
position −3817. It stops there, using an explicitly bounded finite tape and
transition count. It cannot establish future silence or infinitely many events.

## Rebuild and inspect the exact Lean theorem

Install Lean using its [official instructions](https://lean-lang.org/install/).
The project requests the version in `formalization/lean-toolchain`. Keep the
committed lockfile; do not run `lake update` to substitute newer dependencies.
Initial dependency acquisition requires network access to public upstreams.
Building from sources can require substantial time and memory; no measured
clean-build resource bound is claimed here.

```sh
cd formalization
lake env lean --version
LEAN_NUM_THREADS=1 lake build Shared.Beeping.NPcoNP.Bootstrap284AlignedFromBlank
lake env lean Shared/Beeping/NPcoNP/Bootstrap284AlignedFromBlank.lean
LEAN_NUM_THREADS=1 lake env leanchecker -v Shared.Beeping.NPcoNP.Bootstrap284AlignedFromBlank
LEAN_NUM_THREADS=1 lake env leanchecker --fresh -v Shared.Beeping.NPcoNP.Bootstrap284AlignedFromBlank
LEAN_NUM_THREADS=1 lake env python3 scripts/axiom_gate.py --self-test
```

The endpoint source prints axiom inventories for the literal conjunction,
the constructed initial alignment, and the unconditional eventual-silence
equivalence. The rejecting gate audits every included project module and tests
its rejection of temporary bad declarations. It serializes expensive certificate
families before the aggregate build. Axiom checking and inspection of the
intended definitions are different obligations.

For a clean project rebuild, use a fresh copy with no project `.lake/build`.
Record dependency-cache reuse separately. Reusing a project build directory is
an incremental run; starting with cached upstream dependencies is not a complete
source rebuild of all upstream packages. A `--fresh` kernel replay is not a
replacement for rebuilding source or reviewing the mathematical interpretation.

## Boundaries of the release

The formal endpoint is for the exact 284-state marked table. The companion's
one-step event shift is separately explained by its checked finite quotient;
this minimal package does not add a new closed formal companion endpoint.
The 266-state machine is a different conventional result, not a smaller version
of the theorem formalized here. Some unchanged low-level source comments
describe earlier proof frontiers. The composed endpoint and this receipt state
the scope of the present package.
