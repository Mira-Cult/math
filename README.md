# Public mathematical results

An index of results and proof drafts publicly released in this repository.
Each entry states its scope and verification status; publication does not
by itself imply formal verification or external referee acceptance.

## Prime arrays and lattice reductions

| Result | Exact scope | Sources and verification |
| --- | --- | --- |
| **Sude's First Theorem** | For every positive odd n, exactly the first n² odd primes can be arranged, each once, in an n × n square with prime sums in every row, column and both main diagonals. | [Resolution and proof](notes/sudes-first-conjecture/resolution.md), [complete public replay packet](notes/sudes-first-conjecture/packet/README.md), and [internal nonauthor review](notes/sudes-first-conjecture/proof-source/problems/prime-line-sums/reviews/sude-all-odd-independent-review.md). A conventional computer-assisted theorem with explicit analytic imports and independently reproduced exact checks; no end-to-end formalization or external referee acceptance claimed. |
| **Trimmed coded folding for Euclidean GapCVP** | For each fixed rational 0 < ε < 1/2, a deterministic ordinary reduction from sparse Boolean quadratic satisfiability with source-size bound N has exact gap D^(1/2−ε) and full lattice rank D ≤ N^(1/ε+o(1)). The lattice depends on the instance; this is a rank bound, not the runtime exponent. | [Statement, complete proof packet and finite checks](notes/lattices/trimmed-coded-fold/README.md), with [provenance and verification limits](notes/lattices/trimmed-coded-fold/PROVENANCE.md). A complete mathematical **proof draft**, not formally verified or human-expert-reviewed. |

The [prime-array research index](notes/sudes-first-conjecture/README.md)
also records higher-dimensional and other-field generalizations, each with
its own range and proof status. Those ranges are not enlarged by the
all-odd-order square theorem.

## Turing machines and tilings

| Result | Exact scope | Sources and verification |
| --- | --- | --- |
| 12-state binary Collatz evaluator | On each encoded positive input, halts exactly when its ordinary Collatz orbit reaches 1. Universal positive-input termination is equivalent to the ordinary Collatz conjecture. | [Machine and Lean proof](turing-machines/README.md#12-state-input-evaluator) |
| 16-state binary Collatz cycle detector | From a blank tape, halts exactly when a nontrivial positive ordinary Collatz cycle exists. | [Machine and Lean proof](turing-machines/README.md#16-state-blank-tape-cycle-detector) |
| 17-state binary Collatz beeping machine | From a blank tape, beeps infinitely often exactly when every positive Collatz orbit reaches 1. If b is the least counterexample, emits exactly b(b−1)/2 beeps. | [Machine, ordinary mathematical proof and finite checks](turing-machines/collatz-beeping17/README.md) |
| 30 fourteen-sided polygons with recurrence | An unseeded whole-plane tiling with fixed same-root completion recurrence exists exactly when full positive Collatz holds. Ordinary tileability is unconditional. | [Proof, exact geometry and reproducible checks](tilings/collatz-30/README.md) |
| 488 Wang tile types for a seeded half-plane | With seed 487 at the origin of ℤ × ℕ₀, tiles the half-plane exactly when the pinned K215 machine does not halt. The ZFC consequence uses the upstream machine calibration. | [Tile set, ordinary mathematical proof and reproducible checks](tilings/wang-488/README.md) |

These are correctness reductions. They do not prove the Collatz conjecture
or the consistency of ZFC, and make no minimality or record claim.

See attribution and license status for the [Turing-machine results](turing-machines/ATTRIBUTION.md),
the [488-tile construction](tilings/wang-488/ATTRIBUTION.md),
and the [30-polygon construction](tilings/collatz-30/ATTRIBUTION.md).

## Research notes

- [Theories K: a formal substitution catalogue](notes/set-theory/theories-k-substitution-catalogue.md) (2026-10-23 definitions draft). Precise first-order schemas, with established results distinguished from research reductions and outstanding proof obligations; no new full equivalence is claimed as formally verified.
