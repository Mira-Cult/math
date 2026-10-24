# Public mathematical results

An index of results publicly released in this repository.

| Result | Exact scope | Sources and verification |
| --- | --- | --- |
| 12-state binary Collatz evaluator | On each encoded positive input, halts exactly when its ordinary Collatz orbit reaches 1. Universal positive-input termination is equivalent to the ordinary Collatz conjecture. | [Machine and Lean proof](turing-machines/README.md#12-state-input-evaluator) |
| 16-state binary Collatz cycle detector | From a blank tape, halts exactly when a nontrivial positive ordinary Collatz cycle exists. | [Machine and Lean proof](turing-machines/README.md#16-state-blank-tape-cycle-detector) |
| 17-state binary Collatz beeping machine | From a blank tape, beeps infinitely often exactly when every positive Collatz orbit reaches 1. If b is the least counterexample, emits exactly b(b−1)/2 beeps. | [Machine, ordinary mathematical proof and finite checks](turing-machines/collatz-beeping17/README.md) |

These are correctness reductions. They do not prove the Collatz conjecture,
and make no minimality or record claim.

See [attribution and license status](turing-machines/ATTRIBUTION.md).

## Research notes

- [Theories K: a formal substitution catalogue](notes/set-theory/theories-k-substitution-catalogue.md) (2026-10-23 definitions draft). Precise first-order schemas, with established results distinguished from research reductions and outstanding proof obligations; no new full equivalence is claimed as formally verified.
