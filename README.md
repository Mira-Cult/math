# Public mathematical results

An index of results publicly released in this repository.

| Result | Exact scope | Sources and verification |
| --- | --- | --- |
| 12-state binary Collatz evaluator | On each encoded positive input, halts exactly when its ordinary Collatz orbit reaches 1. Universal positive-input termination is equivalent to the ordinary Collatz conjecture. | [Machine and Lean proof](turing-machines/README.md#12-state-input-evaluator) |
| 16-state binary Collatz cycle detector | From a blank tape, halts exactly when a nontrivial positive ordinary Collatz cycle exists. | [Machine and Lean proof](turing-machines/README.md#16-state-blank-tape-cycle-detector) |

These are correctness reductions. They do not prove the Collatz conjecture,
and make no minimality or record claim.

See [attribution and license status](turing-machines/ATTRIBUTION.md).
