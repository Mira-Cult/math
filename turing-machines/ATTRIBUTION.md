# Attribution and license status

## Twelve-state evaluator

The construction originates in Pascal Michel, *Simulation of the Collatz
3x+1 function by Turing machines*, §5.4, machine M8 (13 states, 2 symbols),
[arXiv:1409.7322v1](https://arxiv.org/abs/1409.7322v1).
The released 12-state table removes a redundant state on the valid-input
return path. The Lean proof checks the exact released table directly; it
does not assume that the state reduction preserves behavior.

## Sixteen-state cycle detector and arithmetic proof

The maximum-search strategy and unary-hole starting point are due to
Charlie Reams's 23-state weak-Collatz construction in
[calr3/tinycryptids](https://github.com/calr3/tinycryptids/tree/c73bbd5377d4a06285660c170fccea56cf724155/weakcollatz),
pinned to commit `c73bbd5377d4a06285660c170fccea56cf724155`.

The released 16-state table redesigns the arithmetic and tape endpoints.
Its proof establishes the new table directly; the upstream theorem for the
23-state machine does not certify this redesign.

`proofs/CollatzTM/Arithmetic.lean` adapts the bounded-round induction and
least-cycle-maximum proof structure from upstream
[`lean/TinyCryptids/WeakCollatz/Spec.lean`](https://github.com/calr3/tinycryptids/blob/c73bbd5377d4a06285660c170fccea56cf724155/lean/TinyCryptids/WeakCollatz/Spec.lean),
using the shortcut map and checking it with Lean 4.30.0. Attribution is also
retained in that source file. The unused upstream source files are not
vendored; the release builds without importing them.

## License choice

No repository-wide license has been selected. Public availability is not
an additional license grant. A root license choice remains with the
repository owner; no third-party source is relicensed by this notice.
