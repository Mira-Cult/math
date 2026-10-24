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

## Seventeen-state beeping machine

The [17-state construction](collatz-beeping17/README.md) is released from
`Mira-Cult/turing-machines`, commit
`116c88e23fb6580113b1f86f22816bdce316ba1f`, directory
`experiments/collatz-beeping17/`. Its exact table and two validation programs
are preserved in the public packet, with hashes in
[SOURCE.json](collatz-beeping17/SOURCE.json). The source repository is private;
the public proof and checks are self-contained.

Its arithmetic core is adapted from Charlie Reams's 14-state weak-Collatz
machine in [calr3/tinycryptids](https://github.com/calr3/tinycryptids/tree/ad9c597ad728f301400325b8e2115a4bb62a25d3/weakcollatz),
pinned to commit `ad9c597ad728f301400325b8e2115a4bb62a25d3`.
The upstream [README](https://github.com/calr3/tinycryptids/blob/ad9c597ad728f301400325b8e2115a4bb62a25d3/weakcollatz/README.md)
and [generator](https://github.com/calr3/tinycryptids/blob/ad9c597ad728f301400325b8e2115a4bb62a25d3/weakcollatz/build.py)
explicitly derive that 14-state design from the earlier 16-state release
documented above. The 17-state machine removes the bounded search's equality
and overflow handling, and adds a six-state input-counter increment and copy
routine. No upstream source files are vendored here.

Neither the upstream Lean theorem nor this repository's proofs for the other
two tables certify the 17-state table. The new article proves that table directly
in ordinary mathematics; no proof-assistant certificate is claimed.

## License choice

No repository-wide license has been selected. Public availability is not
an additional license grant. A root license choice remains with the
repository owner; no third-party source is relicensed by this notice.
