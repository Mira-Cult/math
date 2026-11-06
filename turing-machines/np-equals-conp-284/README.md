# A 284-state beeper for NP versus coNP

An explicit deterministic, two-symbol, single-tape Turing machine, started on
the wholly blank two-way tape. Its table has **284 states and 568 transitions**.
It never halts. One particular transition is designated a beep:

> The machine emits finitely many beeps if and only if NP = coNP.
> Equivalently, it emits infinitely many beeps if and only if NP ≠ coNP.

The equivalence for the exact marked table and blank start is proved in Lean.
It is a reduction to an infinite-run property, not a resolution of NP versus
coNP. No finite quiet observation establishes NP = coNP.

## Start here

- [Proof guide](PROOF.md): the mathematical argument and its implementation.
- [Lean interface guide](INTERFACE.md): how to check what the formal theorem says.
- [Exact marked table](events.tm) and [285-state B-exit companion](companion.tm).
- [Formalization](formalization/): the selected source and its local dependencies.
- [Reproduction and verification status](VERIFICATION.md).
- [The smaller 266-state machine](../np-equals-conp-266/README.md), whose proof
  is conventional rather than Lean-checked.

[Attribution and license status](ATTRIBUTION.md).

## What it searches for

The machine enumerates candidates for an NP verifier of the complement of
an NP-complete reference language. It beeps when beginning a candidate, then
compares the candidate and reference on successive inputs. Both acceptance
tests are existential searches over certificates. The candidate is refuted
when the bits are equal, including both `(0,0)` and `(1,1)`.

A correct complement verifier survives forever. The proof supplies such an
enumerated candidate exactly when NP = coNP. Each individual comparison
terminates, so silence cannot result from a stalled finite comparison.

## Exact machine convention

States are 0 through 283. The head starts at integer position 0 in state 0,
and every tape cell initially contains 0. A row gives
`state read write direction next-state event-flag`. Every state/read pair
has exactly one row. Moves are one cell left or right. There are no halting
rows, external input, preloaded program, or uncounted interpreter states.

The sole marked row is **`99 1 0 L 1 1`**. A beep means taking that row, not
visiting an arbitrary state or taking both exits of state 1. Time `t` in Lean
labels the transition out of the configuration after `t` executed steps.

The table SHA-256 is
`0c924f63d3cdd89f97078aef409010fa868b189466ab186a17e105f81e9279aa`.
The 285-state companion has SHA-256
`5b2e39f9df0b872c0854273df7f2b7f050fdce525363538dea5c9dfabdcad868`.
Its exit-from-B convention has the corresponding event one transition later.
That companion correspondence belongs to the conventional construction;
the principal Lean theorem below is specifically for the 284-state marked table.

## The formal statement

The reader-facing endpoint is
[`Bootstrap284AlignedFromBlank.literal_table_silent_iff_classes`](formalization/Shared/Beeping/NPcoNP/Bootstrap284AlignedFromBlank.lean).
It is a closed conjunction of two facts:

1. The pinned literal table text parses to `Table284.machine`.
2. This machine is eventually silent if and only if
   `ComplexityTheory.NP = ComplexityTheory.coNP`.

It assumes neither NP = coNP nor NP ≠ coNP. It does not require the reader to
provide a simulation certificate, a good candidate, or an initialization
hypothesis. The complexity classes are the pinned upstream definitions,
not classes defined by this beeper's behavior.

The proof reaches a correctly aligned graph/tape configuration from the
literal blank start, including the first beep. Every graph step then has a
positive finite physical realization with the same event word. Matching
prefixes are cofinal on both sides, which transfers eventual silence in both
directions.

The mathematical sources are pinned to
`6108c93565701e64775a3f1cbf9627d35c4c30e3`. The upstream owner reports kernel
build and targeted axiom checks at that revision. A separate automated
nonauthor source review examined central mathematical interfaces and selected
proofs. That was not an exhaustive audit, an independent Lean rebuild, a human
expert review, or a formal PR approval. The [verification receipt](VERIFICATION.md)
records exactly which checks have and have not been reproduced for this copy.

## A note about historical source comments

The unchanged formalization contains earlier conditional theorems and comments
describing obligations that were open when those files were written. The
current endpoint discharges the relevant candidate-coverage and reachable
initialization obligations. Read the closed endpoint and its dependency chain,
using the [interface guide](INTERFACE.md), rather than treating an old progress
comment as the current theorem statement.
