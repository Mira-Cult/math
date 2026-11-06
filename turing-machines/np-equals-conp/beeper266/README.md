# A 266-state beeper for NP versus coNP

An explicit deterministic, two-symbol, single-tape Turing machine, started on
the wholly blank two-way tape. Its complete table has **266 states and 532
transitions**. It runs forever, with one designated transition event:

> The machine emits finitely many beeps if and only if NP = coNP.
> Equivalently, it emits infinitely many beeps if and only if NP ≠ coNP.

This result has a **conventional proof with scoped internal nonauthor model
reviews**. It is not a Lean theorem for this table. The separately formalized
[284-state machine](../beeper284/README.md) does not certify the
changed 266-state implementation.

## Start here

- [Proof and compression guide](PROOF.md).
- [Exact marked table](events.tm) and [267-state B-exit companion](machine.tm).
- [Reproducible source package](reproducibility/).
- [Verification status and evidence limits](VERIFICATION.md).
- [Overview of both machines](../README.md).

[Attribution and license status](ATTRIBUTION.md).

## Exact convention

States are 0 through 265. Start state, head position and blank symbol are all
0. The tape is indexed by the integers and initially contains only zeroes.
Every state/read pair has one row; every move is L or R and every destination
is a counted state. There is no halt, external input, preloaded program, or
free arithmetic routine.

The sole marked row is **`104 1 0 L 1 1`**, in the format
`state read write direction next-state event-flag`. Only that row beeps.
The table SHA-256 is
`c5b0a16ce6edba5df3372ab9d6290db8d7ca747a6660a9d10f3a9d1fc8e5331c`.

The companion has 267 states and 534 rows, with SHA-256
`668c5c91d2510aadc0fac6342f80fc3f4d248d6a2fd828d375a45b57e780e712`.
Its corresponding B exit is one transition after the marked event. The
headline 266 count does not use an exit-from-B observer on the same table.

## What saves eighteen states

The reference and candidate remain the two existential acceptance tests
`A(D(i),0,N(i))` and `A(j,i,(N(i)+1)^j)`. Equal returned bits refute a
candidate; unequal bits allow it to continue. Each finite comparison finishes.

Compared with the 284-state construction, the compression sequence changes
return detection and operation dispatch, then reuses dead reference-phase
carriers for candidate description and clock. Nine individually proved-zero
control occurrences are specialized, and the finite control layout is rebuilt.
The final inventory is **154 arithmetic/control-associated states plus 112
others**, including a seven-state return detector and the complete bootstrap.

The bank still has twelve physical register classes and initializes 1,909
fields. Fewer source variables or shorter average paths are not counted as
state savings by themselves. Every table, quotient, event map and initialization
cost must be included in the complete result.

## Provenance and review scope

The immutable producer is
`b6fb1987da70ac826fd8275e7726ee4e536af089`, tree
`e02554432cb76871bfd2ac6e339c342bdc0e3726`.
The separate review delivery is
`7a83222960fd1314668246fb5b4f549bea546059`, tree
`4530a51482412198ce56dba39f212281920df944`.
The delivery changes no producer bytes.

Separate source/control and physical model reviews examined that exact
producer within their documented scopes. They did not author the selected
construction. These were internal automated reviews, not external human
certification, exhaustive independent verification, or Lean/kernel checking.
Finite literal executions provide additional regression evidence, not a proof
of eventual silence. See [VERIFICATION.md](VERIFICATION.md) for the checks
actually repeated on this public package.

This construction does not decide NP versus coNP or claim global state
minimality. In particular, long quiet runs are compatible with either answer.
