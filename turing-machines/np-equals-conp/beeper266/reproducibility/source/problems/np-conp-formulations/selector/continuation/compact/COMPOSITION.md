# Complete 446-state beeper: proof chain

The selected deterministic binary single-tape machine has 446 states, 892
rows and one marked transition. It begins with an all-zero two-way infinite
tape, state zero and head coordinate zero; every row writes 0 or 1 and moves
left or right. No halt state is excluded. The machine runs forever and has
finitely many applications of its marked transition if and only if NP = coNP.

This document composes conventional mathematical arguments and finite
certificates. Independent review, executable tests, exact producer binding
and remote CI are different evidence categories. The new source is a new
construction, not a recovery of historical unpublished bytes.

## 1. Effective search for a complement verifier

The source `source/certificate_popfirst_power.py`, SHA-256
`96f254475ce226a2d5783b259abf0b414ae8d119c4e01430d48adf3fe3f60ac1`,
enumerates total finite descriptions of deterministic relative-direction
binary tape machines. Each simulated computation receives a finite
certificate on the negative half-tape. The physical beeper generates every
certificate itself by finite arithmetic and exhaustive enumeration.

The acceptance function A(e,x,C) tries all 2^C certificates of C bits and
simulates each for C steps. Every decoder, clock, exponent and enumeration
loop terminates on finite arguments. Malformed or missing description
records receive defined values; no candidate can stall a finite check.
All integer values and search bounds remain unbounded.

For an n-bit raw word Y with low-bit integer y, the reference language is
K(Y)=A(2^n+y,0,n). The source proof establishes K in NP and polynomial
many-one completeness using a guarded verifier, a finite input writer and
complete-prefix padding. A candidate j recognizes the complement of K if
A(j,E(Y),(n+1)^j) agrees with it on every Y, where E(Y)=1^n0Y. Padding the
candidate's complete description supplies arbitrarily large indices for the
same verifier, so the coupled exponent covers every polynomial verifier.
The one-step empty-input wrapper handles the clock that is always one when
n=0. The orientation copy after its two-step nonempty relay is explicit.

The controller emits once per candidate and enumerates every finite input
comparison in order. Equality between reference and candidate bits defeats
the candidate: one equality is unsoundness and the other incompleteness.
Each incorrect candidate has a finite witness and is eventually defeated.
If a least correct candidate exists, only finitely many candidates emit,
then input checking continues forever silently. If none exists, infinitely
many candidates emit. Correct-candidate existence is equivalent to NP = coNP.
See `source/PROOF.md` for the full encoding, complexity and progress proof.

## 2. Natural arithmetic and call implementation

The inherited compiler represents unbounded naturals by a fixed finite bank
of unary tape blocks. Source storage is allocated conservatively using live
ranges and acyclic call heights. The selected tuple captures, affine sums,
record pop and paired halving rules retain their previously published
contracts. Their exact source and proof bytes are inherited in `pins.json`.

The new direct-call rule removes staging temporaries only for admitted pure
arguments. Complex arguments are evaluated left to right before any callee
parameter is overwritten. Caller reads, captured values, callee parameters
and arithmetic scratch obey explicit disjointness guards. Calls containing
nested effects or destructive source reads retain the previous lowering.
The return rule consumes the final scalar call's return directly into the
equality kernel after the earlier operand has been captured. No later call
can overwrite that return. Unsupported cases use the inherited rule.
`compiler/PROOF.md` establishes these contracts and their evaluation order.

The arithmetic kernels terminate on finite naturals and leave the required
scratch cells zero at complete boundaries. The program's finite clock,
description and certificate loops therefore become finite primitive
computations. The fixed number of allocated cells is not a bound on their
values or on tape length. The selected complete machine allocates 27 cells.

## 3. Certified zero entry and finite control contraction

The inherited zero-entry transformation supplies a post-fixed abstract
invariant and a separately replayable certificate. Its domain is the clean
all-zero source bank reached by the paid blank bootstrap. The selected
producer emits its exact output as `pre-control-grammar.json`.

The subsequent five-move plan preserves the graph of all ordered INC,
DECNZ and beep occurrences, both outcomes of every DECNZ and the initial
occurrence, after contracting finite administrative jumps. Every jump-only
cycle is rejected. `GRAMMAR_PROOF.md` proves the resulting finite-stutter
simulation and cofinal progress. The plan is explicit and source-specific;
the selected builder does not run an optimization search. Its final grammar
is independently bound to the preceding zero-entry certificate.

## 4. Paid binary runtime and blank initialization

The inherited binary runtime implements every primitive on its valid clean
control-path and unary-bank configuration. The shared selector's finite
scans find marked nonempty blocks and restore the mode/control cells. Its
bootstrap entry uses a separate preserved ABI. Every selected primitive
terminates in finitely many physical steps, even as the naturals grow.

The five-state blank bootstrap and the complete selector, dispatch, program,
register entries, scratch handling and event mechanism are included in the
449-state raw table. The initializer must be checked on those actual bytes:
it reaches source entry with head -3818 and one-cells
{-3821,-3820} union {3,5,...,3821}, with no prior event. This is the inherited
clean bank after translating the control origin. The new literal receipt is
recorded in the independent review; an older table's execution time is not
substituted. The compile-time path and register bounds are checked against
the paid bootstrap's fixed capacity. Initial unused cells are also paid.

The table is complete and total. A counted silent sink handles invalid
runtime-domain behavior; valid-run cofinality proves it does not intercept
the mathematical search. It is not used to make false candidates silently
stall. Each finite source stage consists of finitely many finite primitive
and physical segments, so every such stage is reached in finite physical
time, including arbitrarily late input checks after a last event.

## 5. Quotients and the precise marked event

An exact all-row state map reduces the raw 449-state machine to its 447-state
B-exit companion. Every mapped row preserves its written symbol, head move,
target and B color. This is an all-configuration quotient, not a bounded-run
guess. Both rows of every physical state are checked.

The B-exit machine starts outside B and is total. Each entrance to B is
followed by a B exit exactly one physical step later, and every B exit has
that unique preceding entrance. Moving the event to ingress preserves the
ordered event count and shifts its physical time by one step. The event
quotient then preserves both rows including their event bit, producing 446
states. The unique marked row is:

```text
105 1 0 L 1 1
```

The sixth column marks the applied transition. The event table SHA-256 is
`415489a4537df6d3c7bfa2f14cd3bd03a2763d94b889b0a72bffd220e9e3f70e`.
The B companion SHA-256 is
`423e3f0776b1b34b45aca620cf9591c0eecbec7f437997a1b7a30ffef3bf9d1c`.
The source begins beeping after finite event-free initialization. Neither
physical halting nor an arbitrary finitely visited state defines the event.
The composition above gives exactly the requested eventual-silence polarity.
