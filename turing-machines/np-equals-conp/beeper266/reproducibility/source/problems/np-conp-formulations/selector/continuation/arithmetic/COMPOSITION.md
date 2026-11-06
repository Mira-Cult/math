# Composition for the complete 485-state machine

The selected deterministic binary single-tape blank-start machine emits
finitely many occurrences of its one marked transition **if and only if
NP = coNP**. It runs forever in either case. Quasihalting is eventual silence
of that event. Neither physical halting nor finite visitation of an arbitrary
state is substituted for this condition.

This is a new construction continued from the reviewed 581-state producer.
It is not labelled historical recovery. No permanent claim IDs are allocated
or changed. The frozen 1,036-state control, recovered experiments, 818-state
producer and 581-state producer retain their exact bytes.

## Mathematical search

The exact source is forced_relative.py (historical reference: `source/forced_relative.py`; outside this selected-only export), SHA-256
`c7bcab7ec604f443b67ae44e25b755bd7f3b09e0933e31f842758ad1f7e35f57`.
Its [source theorem](source/PROOF.md) proves the following chain.

1. A finite natural description is a total unary-record program, extended by
   a virtual zero tail. Every bounded nondeterministic simulation terminates,
   including incomplete records, zero clocks and branch overflow.
2. The simulated choice bit is also the written bit. An explicit three-step
   simulation converts an ordinary binary nondeterministic transition into
   this model. Wrong forced writes enter a permanent rejecting sink. Duplicated
   orientation control then converts absolute moves into relative turns. This
   pays constant time overhead and polynomial description length; constrained
   writing is not assumed universal without a construction.
3. The fixed reference language K contains an n-bit raw word Y precisely when
   description `2^n+value(Y)` accepts the blank tape within n transitions.
   The new encoding gives K in NP. A finite input writer, an internally guarded
   time-layered recognizer, the explicit simulation above and unused-record
   padding give a polynomial many-one reduction from every NP language.
   Hence K is NP-complete and its complement is coNP-complete.
4. Candidate j is its described machine on `1^n 0 Y`, clocked by `(n+1)^j`.
   Every fixed candidate is in NP. Complete-prefix padding gives arbitrarily
   large indices for the same machine and unchanged running time. A wrapper
   accepts the empty encoding in one step and restores the exact nonempty
   input, head and correctly recorded orientation. These facts establish
   coverage despite coupling a description with its exponent. A correct
   candidate exists exactly when NP = coNP.
5. The controller enumerates all natural j and every finite raw Y. Equality
   between the two acceptance bits is a finite counterexample to recognizing
   the complement. Both unsoundness and incompleteness are detected. The
   least counterexample to each incorrect candidate is reached after finitely
   many terminating checks. Thus a least correct candidate, if it exists,
   causes eventual silence; if none exists every candidate is rejected and
   a new event is emitted. The initial event has the same designation.

The new description codec changes K and individual event histories. There is
no assertion that this source has the same ordered event trace as the older
581-state source. The shared endpoint is the proved NP=coNP equivalence.

## Source to primitive execution

The selected producer (historical reference: `build_selected.py`; outside this selected-only export) enables pure affine expressions and
updates, mixed tuple literals (historical reference: `compiler/MIXED_TUPLES.md`; outside this selected-only export), the
[unary-record and paired-halving rules](KERNEL_PROOF.md), and the inherited
source-lifetime allocation. Direct affine assignments, affine result forwarding
and the experimental whole-record-lookup rule are disabled. The exact
configured classes, source and finite plan are hash-bound in the selected
metadata (historical reference: `machines/selected/metadata.json`; outside this selected-only export).

The [affine proof](compiler/PROOF.md) establishes correct arithmetic and zero
scratch boundaries. Tuple capture evaluates every nonliteral RHS before any
destination write, preserving parallel reads and eventful calls while omitting
literal temporaries. A unary-record block consumes precisely one `1^a0` record
and its virtual zero tail; the new half kernel consumes pairs of units with
the exact quotient and remainder. These proofs retain unbounded naturals and
finite termination of every primitive loop. They do not introduce an arithmetic
oracle or fixed word size.

The frozen [lifetime-allocation proof](../compiler/PROOF.md) supplies disjoint
simultaneously live source slots, distinct active call heights, owned temporary
storage and preserved return values. The original source AST remains available
to its interference checks. The new rules observe the same live-value relation
and preserve ordered source events. Local source steps may take different
finite numbers of primitive steps.

## Grammar and physical runtime

The inherited zero-entry simplification certifies the separately emitted
pre-rotation grammar (historical reference: `machines/selected/pre-rotation-grammar.json`; outside this selected-only export). The
rotation certificate (historical reference: `machines/selected/rotation-certificate.json`; outside this selected-only export) then binds
it through the fixed four-move plan (historical reference: `grammar-plan.json`; outside this selected-only export) to the final grammar.
The [grammar proof](GRAMMAR_PROOF.md) and full graph comparison preserve every
one of the 622 primitive occurrences and both possible successors of each
DECNZ, including breaks, continues and the event. This is an all-branch
certificate, not an inference from one bounded execution. The older zero-entry
certificate is not falsely relabelled as a certificate of the rotated grammar.

The frozen [runtime proof](../../PROOF.md) supplies closed-sequence sharing,
the unary register representation, finite register-selection scans, finite
control returns, arithmetic primitives and the counted blank bootstrap.
The actual selected program has 31 physical natural registers and maximum
leaf path 90, within the bootstrap's established bounds. Register values,
candidate indices, tape contents, clocks and model sizes have no finite bound.

The exact blank-entry obligation is that the raw literal table reaches state
435, head -3818, with one-cells
`{-3821,-3820} union {3,5,...,3821}` and no events. The companion state is 434.
Independent literal replay of these exact bytes supplies this finite fact;
capacity inequalities alone are not a replacement for it. Thereafter the
unbounded representation invariant and finite primitive proofs give cofinal
progress through every finite source prefix. Infinite administrative stalling
cannot erase the later events of an incorrect-candidate search.

## Total table and designated event

The emitted raw table has **488 states and 976 rows**. The ordinary exact
quotient preserves all actions and B-exit colors and has **486 states and
972 rows**. Moving B exits to their incoming transitions changes no tape
action and moves every event one physical step earlier. The initial state is
outside B and the machine is total, giving the reverse correspondence as well.
The exact event-colored quotient has **485 states and 970 rows**. Its sole
marked row is:

```text
116 1 0 L 1 1
```

The columns are `state read write move next event`; the mark belongs to
application of this row. The tape is two-way infinite and initially all zero;
the head and start state are zero, the alphabet is `{0,1}`, and every move is
L or R. Both read-bit rows and every destination exist for every state. All
bootstrap, embedded control, scratch management, arithmetic, selector,
event-adaptation and totalization states are included. No halt state is excluded.

The selected event-table SHA-256 is
`2dc724ec450da38af3f6dd156891d491d0887f2969d14a1a3b51832e41a79964`.
Its B-exit companion SHA-256 is
`0aadf1578fa698047d5869788ad643bdc45a1ab0ee5587e4263dcac9b1a1e31d`.
Finite event-free startup, cofinal simulation, event relocation and both exact
quotients preserve finite versus infinite event count. Together with the source
theorem this proves the stated eventual-silence equivalence.

The evidence comprises conventional proofs, finite certificates, executable
fixtures and separately attributed independent model-agent reviews. It is not
proof-assistant certification or an experimental decision of NP versus coNP.
The independent delivery record binds acceptance to immutable Git objects and
distinguishes local reconstruction from the actual remote CI result.
