# Source-preserving physical refinement to 284 states

The literal identities are in PUBLICATION.md (historical reference: `PUBLICATION.md`; outside this selected-only export). The frozen
source is byte-identical to `transfer328/control/attempt_reset/source.py`
in producer `81147084e3d81219073ba6b8f0e6a3e3af8cf116`, SHA-256
`4f1f6f317eb196b8d09a67439893622a759c43ef4e02e30adae4e04b0eb39515`.
The [291 source and physical proof](../transfer328/PROOF.md), its
[302 source adapters](../transfer328/PROOF302.md) and the normalized endpoint
are therefore the exact source theorem control. This continuation changes
only physical lowering and the resulting allocation/control/quotient maps.

## Closed swap and actual entry premise

For arbitrary natural L,R and a distinct zero work coordinate Q, the three
terminating additive transfers have successive boundary values

    (L,R,Q)=(old_L,old_R,0)
           ->(0,old_R,old_L)
           ->(old_R,0,old_L)
           ->(old_R,old_L,0).

Each destination is zero when required, every other logical coordinate is
preserved, and work is zero at the exit. Each transfer decreases a finite
source value, so the whole region terminates. There is no source escape or
event in the region. It exactly implements the simultaneous orientation swap.

Q=0 is an external-entry premise. The first transfer's loop header is also
reentered while Q accumulates units and must not be asserted zero at every
visit. Each of the two actual source swap sites has one outside incoming
edge, from the turn HALF branch. The fresh abstract branch image on that
outside edge proves Q=0; the guard itself leaves Q unchanged. The joined
loop-header image legitimately includes nonzero Q. The full intermediate
invariant above, rather than an incorrectly zero joined header, covers
internal visits. [PROOF.md](PROOF.md) gives the new region contract and its
exact source matcher.

All operations are existing INC/DECNZ transfers. No new atomic instruction,
alphabet symbol, track, caller tag or supplied program is introduced.
Fresh allocation gives 19 allocated ->15 projected logical ->12 physical
classes. The operated class equals its logical ghost sum, with all other
peers zero at each operation. At both swap sites L,R,Q occupy distinct
physical classes 8,1,10. The new certificates check every intermediate step,
including the period when both Q and a partly consumed L are nonzero.

The inherited closed clock and seed entry masks and restored sole exits are
checked again on this graph. The complete graph has 362 sharing closure
edges and 184 reached operation ownership obligations; source equivalence
alone would not justify the new aliases. This source also retains all prior
certificate master, destructive attempt reset, input suffix and scratch
conditions. Both acceptance phases remain existential.

## Physical segments and paid return interface

At admitted boundaries the relation records the lexical path, physical head,
entire unary bank and reserve, live masters, zero scratch and class sums.
Inherited INC, DECNZ and HALF contracts give positive finite physical
segments on every admitted finite tape. HALF gives quotient and old parity;
the turn branch may commute it past this swap only because the swap does
not read or write that operand. Its existing interference/ownership proof
is regenerated, not presumed from a numerical slot name.

Maximum prepared path length is 55 and maximum path zero-count is 11. Paid
dispatcher depth 13 equals 11+2 for the preparation zeros. Its complete
countdown/return chain 0..13, the `6.continue.0` read-one entry to
`4.dispatch.13`, and the finite left scan followed by root-sentinel recovery
are checked with this new grammar. The remaining 211 current named runtime
rows agree exactly with the inherited runtime after replacing numerical
states with their frozen names. All 56 operation-entry
rows are checked separately. The 12 active classes fit the 1909 blank-initialized
zero fields. The entire writer and selector/return machinery are counted.

The source parser, normalized witness coverage, one-transition empty wrapper,
coupled j description/exponent, complete-prefix padding and internal guards
are unchanged. The source remains exactly the same even where physical
primitive histories differ. All finite comparisons terminate, both equal-bit
cases refute, and unequal comparisons advance silently.

## Fresh domain, all-row maps and events

The full producer has 294 raw states. All 588 raw rows satisfy its ordinary
quotient to 291 B states /290 marked states. The fresh completion domain is
derived from this table's names and quotient. Every raw preimage of an
excluded quotient row is checked against the named preparation, separator,
HALF-temporary or selector-entry semantic facts. Membership in a totalization
request list is not an exclusion proof.

There are 13 excluded quotient rows and 15 raw preimage row occurrences.
The silent sink has no admitted predecessor. Completion preserves all 569
retained rows of the 291-state B parent. On admitted runs the original and
completed parents therefore agree exactly, step for step, including tape and
head. Their behavior on an excluded prepared configuration need not agree.

All 582 completed-parent rows satisfy the fixed quotient to 285 B states,
with B a distinguished singleton. Every target exists and every state has
both binary rows. The companion starts outside B and neither B row targets
B. Marking its ingress yields each B exit one physical transition earlier.
All 570 ingress rows satisfy the event quotient, giving 284 states/568 rows
and sole marked row `99 1 0 L 1 1`. Earlier numeric event states are not used.
The published completion plan is fixed input; replay does not run discovery.

Every admitted primitive has a positive finite realization, and each closed
swap is a finite composition of such primitives. Administrative contractions
contain no jump-only cycle; erased zero resets are grouped with the next
retained action. Every infinite source execution therefore has infinitely
many retained positive finite physical segments. The exact event relation
transfers the source theorem: finite designated events iff NP=coNP, infinite
physical execution in either case, and infinite events/1-acceptance iff NP
differs from coNP. Silence cannot be an unfinished transfer or cleanup.

## Evidence boundary

Actual blank entry, all events in the finite replay, and real comparison
boundaries are checked from the new literal tables with independent engines.
Prepared operation/lexical fixtures are labeled separately. Damaged closure,
ownership, domain and row maps must fail. Independent source-region review
supplies the external-entry scratch proof, while binary review supplies
the new representation, complete maps and actual execution evidence.
Both bind a separate immutable producer commit. These are conventional
proofs with internal nonauthor model review, not external human or Lean
certification. No finite replay decides eventual silence.
