# Complete normalized-source and physical composition

This manuscript identifies the complete 360-state marked machine. Its source
and physical ingredients have separate proofs and finite certificates; no
permanent claim ID is introduced. Independent review is a later binding step.

## Source relation and all finite inputs

The normalized control is the frozen 387 source at SHA-256
`7d98b2beb3676f7d0e4f0d6785a5a78d4817f05f23ec38c82635a3ea4b31a039`.
Its canonical [endpoint theorem](../phase_search/PROOF.md) depends on the
[independent-write certificate acceptance theorem](../source/PROOF.md).
The new source is control/parser/source.py (historical reference: `control/parser/source.py`; outside this selected-only export), SHA-256
`46f2a7273f0dfeca71c851f02b5e364836f62fad4eef622ea6a8ee48e6515de5`.

For every natural input i, let N(i)=n and D(i) be the low-first marked-pair
parser's length and reversed-payload sentinel description. The new caller
computes the same n,D(i), and residual scan value
`floor(i / 2^(2n+1))`, leaving i unchanged. The
[parser proof](control/parser/PROOF.md) treats every even input, arbitrary
higher ignored bits, a high marker with virtual zero payload, the zero
integer and every finite prefix. Marker HALF consumes the original first
division on success and the original terminator division on failure. Payload
HALF commutes only past its operand-independent update.

The [acceptance refinement](control/PROOF.md) proves
`accept_new(e,x,C)=A(e,x,C)` for all natural triples. It consumes the old
positive state as an ordinal selector, skips exactly s+z-1 records without
accumulating them, and computes the final record normally. Zero and all-one
finite descriptions, absent/truncated records, overlapping windows, the
virtual zero terminator and repeated lookup reset are included. Direct HALF
branches preserve both independent write bits and relative direction. C=0
fails after the unique empty-certificate attempt; acceptance at transition C
succeeds and zero state is absorbing. Description, input and certificate
masters remain intact across destructive attempts.

Consequently the exact compared bits remain
`A(D(i),0,n)` and `A(j,i,(n+1)^j)`. Equality in both (1,1) and (0,0) refutes
the candidate; inequality silently advances to i+1. Every candidate begins
with one event. Description and exponent remain the same integer j.

All normalized coverage hypotheses are inherited unchanged: a complementary
verifier initializes its positive workspace independently of the ignored
suffix, preserves its negative certificate during preparation, has runtime
and witness bounds in n, accepts every empty prefix in one transition, and
has complete reachable records before padding. Internal guards make larger
external bounds harmless. Thus fixed candidates are in NP in ordinary bit
cost; the normalized reference is NP-complete; and a correct complementary
candidate exists iff NP=coNP. The new source does not use the old forced-write
nondeterminism theorem.

Every normalization, clock construction, finite acceptance call, certificate
reset and comparison terminates. Wrong candidates have a finite counterexample.
A correct candidate performs infinitely many finite comparisons silently.
The inherited argument therefore gives finite events iff NP=coNP and an
infinite source execution in both cases. Internal histories and physical times
are not equated with 387,407 or the completed serial backend.

## Lowering and physical ownership

The two acceptance lowering rules and the marker-loop rule emit only inherited
INC, DECNZ, HALF and lexical control. The native HALF replaces a natural by its
quotient by two and succeeds iff the old value is odd. The rules introduce no
new physical instruction, return-tag alphabet, tape track or supplied program.
Their guards and finite positive realization are in the two linked proofs.

Moving HALF before an operand-independent parity branch is compatible with
the source allocator because its operand is source-live through the original
branch. No result is cleared before its source lifetime. The rejected 353
experiment violated precisely this condition and is not used here.

The concrete certificate chain is:

1. Fresh source CFG and 26 allocated registers.
2. Native-aware contextual closure and the fixed finite-control plan.
3. Projection to 24 used logical coordinates, with omitted coordinates zero.
4. Eighteen physical classes, each equal to the sum of its logical ghost values.
5. Existing paid unary kernels, preparation, selectors, returns and bootstrap.

At every primitive occurrence all other members of its physical class are
zero. This is checked over every abstract edge, including both HALF outcomes;
the names are not unrestricted aliases. Every primitive has a positive finite
segment on every admitted finite tape. Removed administrative paths are
acyclic under the explicit control relation. Induction over source segments
preserves the decoded values, master ownership, scratch and boundary relation.

The physical builder emits370 raw states,367 B states and 366 marked states,
with all rows and targets present. Both acceptance call sites and the entire
unbounded caller, clock and certificate enumeration, reset, scratch, program
production, blank initialization and totalization are included.

## Fresh excluded-row completion

The literal runtime has 226 common non-grammar binary rows identical by name
to the actual387 producer. The source changes only primitive control and
ownership, not their admitted entry or return representation. The new maximum
control path 74 is below the paid bootstrap span 3822; eighteen active fields
fit the 1909 initialized zero fields. Actual blank execution establishes the
clean entry separately; primitive induction covers all later entries.

The named exclusions are the same primitive-domain facts proved in
[the native half proof](../compiler/native/PROOF.md),
[native composition](../native/COMPOSITION.md), and
[the named exclusion proof](../tape_local/completion/PROOF.md#the-thirteen-excluded-rows).
They are not inferred from missing rows or from a totalization list. In
particular native selection reaches a base one, preparation pads have their
specified zero values, HALF temporary boundaries have their proved symbols,
and bootstrap preparation supplies its required zero symbol.
Every suffix scan has its finite delimiter and every cleanup restores the
prepared boundary. No new source path violates these contracts.

[coordinator/select.py](coordinator/select.py) derives holes using the new
raw names, source requests and exact quotient. A quotient row is excluded
only if every raw preimage is semantically excluded. Its 13 holes have all 15
raw preimages accounted for, including the two sink rows. The silent sink's
only incoming rows are this excluded set; it has no admitted predecessor.

The fixed plan changes only those 13 rows. All 721 retained rows of the 367-state
B parent are unchanged. Induction on its admitted execution gives exact
physical-step, tape and head agreement between that parent and the completed
parent. This is an admitted-run refinement, not arbitrary-configuration
equivalence to the earlier totalization.

The next quotient is an ordinary all-row relation, checking all 734 equations
of the completed parent and keeping B a singleton colored state. It yields
361 B states. Every new state has both rows and every target exists. Discovery
and replay are separated: fixed replay validates the published mapping without
running a search. The discovery routine also protects B during recursive
target merges; a silent fully excluded state is not silently colored as B.

## Events, progress and literal identity

The B companion starts outside B and neither B row targets B. Its ingress
adaptation marks exactly the rows entering B, one transition before the
corresponding B exit. The subsequent all-row event quotient checks all 722
equations and yields360 states/720 rows. The sole marked row derived from
these maps is `111 1 0 L 1 1`; earlier numerical identities are irrelevant.

The literal marked SHA-256 is
`a606d1a650e76406dafd4b830baaa74d541c4b4e930348f971f2ce4f20de8265`.
The metadata (historical reference: `machines/selected360/metadata.json`; outside this selected-only export), full maps and completed
parent give the other exact identities. No state is excluded as a halt state.
The initial tape is entirely zero, start/head/blank are zero, and moves are L/R.

Every admitted primitive boundary has a positive finite physical realization.
Source administrative steps contracted by lowering form finite acyclic paths;
each infinite source execution contains infinitely many such primitive segments.
Eliminated zero resets need not receive individual physical segments. An infinite
source execution therefore cannot become a finite physical run or get stuck
inside a silent administrative segment. Source events and marked events agree
one for one, with the fixed companion time shift just proved. Combining with
the source theorem proves finite marks iff NP=coNP and infinite marks iff
NP differs from coNP, with infinite physical execution in either case.

Literal traces, prepared fixtures and damaged-certificate checks support the
composition. They do not replace the universal segment arguments and do not
decide eventual silence. This is a conventional proof with explicit finite
certificates; no Lean theorem is asserted to identify the literal table.
