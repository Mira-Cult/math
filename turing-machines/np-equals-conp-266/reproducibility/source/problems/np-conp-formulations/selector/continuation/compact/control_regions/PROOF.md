# Occurrence-specific control and paid comparison experiments

The smallest complete construction in this directory has **266 marked states
and 267 B-exit states**. Its ordinary parent has 272 raw states, 270 B-exit
states and 269 marked states. It saves five complete states against the reviewed
271-state producer, and eighteen against the published 284-state machine.
This final composition changes the source by reusing dead reference-phase
carriers, specializes nine proved-zero control occurrences, and shortens the
retained control paths. It has new source, control, storage, completion and
event maps. No predecessor review acceptance applies to its changed bytes.
No permanent claim ID is introduced here.

## Selected 266-state composition

The selected source is [sources/reuse_clock_roles.py](sources/reuse_clock_roles.py),
SHA-256 `0b0bf4045fec4392de646047d65db90f1959b8086156a418aa40f45e355bb11b`.
The final parent and selected artifacts are
[reuse_clock_roles_zero_geometry](machines/reuse_clock_roles_zero_geometry/metadata.json)
and [reuse_clock_roles_zero_geometry_selected](machines/reuse_clock_roles_zero_geometry_selected/metadata.json).
The separate original-source checkpoints below retain their exact source and
review boundaries; the source identity of those checkpoints is not claimed
for this new winner.

### Exact source comparison relation

Up to and including the returned reference bit, the selected source and
`phase_swap/source.py` execute the same statements. Write `N=N(i)`, `D=D(i)`
and `R=A(D,0,N)` at that boundary. The live enumeration carriers are `j,i`,
the reference bit is `expected=R`, and the old reference description `e=D`
and time `n=N` have no remaining reference-phase use.

The predecessor computes `clock=(n+1)^j`, seeds `2^clock` witnesses and uses
description `j`, input `i` and time `clock` for the candidate. The selected
source instead performs these exact assignments:

```python
e = n
n = (e + 1) ** j
e = j
```

Thus their successive values are `(e,n)=(N,N)`, `(N,(N+1)^j)`, and
`(j,(N+1)^j)`. There is no use of old D after the first assignment and no use
of old N after computing the power. Let C=`(N+1)^j`. The candidate seed loop
starts at branch=1 and consumes a copy of n=C, so it produces exactly `2^C`
as before. Every attempt sets `left=branch`, `right=i`, `state=1`, and
`steps=n=C`. The candidate copies `digit=e=j`. All remaining simulator and
comparison statements are unchanged.

Induct on candidate attempts in the same descending witness order, and within
an attempt on the remaining step count. Both versions have the same immutable
description, input, certificate, state, tape halves and time at the first
simulated step. Their record lookup, write, relative turn and three-transfer
orientation exchange are identical. They therefore return the same acceptance
bit for every witness and the same existential candidate bit Q. The unchanged
XOR/comparison tail exits the candidate exactly when R=Q, including both
`(0,0)` and `(1,1)`, and increments i when R differs from Q.

On either exit path the old `e,n` roles are dead. The next comparison starts
with the unchanged tuple `scan,n,e=(i,0,1)` before either value is read; the
next reference attempt also initializes its tape halves, state and time.
This is a comparison-boundary equivalence, not equality of the two internal
stores at every source statement. It preserves every finite comparison,
the exact `(j,i)` coverage order and ordered events. Every new assignment,
power, seed and attempt is finite by the same natural-number loop ranks as
the predecessor. Neither source can silently stall during a finite stage.

For an empty parsed prefix N=0 the new carriers pass through e=0, n=1, e=j;
the reference still has time zero, and the candidate retains all high input
bits in i with time one. Description padding, exponent j and witness guards
are unchanged. The reference and candidate predicates therefore remain
`A(D(i),0,N(i))` and `A(j,i,(N(i)+1)^j)`. The predecessor theorem and ordinary
bit-cost NP membership arguments apply through this explicit source relation,
not through byte identity or a deterministic zero-witness execution.

### Nine occurrence certificates and complete geometry

The general zero-occurrence argument proved below applies to this fresh
source grammar. Its first contextual certificate has 310 unfolded occurrences.
The new pass's input has 303 occurrences and a postfixed invariant with 391
checked edges. It replaces nine proved-zero DECNZ occurrences: the four paired
simulation roles described below, plus one `$liveframe.0.2` occurrence at
index 143 in the source-specific input grammar. That additional site has mask
exactly 1; its admission does not rely on identifying the cell with a source
name from the predecessor allocation. The certificate records the complete
path, all register masks and operand string. Exact occurrence reinterning and
five checked empty-control reductions link it to the new pre-control grammar.

The frozen geometry plan preserves the entire retained primitive graph,
including both outcomes of every retained test, and rejects every jump-only
cycle. It shortens maximum prepared terminal path length from 56 to 29 but
still pays a seven-state detector: the maximum consecutive prepared zero run
is six. No state saving is credited for the shorter average traversal. The
final total path-zero maximum is thirteen; this does not enlarge the run
detector because that representation counts consecutive zeroes. The one-zero
preparation and all INC/DECNZ/native-HALF interfaces remain the same.

Fresh allocation, projection and class-sum certificates retain twelve physical
classes, 189 primitive occurrences including BEEP, 188 checked register
operations and 85 explicit peer-zero obligations. This source change adds
primitive work while improving shared physical control; primitive count is
not a substitute for complete state count. The old reference carriers can
change roles only at the proved phase boundary, and every intermediate
transfer has its own checked ownership state. The physical bootstrap and
full reserve writer remain paid. New literal blank receipts must bind these
bytes before the initialization obligation is reported as executed evidence.

The complete final partition is the 268-state precursor partition below with
154 compiled arithmetic/control states in place of 156; all other rows of
that disjoint inventory are unchanged, including seven return-detector
states. Hence the final ledger is **154 arithmetic/control +112 others =266**.
The fresh completion and marked/B maps have the same semantic obligations as
the precursor, but their numeric rows and fibers are recalculated. The sole
marked row is `104 1 0 L 1 1`.

| Final artifact | States | SHA-256 |
| --- | ---: | --- |
| Architectural raw parent | 272 | `ac25fb6eb76ebc8c35eca1461605370fee20e8aa4f6028258362082e4437d44d` |
| Ordinary B-exit parent | 270 | `c52f52eade186cc1bd3f67f44e715dee1bff3551b2c379f9e9e4488784cc442e` |
| Completed raw parent | 270 | `776a1b4001052b848a9beb4758e885e5addb1657ff61dc8c7aa60ee052389a8d` |
| Selected B-exit companion | 267 | `668c5c91d2510aadc0fac6342f80fc3f4d248d6a2fd828d375a45b57e780e712` |
| Selected marked table | **266** | `c5b0a16ce6edba5df3372ab9d6290db8d7ca747a6660a9d10f3a9d1fc8e5331c` |

## Original-source 268-state specialization

The following detailed eight-site proof and numerical ledger refer to the
retained `zero_context` precursor. They give the local control theorem reused
in the selected nine-site composition above. The precursor itself leaves the
source byte-identical; only the final source composition changes its carriers.

## Scope and exact predecessor

The `zero_context` precursor uses the exact canonical
[phase_swap/source.py](../phase_swap/source.py), SHA-256
`4f1f6f317eb196b8d09a67439893622a759c43ef4e02e30adae4e04b0eb39515`.
The source is unchanged from the 284 producer and the 271 producer
`cc55f5e39a98b75062fdd8ad2029ae9a0efeef13`. The construction retains the
operation-specific INC/DECNZ selectors and unary/native-HALF runtime whose
contracts are stated in [operand_dispatch/PROOF.md](../operand_dispatch/PROOF.md).
It changes a source-entry control transformation before the fixed grammar,
projection and physical bank are generated.

The reference predicate remains `A(D(i),0,N(i))` and the candidate predicate
remains `A(j,i,(N(i)+1)^j)`. Both are existential over the protected negative
certificate tape. The normalized low-first marker/payload parser, payload
orientation, virtual zero behavior, description and exponent padding, witness
guards and bit-cost NP membership therefore have precisely the predecessor
source scope in [phase_swap/COMPOSITION.md](../phase_swap/COMPOSITION.md).
In particular, every even input has an empty parsed prefix while its higher
bits remain candidate tape data. The complement-covering verifier still
initializes its used workspace and handles the empty prefix in one transition.
Both equal returned-bit pairs `(1,1)` and `(0,0)` refute the proposed complement;
unequal bits continue silently. No finite simulation decides eventual silence.

The exact overlapping record address is `s+z-1`. Write and relative-turn bits
remain independently encoded. Description masters are copied for every step,
so ordinal skipping and the selected pop never consume a program needed by a
later overlapping window. Absent and truncated records use virtual zero tails;
state zero remains absorbing. Neither numerical clock construction nor the
`2^C` witness capacity changes in the selected source. Both actual acceptance
sites are retained. The three-transfer left/right exchange still uses a
proved-zero work cell and preserves its intermediate ownership conditions.

## Why shared zero-test removal missed these occurrences

The previous contextual pass may replace a shared grammar child only when
every admitted occurrence of that same child has a zero operand. In its output
there are eight individual zero-valued DECNZ occurrences, but no additional
shared child whose admitted occurrences are all zero. A grammar child used
for a clear at one site also serves a nonzero clear elsewhere.

The new pass separates occurrences before interning identical pairs again.
Its input is the *output* of the original contextual pass, not an invented
source IR or a bounded execution trace. The original certificate is retained
unchanged in `contextual-tree-certificate.json`. The next exact link, including
both grammars, all invariant states, every changed path and the final cleanup
certificate, is zero-context.json (historical reference: `machines/zero_context/zero-context.json`; outside this selected-only export).

The eight replacements are four logical operand roles at each acceptance
site. Allocation aliases alone are not their admission proof; the exact
occurrence path and its full invariant state supply that proof.

| Source role in these occurrences | Allocated logical operand | Occurrences |
| --- | --- | ---: |
| Description work / write accumulator | `$liveframe.0.10` | 2 |
| Ordinal / selected-record accumulator | `$liveframe.0.8` | 2 |
| Left tape half | `$liveframe.0.6` | 2 |
| Scan / reference-result temporary | `$liveframe.0.4` | 2 |

The canonical certificate records the full binary paths, operation strings,
operand names, occurrence indices and complete abstract states. In particular,
it does not infer a semantic phase from physical state number or visual
proximity in a printed table.

## Inductive admission proof

For each logical register use the three sets `{0}`, `{1}` and `{2,3,...}`,
represented by bits 1, 2 and 4. Their seven nonempty unions form the abstract
domain. An occurrence state is a product of these sets; a missing state means
the occurrence has no admitted predecessor in this inductive overapproximation.

The entry abstract state contains the all-zero logical store. Every supplied
state is closed under every admitted outgoing branch, including both ordinary
DECNZ outcomes and both native HALF parity outcomes. INC maps zero to one and
positive values into the appropriate one/many set. DECNZ maps positive one to
zero, positive many into one/many, and zero to zero on its false branch. HALF
maps zero to zero on its even branch, odd one to zero, odd many into one/many,
and positive even values into one/many. These finite abstract transfers cover
all natural operands; values 2 through 5 distinguish all many-set images.
Return and continue paths preserve the store; BEEP preserves it and emits the
event.

The checker uses the preexisting tuple-path interpreter to resolve control
edges. It checks the initial state and subset inclusion at every edge, rather
than rerunning the producer's fixed-point search. For this input grammar it
checks 283 unfolded occurrences and 366 admitted edges. The supplied states
therefore contain every finite source-entry execution by induction on the
number of primitive/control steps. This argument applies after the separate
blank bootstrap lemma; a finite blank prefix is not substituted for it.

At each of the eight selected occurrences the operand mask is exactly 1.
The actual logical operand is consequently zero on every admitted visit.
All unselected occurrences, including other occurrences of the same shared
child, keep their original operation.

## Local rewrite and return relation

At a DECNZ occurrence on zero, the register remains zero and the false lexical
return skips one enclosing left branch. Its logical action and control target
are exactly `_break.1`. It emits no event. A zero-valued HALF would satisfy the
same relation: `floor(0/2)=0`, the parity branch is even, and its reserve
extension is zero. The frozen selected instance removes ordinary DECNZ tests;
the checker also recognizes the native-HALF operand syntax and would require
the same zero premise before allowing that case.

The pass unfolds the complete finite grammar by occurrence path, replaces only
these eight leaves with `_break.1`, and interns identical pairs. Every other
leaf remains at the same path with the same operation. Reinterning changes
node names and sharing but does not change the expanded tree or lexical
return semantics. This gives a direct stuttering simulation: retain the full
logical store, ordered event history and resolved next source occurrence;
replace a finite zero-test segment by its equal false return.

The specialized grammar has 179 pair nodes. The existing checked contextual
cleanup then removes five finite empty-control structures and leaves 174 pair
nodes. Its separate certificate binds the specialized grammar to
`pre-control-grammar.json`. The original source-to-context certificate is not
relabelled as though it proved this new output. The three successive bindings
are:

1. Original source lowering/context certificate to the new pass's input.
2. Eight checked occurrence replacements and exact reinterning to the
   specialized grammar.
3. Existing finite cleanup certificate to the new pre-control grammar.

check_zero_context.py (historical reference: `check_zero_context.py`; outside this selected-only export) checks each link without
importing the new producer pass or invoking its analyzer/rewriter. This is
author checking, not an independent review. Deliberate mutations to the input
binding, occurrence inventory/path, operand, zero mask, false return, cleanup
binding and predecessor binding must all be rejected.

## Termination and physical refinement

On an admitted finite unary bank, every removed zero test and each retained
primitive completes in a positive finite number of physical transitions under
the existing scalar/native contracts. The replacement lexical return traverses
a finite control word. It does not add a new primitive, operand tag, tape
counter, caller adapter or private kernel.

After cleanup the fixed weak-grammar plan is replayed. Its core graph contracts
only finite administrative paths, preserves the retained primitive order and
both retained test outcomes, and rejects *every* jump-only cycle, including
ones outside the selected starting trajectory. The removal of a zero test
cannot remove an event. Nor can it create an infinite execution made solely of
administrative actions: that would contain a jump-only cycle in the finite
control graph, which the complete check rejects. Between retained primitives
the physical scans and returns terminate by their finite delimiter/rank
arguments. Every finite source comparison consequently still finishes; silence
cannot arise from a stalled selector, a removed clock decrement or an
administrative-only loop.

Allocation, unused-zero projection and class-sum coalescence are regenerated
from this new grammar. The selected result still uses twelve physical classes,
but now has 177 retained primitives including BEEP and 176 checked register
operations. Each coalesced physical value is the sum of its logical ghost
values. At every operated member all peer ghost values are zero; the fresh
certificate checks this at every admitted occurrence. Simultaneous source
operands and the intermediate states of the unchanged three-transfer swap
remain covered. No new phase alias is presumed from boundary values alone.

Fresh path geometry requires a **seven-state** zero-run return detector. The
maximum path length is 53, maximum total path-zero count is eleven, and maximum
prepared consecutive zero run is six. A detector that waited for only six
zeroes would be unsound for this new tree; the complete saving pays the seventh
state. The unchanged root `11` resets the detector, and the finite blank margin
to its left supplies seven zeroes. The existing right scan then reaches the
same root boundary with the same tape/head relation in finite time. The
complete counted writer still initializes 1,909 zero fields. No reduction of
reserve size is credited as a physical state saving.

All source initialization, program construction, selectors, native HALFs,
clock/certificate operations, resets, event preparation and totalization are
present in the ordinary parent. The exact blank-entry configuration and event
times must be established on these new bytes by fresh execution receipts. Old
284 and 271 blank receipts remain historical exact-byte evidence only.

## Fresh completion, event correspondence and complete cost

The admitted primitive ABI has the same five named excluded reads as the
operation-specific predecessor: ordinary preparation/read1, native
preparation/read1, native begin/read0, native boundary/read1 and native
undo/read0. Their reasons are respectively the clean zero separator, the same
native separator, a nonempty unary block, a zero field delimiter and the
temporary quotient one that is being restored. Those are all-natural segment
invariants. They are not inferred from totalization metadata or from an
unvisited read in a finite trace.

The new domain.json (historical reference: `machines/zero_context_selected/domain.json`; outside this selected-only export) recomputes
every raw preimage before excluding any ordinary quotient row. The six
ordinary quotient holes include both unreachable sink rows. The fixed
completion changes only those holes; every other row is retained. It protects
the B class. Ordinary quotient and ingress-event quotient equations are checked
on both reads of every state, with complete target closure and L/R moves only.
The sole selected marked row is `104 1 0 L 1 1`, exactly one applied transition
before its companion's B exit. No other state/read emits a marked event.

| Whole construction | Raw states | B-exit states | Marked states |
| --- | ---: | ---: | ---: |
| Reviewed operation-specific ordinary parent | 277 | 275 | 274 |
| Reviewed selected predecessor | 275 | 272 | 271 |
| Occurrence-zero ordinary parent | 274 | 272 | 271 |
| Occurrence-zero selected successor | 272 | 269 | **268** |

Here the selected raw table means the completed ordinary parent; it is not the
architectural raw table. The state reduction comes from four fewer compiled
arithmetic/control states, offset by one extra return-detector state. It is
not a full-table quotient of the old machine and not a compressed rendering.

| Disjoint selected state origins | States |
| --- | ---: |
| Compiled arithmetic and control | 156 |
| Ordinary register entries | 24 |
| Operation-specific operand selectors | 24 |
| Native HALF entries | 4 |
| Native HALF kernel | 13 |
| Native HALF selection/preparation | 5 |
| Mixed native kernel/selection/remaining-engine class | 1 |
| Remaining engine and dispatch | 27 |
| Return delimiter scan | 7 |
| Blank bootstrap | 4 |
| Mixed bootstrap/totalization class | 1 |
| Event adapter | 1 |
| Mixed event/remaining-engine class | 1 |
| **Total** | **268** |

The complete class inventory is
physical-ledger.json (historical reference: `machines/zero_context_selected/physical-ledger.json`; outside this selected-only export).
The occurrence-only precursor's selected marked SHA-256 is
`a591b028c401dcbf7f1f80e00503b8123464b52c324b0ec134ddfded6d793a79`;
the companion SHA-256 is
`0ed1046ba4325140f860ca1972192ec098cd6de6defcbbf5de21fdb6d5c7edb5`.
The ordinary parent marked hash is a different artifact and must not be used
as a binding for this 268-state table.

Composition of the unchanged source theorem, the new admitted control
simulation, fresh storage relation, terminating primitive implementation,
separate initialization lemma and exact event maps yields the intended
endpoint: the ordinary blank-start machine runs forever, and emits finitely
many designated events exactly when NP=coNP. Infinite events or established
1-acceptance mean NP differs from coNP. These are conventional proof
obligations; finite tests, internal review, remote CI, external certification
and Lean/kernel checking remain separate evidence categories.

## Paid source alternatives and their proof boundaries

The other complete variants retain the same predicates but change source
internal histories. Their frozen complete plans and tables are preserved in
[recipes.json](recipes.json); none is credited as a reduction of the selected
266-state machine. They require their own source and physical review before
any promotion.

**Unchanged-source 267 checkpoint.** Scoring the actual longest prepared zero
run, rather than total left depth alone, admits a control rotation that lowers
the occurrence-only return detector from seven to six states. Its complete
selected table has 267 marked states. The full geometry plan has 35 retained
transformations, of which 26 follow the original zero-context plan; its
maximum terminal path length is 29 and maximum prepared zero run is five.
The prefix plan retains just the first additional rotation and has the same
complete state count but longer paths. Both retain the full core graph with
both test outcomes and no jump-only cycles. The exact source remains
`phase_swap/source.py`; its marked hash is
`8545902087c52ddd8ee9f01a7dc6cbe32ad0284c30261b3748db3a3061389b20`
for the full plan. This is a separately preserved checkpoint with its own
literal tables and bindings, not the source-identical status of the 266 winner.

**One acceptance loop for two phases.** The shared-phase sources initialize a
finite reference witness domain, run the complete shared simulator, then run
the candidate witness domain. A phase bit selects input zero or input `i`.
The description/time carrier normalization changes `e,n` to `j,C` only after
the reference predicate has returned. In the clock-role variant, after the
reference the old `e` is dead, so `e=n; n=(e+1)^j; e=j` constructs exactly the
same clock and description. In the ternary encoding, expected=0 denotes the
reference phase and expected=1+reference_bit denotes the candidate phase;
subtracting one after that phase restores the bit before optional XOR.
Both witness domains have at least one attempt. Every attempt resets input,
certificate, state and time; neither phase consumes an immutable master. A
finite two-phase loop does not alter the `(j,i)` enumeration. The complete
cost includes this phase flag, two setups, conditional input initialization,
description/time copying, all returns and restart paths. These costs outweigh
the shared body in the measured variants.

**Normalized carriers without a shared phase loop.** `reuse_description_time`
retains both full source acceptance bodies, assigns `e=j` after reference and
`n=C` after certificate seed construction, then uses those carriers in the
candidate body. `reuse_clock_roles` also constructs C in the dead old reference
roles. At the first candidate attempt, description, input, time and witness
capacity agree exactly with the predecessor. Both complete ordinary tables
tie 274 marked states and both fresh selected tables tie 271. Identical-looking
calls improve sharing but the added carrier setup/return geometry consumes the
potential savings.

The complete occurrence-composition pass repairs that tie: normalized
description/time plus zero specialization reaches 267 selected states, while
normalized clock roles plus zero specialization reaches 266. The latter's
geometry repair leaves the 266 count unchanged and shortens its maximum
terminal path to 29. The selected-source relation is proved at the start of
this document. Bounded compositions of the shared expected/phase variants
reach 273 and 274 ordinary marked states; explicit shared phase roles reach
275, and description-only reuse reaches 278. All complete losses remain in
the fixed recipe inventory.

**Overflow-guard witness enumeration.** These sources enumerate b=0,1,2,... .
Before an attempt they compute `floor(b/2^C)` by exactly C halvings. A zero
result admits b; a positive result exits without simulating. Thus the admitted
domain is exactly `{0,...,2^C-1}`. For C=0, only b=0 is admitted. Every prior
attempt terminates, and b increases, so the finite enumeration exits at the
first overflow b=2^C unless acceptance already ended it. Reversing the old
descending order preserves the existential result. It does not remove the
required C-bit certificate domain or bound it for free.

The native guard copies b to D and C to S, halves D while consuming S, and
leaves B,C unchanged. The borrowed-clock repair instead clears D,S, copies B
to D, and repeats `DECNZ(C); INC(S); HALF(D)` until C=0, then transfers S back
to C. After t iterations, D=`floor(B/2^t)`, C=`old_C-t` and S=t. It returns
D=`floor(B/2^old_C)`, S=0, C restored and B preserved. D,B,S,C are explicitly
distinct in source allocation; copy scratch starts and ends zero. The
interference and exact-AST region certificates are freshly emitted. Every
clear, copy, decrement, half and restoration is paid and finite. The best
guard repair still costs 285 ordinary marked states, so it is a measured loss.

**Zero selected-pop accumulator.** The isolated `zero_pop` repair recognizes
the exact ordinal drain and following selected-record pop at both callers.
The ordinal loop terminates only with its accumulator zero; therefore the
intervening clear has no effect. The selected pop counts r finite trailing
ones and consumes the next real or virtual zero, leaving r in the accumulator
and the shifted residual description. If the description is all ones, the
virtual terminator is zero and the residual is zero. The immutable description
master is not changed. Both exact source AST spans and fixed paths are in the
certificate. This complete repair reaches 270 selected marked states; the
general occurrence treatment reaches 268.

**Neutral excursion attempt.** `neutral_context.py` searches for an INC whose
next primitive after a finite administrative chain is a same-operand DECNZ.
Their composed action is identity for every natural value, with the positive
DECNZ branch forced. It considers changing only that INC occurrence to an
existing break/continue path reaching the positive successor, preserving other
DECNZ callers. Both candidate pairs have shared decrement ingresses. Neither
bypass is expressible by one existing lexical return in the current tree; the
complete measured experiment therefore makes no replacement and reproduces
the 268-state selected bytes. No hypothetical unencoded jump is credited.

**Direct comparison join.** Candidate capacity is at least one, so the state
after the finite witness loop is zero exactly on candidate acceptance and is
positive exactly when all attempts reject. The reference expected bit is 0 or
1. The direct-join sources test equality of those two bits using nested
branches. In `equality_consumed`, the positive state and expected tests consume
one unit because both values are overwritten before their next use on either
restart path; the source supplies those decrements explicitly. Equal `(0,0)`
and `(1,1)` outcomes restart the candidate; unequal outcomes increment i. The
paid comparison branches do not improve the 268-state construction in the
measured complete tables.

## Review and recovery boundary

The complete source-independent oracle and prepared checks are separate from
literal binary execution. Fixed reproduction invokes no grammar or completion
search. The conventional arguments above do not inherit predecessor review
acceptance onto changed source variants or changed physical rows. Fresh
independent source/physical review must name the immutable producer revision;
its delivery is separate. Exact blank and silent-progress receipts, remote
publication/fetched bytes and CI status are recorded by the integrated
delivery, not asserted by this author proof.

source_oracle.py (historical reference: `source_oracle.py`; outside this selected-only export) checks all seventeen source files against
a separate sparse signed-tape interpreter. For each source it runs 72 actual
clock comparisons and 208 explicitly prepared clock comparisons. Every one
of the 16,473 observed source attempts is checked at its actual initialized
description/input/witness/time and final bit. The cases include all four
comparison outcomes, real high bits after empty prefixes, and 130 finite
all-ones/virtual-terminator record checks. These finite counts are regression
evidence; the universal phase and control arguments above remain necessary.
