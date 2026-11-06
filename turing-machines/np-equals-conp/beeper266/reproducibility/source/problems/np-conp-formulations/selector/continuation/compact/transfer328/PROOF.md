# Complete 291-state refinement through sequential attempt reset

The selected source is `control/attempt_reset/source.py`, SHA-256
`4f1f6f317eb196b8d09a67439893622a759c43ef4e02e30adae4e04b0eb39515`.
Its selected marked table has 291 states/582 rows and SHA-256
`5c2efa665402e3b99e95b56670923575c61e02cb9773ae135f9550dfbddf0dcc`.
The 292-state/584-row B companion has SHA-256
`f23ef282e52c23b40eee90da00086f575d1807c692eff9129f66e5a0cfb25da5`.
The sole mark is `100 1 0 L 1 1`; it precedes B exit by one transition.

This proof composes the preserved [302 source theorem](PROOF302.md) with an
exact reset transformation and entirely regenerated storage/physical maps.
The earlier 302 source, complete parent, selected tables, fixed inputs and
independent review receipts remain intact. No former physical certificate
or numeric state identity is applied to the new table without regeneration.

## Exact source transformation

The only source change from `coordinator/source-consume.py` is at the two
attempt entries. The reference tuple

```python
left, right, state, steps = branch, 0, 1, n
```

becomes the four sequential assignments `left=branch; right=0; state=1;
steps=n`. The candidate tuple similarly becomes `left=branch; right=i;
state=1; steps=clock`. All right-hand-side names and literals refer to
masters or constants; none depends on old left, right, state or steps. The
four targets are distinct source variables. Therefore, for every prior
working state, the sequential reset has exactly the same post-reset source
store as the tuple. It has no call, event or branch between assignments.
`control/attempt_reset/generate.py` recognizes exactly those two tuple ASTs;
the frozen final source makes this transformation reviewable directly.

Both attempt entries consequently preserve the independent description,
initial input, certificate enumeration and clock masters. The working
certificate copy can be overwritten by simulation without losing the master.
All-zero, all-one and empty witnesses, rollover, zero clocks and stale
working fields have the same source meaning. Source liveness and physical
ownership must still be rebuilt: this source equivalence is not permission
to alias a target with a master during an intermediate assignment.

The normalized parser, reference witness capacity D(i), both existential
simulation bodies, candidate clock `(N(i)+1)^j`, consuming guards, XOR result,
comparison polarity, input/candidate order and source event order are
otherwise identical. Sections 1–4 of [PROOF302.md](PROOF302.md) prove the
required all-natural source and closed-region contracts. In particular the
oversized reference witness range is safe because it covers every n-bit word
and unread higher bits cannot change an n-transition run. The candidate
still enumerates all C-bit certificates and still constructs its exact 2^C
capacity. Neither acceptance phase uses the donor's deterministic candidate.

All normalized source-theorem hypotheses remain explicit: input i retains
its ignored suffix; the complementary verifier initializes positive workspace
independently of that suffix; negative certificates survive preparation;
runtime and useful witness bounds depend on parsed n; the empty wrapper
accepts in one transition; j is both description and exponent; complete-prefix
padding and internal guards justify coverage. No different clock theorem,
nondeterministic forced-write semantics or P=NP decision theorem is used.

Every finite source comparison still terminates. Refuting equal returned
bits handles both (0,0) and (1,1); unequal bits advance silently. The source
therefore emits finitely many events iff NP=coNP, and executes infinitely
many correct comparisons after a correct candidate is reached. It runs
forever in either case. Internal physical timing need not match 302,360,387,
407 or the serial backend.

## Fresh allocation, regions and boundary configurations

The sequential source eliminates simultaneous-assignment snapshots that
were unnecessary for these two reset sites. Its fresh chain is 23 source
logical coordinates  -> 20 allocated registers  -> 16 projected logical
coordinates  -> 13 physical classes. The same explicit clock/seed interference
edges protect each borrowed master throughout its closed region. The full
intermediate primitive graph is regenerated; it has 81 zero-peer sites.
Each physical class is the sum of its logical ghosts, and every non-operated
peer is zero at an operation. Source allocation alone does not establish this.

The clock, seed and consuming-guard lowerers are unchanged exact rules from
the 302 proof. The new certificates must establish their actual entry masks
again, particularly B=Q=C=0 at the clock entry and S=Q=0 at the retained seed
entry. Sole exits follow restoration. Finite stale-output resets, finite
inner/outer countdowns and finite restoration prevent administrative silence.
No new atomic multioperand opcode or uncounted physical representation is
introduced by sequential reset.

The boundary relation retains the full lexical path, head coordinate, unary
bank, zero reserve, live masters and scratch. Existing INC/DECNZ/HALF segment
contracts give positive finite realization on every admitted finite bank.
The path maximum remains 57; 13 active fields fit 1909 initialized zero fields
and the paid span 3822. All program construction, initialization, selectors,
returns, both caller phases, resets, clocking and event paths are included
in the complete binary table. Actual blank initialization is checked on this
new table, separately from prepared configurations.

The new grammar's maximum path zero-count is 11. The paid return dispatcher
therefore uses depth 13 = 11+2, allowing the two preparation zeros. Its full
countdown chain from 0 through 13 and the `6.continue.0` read-one target at
`4.dispatch.13` are checked against this bound. The finite leftward scan
passes the entire permitted control path and padding into the blank region
to its left; the following rightward scan recovers the root sentinel. This
parameterized continuation change preserves the inherited return contract.
The other 213 current runtime rows agree exactly by name with the inherited
runtime. Byte identity alone is not claimed for the changed dispatcher row.

## New completion and literal identity

The complete sequential-reset producer has 301 raw states and an ordinary
all-row quotient of 298 B states /297 marked states. The raw quotient checks
all 602 rows. `coordinator/select_reset.py` applies the newly discovered and
published fixed `selected291.json` plan; replay does not run discovery.

Its domain is freshly derived from this producer's names, requested rows and
raw quotient. All raw preimages must satisfy the named semantic preparation,
separator, HALF or selector-entry exclusion facts from the inherited runtime
proof. A request to totalize a row is not itself that proof. There are 13
excluded quotient rows and 15 raw preimage row occurrences; the silent sink
has no admitted predecessor. The completed 298-state parent preserves all 583
retained rows and changes only the excluded rows. Its admitted execution
therefore agrees step for step, including full tape and head, with the
complete parent; arbitrary inadmissible configurations need not agree.

All 596 rows of that completed parent satisfy the fixed quotient to 292 B
states, with B kept as a singleton distinguished class. Every target exists
and every binary row is present. The companion starts outside B, and B does
not immediately target itself. Marking ingress into B gives exactly one mark
per B exit with fixed time shift minus one. The subsequent event quotient
checks all 584 ingress rows and yields 291 states/582 rows. Its new sole mark
is derived from these maps, not inherited from 302's numerical state 104.

The completed-parent SHA-256 is
`33cb9f79219fbb5d6169029065a9d7b8fd1858ef52cbd5d85762595f048d0d07`.
The exact marked and B hashes at the beginning of this proof identify the
literal target. Start/head/blank are zero; the initial two-way binary tape
is all zero and moves are only L/R. No halt state is omitted from counting.

Administrative contractions have no jump-only cycle and are grouped with
the next retained source action where a zero reset disappears. Every infinite
source run contains infinitely many retained positive finite primitive
segments. It therefore yields an infinite physical run, with exactly the
source's event sequence. The source theorem transfers: finite marked events
iff NP=coNP; infinite events, the 1-acceptance convention, iff NP differs from
coNP. Eventual silence cannot be a stalled reset, clock, restoration or
simulation.

## Review and evidence scope

Independent reviewers rerun source differential checks, actual closed-region
entry and restoration checks, the fresh storage chain, all-row maps and
deliberately damaged certificates. Independent literal engines start on the
blank tape and compare whole configurations; a third checker inspects actual
primitive and comparison boundaries. Injected fixtures are separately labeled.
None of these finite checks decides eventual silence. They support the
general refinements above, with exact producer bindings supplied separately.
Internal nonauthor model review is not external human or Lean certification,
and skipped remote jobs are not passing CI. The historical original 1334
artifact remains unrecovered.
