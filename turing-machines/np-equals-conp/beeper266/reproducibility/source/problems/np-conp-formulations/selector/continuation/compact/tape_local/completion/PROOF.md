# Admitted-execution completion and the 401-state beeper

## Scope and exact source

This construction retains the [certificate-tape source theorem](../../source/PROOF.md)
and every source byte of the reviewed 407-state control. It changes neither A,
the fixed NP-complete reference K, the coupled candidate clock `(n+1)^j`, the
descending certificate order, the input/candidate enumeration, nor the marked
event convention. The author of this completion and its fixed producer is
`/root`; nonauthor domain and implementation reviews are recorded separately.

The selected output is a complete deterministic binary two-way single-tape
blank-start machine with 401 states and 802 rows. Every state has both rows,
every target exists, and every move is L or R. No halt state is omitted. It
runs forever and emits finitely many marked events exactly when NP=coNP.
Under the established convention, infinitely many events mean 1-acceptance
and characterize NP!=coNP.

This is a domain-specific refinement followed by ordinary all-row quotients.
It is not an equivalence on every arbitrary configuration of the old totalized
machine. The experimental binary-bank and transactional architectures are
separate complete losses, not premises of this result.

## The thirteen excluded rows

The inherited [composition](../../native/COMPOSITION.md),
[native kernel proof](../../compiler/native/PROOF.md), and the shared-selector
proof reached through that composition establish the physical entry and exit
contracts. Exactly these named raw rows were explicitly absent before the
inherited totalizer filled them with a silent sink:

| Named raw state | Excluded read | Required bit on every admitted visit |
| --- | ---: | --- |
| `1b.reg.prep_1` | 1 | The first clean gap cell is zero. |
| `2h.native_half.begin` | 0 | A selected unary block starts with its base one. |
| `2h.native_half.boundary` | 1 | The quotient/input boundary is the zero separator. |
| `2h.native_half.prep` | 1 | Native preparation starts on a clean gap zero. |
| `2h.native_half.undo` | 0 | The tentative quotient increment being undone is one. |
| `shared.selector.bootstrap.prep` | 1 | The separately checked finite bootstrap supplies zero. |
| `shared.selector.mark` | 0 | The selected nonempty block starts with one. |
| `shared.selector.mode0.pad1` | 1 | The first mode-pad cell is zero. |
| `shared.selector.mode0.pad2` | 1 | The second mode-pad cell is zero. |
| `shared.selector.mode1.pad1` | 1 | The first mode-pad cell is zero. |
| `shared.selector.mode1.pad2` | 1 | The second mode-pad cell is zero. |
| `shared.selector.prep` | 1 | The additional shared preparation pad is zero. |
| `shared.selector.skip_separator` | 1 | The cell before the erased block marker is its zero separator. |

These contracts apply to every finite admitted natural bank, including
arbitrarily large values and reserve tails. They do not follow from sampled
small inputs. The exact finite blank prefix separately reaches the proved clean
entry without entering the old absorbing sink. After entry, ordinary source
calls use their respective contracts. Thus none of the thirteen raw request
rows is reached. The silent sink is also unreachable, because all its incoming
rows are these excluded requests or its own rows.

The original exact raw-to-B quotient merges three preparation names. Therefore
the B table has eleven excluded nonsink rows, plus the two sink rows: thirteen
holes in total. `domain.json` lists the complete raw preimage of every projected
hole. A projected row is excluded only when **all** its raw preimages belong to
the above set or to the unreachable sink. No other row is made optional. In
particular, quotient/parity is not interpreted as decrement, and no extra
zero-partner or source-register alias is assumed.

## Completion lemma

Let T be the old total 408-state B-exit table and H its thirteen excluded rows.
The completed 408-state table T' changes only H. Starting from the same blank
configuration, T and T' have exactly the same configurations at every finite
time: assume equality through time t. The original run does not use H at t,
so both machines apply the same write, move and target. Induction gives the
next equality. This induction uses the original domain theorem; it does not
assume the new run avoids H without proof.

The same proof preserves B exits at identical physical times. It also
transfers the original cofinal simulation: each finite source comparison,
counterexample and candidate reset still completes, including every comparison
after a final event. A silent stall cannot replace the original computation.

## Full row equations and event convention

The fixed [plan](plan.json) supplies a map from 408 completed parent states to
402 states. The builder first checks all 803 unchanged old B-row equations.
Each merged class requires identical writes, L/R moves, B color and mapped
targets on those rows. Missing rows receive the selected class row, with its
target lifted to a concrete parent representative. The completed table is
then explicit and total, and an independent ordinary quotient checker verifies
**all 816 rows** against the 402-state B companion. B is a singleton-colored
class; the sink has not been relabeled as B.

The B companion starts outside B. On its admitted execution each B entrance
is followed by its exit one step later, as in the unchanged control. Moving
the mark to ingress preserves the finite/infinite distinction and puts each
marked event exactly one step before its B exit. The inherited ingress checker
checks the relocation, and the final event-colored quotient checks **all 804
ingress rows**, yielding the 401-state marked table.

Its sole marked row is `112 1 0 L 1 1` in state/read/write/move/next/event
columns. This unchanged row identity does not mean the whole table is unchanged:
the new marked table's SHA-256 is
`b5da3eb3397235c27482cb7ca2f523cefa9d880e9bd5b26acbfb8c588156c65e`.
The 402-state companion's SHA-256 is
`2d85548a77bfd10de42327d177b5b0fbb7a0ad7ce9745b0512896370c4bf5bb2`.

All initialization, program/control production, arithmetic, simulation,
certificate search, scratch, dispatch, event adaptation and totalization remain
inside the complete counted tables. The old source/compiler dependency pins
and 33 canonical artifacts are reproduced before the selected fixed plan is
used. The plan is not an independent proof of its unreachability premise.

## Evidence and limitations

Independent C++ deque and C11 bitset execution reaches the clean source entry
at 61,009,974 steps with complete configurations related by the maps. Marked
events occur at 61,017,648, 81,109,104 and 107,515,008; B exits are one step
later. These observations check exact finite behavior. The inherited source
and runtime proofs, the hole-domain lemma, and the all-row equations establish
the unbounded endpoint.

The six-state saving is a local implementation refinement. It does not achieve
the requested large architectural reduction, a sub-250 count, or a universal
lower bound. Internal model-agent review, conventional proof, finite executable
certificate checking, literal execution, proof-assistant formalization and
remote CI are distinct statuses. No new Lean theorem identifies this literal
table yet.
