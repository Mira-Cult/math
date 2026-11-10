# Exactly what “ω-accepts” means

This defines the fixed observer used in the [M236 theorem](README.md).
Nothing in the observer definition mentions PA, the producer, or a truth
predicate. The connection to PA is the theorem, not part of the definition.

## 1. From physical transitions to records

Run the machine from its specified blank initial configuration. At physical
time `t`, the transition either emits no event, emits `0`, or emits `1`.
Discard silent transitions but preserve the order of all emitted bits.

Encode a natural number by unary `u(k) = 1^k 0`, so `u(0)=0`, `u(1)=10`,
and `u(2)=110`. A record is

$$
u(n)\,u(p)\,u(x_1)\cdots u(x_n)\,u(b),
$$

where `n>0`, `p,x₁,…,xₙ` are arbitrary natural numbers, and `b` is `0` or
`1`. Its **address** is `(n,p,[x₁,…,xₙ])`, and its value is `b`. After reading
`n`, the online parser expects exactly `n+2` further fields: the game, the `n`
moves, and the Boolean value. No delimiter separates records beyond the unary
zeros and the field count supplied by `n`.

A zero rank, non-Boolean final field, or conflicting completed records causes
a permanent parser error. Equal duplicate records are allowed. A finite prefix
that ends partway through a field or frame is unfinished, not yet erroneous.
The actual Lean definitions are in
[UnaryCodec](formalization/lean/PASoundness/UnaryCodec.lean).

## 2. The guards

A trace must satisfy all of these requirements:

1. **No parser error** at any finite time.
2. **Coverage:** every legal address `(n,p,xs)`, where `n>0` and `length(xs)=n`,
   eventually has a completed record of one of the two values.
3. **Consistency:** no legal address has completed records with both values.
   Every emitted record must have a legal address.
4. **Frame progress:** after every finite number `t` of physical transitions,
   there is some finite `u≥t` at which the parser is at the start of a new
   frame and has no unfinished unary run.

The first three conditions are `Complete`; the last is `FrameProgress` in
[M236Observer](formalization/lean/PASoundness/M236Observer.lean).
They refer to completed records and actual output, not filled-in defaults.
For a one-bit-per-transition physical system, coverage together with correct
parsing already implies the progress clause; the definition nevertheless
retains it explicitly. See
[M236FrameProgressBinding](formalization/lean/PASoundness/M236FrameProgressBinding.lean).
For error-free physical streams, progress equivalently says every emitted bit
eventually belongs to a completed frame, as proved in
[M236FrameSegmentation](formalization/lean/PASoundness/M236FrameSegmentation.lean).
There may be a temporary unfinished suffix at arbitrarily late finite times.

On a guarded trace, let `B(n,p,xs)` be its unique recorded value. A
first-record-with-default formulation gives the same values under these
guards; the default must never excuse a missing legal record.

## 3. The games

For **each** `n>0` and **each** game number `p`, play exactly `n` moves.
The existential player chooses the first natural number, the universal player
chooses the second, and they alternate. Moves are unrestricted natural numbers.
The existential player wins precisely when the completed address has value
`0`. The observer requires a winning strategy for every one of these games:

$$
\forall n>0\ \forall p\quad
\exists x_1\ \forall x_2\ \exists x_3\ \cdots Q_n x_n:
B(n,p,[x_1,\ldots,x_n])=0.
$$

Each existential choice may depend on the preceding universal moves. An
equivalent formulation is

$$
\forall n>0\ \forall p\ \exists S_{n,p}\quad
\text{every play consistent with }S_{n,p}\text{ ends in a zero record}.
$$

The strategy is a finite-height, possibly infinitely branching tree. There is
no requirement of computability, one first move for all games, one finite
strategy serving all ranks, or one finite natural encoding of the entire
family. `strategy_iff` proves the equivalence of the strategy-tree and
alternating-quantifier formulations using classical choice.

**M236 ω-accepts if and only if the guards hold and all these games have winning
strategies.** This is exactly `TraceAccept` and the checked expansion
`selected_trace_iff_complete_and_strategies`.

Equivalently, no positive rank has a game satisfying the dual rejecting
condition `∀x₁ ∃x₂ ∀x₃ … : B(...)=1`, provided the guards hold. A single
`1` record is not a rejection of the entire machine.

## 4. Examples that distinguish the conditions

- The frame for `(1,0,[0])` with value `0` is `10 0 0 0`, namely `10000`.
  Repeating it is consistent, but repeating only it forever lacks coverage.
- Silence is not acceptance: all legal addresses are missing.
- A `0` record and a later `1` record for the same address are a conflict.
- A single emitted `1` followed by silence leaves an unfinished unary field
  forever and violates progress. Merely observing no parser error is too weak.
- A rank-one game can have a `1` at move `0` and still be won by move `1`.
- In a three-move game whose winning rule is `x₃=x₂`, a strategy chooses any
  `x₁`, observes arbitrary `x₂`, and answers with `x₃=x₂`. Bounding the universal
  moves would change the question.
- A family with winning rule `x₁=p` has a strategy for each game `p`, although
  no single first move works for every game.

Checked controls appear in
[M236ObserverFrontDoor](formalization/lean/PASoundness/M236ObserverFrontDoor.lean)
and [M236Observer](formalization/lean/PASoundness/M236Observer.lean).

## 5. Relation to the historical observer

[M236HistoricalGuard](formalization/lean/PASoundness/M236HistoricalGuard.lean)
defines a historical-style observer from raw frame occurrences and first
record values. For physical bit streams, it proves equivalence to the guarded
Lean observer above.
[M236HistoricalPASoundness](formalization/lean/PASoundness/M236HistoricalPASoundness.lean)
then gives the PA-soundness corollary for the literal machine.

The comparison of this formal transcription with the original prose is a
scoped review judgment. It is not a formal semantics of English, nor an
identity between historical normalized-PA records and the selected H-game
records. Neither observer equivalence by itself establishes acceptance.
