# Guide to the Lean statement and proof

This guide is for a reader who wants to check that the formalization concerns
the advertised binary table, its real blank start, the intended event, and
the usual complexity question. It follows the exact mathematical source
revision `6108c93565701e64775a3f1cbf9627d35c4c30e3`.

Source meaning, source identity, kernel checking, and mathematical review
remain separate. The [verification receipt](VERIFICATION.md) gives build
commands and distinguishes reproduced checks from upstream reports.

## Start with the closed theorem

Open
[`Bootstrap284AlignedFromBlank.lean`](formalization/Shared/Beeping/NPcoNP/Bootstrap284AlignedFromBlank.lean).
The full namespace is
`Shared.Beeping.NPcoNP.Bootstrap284AlignedFromBlank`.

Its theorem `literal_table_silent_iff_classes` states:

```lean
Table284LiteralBinding.parseMachine Table284.SourceChars.source = some machine ∧
  (machine.system.EventuallySilent ↔ NP = coNP)
```

Here `machine` is the fixed `Table284.machine`, and `NP` and `coNP` are
`ComplexityTheory.NP` and `ComplexityTheory.coNP`. There are no explicit
mathematical hypotheses on this theorem. The first conjunct binds serialized
bytes to the machine; the second is the blank-run complexity equivalence.

The shorter `selected_table_silent_iff_classes` states just the equivalence.
`aligned_from_blank` supplies the physical initialization argument. The file
prints the axioms of all three declarations. Ordinary reported proof axioms
are `propext`, `Classical.choice`, and `Quot.sound`; this is not an axiom-free
proof. See the receipt for the scope and execution status of the rejecting
axiom checks.

## 1. The literal machine and the observer

Read [`Machines.lean`](formalization/Shared/Beeping/Machines.lean) before any
compiler code. `Machine 284` has a vector of two rows per finite state. Each
row contains a write bit, an L/R move, a destination in `Fin 284`, and one
event flag. A configuration has a finite state, an integer head position,
and a tape of type `Int → Bool`.

`Machine.initial` makes the entire tape constant blank. `Machine.step` reads
the current head cell, writes that row's bit at that cell, moves exactly one
cell, and returns that row's event flag. Its step function is total. It does
not invoke a host-side arithmetic oracle, stop at a timeout, or take input
from outside the tape.

[`Table284.lean`](formalization/Shared/Beeping/NPcoNP/Table284.lean) constructs
the actual machine from checked numeric data. Inspect `rows_length`,
`rows_valid`, `machine_data`, and `machine_starts_zero`. The latter identifies
start state 0, blank bit false, and head 0.

The numeric representation is not the whole byte binding. In
[`Table284LiteralBinding.lean`](formalization/Shared/Beeping/NPcoNP/Table284LiteralBinding.lean),
`source_parses` connects the embedded string to the numeric table.
`parseMachine` requires the declared count to be exactly 284 before calling
the finite-table parser. `source_parses_to_machine` proves that the result is
this machine. Follow its imports through the header, line splitting, and row
coverage proofs. An independent reader should also compare the embedded table
with root [events.tm](events.tm) and its SHA-256.

In [`Events.lean`](formalization/Shared/Beeping/Events.lean),

```lean
def BeepAt (t : Nat) : Prop := (M.step (M.run t)).2 = true
def EventuallySilent : Prop := ∃ T, ∀ t, T ≤ t → ¬ M.BeepAt t
```

`eventuallySilent_iff_finiteEventTimes` identifies this with a finite set of
event times. The sole marked row is `99 1 0 L 1 1`. It is the transition
executed in state 99 while reading 1. Neither entering state 1 nor exiting
state 1 is the marked-table definition.

The conventional 285-state B-exit companion is a separate table with a
one-transition observation shift. Do not replace the above row flag by a
state predicate while retaining the 284-state claim. This endpoint does not
formalize that companion correspondence.

## 2. Blank initialization and physical progress

The general physical endpoint is deliberately conditional in
[`Grammar284ActiveEndpoint.lean`](formalization/Shared/Beeping/NPcoNP/Grammar284ActiveEndpoint.lean).
`AlignedActiveWindow` requires a literal run configuration, an equal emitted
event prefix, and a valid graph/tape window. It is not itself an assumption
about NP or coNP. The final endpoint discharges it using `aligned_from_blank`.

That proof calls
[`Bootstrap284FirstBeepBlankRay.blank_start_reaches_first_beep_with_blank_ray`](formalization/Shared/Beeping/NPcoNP/Bootstrap284FirstBeepBlankRay.lean).
It retains the infinite blank ray needed by later scans, not only a displayed
finite tape patch. It then runs the real beep entry, verifies the silent
prefix and singleton event word, and matches graph time 1. The configured
bank starts with twelve zero register classes plus the initialized reserve.
No paid physical prefix is silently replaced by a preloaded tape.

The recurring relation is
[`Grammar284ActiveWindow.ActiveWindow`](formalization/Shared/Beeping/NPcoNP/Grammar284ActiveWindow.lean).
It distinguishes an ordinary reserved window from the special root-ready
case. Its `step` theorem covers every graph state and register bank satisfying
that relation. The theorem returns a strictly positive physical duration,
the next active window, literal run equality, and exact event-word equality.
It explicitly separates ordinary instructions, graph state 184's root
transition, and graph state 0's beep, including the root-to-beep path.

Read [`Grammar284ActiveRun.prefix_runs`](formalization/Shared/Beeping/NPcoNP/Grammar284ActiveRun.lean)
next. It quantifies over every finite graph prefix, not a fixed test count,
and returns at least that many physical transitions. Registers alone are
not the relation: graph control, parser position, the represented bank,
required tape regions, and framing conditions are carried by the window
proofs and their imports. The physical execution equality uses the literal
machine and whole tape functions, not an interpreter that skips physical work.

## 3. Why cofinal prefix matching suffices

`Grammar284ActiveEndpoint.cofinal_of_aligned` uses those positive finite
segments to produce matching event prefixes at arbitrarily late times on
both sides. Its last step uses
[`WordUnboundedPrefix.eventuallySilent_iff_of_cofinalPairs`](formalization/Shared/Beeping/WordUnboundedPrefix.lean).

`CofinalPairMatch` quantifies over every natural lower bound `N` and supplies
graph and physical times both at least `N`, with exactly equal ordered event
prefixes. It does not merely say that an observed finite prefix agrees.
It also does not require the separately chosen witnesses to form one
coherently selected sequence, which is unnecessary for this conclusion.

The shared proof identifies eventual silence with a uniform bound on the
lengths of all finite emitted prefixes. Event prefixes only grow. If either
stream had unboundedly many events, cofinal exact matches would force the
other to do so too. The theorem therefore cannot certify silence by hiding
late physical events between sampled times.

## 4. Source comparison and complete input coverage

Read
[`Source284Comparison.lean`](formalization/Shared/Beeping/NPcoNP/Source284Comparison.lean).
It fixes the actual two certificate-existential predicates, the candidate
clock `(N(i)+1)^j`, and comparison by unequal Boolean results.
`Source284Parser` computes `N(i)` and `D(i)` by marker/payload parsing.

The candidate uses `j` for both its program and exponent and sees all bits of
the original natural input. The reference parser may ignore a high suffix;
the candidate input does not discard it. Empty parsed prefixes have candidate
clock one. Missing source records, truncated records, virtual zero tails,
and independent write/turn bits belong to the source evaluator's specified
semantics and must be preserved across its implementation bridges.

In
[`Source284CanonicalConditional.lean`](formalization/Shared/Beeping/NPcoNP/Source284CanonicalConditional.lean),
`referenceLanguage` and `candidateLanguage` interpret arbitrary Boolean lists
as little-endian naturals. Redundant high zeroes are allowed.
`candidate_agrees_iff` connects natural-input agreement with equality of the
total languages. There is no hidden promise problem.

The register-graph search equivalence is
[`Source284GraphSilence.eventuallySilent_iff`](formalization/Shared/Beeping/NPcoNP/Source284GraphSilence.lean).
Follow `Source284GraphControllerRefinement` for the graph-to-search connection.
It connects to the same source comparison, not the deterministic comparison
used by the P versus NP machine.

## 5. Canonical NP and coNP

The class definitions come from the pinned public dependency
[`FormalConjecturesForMathlib/Computability/Complexity.lean`](https://github.com/google-deepmind/formal-conjectures/blob/5a2fb85045c86e4a184b15ce7531ba199a3c4580/FormalConjecturesForMathlib/Computability/Complexity.lean).
NP uses polynomial-size Boolean-list witnesses and polynomial-time verifiers;
the underlying `IsPolyTime` uses mathlib's canonical TM2 complexity model.
The definition of coNP takes complements. Cost proofs use these encodings
and machine computations, not unit-cost arithmetic on arbitrarily large
natural numbers.

The class argument has four audit points:

- [`Source284ReferenceNP.reference_mem_NP`](formalization/Shared/Beeping/NPcoNP/Source284ReferenceNP.lean)
  supplies actual reference membership, including the witness guard and bit costs.
- [`Source284SelectorClosed.sat_hard`](formalization/Shared/Beeping/NPcoNP/Source284SelectorClosed.lean)
  supplies the polynomial SAT reduction. The canonical SAT completeness
  theorem used upstream is in
  [`GeneratorGateListClosed.lean`](formalization/Shared/ComplexityBridge/GeneratorGateListClosed.lean).
- [`Source284CandidateNP.candidate_mem_NP`](formalization/Shared/Beeping/NPcoNP/Source284CandidateNP.lean)
  supplies membership for every fixed candidate with its actual full input
  and coupled clock.
- [`Source284AllInputReferenceCoverage.reference_coverage`](formalization/Shared/Beeping/NPcoNP/Source284AllInputReferenceCoverage.lean)
  supplies one fixed candidate for the reference complement whenever that
  complement belongs to NP.

For the last item, inspect
[`Source284AllInputCandidate.canonical_np_all_input_candidate`](formalization/Shared/Beeping/NPcoNP/Source284AllInputCandidate.lean).
It treats all frames and arbitrary suffixes. The empty-prefix wrapper handles
the exact one-step clock; positive-prefix execution pays its entry cost.
Acceptance-preserving program padding gives an arbitrarily large candidate
number so that the *same* number can be the required clock exponent.
`reference_coverage_unbounded` transfers this to every natural input.

Finally,
`Source284AllInputReferenceCoverage.graph_eventuallySilent_iff_classes`
is the unconditional graph theorem used by the physical endpoint.
Earlier files with `Conditional` in their names expose intermediate
obligations; the final theorem does not retain those obligations as premises.

## 6. A short skeptical review plan

1. Parse `events.tm` independently: check its hash, 284 states, 568 rows,
   start/head/blank, total destinations, L/R moves, and unique marked row.
2. Read `Machine.step`, `EventuallySilent`, and the full endpoint type.
3. Trace serialized table binding, rather than checking only generated
   numeric data.
4. Trace blank-ray preservation, first-beep alignment, the root and beep
   cases, and the positive physical progress statement for every graph step.
5. Inspect cofinal matching and the event-prefix boundedness proof.
6. Check the actual complement comparison and complete input universe,
   especially empty prefixes, ignored suffixes, and equal-bit refutations.
7. Check canonical class definitions, reference completeness, fixed-candidate
   NP membership, and the coupled-program/exponent coverage theorem.
8. Rebuild the exact pinned package and audit the printed axioms. Record
   whether project artifacts or dependency caches were reused.

A passing build establishes that Lean accepts the statements from the given
sources under its trusted kernel and declared axioms. The interface review
checks that those statements express the intended mathematical claim. Neither
should be represented as a substitute for the other.
