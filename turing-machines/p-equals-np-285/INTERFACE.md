# Does the formalization say the right thing?

This is a reading map for a skeptical reader who does not want to read the
whole Lean development. It records an independent automated source/interface
inspection of upstream revision `576f0f2d69d37e4ba29d75ea712ddac6174832ca`.
It is not a full line-by-line proof review or independent human mathematical
review. Actual build and axiom results belong in [VERIFICATION.md](VERIFICATION.md).

## The single endpoint to inspect

[`LiteralEndpoint.lean`](formalization/Shared/PNP/Record285/LiteralEndpoint.lean)
contains `Shared.PNP.Record285.LiteralEndpoint.selected_literal_endpoint`.
Its statement is a closed conjunction about the actual parsed literal table:

- Every initial cell is 0, the state is 0, and the head is at 0.
- Every physical row equals the checked numeric row.
- An event at time `t` occurs exactly when the current state is 121 and the
  current cell is 1.
- Every next configuration exists.
- The event-time set is finite iff `ComplexityTheory.P = ComplexityTheory.NP`.
- There are infinitely many events iff those classes differ.

There is no explicit wrapper, simulation, hardness, or P/NP assumption in
that theorem's type. This is not a halting equivalence or a decision of P vs NP.

## 1. Bytes, machine model, and observation

[`Machines.lean`](formalization/Shared/Beeping/Machines.lean) defines
`Machine.step`: read the current cell, select a fixed row, write, move one
cell left or right, enter the next state, and return the row's Boolean event
flag. The tape is `Int → Bool`. There is no oracle or unit-cost arithmetic
operation in a physical machine transition.

[`Events.lean`](formalization/Shared/Beeping/Events.lean) defines `BeepAt t`
as the flag of the outgoing transition from `run t`. `FiniteEventTimes`
means a finite list contains every event time. The theorem
`eventuallySilent_iff_finiteEventTimes` connects it to eventual silence.
[`Refinement.lean`](formalization/Shared/Beeping/Refinement.lean) defines
infinitely many events by an event at or beyond every natural time threshold.

[`Table.lean`](formalization/Shared/PNP/Record285/Table.lean) embeds its adjacent
`events.tm`. It requires the exact 285-state/start-0/blank-0/head-0 header,
570 ordered rows, valid destinations, and the unique event flag at index 243.
[`Machine.lean`](formalization/Shared/PNP/Record285/Machine.lean) contains
fallback parsing, default rows, and modulo conversion, which deserve scrutiny:
[`ArtifactEndpoint.lean`](formalization/Shared/PNP/Record285/ArtifactEndpoint.lean)
proves `literal_parse`, `literal_valid`, and `literal_rows`, discharging those
obligations for the exact embedded bytes.
[`Certificate.lean`](formalization/Shared/PNP/Record285/Certificate.lean)'s
`validated_row_exact` and `validated_destination` explain why defaults and
wrapped destinations cannot enter the certified table. `literal_beep`
identifies the unique row `121 1 0 L 1 1`.

The 286-state companion is not the selected table.
[`LiteralQuotient.lean`](formalization/Shared/PNP/Record285/LiteralQuotient.lean)
proves a complete-configuration, step-for-step event refinement when the
companion is observed on entry to B. Its `beep_shift` theorem places the
companion's exit-from-B observation at `t+1`. Marking both exits of state 1
in the selected table would be a different observer.

## 2. Blank start and genuine progress

`Record285.perpetual` is totality, not by itself exclusion of an infinite
administrative loop. The stronger property is the direct refinement in
[`AlignedPhysicalEvents.lean`](formalization/Shared/PNP/Record285/AlignedPhysicalEvents.lean):
`AlignedPhysical.refinement` and `source_action_physical_segment`.

[`SourceControllerSimulation.lean`](formalization/Shared/PNP/Record285/SourceControllerSimulation.lean)
proves a positive finite segment for every source action, preserving the
bank/scratch invariant and exact event count. `ExpansionBoundary` and
`ZeroBoundary` align source boundaries through the finite compiler passes.
[`AlignedPhysical.Rel`](formalization/Shared/PNP/Record285/AlignedPhysical.lean)
composes source state, projected/expanded/coalesced/rewritten banks, grammar
control, and `PhysicalNumeric.Rel`, which fixes every tape cell and the
absolute head. `related_at_boundary` establishes this at every boundary.

`boundary_strict` and `boundary_unbounded` supply positive progress and
cofinality. `boundary_event_iff` and `boundary_event_unique` say that a
beeping source action has exactly one marked physical transition in its
segment and a silent action has none. The proof therefore covers all late
physical transitions, rather than selected snapshots or sampled tape cells.

[`InitializationComplete.blank_start_entry`](formalization/Shared/PNP/Record285/InitializationComplete.lean)
reaches the initialized bank after 89,806,142 transitions, with no earlier
events. [`AlignedPhysicalInitialization.initial_prefix_silent`](formalization/Shared/PNP/Record285/AlignedPhysicalInitialization.lean)
covers the entire prefix before the first aligned source boundary.
[`FirstEvent.first_event`](formalization/Shared/PNP/Record285/FirstEvent.lean)
places the first event at zero-based index 89,844,409.
`first_event_in_first_source_segment` locates it uniquely in source segment 0.

[`DirectSilentProgress.P_eq_NP_silence_is_continued_correct_work`](formalization/Shared/PNP/Record285/DirectSilentProgress.lean)
says that, under P = NP, every sufficiently late physical transition lies
in a finite segment checking an input with one fixed good candidate, in the
prescribed input order, and is unmarked. This addresses silence caused by
a stuck simulation.

## 3. Input universe and candidate enumeration

[`Source.lean`](formalization/Shared/PNP/Record285/Source.lean) defines the
bounded reference and deterministic candidates. A candidate uses choice 0
and clock `(n+2)^exponent`; `mismatch` is disagreement, not complementation.
Programs and positive exponents are enumerated diagonally. All n-bit
payloads are visited. `SourceEndpoint.eventuallySilent_iff_goodCandidate`
is the equivalence with one uniformly correct candidate.

[`CanonicalInput.lean`](formalization/Shared/PNP/Record285/CanonicalInput.lean)
fixes raw frames to `1^n 0 payload`, with exactly n payload bits in low-bit-first
order. `parse_sound` accounts for every bit. The empty raw word is malformed;
the one-bit word `[false]` is the unique zero-payload frame. `referenceLanguage`
rejects malformed words. `goodCandidate_iff_all_bitstrings` connects the
numeric sweep to the total language on all binary strings. It is not an
unannounced promise problem.

## 4. Canonical complexity and paid conversions

The class names come from
[`FormalConjecturesForMathlib/Computability/Complexity.lean`](https://github.com/google-deepmind/formal-conjectures/blob/5a2fb85045c86e4a184b15ce7531ba199a3c4580/FormalConjecturesForMathlib/Computability/Complexity.lean),
not classes invented to fit this machine. `P` uses Boolean-list decision
functions with `IsPolyTime`. `NP` uses polynomial-length Boolean-list
witnesses and a polynomial-time pair verifier. `IsPolyTime` uses mathlib's
`TM2ComputableInPolyTime` with the canonical Boolean encoding. TM2 time counts
fixed statement blocks, with constants depending on the fixed machine; it
is not unbounded integers manipulated for free.
[`Encodings.lean`](formalization/Shared/ComplexityBridge/Encodings.lean)
proves the exact linear list/pair encoding lengths.

**A good candidate implies P = NP.**
[`CandidateCanonicalParsing.candidateLanguage_isPolyTime`](formalization/Shared/PNP/Record285/CandidateCanonicalParsing.lean)
pays for parsing and bounded candidate simulation.
`reference_isPolyTime_of_good` covers the complete reference language.
[`MaskedFramePoly.alignedFrame_isPolyTime`](formalization/Shared/PNP/Record285/MaskedFramePoly.lean)
pays for table construction, row serialization, padding, and the whole header.
`sat_reduces_reference` and `reference_np_hard` connect this to the canonical
SAT completeness proof in
[`GeneratorGateListClosed.lean`](formalization/Shared/ComplexityBridge/GeneratorGateListClosed.lean).
The resulting statement is `ReferenceVerifier.reference_P_iff_P_eq_NP`.

**P = NP supplies an enumerated good candidate.**
[`ReferenceVerifier.reference_in_NP`](formalization/Shared/PNP/Record285/ReferenceVerifier.lean)
supplies a polynomial verifier, rejects malformed frames, and uses
`WitnessTruncation` to rule out an unsearched witness suffix.
[`PayloadClosed.source_silent_of_reference_P`](formalization/Shared/PNP/Record285/PayloadClosed.lean)
compiles a decider for the reversed payload predicate using
[`FiniteProgramSingleUntag.canonical_decision_iff_finite`](formalization/Shared/Codes/FiniteProgramSingleUntag.lean).
[`PayloadHandoff.bounded_reflected`](formalization/Shared/PNP/Record285/PayloadHandoff.lean)
checks the actual auxiliary loader, exact reversed encoding, zero payload,
mirrored continuation, and bounded result after the setup duration.
`PayloadClosed.budget_bound` pays the quadratic setup and evaluator clock.
`CanonicalPolynomialCoverage` and `PolynomialClock` supply one fixed program
and positive exponent. The auxiliary loader is not the 285-state machine.

Finally,
[`DirectEndpoint.literal_silent_iff_P_eq_NP`](formalization/Shared/PNP/Record285/DirectEndpoint.lean)
composes the direct physical refinement, source equivalence, and canonical
complexity bridge. Its finite/infinite corollaries use the shared event
definitions, not a new acceptance convention.

## Remaining boundary and a minimal review plan

The stronger historical `CanonicalPBridge.FrameEncodingWrapper` is not proved,
but is not a premise of this endpoint. A checked translation of the producer's
Python AST is still open; the direct theorem follows checked intermediate
graphs to the Lean source. Historical comments about then-open downstream
obligations remain unchanged in the imported sources and should not be
mistaken for current theorem premises.

A compact skeptical review can proceed in this order:

1. Independently parse `events.tm` and compare its hash, header, 570 rows,
   and unique mark with the certificate inputs.
2. Read `Machine.step`, `BeepAt`, and the principal theorem's type.
3. Inspect the full-tape relation, positive/cofinal segment statements,
   initialization, and exact event accounting.
4. Check the raw-frame language and canonical P/NP definitions.
5. Check that both complexity directions pay their encoding and clock costs.
6. Rebuild from the pinned sources, print the endpoint's axioms, and compare
   the resulting evidence with the separately stated review scope.
