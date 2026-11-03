# Proof guide

This guide explains the mathematics and locates its formal interfaces. It is
not a substitute for the low-level tape proofs or a claim that those proofs
have received independent human review. The literal endpoint and its complete
local source dependency closure accompany this guide.

## 1. Search for a polynomial-time decider

Fix the binary reference language defined in
[`CanonicalInput.lean`](formalization/Shared/PNP/Record285/CanonicalInput.lean).
Its well-formed inputs are frames `1^n 0 payload` with exactly `n` payload bits;
malformed strings are rejected. The reference predicate uses a bounded
nondeterministic finite-program computation. Its NP membership is proved in
[`ReferenceVerifier.lean`](formalization/Shared/PNP/Record285/ReferenceVerifier.lean),
and hardness in
[`MaskedFramePoly.lean`](formalization/Shared/PNP/Record285/MaskedFramePoly.lean),
using explicit polynomial-time encoding and simulation lemmas.
`ReferenceVerifier.reference_P_iff_P_eq_NP` assembles the consequence:
this language is in P exactly when P = NP.

The controller enumerates pairs `(program, exponent)` with a natural program
code and a strictly positive exponent. A candidate is a deterministic bounded
simulation with clock `(n+2)^exponent`. For one candidate, it checks all payloads
of length 0, then length 1, and so on, comparing its bounded acceptance bit with the
reference predicate. Each individual comparison is a finite computation.

On beginning a candidate it beeps. If a comparison disagrees, it proceeds to
the next candidate. If no comparison disagrees, it continues checking forever
without another beep. The enumeration reaches every program/positive-exponent
pair, and the payload enumeration reaches every admissible input.

## 2. Why silence means a correct candidate

If a candidate is not correct, there is a particular finite counterexample.
The exhaustive input scan eventually reaches it, and finite comparison
termination lets the controller move on. If every candidate is bad, candidate
beginnings occur arbitrarily late, hence there are infinitely many beeps.

Conversely, if some candidate is correct, either an earlier correct candidate
is reached or each earlier candidate is rejected after finite work. In both
cases the controller eventually stays with a correct candidate and becomes
silent. This is the exact equivalence
`Source.eventuallySilent_iff_goodCandidate` in
[`SourceEndpoint.lean`](formalization/Shared/PNP/Record285/SourceEndpoint.lean).

This argument does not decide whether any candidate is correct. A long quiet
prefix can always belong to a bad candidate whose first counterexample has
not yet been reached.

## 3. Why the candidates capture P, in both directions

A uniformly correct candidate gives a polynomial-time algorithm for the
entire reference language, including rejection of malformed frames. The
formal simulation charges for parsing, tape encoding, and the bounded
finite-program computation. By NP-hardness of the reference language, this
implies P = NP.

For the converse, suppose P = NP. The reference language then has a canonical
polynomial-time decider. The proof converts that decider to a finite program,
prepares the exact input expected by the evaluator, and absorbs setup and
simulation time into one fixed positive-exponent clock. The payload is
reversed where required by the tape encoding, including the zero-length case.
Those costs matter: an unproved free input-conversion wrapper would leave a
gap in this direction. The actual auxiliary encoder and the paid clock are
proved in `PayloadHandoff`, `PayloadClosed`, and `PolynomialClock`.
Thus a good candidate occurs in the controller's enumeration.

The older proposition `FrameEncodingWrapper` is not used as a premise of the
selected endpoint. The auxiliary encoder is a proof of a complexity bridge;
its state count is not being substituted for the physical 285-state machine.

## 4. Why this particular table implements that search

The literal table is embedded from the adjacent `events.tm` at Lean
elaboration. Kernel-checked character and row certificates bind every one
of its 570 rows to the numeric table used in the low-level proofs. The
successful parse, valid destinations, exact rows, and unique event mark are
theorems, so fallback parser values and modulo reductions are not assumptions
about the released machine.

The physical proof starts with the wholly blank tape. A finite, silent
initialization establishes the complete register-bank and control layout.
For every subsequent source action, a relation specifies the whole physical
tape, absolute head, control, and register values at its boundary. The next
source action is simulated by a positive finite physical segment. That
segment contains exactly one marked transition for a beeping action and no
marked transition for a silent action.

The boundary times are strictly increasing and unbounded. Therefore every
sufficiently late physical transition lies in some such finite segment;
there cannot be an unaccounted infinite physical interval between source
actions. The initialization prefix is silent. These facts transfer finite
and infinite beeping in both directions. See
[`AlignedPhysicalEvents.lean`](formalization/Shared/PNP/Record285/AlignedPhysicalEvents.lean),
[`AlignedPhysicalInitialization.lean`](formalization/Shared/PNP/Record285/AlignedPhysicalInitialization.lean),
and the [interface map](INTERFACE.md).

## 5. Compose the equivalences

For the released table, the chain is:

1. Finitely many marked physical transitions ⇔ eventual physical silence.
2. Eventual physical silence ⇔ eventual source-controller silence.
3. Eventual source silence ⇔ existence of one uniformly correct candidate.
4. Existence of such a candidate ⇔ reference language in P ⇔ P = NP.

The shared event definitions turn the negation into infinitely many beeps
iff P ≠ NP. All physical transitions remain defined in either case. The
conjunction is assembled in
[`LiteralEndpoint.lean`](formalization/Shared/PNP/Record285/LiteralEndpoint.lean).

## What the proof does not establish

- It does not establish P = NP or P ≠ NP.
- It does not give a finite experiment deciding either alternative.
- It does not establish global minimality of 285 states.
- It does not certify the entire historical Python compiler or its AST
  translation. The checked path begins with the frozen literal and explicit
  intermediate graph data supplied here.
- A successful kernel build and a small axiom inventory do not by themselves
  show that the definitions express the intended informal problem. That is
  the purpose of the separate interface audit.
