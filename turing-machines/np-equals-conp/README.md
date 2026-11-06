# Two small beepers for NP versus coNP

These are explicit deterministic, two-symbol, single-tape Turing machines.
Each starts on an entirely blank two-way tape, runs forever, and emits a beep
on one designated transition. For each machine:

> There are finitely many beeps if and only if NP = coNP.
> There are infinitely many beeps if and only if NP ≠ coNP.

This does not settle NP versus coNP. It encodes the question in a property of
an infinite computation. No finite stretch of silence distinguishes a correct
candidate from one whose counterexample has not yet been reached.

| Machine | Marked table | B-exit companion | Proof status |
| --- | ---: | ---: | --- |
| [284-state machine](beeper284/README.md) | 284 states, 568 rows | 285 states, 570 rows | Lean theorem for the exact marked table and blank start |
| [266-state machine](beeper266/README.md) | 266 states, 532 rows | 267 states, 534 rows | Conventional proof with scoped internal nonauthor reviews |

The smaller machine saves eighteen complete states, but its literal-table
theorem has not been formalized in Lean. The 284-state proof does not certify
the changed source, compiler transformations, or table of the 266-state machine.
Neither state count is claimed to be globally minimal.

## What the machines search for

Fix an NP-complete reference language. A candidate is a clocked verifier
that is supposed to recognize its complement. Both the reference computation
and the candidate computation search over a finite set of certificates.
For each input they produce two acceptance bits.

The search beeps when beginning a candidate and tests inputs in order. Unequal
bits mean that the candidate has behaved correctly on this input. Equal bits,
including both `(0,0)` and `(1,1)`, refute the candidate and cause the search
to move on. Every individual comparison finishes.

If NP = coNP, one enumerated candidate recognizes the reference complement
on every input. The search eventually reaches a candidate that never fails,
so the beeps stop. If NP ≠ coNP, every candidate fails somewhere. The search
keeps moving to new candidates and beeps infinitely often.

The important implementation work is making this argument apply to a complete
small binary table: accounting for actual input and certificate encodings,
the coupled program and clock enumeration, every arithmetic operation,
initialization, physical progress, and the exact event convention. The linked
proof guides explain those parts.

## How this differs from the P versus NP machine

The [285-state P versus NP machine](https://github.com/Mira-Cult/math/blob/24a7a74a66885c95d29da1deea9dbe2968595d35/turing-machines/p-equals-np-285/README.md) looks for a
deterministic polynomial-time decider agreeing with an NP-complete language.
These machines look for an existentially verified complement, so successful
comparison means **disagreement**, not agreement. NP = coNP is not identified
with P = NP.

## Reading and checking

- Start with the [284-state proof guide](beeper284/PROOF.md).
- Use its [Lean interface guide](beeper284/INTERFACE.md) to trace the
  exact table, blank start, physical simulation and canonical complexity classes.
- Read [how the 266-state construction saves states](beeper266/PROOF.md).
- Keep the separate verification receipts in view: [284](beeper284/VERIFICATION.md)
  and [266](beeper266/VERIFICATION.md). Source identity, finite tests,
  kernel checking, and mathematical review are different kinds of evidence.

The headline counts use a marked-transition observer. A beep is the flag of
the row actually taken. Observing exits from a designated state B uses the
larger companion in each case. In the conventional companion construction,
the corresponding B exit is one transition later. The 284-state Lean endpoint
described here concerns its marked table, not a new formal theorem for the
companion.

The [layout history](MIGRATION.md) maps the original public paths to these
packages and links the earlier snapshot.
