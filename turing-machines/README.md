# Turing machines

A machine package includes its writeup, exact transition table, proof material,
provenance, attribution, and verification instructions. Related machines are
grouped into families.

## P versus NP

The [285-state beeper package](p-equals-np-285/README.md) contains a literal
blank-tape binary machine with finitely many designated transition events iff
P = NP, equivalently infinitely many iff P ≠ NP. It includes the table,
proof guide, skeptic-facing interface map, pinned Lean dependency closure,
provenance, and certificate generators. Execution never halts in either case.
The [verification receipt](p-equals-np-285/VERIFICATION.md) distinguishes source
checks, kernel-build evidence, and independent mathematical review.

## NP versus coNP

The [NP versus coNP family](np-equals-conp/README.md) contains the 284-state
marked-table machine and its Lean guide, alongside the smaller 266-state
machine and its conventional proof. Each package records its own verification
limits; neither machine resolves NP versus coNP.

## Collatz family

[Browse the Collatz machines](collatz/README.md), including their shared
certified proof infrastructure and source-identity checks.

### 12-state input evaluator

The [12-state evaluator package](collatz/evaluator12/README.md) proves that
on every encoded positive input the machine halts exactly when the ordinary
Collatz orbit reaches 1. Universal positive-input termination is equivalent
to the ordinary Collatz conjecture. Lean-certified.

### 16-state blank-tape cycle detector

The [16-state cycle-detector package](collatz/cycle16/README.md) proves that
the blank-tape machine halts exactly when a nontrivial positive ordinary
Collatz cycle exists. It does not detect nonperiodic divergence. Lean-certified.

### 17-state blank-tape beeping machine

The [17-state beeper package](collatz/beeping17/README.md) has infinitely
many blank-tape beeps exactly when every positive ordinary Collatz orbit
reaches 1. It includes an ordinary mathematical proof and finite checks,
not a Lean or Rocq certificate.

## Verification, provenance and attribution

Each package carries its own provenance and attribution. The certified Collatz
packages share [one byte-preserving build recipe](collatz/README.md#verify-locally).
See [attribution](ATTRIBUTION.md) and [migration notes](collatz/MIGRATION.md).
No minimality, record, or proof of the Collatz conjecture is claimed.

[Back to the mathematical research index](../README.md).
