# Collatz research

The ordinary Collatz conjecture asks whether every positive integer reaches 1. In the shortcut convention, the $`3x+1`$ step at an odd integer is followed immediately by a division by two. The target cycle is $`1\leftrightarrow 2`$.

## Changes to the rule

- **[Collatz with a density-zero set of changed steps](density-zero-modification.md):** One explicit density-zero set of replacements makes every positive orbit converge. Arbitrarily sparse periodic replacements also force convergence to the same cycle. A separate sharp bound gives the minimum fraction of classes needed for uniform descent. Includes the proofs and an exact finite checker. These results concern modified rules, not a proof of ordinary Collatz.

## Formulations of the ordinary conjecture

- [Collatz Turing machines](../../../turing-machines/collatz/README.md): the evaluator, cycle detector, and beeper encode different Collatz statements.
- [A recurrent tiling formulation](../../../tilings/collatz-30/README.md): the conjecture is equivalent to an unseeded tiling with an additional recurrence requirement.
