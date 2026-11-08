# Verification and scope

Date: 2026-11-08.

The package contains a conventional invariant proof and exact finite tests.
The proof, rather than the tests, establishes the all-dimensions theorem.
No proof-assistant formalization, external referee acceptance, human-expert
review, priority, or optimality is claimed.

## Reproduce the tests

Use Python 3.10 or later, with only its standard library, from this directory:

```sh
python verify.py
python check_gadget.py
python check_profile.py
python permanent.py 3 1 1
python permanent.py -- 5 1/2 -2/3
```

The CLI commands exercise integer and signed-rational inputs. A `--` before
the positional arguments prevents a negative fraction being parsed as an
option. Inputs of different lengths and negative dimensions are rejected.

## Direct recurrence checks

`verify.py` passes **1,311 exact instances** with seed `3708`:

- 392 signed AP cases: n = 0,...,7 and A,B = -3,...,3, checked against
  independent subset assignment DP. Each also checks the identity
  P_n(-A-(n-1)B,B) = (-1)^n P_n(A,B). The cases n <= 5 additionally use
  direct permutation enumeration.
- 150 rational AP cases: 15 per dimension n = 0,...,9.
- 180 signed generalized cases: 20 per dimension n = 0,...,8, with
  permutation checks as well as subset DP through n = 6.
- 96 generalized rational cases: 12 per dimension n = 0,...,7, with
  independently chosen denominators for every input.
- 392 generalized finite-ring cases: eight per dimension n = 0,...,6 for
  each modulus 2,3,4,6,9,11,25. The tested recurrence runs on actual residue
  objects, including composite characteristics and zero divisors, and is
  compared to the integer reference reduced modulo that modulus.
- 17 values of [OEIS A086759](https://oeis.org/A086759), n = 1,...,17;
  subset DP independently confirms them through n = 13.
- 66 exact evaluations: n+1 distinct A values at B=1 for each n = 0,...,10.
  Because both expressions are homogeneous of degree n, these determine the
  entire AP polynomial at each tested dimension over the integers.
- 18 constant matrices: n = 0,1,2,5,12,20 and A = 0,-2,3, compared with n! A^n.

It also checks the example per(Circ(1,2,3)) = 54 and two input-validation
errors, beyond the 1,311 counted instances. The finite tests cover negative
weights, zero inputs, the empty matrix, unequal independent row and column
parameters, rationals, and rings where factorials can vanish.

The independent references enumerate permutations or assign a row to a
column subset. Neither reference uses the endpoint-color recurrence.

## Reduction and matching profile checks

`check_gadget.py` passes **90** deterministic signed cases, 15 for each
n = 0,...,5, using seed `37082026`. It constructs the gadget graph directly,
independently evaluates the eleven-label expression and compares full
weighted adjacency matrices, and compares exhaustive graph matching sums
against direct permanent enumeration.

`check_profile.py` passes **180** deterministic signed cases, 20 for each
n = 0,...,8, using seed `20261108`. It compares the unmatched-label matching
recurrence with direct permutation enumeration. The 100 cases through
n = 4 also compare with exhaustive gadget matching sums. It asserts both
profile-balance identities during execution.

These graph tests do not call the direct endpoint-color implementation.
The profile implementation stores five counts for readability; the proved
balance identity leaves only four independent coordinates.

## Independent review and rendering

[INDEPENDENT_REVIEW.md](INDEPENDENT_REVIEW.md) records the independent
automated review, its exact file hashes, additional checks and limitations.
That review is separate from authorship of the public writeup. It does not
stand in for a human specialist or external referee.

GitHub math source uses protected inline math and fenced `math` blocks to
avoid Markdown consuming TeX escapes. Actual GitHub rendering is checked
on the publication candidate separately from the mathematical review.
