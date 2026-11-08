# Verification and reproduction

## Status and scope

The [main note](README.md) contains a conventional proof for all explicitly
supplied finite grids. The code constructs an exact sparse matrix; its output
uses rational weights, not floating-point approximations. Finite computations
are supporting checks, not substitutes for the proof.

An independent mathematical review checked the transposed cofactor identity,
the cancellation grouping, the external-port count, the completion
correspondence, singleton propagation, terminal cases, and the exact size and
alphabet bounds. It found no mathematical correction necessary. The
[review record](INDEPENDENT_REVIEW.md) pins the reviewed sources and states the
scope of the independently implemented tests.

This release does not claim formal verification, external human referee
acceptance, novelty, optimality, removal of zero, or a faster general counting
algorithm.

## Requirements

Python 3.10 or later, standard library only. The release checks were run using
Python 3.12.14. No packages, network access, theorem prover, or external data are
needed for the computations.

From the repository root:

```sh
python3 notes/combinatorics/latin-completion-permanent/verify.py
python3 notes/combinatorics/latin-completion-permanent/verify_independent.py \
  notes/combinatorics/latin-completion-permanent/construct.py
```

The first command prints the deterministic report stored in
[verification.json](verification.json). To write a fresh copy elsewhere, use
`verify.py --output FILE`.
The second command prints the separate report stored in
[independent-verification.json](independent-verification.json).

To generate the matrix for the displayed order-three example:

```sh
python3 notes/combinatorics/latin-completion-permanent/construct.py \
  notes/combinatorics/latin-completion-permanent/examples/two-missing-rows.json
```

The result has order 24 and 66 listed nonzeros; its permanent is 2. Matrix
products are not checked into the repository: they can be regenerated from
the supplied inputs and source.

## Primary finite suite

[verify.py](verify.py) uses row-permutation enumeration to obtain completion
counts independently of the construction. Its generic permanent evaluator
uses exact column-subset recursion, with no gadget or Latin identity.
Ryser inclusion-exclusion provides a second permanent evaluation for two
order-16 examples.

The saved run passed:

- the cyclic identities for all q from 1 through 8, including each full
  cofactor matrix and P^q = −I;
- all 2 order-one and 81 order-two in-range grids, including contradictions;
- nine named edge-case and nontrivial examples;
- 493 erasures of a cyclic order-three square whose resulting matrix order
  was at most 28;
- 223 seeded random order-three/order-four grids with resulting matrix order
  at most 28;
- eight malformed-input rejection tests;
- exact order, nonzero count, alphabet and coordinate checks.

This totals 808 completion/permanent comparisons. Many grids yield the same
matrix, including [0] and [1], so this suite caches 14 distinct permanent
computations. It explicitly skips 19 larger erasure cases and 17 larger random
cases. It checks only the dimensions/alphabet and independently counts the
Latin squares for the empty order-three input; it does not numerically
compute that permanent in this primary suite.

## Independent exhaustive suite

[verify_independent.py](verify_independent.py) uses a separately implemented
generic permanent recursion that dynamically expands a remaining row or
column of minimum degree. Its completion oracle independently enumerates
Latin arrays by row permutations.

The saved independent run passed all **262,227** in-range grids of orders
one through three:

| Order | Grids | Returned [0] | Returned [1] | Residual matrices |
| --- | ---: | ---: | ---: | ---: |
| 1 | 2 | 0 | 2 | 0 |
| 2 | 81 | 50 | 30 | 1 |
| 3 | 262,144 | 256,308 | 5,592 | 244 |

Every returned matrix was evaluated using exact arithmetic. This includes
the empty order-three matrix: order 45, 144 nonzeros, permanent 12.
The suite also checks 18 cyclic squares of orders four through seven with two
rows erased, producing matrix orders up to 56, and 14 malformed input cases.
It checks that construction does not mutate its input and that the sparse JSON
encoding round-trips exactly.

The independent exhaustive suite therefore covers the empty order-three case
that the smaller primary suite intentionally leaves unevaluated. It does not
assert exhaustive coverage at order four or above, nor efficient evaluation
of arbitrary larger permanent instances.

## GitHub mathematical rendering

The initial mathematical source was correct but its GitHub preview had rendering
defects: rejected operator macros, Markdown-consumed escapes, malformed matrix
row breaks, and unrendered inline expressions. The rendering-only correction
uses protected inline math, fenced math blocks, and supported upright operator
text. No construction or verifier source was changed.

The corrected note (SHA-256
`ead6e54f5353062b9ac378d56f962047023b72e6c86d81731210cc8286fc0436`)
was checked in the actual GitHub Preview in a browser on 8 November 2026:

- all 177 expressions rendered as mathematical elements: 156 inline and 21 display;
- no math error boxes or leftover dollar-delimited/raw TeX expressions;
- all three displayed matrices have two rows and two columns;
- the entrywise definition has three correctly aligned rows;
- the seven expressions using set braces visibly retain those braces.

Screenshots were inspected at the opening statement and the cyclic/cofactor
and matrix-definition sections. These are rendering checks, separate from the
mathematical proof review and numerical tests above. The historical reviewed
manuscript hash is preserved in the review record, with a rendering-only
comparison recorded separately.

## Publication boundary

The public package contains the proof, construction source, verification
source, a small example input, and scoped verification/review metadata.
Background literature is cited in the note. No conversation transcripts,
private source links, credentials, or generated matrix/build products are
included.
