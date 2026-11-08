# Independent mathematical and implementation review

## Conclusion and scope

The direct construction in `README.md` has a complete conventional proof of
`per(M_P) = C(P)` over `{-1, 0, 1/2, 1}`. Review found no mathematical correction
necessary in the reviewed version. The executable generator agrees with the
stated construction and passed the independent finite tests below.

This is a mathematical and executable review, not formal verification,
external human referee acceptance, a novelty certification, or a minimality
claim. Finite tests support the proof; they do not replace it.

## Reviewed sources

The scope is pinned by SHA-256:

- `README.md`: `ac8d4ebe45d72b5d37516de29d28337a91e1185082ebb62e9eaf9d6ecf3a28af`
- `construct.py`: `e3caf396755c862731742090d979102fd1ed5ba813bc5b01078a32b34de33cd4`
- `verify_independent.py`: `532603712ffc170230dce691ff7b569929f500a61c5a6e18db3ac92c9b067b51`

The first digest includes the clarification that the sparse matrix-coordinate
size bound excludes optional forced-cell history and original-grid labels.
The saved `independent-verification.json` independently records the generator
and verifier source hashes.

## Mathematical checks

1. **Cofactor orientation and signs.** For `H[s,u]`, row `u` and column `s`
   are deleted. The forced directed path runs from `s` to `u`, so its weight
   is the corresponding entry of a power of `P`, with no determinant-style
   cofactor sign. This gives `H = I + P + ... + P^(q-1)`. The signed wraparound
   gives `P^q = -I`, hence `(I-P)H = 2I`. The unused block has permanent zero.
   The exceptional `q=1` identity is correct and is avoided in the generated
   residual matrix by forced-cell propagation.
2. **Global cancellation.** Fixing external edges makes the remaining internal
   sums factor over the cell blocks. Row-column balance gives equal input and
   output multiplicities in each block. An unused block contributes zero;
   with exactly `h` external rows and `h` blocks, every nonvanishing group
   therefore has precisely one input and one output in every block. This is
   correctly stated for grouped weighted sums, not individual matchings.
3. **Completion correspondence.** The one-port response is `2` for equal
   input/output symbol labels and zero otherwise. All external row-symbol and
   column-symbol slots are used once. Therefore each Latin completion has
   total weight `2^h`, and no other external assignment contributes. Adjoining
   `(1/2)I_h` produces literal equality with the completion count.
4. **Preprocessing and boundary cases.** Singleton cells are forced in every
   completion. Sequential propagation, recomputation of all three requirement
   families, contradiction detection, and the terminal matrices `[0]` and
   `[1]` preserve the count. It is unnecessary to propagate singleton
   row-symbol or column-symbol requirements. The theorem assumes an explicit
   grid and `n >= 1`; the program rejects malformed shapes, out-of-range
   symbols, Boolean values and other noninteger symbols.
5. **Exact size and alphabet.** For every residual block, `q >= 2` makes the
   diagonal and cyclic positions distinct. It contributes `5q` nonzeros,
   `4q` positive-one entries and `q` negative-one entries. The final matrix has
   order `t+2h`, exactly `5t+h` nonzeros, and exactly `h` half entries. The
   quantities `h,t` are measured after propagation. The global polynomial
   bounds and the distinction between sparse matrix data, optional metadata,
   and dense serialization are consistent.

## Independent executable checks

The verifier imports only the generator under review. Neither counting oracle
uses the cyclic identities or obtains an expected completion count from the
reduction:

- The permanent oracle uses exact rational arithmetic and recursively expands
  a remaining row or column of minimum degree, with memoization.
- The completion oracle enumerates row permutations and tests column
  uniqueness. For exhaustive orders one through three it independently
  enumerates the full Latin squares and counts compatible completions.

All **262,227** in-range grids of orders one, two and three were tested,
including contradictory clue arrays:

| Order | Grids | Returned `[0]` | Returned `[1]` | Residual matrices |
| --- | ---: | ---: | ---: | ---: |
| 1 | 2 | 0 | 2 | 0 |
| 2 | 81 | 50 | 30 | 1 |
| 3 | 262,144 | 256,308 | 5,592 | 244 |

Every returned matrix was evaluated, with no skipped well-formed test inputs.
In particular the empty order-three matrix has order 45 and permanent 12.
There were 18 additional tests obtained by deleting rows `0` and `delta` from
cyclic squares of orders four through seven, for every `delta` from `1` through
`n-1`. These reached matrix order 56 and also passed exact comparison.

Total: **262,245 completion/permanent comparisons**, plus **14 malformed-input
rejection tests**. The suite also checks input immutability, exact JSON weight
round-tripping, coordinate ranges, global bounds, the residual size formulas,
and the number of entries of each nonzero weight.

From the repository root, reproduce with:

```sh
python3 notes/combinatorics/latin-completion-permanent/verify_independent.py \
  notes/combinatorics/latin-completion-permanent/construct.py
```

The deterministic standard-output report is `independent-verification.json`;
short progress records are written separately to standard error. Python 3.10
or later and only the standard library are required.

No exhaustive claim is made at order four or above. The tests do not certify
novelty, optimality, the feasibility of eliminating zero, or an improved general
counting algorithm. No claim depends on an unproved complexity separation.
