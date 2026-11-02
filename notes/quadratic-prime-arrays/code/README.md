# Exact quadratic-prime-array prototype

## Running code

Use Python 3.11 or newer; the recorded run used CPython 3.12.14. All modules
use only the standard library. From the repository root:

```sh
python3 -B notes/quadratic-prime-arrays/code/check_certificate.py --negative-controls notes/quadratic-prime-arrays/inputs/gaussian_*.json notes/quadratic-prime-arrays/inputs/eisenstein_*.json
```

This independently reconstructs each prescribed pool, all deduplicated signed
coordinate lines, every entry and line sum, and every prime-element certificate.
It also consumes complete residue-obstruction proof trees. It does not invoke
the producer, numerical primality probabilities, or a SAT solver.

The separately labeled physical-trade fixtures have a different format:

```sh
python3 -B notes/quadratic-prime-arrays/code/vector_trade_fixture.py verify notes/quadratic-prime-arrays/inputs/vector_trade_*.json --negative-controls
python3 -B notes/quadratic-prime-arrays/code/local_audit.py --self-test
```

Do not pass `vector_trade_*.json` to the array-certificate checker. Those
fixtures demonstrate legal vector trades, not arrays with all line sums prime.

## Reproducibility

`prime_arrays.py` is the producer library. Its canonical pool is a lattice
scan in increasing norm disks, sorted by `(norm,a,b)`, retaining conjugate
associate classes and positive-real inert primes. Exactly the ramified class
is omitted. Its line enumerator scans fixed/forward/reverse coordinate patterns.

`check_certificate.py` imports no producer functions. It independently scans
integer norms and solves the coordinate quadratic equations to regenerate the
pool. Its line enumerator chooses the varying-coordinate subset and direction
signs, fixing the first sign to remove reversal duplicates. Both enumerate
deduplicated cell sets. All certificate arithmetic is integral.

For primality the checker trial-divides the rational norm through its square
root, or, for an inert rational associate, trial-divides the underlying
rational prime and checks its inert residue class and unit ray. A composite
norm is therefore permitted exactly where it should be. The JSON records
specify the type, rational prime, and exact trial-division bound, making every
claim reproducible without external primality software. Trial division is
deliberately sufficient for these small certificates, not an efficient large
instance primality algorithm.

`search_arrays.py` uses seeded swap annealing with exact integer line scores.
Its floating acceptance probability is only a finite search heuristic. A
search budget exhausted without a solution proves nothing. Reproduce the
retained nontrivial successful searches (each uses seed 20261102):

```sh
python3 -B notes/quadratic-prime-arrays/code/search_arrays.py --ring gaussian --n 3 --steps 20000 --restarts 10 --output /tmp/gaussian_square3.json
python3 -B notes/quadratic-prime-arrays/code/search_arrays.py --ring eisenstein --n 3 --steps 20000 --restarts 10 --output /tmp/eisenstein_square3.json
python3 -B notes/quadratic-prime-arrays/code/search_arrays.py --ring gaussian --n 5 --steps 100000 --restarts 30 --output /tmp/gaussian_square5.json
python3 -B notes/quadratic-prime-arrays/code/search_arrays.py --ring eisenstein --n 5 --steps 100000 --restarts 30 --output /tmp/eisenstein_square5.json
python3 -B notes/quadratic-prime-arrays/code/search_arrays.py --ring eisenstein --n 6 --steps 100000 --restarts 30 --output /tmp/eisenstein_square6.json
python3 -B notes/quadratic-prime-arrays/code/search_arrays.py --ring gaussian --n 3 --dimension 3 --steps 100000 --restarts 30 --output /tmp/gaussian_cube3.json
```

The search metadata in every certificate records the budget, seed, restart,
and successful step. Replaying the same Python implementation reproduces the
certificates. The four singleton files are obtained directly by applying
`certificate(ring,1,dimension,canonical_pool(ring,1),{"method":"singleton"})`.
The Eisenstein singleton is the inert element 2, whose norm is 4.

## Certified finite results

| Ring | Dimension | Successful orders | Required distinct lines |
|---|---:|---|---|
| Gaussian | 2 | 1, 3, 5 | 1, 8, 12 |
| Gaussian | 3 | 1, 3 | 1, 49 |
| Eisenstein | 2 | 1, 3, 5, 6 | 1, 8, 12, 14 |
| Eisenstein | 3 | 1 | 1 |

The Eisenstein order-six square shows concretely that neither oddness nor
`3 not dividing n` is a necessary condition for the frozen sector pool.
Successful finite arrays do not prove any eventual-existence theorem.

## Complete finite obstruction proofs

For an Eisenstein element `a+b*omega`, reduction modulo `1-omega` is `a+b`
modulo 3. A bit 1 denotes residue +1; a bit 0 denotes residue -1. An n-cell
line containing k plus entries has sum `2k-n` modulo 3. If this vanishes,
the line cannot be prime: the positive-real-part lower bound checked from the
pool excludes an associate of the ramified norm-3 prime.

The retained obstruction certificates contain complete binary search trees.
Every propagation has a particular line or pool-count reason. Every branch
has both children, and every leaf gives a violated line/count constraint.
The independent checker reconstructs these constraints and checks the entire
proof, rather than trusting an `unsat` assertion or absence of a found array.

```sh
python3 -B notes/quadratic-prime-arrays/code/search_arrays.py --ring eisenstein --n 2 --obstruction --output /tmp/eisenstein_square2_obstruction.json
python3 -B notes/quadratic-prime-arrays/code/search_arrays.py --ring eisenstein --n 4 --obstruction --output /tmp/eisenstein_square4_obstruction.json
python3 -B notes/quadratic-prime-arrays/code/search_arrays.py --ring eisenstein --n 3 --dimension 3 --obstruction --ignore-total-count --output /tmp/eisenstein_cube3_obstruction.json
```

| Impossible instance | Plus/minus input counts | Proof nodes | Contradiction leaves | Count used? |
|---|---|---:|---:|---|
| Eisenstein 2-square | 1 / 3 | 3 | 2 | yes |
| Eisenstein 4-square | 7 / 9 | 567 | 284 | yes |
| Eisenstein full signed 3-cube | 12 / 15 | 47 | 24 | no |

The cube proof establishes the stronger finite fact that **every** two-coloring
of the 27 cells of `[3]^3` has a monochromatic one of the 49 signed lines. It does not need
the exact 12/15 color count. This is a finite exception, not an obstruction to
all sufficiently large orders. See the local-arithmetic manuscript for its
mathematical role and the hand proof of the order-four square obstruction.

## Negative controls and limits

The checker rejects omitted lines, false sums/norms, corrupt prime records,
wrong cell coordinates, unit-rotated entries, duplicate entries, and changed
pool order. Obstruction controls corrupt the color count, allowed line counts,
contradiction, or branch completeness. It also tests inert associates on several
unit rays, ramified elements, units, split rational composites, and the first
three pool representatives.

The finite replay covers ten array certificates and three obstruction
certificates, with 84 rejected mutations and 14 arithmetic controls. It is
not a proof of the analytic supply lemmas, controller capacities, or an
asymptotic theorem. The source revision and independent-review attribution
belong in the coordinating recovery record, separate from these mathematical
and computational claims.

## Two directions in one physical cube

`vector_trade_fixture.py` supplies a reproducible finite trade in each ring.
Each fixture uses exactly the first 6,859 canonical representatives in an
order-19 cube, with eight disjoint actual pairs on sixteen reserved cells.
The remaining entries fill the remaining lexicographic cells in canonical
pool order. The two increments are `(2,0)` and `(0,2)` in the ring's fixed
integer basis; their generated lattice has Smith invariants `(2,2)` and
index four. The attainable native changes are `0`, `(2,0)`, `(0,2)`, and
`(2,2)`, each implemented by a single permutation of whole prime elements.

Each cuboid has four simultaneous equal-gap pairs. Its alternating vertex
signs preserve every axis line and the other three body diagonals. Its
native body change has six recorded face-line side effects. The two stages
use fresh reflection orbits, so these effects occur at different slice
levels. All four orientations are reconstructed and checked against all
1,201 signed lines. The compact JSON records the exact pairs, supports,
cutoff including its next representative, all changed line sums, total,
and digests of the fully reconstructible arrays and complete sum lists.
The Eisenstein fixture includes the inert endpoint `11`, of norm `121`.

```sh
python3 -B notes/quadratic-prime-arrays/code/vector_trade_fixture.py generate --ring gaussian --output /tmp/vector_trade_gaussian.json
python3 -B notes/quadratic-prime-arrays/code/vector_trade_fixture.py generate --ring eisenstein --output /tmp/vector_trade_eisenstein.json
```

Both regenerate byte for byte. Verification reconstructs the pool through
the independently authored norm-shell checker, checks the tensor incidence
formula against actual sums, and rejects ten corruptions per ring. The
fixture generator and its verifier share one module; their nonauthor source
review is recorded in [the provenance record](../PROVENANCE.md).
These fixtures neither claim all-prime line sums nor implement the eventual
asymptotic construction. No fixed-gap infinitude is inferred from them.
