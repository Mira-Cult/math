**Public reading copy.** Presentation and links have been normalized. Historical status statements below belong to their source revisions; see the [current publication status](../README.md#review-and-verification-status). The matching original bytes are in the [source archive](../originals/PROBLEM.md).

# Prime arrays beyond the square

## Statement

For a prescribed finite set A of N distinct positive integers and a hypergraph
H on N labeled cells, seek a bijection from A to the cells for which every
edge sum is prime. Entries are used exactly once. Sums may repeat. The
constraint family is fixed before seeking the bijection.

Write p_j for the jth prime including p_1=2, and r_j=p_(j+1). The square
baseline uses exactly {r_1,...,r_(n²)}, every row, every column, and both
main diagonals, for all sufficiently large odd n.

## Goals

1. For each fixed C≥0, prove a threshold uniform over 0≤s≤Cn² for squares
   with the exact pool {r_(s+1),...,r_(s+n²)} and the baseline constraints.
2. Prove an eventual theorem for every odd n using exactly the first n³
   odd primes in [n]³ with all 3n² axis-parallel full lines prime.
3. Extract a non-tautological pool/controller/prime-target assembly theorem,
   reusable incidence and physical-trade code, and rigorous obstructions.

The fixed-residue-class square extension, full signed lines, proper sections,
cyclic directions, windows, and quadratic index sampling are separate variants.
Neither flagship includes an explicit numerical threshold unless one is
separately proved.

## Model and scope

For each fixed D≥2 the initial array pool is {r_1,...,r_(n^D)}.
The order n is odd. D is fixed before increasing n.

- **A:** all axis-parallel full lines, D n^(D−1) distinct edges.
- **B:** all full signed-coordinate lines: each coordinate is fixed, t, or
  n+1−t, and at least one coordinate varies. Identical subsets are deduplicated.
- **C:** all proper signed-coordinate sections of dimensions 1,...,D−1.
  Each coordinate is fixed or equals t_j or n+1−t_j; every independent
  parameter occurs. Sections are subsets, with repetitions removed.

For a cube and n≥3, B has 3n²+6n+4 lines; there are 3n+6 two-dimensional
sections. The latter include all interior axis slices and six diagonal squares.
The whole cube is excluded: its sum is immutable. A diagonal square is distinct
from a body diagonal. Even edge sizes greater than one force composite sums
for these positive odd pools.

For squares, wrapped direction c means an explicitly specified congruence
such as i+j=c mod n. Finite-field affine lines are a separate family, defined
only over a field. For N=n² cyclically ordered cells, the cyclic-window family
consists of all N windows of length n, indices taken modulo N. A spiral merely
relabels this order unless additional geometric constraints are retained.

Quadratic **index** samples have entries r_(f(k)), 1≤k≤n², for a positive
increasing integer-valued quadratic f. They are not squares of primes or the
prime values of f. The latter require separately stated supply assumptions.

Mathematical proof, independent review, finite certificates, integrity checks,
remote CI, and maintainer integration are separate statuses throughout.
