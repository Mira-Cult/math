# Sude's First Conjecture

*Mira-Cult research note · updated 3 November 2026*

Can the first $`n^2`$ odd primes be placed in an $`n\times n`$ square so that every row, column, and both main diagonals have prime sums?

**Yes: the complete computer-assisted theorem covers every positive odd order.** The [resolution manuscript](resolution.md) combines exact certificates for all odd orders 1 through 1999 with the complete classical construction for every odd order from 2001 onward. It retains the prescribed prime pool and both diagonals. No finite range remains in the stated conjecture.

## Resolution and reproducible certificates

- **[Resolution of Sude's First Conjecture](resolution.md).** The full statement, two-case proof, finite certificate specification, tail construction, exact order-band map, explicit analytic imports, and verification instructions.
- **[Complete proof source and dependency map](proof-source/problems/prime-line-sums/manuscripts/sude_all_odd_theorem.md).** The full tail proof, source inputs and review records are supplied in the [complete public replay packet](packet/README.md). The linked browsable manuscript is also copied here.
- **[Actual witnesses for every odd order below 2001](certificates/odd-orders-1-1999.bin.gz).** A lossless 10,500,031-byte certificate reconstructs all 1,000 squares. The independent checker enumerates the exact primes and recomputes every required line sum.
- **[Final composition review](proof-source/problems/prime-line-sums/reviews/sude-all-odd-independent-review.md).** Exact scientific revision, review scope, and the distinction between conventional proof and computational checking.

The theorem is conventional computer-assisted mathematics with internal nonauthor review and independently reproduced exact checks. It is not an end-to-end Lean proof or a claim of external referee acceptance. The named analytic results, including published finite zero verifications, remain explicit imports. See [the resolution's import map](resolution.md#5-explicit-external-imports) and [reproduction instructions](resolution.md#6-reproduce-the-computational-component).

## Best reviewed bound for each family

Bounds are sufficient, not claimed optimal. The research bounds below are the latest internally reviewed results; the cube and 4D improved-bound manuscripts are not yet publicly reproduced. Their older public expositions remain available below.

| Family | Best reviewed bound | Scope / source |
|---|---|---|
| Ordinary prime squares | **1** | Every positive odd order; [resolution](resolution.md) |
| Ordinary prime cubes | **2^192** | Every odd order at or above the bound; internally reviewed research result with unpublished proof; not an all-odd-order theorem |
| Ordinary prime 4-hypercubes | **2^1460** | Every odd order at or above the bound; internally reviewed research result; improved-bound proof not yet public |
| Ordinary prime hypercubes, every fixed k≥2 | N(k), not numerically evaluated | Every sufficiently large odd order for each fixed dimension; all full signed-coordinate lines; [complete public proof and controls](integer-prime-hypercubes/README.md) |
| Gaussian prime squares | Not numerically evaluated | Every sufficiently large odd order; [proof](quadratic-prime-arrays/README.md) |
| Gaussian prime cubes | Not numerically evaluated | Every sufficiently large odd order; [proof](quadratic-prime-arrays/README.md) |
| Eisenstein prime squares | Not numerically evaluated | Every sufficiently large integer order; [proof](quadratic-prime-arrays/README.md) |
| Eisenstein prime cubes | Not numerically evaluated | Every sufficiently large integer order; [proof](quadratic-prime-arrays/README.md) |
| Canonical irreducible quadratic-polynomial arrays | **2^120 (D=2), 2^67 (D=3), 2^47 (D=4)**; all D≥2: **max{2^120, 2^24(D+1)^2}** | Both parities; every full signed-coordinate line; sums irreducible over Q; [complete public proof and controls](quadratic-polynomial-arrays/README.md) |

The cube and 4D research bounds retain the exact initial prime pools and every full signed-coordinate line. The public cube exposition below records the earlier 2^61750 bound; the public 4D exposition is qualitative. The smaller research bounds are recorded as internally reviewed, not silently substituted into those older public proofs.

## Generalizations

The following are distinct theorems. The resolution of the original square conjecture does not remove their stated thresholds or extend their ranges.

4. **[IV. The full signed-line prime cube](prime-cube.md).** For every sufficiently large odd $`n`$, exactly the first $`n^3`$ odd primes can be placed in a cube with prime sums on all $`3n^2+6n+4`$ full signed-coordinate lines: axes, both diagonals in every coordinate-parallel square slice, and the four body diagonals. The threshold is not evaluated. Its [supporting proofs](cube/README.md) establish integer compatibility, physical trades, and compatible prime targets.

5. **[V. Explicit full signed-line prime cubes](explicit-prime-cube.md).** Every odd $`n\ge2^{61750}`$ works for exactly the first $`n^3`$ odd primes and all $`3n^2+6n+4`$ full signed-coordinate lines. The [complete supporting proofs](cube-explicit/README.md) supply effective logarithmic prime windows, finite packing and centering, phased reflected allocation, and compatible exact-total targets. This numerical cube bound is separate from the square bound above.

6. **[VI. Full signed-line prime hypercubes in dimension four](prime-hypercube-4d.md).** For every sufficiently large odd $`n`$, exactly the first $`n^4`$ odd primes can be placed bijectively with all $`4n^3+12n^2+16n+8`$ full signed-coordinate line sums prime. The [four complete supporting proofs](hyper4/README.md) establish integer compatibility, joint prime targets and physical realization. No numerical cutoff is evaluated; the incidence threshold $`n\ge17`$ is not a prime-array cutoff.

7. **[VII. Gaussian and Eisenstein prime squares and cubes](quadratic-prime-arrays/README.md).** With the prescribed canonical prime-element pools, Gaussian squares and full signed-line cubes exist at every sufficiently large odd order; Eisenstein squares and cubes exist at every sufficiently large integer order, including even orders and multiples of three. The note includes the complete proofs, small obstructions, exact examples and runnable checks. No numerical cutoffs are evaluated.

8. **[VIII. Irreducible quadratic-polynomial arrays in every dimension](quadratic-polynomial-arrays/README.md).** For every dimension D≥2, the first n^D primitive irreducible integer quadratics in the fixed height-and-coefficient order admit a bijective placement with all full signed-coordinate line sums irreducible over Q once the stated explicit bound holds. Both even and odd side lengths are covered. The result includes complete proof sources, exact controls, source hashes and independent review. It does not assert primitive sums in Z[X] or an efficient construction.

9. **[IX. Integer-prime hypercubes in every fixed dimension](integer-prime-hypercubes/README.md).** For every fixed k≥2, the exact first n^k odd primes admit a bijective placement with prime sums on all ((n+2)^k−n^k)/2 full signed-coordinate lines for every sufficiently large odd n. The complete proof, named analytic/probability imports, fixed-frame and integral-kernel arguments, source hashes, internal reviews and offline controls are public. No numerical N(k), all-small-order assertion, growing-dimension theorem, or section-sum claim is made.

## The conjecture

Let $`p_j`$ be the $`j`$-th prime, with $`p_1=2`$, and set



```math
P_n=\{p_2,p_3,\ldots,p_{n^2+1}\}.
```



**Sude's First Conjecture.** For every positive odd integer $`n`$, there is an
$`n\times n`$ array containing every element of $`P_n`$ exactly once such that
every row, every column and each of the two main diagonals has a prime sum.

The pool is prescribed: it is exactly the first $`n^2`$ odd primes, beginning
with 3. No entry can be omitted, repeated or replaced. The **line sums** need
not be equal, need not be distinct, and may equal an entry. There is no extra
requirement that the sum of all entries be prime.

The odd-order restriction is necessary. For even $`n\ge2`$, each line sum is
an even integer greater than 2 and therefore composite. At $`n=1`$, the square
$`[3]`$ works; the row, column and both diagonal labels all refer to that same
single entry.

## A small example

At order three the prescribed entries are
$`3,5,7,11,13,17,19,23,29`$. One successful square is

|  |  |  | Row sum |
|---:|---:|---:|---:|
| 7 | 5 | 19 | **31** |
| 13 | 11 | 29 | **53** |
| 17 | 3 | 23 | **43** |
| **37** | **19** | **71** | Column sums |

The two diagonal sums are $`7+11+23=41`$ and $`19+11+17=47`$.
All eight required sums are prime. Exact order-three examples predate this
note; see the [example reference](REFERENCES.md#order-three-example).


## Historical appendix: earlier square proofs and bounds

These manuscripts are preserved as the successive proof stages, not as the current unresolved range. Their original arguments and supporting sources remain available; the complete all-odd resolution above supersedes their numerical cutoffs for the original square problem.

1. **[I. Eventual existence](proof.md).** Every sufficiently large odd order works. This is the original qualitative argument: it constructs a placement but does not provide an effective numerical threshold. Supporting manuscripts: [centered controller](controller.md) and [prime targets with an exact total](prime-targets.md).
2. **[II. The initial published explicit bound](explicit-bound.md).** Every odd $`n\ge2^{2^{40}}`$ works. This separate quantitative proof replaces the ineffective analytic inputs and pays all construction costs. Supporting manuscripts: [classical prime supplies](classical-primes.md), [finite controller](explicit-controller.md), and [exact prime targets](explicit-targets.md). This manuscript is preserved as the initial public numerical result.
3. **[III. The optimized explicit bound](optimized-bound.md).** Every odd $`n\ge2^{4320}`$ works. The improvement changes the analytic estimates, reservoir allocation, graph degree, and target window together. Its full composition and linked supporting proofs are published here.

The earlier [provenance record](PROVENANCE.md) and [reference list](REFERENCES.md) retain their historical scope. The resolution manuscript and complete packet give the current scientific pins and dependency boundary.

### How the historical optimized-bound proof works

The proof reserves disjoint reversible moves inside the prescribed pool, chooses compatible nearby prime sums, and uses the moves to attain those targets without replacing or repeating any entry.

- **Uniform prime supplies.** A density and matching argument finds many disjoint pairs with one common even gap. Explicit arithmetic-progression estimates supply the additional primes at each actual scale. The analysis keeps the sign of a possible exceptional-zero contribution, retains the constants in the original zero-sum integrals, and proves the domain needed for their use.
- **Cheaper disjoint reservoirs.** Delicate residue and prefix gadgets are reserved first. Wider reservoirs then use all reduced residue classes, with every deletion charged against the aggregate remaining stock. Reflected interval bins keep pair midpoints close to the pool mean even though the supply bands are wide.
- **Lower-degree routing.** A degree-10 multigraph still supports the full integral row and column correction range. The reduced degree lowers reservation, placement, and centering costs. Independent rectangle trades handle both diagonals while preserving the row and column sums.
- **A constant relative target window.** With $`X=p_{n^2+1}`$ and $`y=(\sum_{p\in P_n}p)/n`$, the selected parameters are $`K=\lfloor n/1308\rfloor`$ and $`D=y/1370`$. A finite repeated-target construction produces row and column prime lists with the exact pool total. Repeated target values are allowed; repeated entries are not.
- **One coupled calculation for every larger order.** The final proof checks prime-supply scales, all reservations, floors and ceilings, centering, target size, and correction capacity together. Pointwise estimates and monotone envelopes establish persistence throughout the infinite tail.

The [optimized composition](optimized-bound.md) supplies the exact dependency graph. Its most direct supporting arguments are the [constant-window analytic estimates](optimized/cutoff_constant_window_analytic.md), [constant-window controller](optimized/cutoff_constant_window_controller.md), [degree-10 graph](optimized/cutoff_degree10_graph.md), [seed and target-modulus refinement](optimized/cutoff_seed_density_refinement.md), and [finite target lemma](optimized/cutoff_target_optimization.md). Earlier quantitative lemmas remain linked where they supply a proof dependency; their historical numerical profiles are not substituted into the final theorem without checking their hypotheses.


