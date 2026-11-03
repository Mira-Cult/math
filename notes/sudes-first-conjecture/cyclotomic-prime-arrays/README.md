# Prime squares and cubes in every fixed cyclotomic field

*A generalization of Sude's First Conjecture · 3 November 2026*

**Every fixed nontrivial cyclotomic field admits prescribed prime-element squares and full signed-line cubes at every sufficiently large admissible order.** There is no bound on the field degree and no class-number-one assumption. The arithmetic field is fixed; this is a theorem in spatial dimensions two and three, not in every spatial dimension.

## The theorem

Fix an integer m≥3 and K=Q(ζ_m). Reduce the conductor to c=m/2 when m≡2 modulo 4, and otherwise c=m. There is a field-dependent threshold N_m such that the exact first n² or n³ canonical unramified prime elements can be placed bijectively in a square or cube, respectively, with every required line sum prime:

- If c is a power of two, every odd n≥N_m works. Every even n≥2 is impossible.
- If c is not a power of two, every integer n≥N_m works, including even orders.
- A square includes all 2n+2 rows, columns and main diagonals.
- A cube includes all 3n²+6n+4 full signed-coordinate lines: axis-parallel lines, both diagonals of every coordinate-parallel square slice, and the four body diagonals.

“Signed” describes the directions of a line, not subtraction: each sum adds its n entries with coefficient +1. Each prescribed entry is used exactly once, without replacement, omission or later unit rescaling. Line sums may repeat and need not be canonical representatives. The construction can choose unramified targets, but the definition of a successful finite array permits any prime-element targets.

The threshold is **ineffective**, not merely unevaluated, because the analytic input uses an ineffective Siegel estimate. It may depend on m. No growing-conductor statement, efficient asymptotic construction, classification of all small orders, or numerical cutoff is claimed.

## Exactly which primes?

An element is prime here when its principal ideal is a nonzero prime ideal. Irreducibility alone is insufficient in a ring with nontrivial class group. Each principal prime ideal not lying over a rational prime dividing c contributes one canonical generator. Nonprincipal prime ideals have no prime-element generators and do not contribute. All principal higher-residue-degree primes are retained, not only split rational primes.

For the extended family, the previously fixed balanced-log normalizations at c=5,8,12 are retained. Their complete definition and tie rules are in [the original normalization manuscript](manuscripts/normalization_local.md) and [model specification](PROBLEM.md).

For every other c≥3, choose a generator by minimizing its full Minkowski trace energy over **all** unit associates:

```math
E(\alpha)=\tfrac12\mathrm{Tr}_{K/\mathbb Q}(\alpha\overline\alpha)
=\sum_{j=1}^{\varphi(c)/2}|\sigma_j(\alpha)|^2.
```

Among the energy minimizers, restrict the first complex embedding to the half-open sector −π/w≤arg(σ₁(α))<π/w, where w=c for even c and w=2c for odd c. Break remaining ties by the lexicographically least integral coefficient tuple in the power basis 1,ζ_c,…,ζ_c^(φ(c)−1). Order the resulting representatives by absolute norm, then by that coefficient tuple. Take the exact initial n^D elements, including a possibly incomplete final norm tie. The [whole-unit normalization proof](manuscripts/general_normalization_local.md) proves this is effective, complete and unambiguous; it does not assume a convenient subgroup generates every unit.

The general proof also works for the energy normalization at c=5,8,12, but those are different pools from the frozen balanced-log examples. No equivalence of normalizations is asserted. The rational endpoints m=1,2 are separate: retaining 2 makes every n≥2 impossible; omitting 2 recovers the original odd-prime problem.

## How the proof works

1. **Normalize whole unit classes exactly.** Trace-energy ellipsoids turn comparison with every unit associate into a finite exact problem. The canonical domain has a bounded regular shape, and exact norm prefixes have a controlled mean. Principal-prime density retains the factor 1/h_K.
2. **Obtain enough prime pairs and compatible targets.** Fixed-field prime distribution and linear-pattern theorems supply prime elements in suitable boxes and exact-total prime targets. Centered endpoint geometry handles conjugate coordinates whose mean vanishes. Every local prime-ideal factor is checked; norm-two primes account for the power-of-two parity restriction.
3. **Realize the targets with one permutation.** Disjoint reversible trades and integer tensor corrections adjust every required line while preserving the pool. The physical controller tracks arbitrary fixed arithmetic rank and uses the previously proved square/cube incidence geometry. Its rounding remainder is O(n), rather than an arithmetic-degree-dependent power of n.

The complete composition and each of these arguments are published, not replaced by this outline:

| Obligation | Complete proof |
|---|---|
| Statement and end-to-end composition | [Theorem CYC](manuscripts/general_composition.md) |
| Canonical elements, full unit group, local obstructions | [GN1–GN4](manuscripts/general_normalization_local.md) |
| Prime distribution, representative geometry, prime patterns and targets | [General analytic proof](manuscripts/general_analytic.md) |
| Arbitrary fixed arithmetic rank, trades and exact corrections | [General physical controller](manuscripts/general_controller.md) |
| Retained quartic pools and theorem | [Quartic composition](manuscripts/composition.md), [normalization](manuscripts/normalization_local.md), [analytic proof](manuscripts/analytic.md), [controller and integer tensor correction](manuscripts/controller.md) |

### Public inherited dependencies and external imports

The inherited spatial arguments are available without access to a research repository:

- [Signed cube geometry](../prime-cube.md), [integral signed incidence](../cube/signed_incidence.md), [physical signed trades](../cube/signed_trades.md), [cube controller](../cube/cube_controller.md), and [tensor-expander incidence](../cube/incidence.md). Their [source map](../cube/source-map.json) pins the ordinary scientific source a2445962ec6e06b2a893980fb7a183057eb9bcee.
- [Scalar square support](../explicit-controller.md), especially §3, from c2118dfad1aeb660d66308dc6a94d6c959f5010c.
- [Quadratic vector controller](../quadratic-prime-arrays/manuscripts/vector_controller.md) and [local arithmetic and even-order extension](../quadratic-prime-arrays/manuscripts/local_arithmetic.md), with the [quadratic source map](../quadratic-prime-arrays/source-map.json) binding e6e581efb9b676a7d5bc88b91c01571b087ed5da.

Named external inputs remain imports: Wataru Kai's [Notes on Mitsui's Prime Number Theorem with Siegel zeros, v3](https://arxiv.org/abs/2209.11816v3), Theorem 3.1.1, and [Linear patterns of prime elements in number fields, v5](https://arxiv.org/abs/2306.16983v5), Theorems 6.1 and 12.1 with Remarks 12.2–12.4. Standard number-field and full-unit-group facts are identified in [References](REFERENCES.md), including Milne's Algebraic Number Theory notes. The analytic manuscript checks fixed-field/basis hypotheses, coefficient growth, finite cokernels, local factors and enclosing-volume errors; this publication does not claim to reprove the imported theorems.

## A genuine small-order obstruction

For every a≥1, in Q(ζ_(3^a)), a full signed-line cube of order three is impossible when all entries are unramified prime elements in the specified first sector. The obstruction does not require distinctness or an initial-prime-pool assumption. Reduction to F₃ gives a two-coloring problem on the 3×3×3 cube; an exact finite certificate shows that a required line must be monochromatic. The arithmetic proof additionally rules out the exceptional possibility that its sum is an associate of the ramified prime. Omitting this last step would not prove impossibility.

See the [complete ternary obstruction](manuscripts/ternary_cube_obstruction.md), [independent finite checker](code/check_ternary_cube_obstruction.py), and [proof-tree certificate](inputs/ternary_cube3_unsat.json). For K=Q(ζ₉), order four has a positive exact certificate: the first 64 energy-normalized elements, with all 76 required sums prime. This next-order example is asserted for K₉ only, not every 3-power conductor.

## Verification, provenance and reproduction

This is a **conventional proof with internal nonauthor reviews and exact finite controls**, not an end-to-end kernel-checked proof or external referee acceptance. The three general review records disclose their authorship exclusions: [analytic/local](reviews/general-analytic-local-review.md), [normalization/controller](reviews/general-normalization-controller-review.md), and [composition](reviews/general-composition-review.md). The [supplemental review](reviews/ternary-obstruction-review.md) covers the ternary obstruction.

The scientific source is d9bd9ac92851a9996c14dd2fdf49f1879bcae97b; the supplemental source is 3fe1dfbcec2e2c500ac974081f0f5eda8b9e344d; the publication was assembled from delivery 763d1486f3289654d36a00f6423a8a7600c75257. [Source map](source-map.json) records SHA-256 hashes of exact originals and public reading copies. [Original source files](originals/) preserve the scientific manuscripts and research/review metadata unchanged. Reading copies only adapt links and mathematical typesetting. [Publication checks](PUBLICATION-CHECKS.md) records what was rerun for this publication, separately from the source's recorded checks and repository CI.

All code and inputs are public. From this directory run, using Python 3.12 and its standard library:

```sh
python -B code/check_energy_certificate.py --negative-controls inputs/energy_*.json
python -B code/check_certificate.py --negative-controls inputs/m*_square*.json inputs/m*_cube*.json
python -B code/check_ternary_cube_obstruction.py --negative-controls --independent-search inputs/ternary_cube3_unsat.json
python -B code/replay_ternary_cube_tree.py --negative-controls inputs/ternary_cube3_unsat.json
python -B code/tensor_rounding_check.py
python -B code/vector_fixture.py verify inputs/physical_*.json --negative-controls
python -B code/local_audit.py verify inputs/local_ledger.json --negative-controls
python -B code/general_unit_certificates.py --output /tmp/general_unit_subgroups.json
cmp /tmp/general_unit_subgroups.json inputs/general_unit_subgroups.json
```

The finite energy-array producer supports c=7,9,15,16. It is not an efficient implementation for every field. Its finite examples and mutation tests support, but do not replace, the asymptotic proof. Original source-root command paths in [code instructions](code/README.md) should be read relative to this directory for the public package.
