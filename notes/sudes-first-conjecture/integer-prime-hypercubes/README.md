# Prime hypercubes in every fixed dimension

*Part of the [Sude's First Conjecture collection](../README.md). Published 3 November 2026.*

## The theorem

**For every fixed integer k ≥ 2, there is a threshold N(k) such that every odd n ≥ N(k) admits a bijective placement of exactly the first n^k odd primes in an n-by-…-by-n hypercube, with a prime sum on every full signed-coordinate line.**

Every prescribed prime is used exactly once. Line sums may repeat. The theorem is qualitative: no numerical value of N(k) is evaluated here, and the analytic argument may be ineffective. It does not prove the statement for every small odd n, for dimension growing with n, or for face, section or hyperplane sums.

These are full-length lines: in centered coordinates I = {−m,…,m}, n = 2m+1, select any nonempty set A of varying coordinates, give each a sign, and let those coordinates equal ±t for t in I; fix all other coordinates. Reverse orientations name the same line. Thus axes, both diagonals of every coordinate-parallel square slice, and all higher-dimensional main diagonals are included. Shifted shorter diagonals and arbitrary slopes are not included.

For n ≥ 3 there are

```math
L_k(n)=\sum_{r=1}^k\binom{k}{r}2^{r-1}n^{k-r}
=\frac{(n+2)^k-n^k}{2}
```

such lines. This gives 2n+2 for squares, 3n²+6n+4 for cubes, and 4n³+12n²+16n+8 in dimension four. Even n ≥ 2 is impossible: every line would sum an even number of odd primes to an even integer greater than two.

## Complete proof and reading order

Start with **[Theorem FP and the complete physical composition](sources/manuscripts/hyperk_full.md)**. The proof separates compatible prime target sums from actual permutation of the exact prime pool. An integer lift alone is not an array of primes.

1. **[Integer compatibility](sources/manuscripts/hyperk_incidence.md).** The signed-line incidence image is exactly characterized by partition identities; it is saturated, and compatible odd targets have odd lifts.
2. **[Compatible prime targets](sources/manuscripts/hyperk_targets.md).** Weighted finite target lists produce prime values with all compatibility identities and the exact pool total. The [finite list lemma FL](sources/manuscripts/explicit_prime_targets.md) is included in full; its distribution hypotheses are supplied by the stated analytic import, not assumed without explanation.
3. **[Pure selectors](sources/manuscripts/hyperk_kernel_research.md)** and **[axis controller](sources/manuscripts/hyperk_controller.md)** give the local switch language and axis correction hierarchy.
4. **[Uniform real frame UF](sources/manuscripts/hyperk_full_controller.md)** is chosen before the demand, has bounded supports and logarithmic point degree, and achieves a subpolynomial coefficient loss.
5. **[Integral absorber AF](sources/manuscripts/hyperk_reconstruction_alt.md)** and **[bounded-load integral kernel BK](sources/manuscripts/hyperk_distributed_kernel.md)** round that fixed real frame, absorb the small remainder integrally, and provide generation over composite residue rings.
6. **[Fresh prime resources and centering](sources/manuscripts/hyperk_resources.md)** pay for distinct endpoints, whole-bundle concentration and the changed mean of the unused pool.
7. **[Full composition FC → FP](sources/manuscripts/hyperk_full.md)** packs disjoint physical switches, pays the amplification of shared traces with replicas, repairs residues, and closes one dimension-dependent finite resource ladder.

The notable all-dimensional step is not extrapolating finite experiments. The proof gives algebraic resource margins for every fixed k and handles the increasingly complicated shared intersections of signed-line families. Its constants and depth depend on k; n then tends to infinity.

## External imports and inherited sources

- **Thorner–Zaman**, *Refinements to the prime number theorem for arithmetic progressions*, [arXiv:2108.10878v2](https://arxiv.org/pdf/2108.10878v2), Theorem 1.1, Remark 1.2, equation (1.6), and the short-interval consequence in §1.2. The required polylogarithmic-modulus windows and exponent slack are checked in [targets §4](sources/manuscripts/hyperk_targets.md#4-one-dimensional-prime-inputs) and [resources](sources/manuscripts/hyperk_resources.md). Exceptional-zero ineffectivity is retained.
- **Tropp**, *User-Friendly Tail Bounds for Sums of Random Matrices*, Theorem 1.6, [primary preprint](https://tropp.caltech.edu/papers/Tro11-User-Friendly-preprint.pdf), published in *Foundations of Computational Mathematics* 12 (2012), 389–434. The rectangular matrix Bernstein hypotheses, variance parameters and uniformity are verified in the UF manuscript.
- Standard prime number theorem, elementary integral max-flow/min-cut, and bounded-variable concentration. The relevant finite estimates and uses are displayed in the included proofs; these are mathematical imports, not kernel-checked dependencies.
- The bounded-degree graph existence proof used by the controllers is publicly available as [controller Lemma F1](../controller.md#f-independent-row-and-column-controls). The inherited [tensor-expander proof](sources/manuscripts/incidence.md), [cube controller](sources/manuscripts/cube_controller.md), [local prime-counting consequence](sources/manuscripts/cube_targets.md), and [four-dimensional controller](sources/manuscripts/hyper4_axis.md) are also included.

No access to the private research repository is needed to read the proof or run the listed checks. References in frozen originals to historical research revisions are provenance, not additional inaccessible proof assumptions.

## Review and verification status

The final scientific package has completed internal nonauthor component reviews of [UF](sources/reviews/hyperk_uniform_frame_review.md), [AF/BK](sources/reviews/hyperk_absorber_review.md), and [full composition](sources/reviews/hyperk_full_composition_review.md). The composition review reports no outstanding named mathematical obligation for this qualitative fixed-dimension theorem, relying on the separately reviewed components.

This is conventional mathematical proof with internal review and finite executable controls, **not an end-to-end proof-kernel verification or external referee acceptance**. The uniform-frame review's control program imports the frozen author's selector helper; the absorber and full-composition controls do not import author code. No blanket independence claim is made for every test.

The public replay checks scientific source hashes before running the unmodified controls. The full-composition replay checks 6,674 signature equations, 20 compatible splits, 249 residue calculations, 20,160 exhaustive packing injections, fixtures through dimension six, and 14 negative controls. These finite checks test implementations and examples, not the asymptotic theorem itself. No full higher-dimensional prime-array witness certificate is claimed by this package. The exact delivery's remote CI was skipped, not passed.

## Reproduce

From a checkout of this public repository:

```sh
python3 -B notes/sudes-first-conjecture/integer-prime-hypercubes/replay.py
```

Python 3.12 and the standard library suffice for the listed replays. The wrapper verifies [SHA256SUMS.json](SHA256SUMS.json), creates a temporary source-layout copy for the archived programs, and invokes the unmodified author full-composition self-test and the three final review controls. It needs neither private Git history nor network access.

The [provenance note](PROVENANCE.md) explains frozen scientific bytes and presentation copies. Earlier partial results and their historical limitations remain in the archive; the final FP composition, not an older partial-result status paragraph, states the current theorem.
