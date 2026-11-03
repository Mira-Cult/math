# Irreducible quadratic-polynomial arrays in every dimension

This is a polynomial analogue of [Sude's prime-array problem](../README.md). Instead of arranging an initial segment of odd primes, arrange a prescribed initial segment of irreducible integer quadratics. In every dimension at least two, all sufficiently large side lengths admit an arrangement whose full signed-coordinate line sums are irreducible over the rationals. Unlike the integer-prime problem, both even and odd side lengths are allowed.

The result includes explicit bounds. It is a conventional proof with exact numerical controls and internal nonauthor review, not a Lean theorem or a claim of external referee acceptance.

## Exact pool and geometry

Consider all polynomials

```math
f(X)=aX^2+bX+c\in\mathbb Z[X],\qquad a>0,
```

which are primitive (the three coefficients have greatest common divisor one) and irreducible over $`\mathbb Q`$. Order them by increasing height $`H(f)=\max\{a,|b|,|c|\}`$, breaking ties by the ascending lexicographic tuple $`(c,b,a)`$. This is one fixed ordering, including its potentially incomplete final height shell. Representatives are never rescaled.

For dimension $`D\ge2`$ and side length $`n`$, take exactly the first $`n^D`$ polynomials in this list. Place each once in $`\{1,\ldots,n\}^D`$.

A required line is parametrized by $`t=1,\ldots,n`$: each coordinate is either fixed, $`t`$, or $`n+1-t`$, and at least one coordinate varies. Identical cell sets are counted only once. Thus axes, diagonals in coordinate slices, and full body diagonals are all included. For $`n\ge2`$, their number is

```math
L_D(n)=\frac{(n+2)^D-n^D}{2}.
```

No wrapped lines, arbitrary slopes, section sums, or hyperplane sums are imposed. Different line sums may coincide.

## The theorem and sufficient bounds

**Theorem.** For every integer $`D\ge2`$ and every integer

```math
n\ge\max\{2^{120},\;2^{24}(D+1)^2\},
```

there is a bijective placement of the prescribed pool for which the sum on every required line is irreducible over $`\mathbb Q`$.

The proof supplies sharper bounds for particular dimensions:

| Dimension | Sufficient side length | Required lines |
|---:|---:|---|
| 2 | $`n\ge2^{120}`$ | Rows, columns, both main diagonals |
| 3 | $`n\ge2^{67}`$ | Axes, all coordinate-slice diagonals, body diagonals |
| 4 | $`n\ge2^{47}`$ | All full signed-coordinate lines |
| 5 | $`n\ge2^{37}`$ | All full signed-coordinate lines |
| 6 | $`n\ge2^{31}`$ | All full signed-coordinate lines |
| 10 | $`n\ge2^{21}`$ | All full signed-coordinate lines |
| 100 | $`n\ge2^{24}`$ | All full signed-coordinate lines |
| 1000 | $`n\ge2^{27}`$ | All full signed-coordinate lines |

Each entry covers **every** integer side length above its bound, of either parity, not just powers of two. These are sufficient thresholds, not asserted least thresholds. The nonmonotone table reflects competing terms in the estimates; it is not a classification of the true minimal orders.

## Why the proof works

**1. The exact input pool is dense in a coefficient box.** Let $`H`$ be the largest input height. Elementary counts bound reducible and nonprimitive quadratics and the entire unfinished boundary shell. At the certified heights, the canonical prefix occupies at least $`13/16`$ of the box. After the deletions needed for sampling, density remains at least $`4/5`$. The proof also estimates the actual coefficient means, rather than assuming uniformly distributed independent coefficients.

**2. Random line sums spread out.** A dense-fiber Fourier estimate controls the characteristic function of the remaining pool. A pairing construction represents uniform sampling without replacement using distinct pairs and independent endpoint choices. Sequential conditioning gives concentration and anti-concentration bounds both for an ordinary line and for a line conditioned to contain any specified input.

**3. Reducible sums are counted more economically.** The zero-constant case is treated separately. For other reducibles, concentration confines the lower coefficients to a narrow window while the positive leading coefficient is large. Rational roots must consequently be small. Counting the possible linear factors in that window gives a stronger bound than counting every reducible quadratic in a large box.

**4. The permutation local lemma makes all lines work together.** The array is a random bijection, so line events are not independent. The proof uses a negative-dependency theorem for random injections and explicitly pays for conflicts through both shared cells and shared polynomial values. It bounds the probability of a bad line even after specifying one of its entries. A uniform upper bound for the number of required lines through a cell is

```math
r_D=\frac{3^D-1}{2}.
```

The local-lemma budget is $`8nr_D\beta\le1`$, where $`\beta`$ bounds those conditional bad-line probabilities. This replaces a crude union bound over all $`L_D(n)`$ lines.

**5. Exact inequalities prove complete tails.** Six integer/rational comparisons certify each listed exponent. Monotonicity then proves the inequalities at every larger side length, including incomplete height shells. A separate argument proves the displayed bound uniformly in dimension.

Higher dimension supplies a much larger coefficient pool for a line of the same length: its height grows on the scale of $`n^{D/3}`$. This helps the anti-concentration estimates, while the incidence cost $`r_D`$ grows with dimension. The theorem balances both effects; it does not assume that adding dimensions is free.

## What the theorem does not say

The **inputs** are primitive integer quadratics. Their **sums** need only be irreducible over $`\mathbb Q`$, and may have a common coefficient divisor. For example, multiplying a rationally irreducible polynomial by two preserves irreducibility over $`\mathbb Q`$ but makes it nonprimitive over $`\mathbb Z`$. The proof does not establish prime-element sums in $`\mathbb Z[X]`$.

It also does not provide an efficient constructor. Exhaustive search makes the existence statement effective, but the bounds are enormous. Higher polynomial degrees, complete fixed-finite-field analogues, and full integer-prime arrays in every higher dimension remain separate questions.

## Proofs, imports, and verification

- [Complete improved proof and exact cutoff conditions](sources/transfer.md), especially PQ1–PQ4 and PQ-C/PQ-U.
- [Canonical-pool estimates and original quadratic proof](sources/characteristic_zero.md).
- [Permutation local-lemma bridge](sources/permutation_bridge.md), including cell and value conflicts.
- [Independent review of the improved theorem](sources/review.md).
- [Exact numerical controls](code/).

The non-elementary probability input is Lu and Székely, *Using Lovász Local Lemma in the Space of Random Injections*, Electronic Journal of Combinatorics **14** (2007), R63, Theorem 1 and Lemma 3 ([author PDF](https://people.math.sc.edu/lu/papers/randinj.pdf)). Primitive factorization uses Gauss's lemma; see Milne, *A Primer of Commutative Algebra*, §4 ([author PDF](https://www.jmilne.org/math/xnotes/CA.pdf)). The remaining displayed estimates are proved in the accompanying manuscripts. No conjecture about primes or polynomial tuples is assumed.

The controls reproduce the sufficient thresholds and test supporting finite calculations. They do not replace the mathematical proof, materialize arrays at the displayed thresholds, or establish optimality.
