# Resolution of Sude’s First Conjecture

## Statement and status

**Theorem.** For every positive odd integer **n**, the first **n² odd primes** admit a bijective placement in an n-by-n square such that every row sum, every column sum, and both main diagonal sums are prime. Different line sums are allowed to coincide.

Here “first odd primes” means 3, 5, 7, 11, …, excluding 2. Every member of the prescribed initial segment occurs exactly once. The assertion is not a magic-square equal-sum condition, does not permit replacing the input primes, and is not restricted to a subsequence of odd orders.

This is a **conventional computer-assisted proof**, comprising a fully specified finite certificate and a classical analytic/combinatorial tail theorem. It has received internal nonauthor review, and the supplied packet has been independently replayed. It is not a Lean theorem, an end-to-end kernel verification, or a claim of external referee acceptance. The analytic imports are explicitly identified below; their published finite zero verifications are imports, not computations reproduced here.

The smallest cutoff in the all-positive-odd formulation is consequently **1**. The constructive tail starts at **2001**, and a separate exact certificate covers every smaller positive odd order. Even orders n ≥ 2 are impossible: each line is a sum of an even number of odd primes and is therefore an even integer greater than 2.

This exposition is a guide to the complete proof, not a replacement for its component lemmas. The [pinned source and certificate composition](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/sude_all_odd_theorem.md) identifies those proofs, the exact data, all required checkers, and the review records in the pinned research tree. Historical component manuscripts retain the status statements written when they were produced; the [final composition review](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/reviews/sude-all-odd-independent-review.md) records the later acceptance of the precise combined revision.

## 1. Proof of the theorem

Let n be a positive odd integer.

1. If n ≤ 1999, use the finite certificate described in §2. It provides and verifies a complete witness for each of the 1,000 consecutive odd orders 1, 3, …, 1999.
2. If n ≥ 2001, use the complete tail theorem described in §§3–5. Its conclusion has exactly the same input pool and required lines.

There is no positive odd integer strictly between 1999 and 2001. These cases are exhaustive, so they prove the theorem. No assertion for a missing order is inferred from examples, random-search success rates, or continuity in n. The two components do not assume one another.

For n = 1 the witness is simply [3]. The row, column, and two diagonal labels all have sum 3.

The canonical version of this argument is [AO1–AO5](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/sude_all_odd_theorem.md). Its substantive obligations are the finite verification and the tail construction, spelled out next.

## 2. Actual witnesses for all odd orders below 2001

### 2.1 What is stored

The [compressed certificate file](certificates/odd-orders-1-1999.bin.gz) is a lossless representation of all 1,000 squares. It contains the information needed to reconstruct the actual entries, not merely claimed line sums or hashes of missing matrices.

| Property | Value |
|---|---:|
| Compressed certificate size | 10,500,031 bytes |
| Uncompressed certificate size | 13,522,748 bytes |
| Number of recorded swaps | 1,686,341 |
| Cells checked across all squares | 1,333,333,000 |
| Labelled line sums checked | 2,002,000 |
| Largest input prime | 67,796,177 |
| Largest observed line sum | 68,630,847,793 |

Its compressed SHA-256 is

`5f8be996b548afac76e276088da5a094e3ff4375075ecea14aec77c71522b27c`.

The uncompressed SHA-256 is

`c8f41eb90f2a2d6d08428b5eb1d86cb373abf38467996920d9470e75045a40fd`.

The storage format begins with `SUDEFR01` and the endpoints and count of the covered orders. Each order has a seed and a list of swaps of row-major cell indices. Starting from ranks 0 through n²−1, a specified 64-bit integer shuffle and those swaps produce the final rank permutation. Rank 0 means 3, rank 1 means 5, and so on. The complete byte layout, arithmetic, shuffle, count bounds and swap conventions appear in [FR2](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_finite_remainder_squares.md#fr2-complete-binary-and-permutation-specification).

A seed is not taken on faith as a successful construction. The checker reconstructs the square, including the complete recorded repair sequence. No statistical quality of the shuffle is used in the proof.

### 2.2 Why verification proves the finite assertion

The [standalone C++ checker](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/code/cutoff2_finite_remainder_squares_verify.cpp) is separate from the search generator. Its proof obligations are elementary:

- An Eratosthenes sieve enumerates the exact prime pool. Every composite has a prime divisor at most its square root, so the sieve marks every composite and no prime. The implementation checks that enough primes were produced.
- Shuffling and swapping are permutations. The checker additionally checks every rank for range and uniqueness.
- Row, column, and both diagonal sums are recomputed from the completed square. Recorded search sums are not trusted.
- Primality is decided by the complete sieve where available, and otherwise by trial division through all possible prime divisors up to the square root. The trial-prime range is checked to be sufficient. No probable-prime acceptance is used.
- The records must be exactly the consecutive odd orders from 1 through 1999, with no missing, duplicated or trailing record.

Every line sum is less than 1999 × 67,796,177, hence less than 2³⁷; the checker’s 64-bit accumulation cannot overflow on a valid input. Index and count bounds are also checked. The gzip wrapper verifies both hashes and sizes and rejects extra members, truncation and excessive expansion.

The [finite manuscript, FR1–FR5](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_finite_remainder_squares.md) proves this verification logic and documents negative controls, including two squares with exactly one failing main diagonal. Successful search is not an assumption: the supplied witnesses, once checked, establish existence regardless of how they were discovered.

## 3. How the tail construction works

For a fixed odd order n, let p_j denote the j-th prime including p₁ = 2, and put

```math
X=p_{n^2+1},\qquad T=\sum_{j=2}^{n^2+1}p_j,
\qquad m=T/n^2,\qquad y=T/n.
```

Thus X is the largest allowed entry, m the mean entry, and y the mean row sum. The construction does not freely choose its entries: all reservations, completions and corrections use the same prescribed pool.

The proof separates five tasks.

**Prime targets with exact totals.** Choose n prime row targets adding to T and n prime column targets adding to T, all close to y. Choose prime targets for the two diagonals as well. Equality of the two axis totals is essential for the later flow correction. For orders 2001–19483, exact finite data supply primes q, p, r such that

```math
(n-2)q+p+r=T,
```

with every target within X/1000 of y. Use this n-term list for both axes and q for both diagonals. Larger bands use the proved parity-target and dense-seed constructions with explicit progression counts, rather than assuming a Goldbach-type conjecture.

**Reserve disjoint correction controls.** Selected pairs of allowed primes have prescribed differences. Their placements in small rectangles give changes to selected row or column sums while preserving the other axis. Separate diagonal controls handle the two diagonal targets. The geometric packing lemmas guarantee disjoint cells and account for the shared central cell. The prime-supply estimates count actual unused primes after all prior reservations; they do not reuse one reservoir as several independent supplies.

**Build a complete correction grid.** Small initial differences supply an interval of attainable integer corrections. Bridge stages extend that interval, and wider stages produce the needed final capacity. In the lowest band, explicit prime pairs have differences 2, 4, …, 2ᴾ. Their subset sums cover every even value through 2ᴾ⁺¹−2. Later appended differences are bounded by the existing coverage, preserving a complete even grid. Because n is odd, all line sums and prime targets are odd, so their discrepancies are even.

**Complete the permutation while controlling its sums.** The remaining unused entries fill all unreserved cells. Central diagonal preassignment, a regular factor of the row-column incidence graph, and balancing estimates keep the completed line sums within the correction ranges. All entries are retained; completion does not discard an inconvenient prime. In the lowest band the exact unused mean and actual central stocks are used, rather than a guessed mean for an asymptotic distribution.

**Route the remaining discrepancies.** Degree-six correction graphs with proven expansion provide enough cut capacity. Since the axis targets have total T, the demands sum to zero. Integral flow routes the row and column corrections, and the reserved controls realize those integer flows. The independent diagonal corrections preserve the already repaired axes and the other required lines. The controller inequalities ensure that every requested correction fits its actual capacity.

These are mathematical construction lemmas. Checking their numerical hypotheses is not a substitute for their proofs. The complete lowest-band specialization is [FC2K](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_controller_finite2001.md), with its explicit dependencies: [prefix balancing](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_prefix_balance_experiment.md), [rectangle packing](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_rectangle_packing.md), [cyclic centering](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_cyclic_residue_centering.md), [bridge balancing](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_bridge_balance.md), [wide balancing](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_wide_balance_experiment.md), and [central completion](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_central_completion.md).

## 4. Exhaustive tail partition

The following rows partition all odd orders from 2001 onward. Endpoints in finite rows are the first and last *odd* orders; adjacent rows differ by two.

| Odd orders | Construction |
|---|---|
| 2001–19483 | [FC2K: exact finite prefix and target data](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_controller_finite2001.md) |
| 19485–27553 | [FW: far-wide controller](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_controller_far_wide.md) |
| 27555–35733 | [EW: early-wide controller](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_controller_early_wide.md) |
| 35735–38967 | [NC: narrowest controller](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_controller_narrowest.md) |
| 38969–46339 | [SC: stratified controller](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_controller_stratified.md) |
| 46341–55107 | [GP: gap-profile controller](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_controller_gap_profiles.md) |
| 55109–65535 | [CF: regular-factor controller](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_controller_factor.md) |
| 65537–92681 | [WC: wheel controller](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_controller_wheel.md) |
| 92683–262143 | [BCM: bounded controller](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_controller_bounded.md) |
| 262145–311743 | [MC18: multiclass controller](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_controller_multiclass.md) |
| Every odd n ≥ 311745 | [Complete classical continuation](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_lower_campaign_theorem.md) |

The [complete tail theorem, T2001.1–T2001.6](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_tail2001_theorem.md), specifies the exact inequalities defining these bands and each band’s target provider. Integer-power comparisons establish the boundary conversions. Floors and ceilings are bounded pointwise, or evaluated for every actual order; no smooth estimate is differentiated through an unexamined rounding jump.

FC2K checks all 8,742 consecutive odd orders from 2001 through 19483. Its [target table](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_finite_target_table.md) uses exact prime-prefix sums and recursive Lucas primality certificates. Its [prefix families](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_finite_prefix_family.md) are explicit finite prime-pair populations. These checks establish hypotheses of the construction, rather than storing 8,742 full squares.

The last row is a complete unbounded theorem with its inherited source closure, not an extrapolation from bounded experiments. The complete packet retains the earlier continuation proofs and their numerical certificates. The top-level source map requires them, and the default verifier executes the component certificates rather than merely checking the interval labels.

## 5. Explicit external imports

The following are classical, unconditional analytic inputs. Their use does **not** assume RH, quasi-RH, or an unproved prime-pattern conjecture. In particular, using a published verification of zeros up to a specified finite height does not assume anything about all higher zeros.

1. **Rosser–Schoenfeld, “Approximate formulas for some functions of prime numbers” (1962).** Prime-index and prime-count estimates are applied in their stated ranges to the actual pool size n²+1. See the [original paper](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf) and the local [pool-statistics proof](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_pool_statistics.md). The finite certificate below 2001 needs no such estimate: it counts its primes exactly.
2. **Bennett–Martin–O’Bryant–Rechnitzer, “Explicit bounds for primes in arithmetic progressions,” Illinois J. Math. 62 (2018), 427–532.** [Author-hosted paper](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf). The bounded entry estimates use Theorem 1.9 and definition (1.18), printed pp. 434–435. The low-zero route additionally uses the smoothed formula (Proposition 2.1), two-sided zero count (Definition 2.2 and Proposition 2.5), finite-height verification (Proposition 2.7), partial summation (Lemma 2.11), and the higher-zero region (Proposition 4.34). The exact conventions, primitive-conductor correction and domains are recorded in the [low-zero analytic component](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_analytic_low_zero_band.md). The published finite zero verification is an import, not newly rerun here.
3. **Montgomery–Vaughan, “The large sieve,” Mathematika 20 (1973), 119–134, Theorem 2, equation (1.10), printed p. 121.** [Original author-hosted paper](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf). The short-progression upper bound is used only in the prefix phases that invoke it, with its hypothesis that the interval length exceeds the modulus. Its exact specialization and role are in the [short-progression prefix proof](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_bruntitchmarsh_prefix.md).
4. **McCurley’s explicit Dirichlet-L-function estimates (1984), DOI 10.1090/S0025-5718-1984-0726004-6.** [Original paper](https://www.ams.org/mcom/1984-42-165/S0025-5718-1984-0726004-6/S0025-5718-1984-0726004-6.pdf). The preserved large-scale continuation uses the parameterized calculations, notably (3.34), (3.36), and the proofs of Lemmas 3.7–3.8, rather than extrapolating a bounded-modulus numerical corollary beyond its domain. See the [height-domain derivation](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff_relaxed_height_analytic.md) and [constant-window refinement](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff_constant_window_analytic.md).

Each analytic branch states its precise scale, modulus, character and interval hypotheses. The complete proof pays for exceptional-zero terms, primitive/imprimitive corrections and removal of prime powers. Entry-prime supply is evaluated near X; target-prime supply is evaluated near y. These different scales must not be interchanged.

The remaining ingredients are conventional finite arguments supplied in the packet: pair counting, disjoint matching and rectangle placement, balancing and completion, the graph expansion existence argument, integer flow, and exact primality verification. The final manifest, not this short reading list alone, identifies the full proof closure. Historical alternative approaches remain historical; their presence in a recoverable source archive does not make them assumptions of the selected classical route.

## 6. Reproduce the computational component

The actual finite witnesses and a standalone exact C++ checker are included in this public directory. From `notes/sudes-first-conjecture`, run:

```sh
gzip -dc certificates/odd-orders-1-1999.bin.gz > /tmp/sude-odd-orders.bin
c++ -O2 -std=c++20 certificates/verify_finite.cpp -o /tmp/sude-verify
/tmp/sude-verify /tmp/sude-odd-orders.bin 1999
```

The checker enumerates the exact prime pool, reconstructs every square, and checks all row, column and both diagonal sums using exact primality. It does not merely trust the listed seeds or checksums. The [full finite-verifier proof](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_finite_remainder_squares.md) specifies its algorithm and correctness argument.

For the complete tail and composition replay, obtain the pinned [research source tree](https://github.com/Mira-Cult/math-wip/tree/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc), then run from its root:

```sh
python3 -B problems/prime-line-sums/code/verify_sude_all_odd.py
```

Python 3 and a C++20 compiler are sufficient; the complete default replay uses standard libraries and compiles its numerical components. Its expected status is `PASS_ALL_POSITIVE_ODD_ORDERS_FINITE_CERTIFICATE`. The `--composition-only` option is explicitly weaker and does not replace a complete replay. This public exposition links the complete pinned proof source and imports; it does not duplicate every historical numerical input here.

An independently materialized standalone export of the same scientific closure passed all 579 member-hash audits, the full default verifier, the separately authored finite checker, the tail-composition oracle, and the final 26,974-control composition oracle. The finite checker processed 1,333,333,000 cells and 2,002,000 labelled lines. These checks support the conventional proof; no end-to-end kernel formalization of every dependency is claimed or required for this presentation.

## 7. Provenance and reading order

The all-odd scientific revision is `67647907ad0693631f42c169df61cbe46a13a3ff` in the research repository. The finite component is frozen at `5f9c86d1dd8b075547ad5041fb2ee64ebfc59ddf`; the complete 2001 tail at `48c93bc07d78223d7cec64d0bb1257f11c07c282`. These science pins are distinct from later packaging and review commits.

For a focused mathematical reading, use this order:

1. [All-odd composition](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/sude_all_odd_theorem.md).
2. [Finite certificates and verifier correctness](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_finite_remainder_squares.md).
3. [Complete 2001 tail and exact band/target map](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_tail2001_theorem.md).
4. [Lowest-band controller](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_controller_finite2001.md), then its named conventional components and the relevant analytic imports.
5. [Unbounded continuation](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/manuscripts/cutoff2_lower_campaign_theorem.md), following its links through the preserved full tail.
6. [Final independent composition review](https://github.com/Mira-Cult/math-wip/blob/965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc/problems/prime-line-sums/reviews/sude-all-odd-independent-review.md) and the component reviews linked there.

The pinned composition and review identify the scientific source closure. The separately replayed standalone export additionally carried a 579-member hash audit; that export is not duplicated in full here. The public certificate and checker are byte-identical copies from the reviewed closure. This exposition adds the statement, proof organization and reading map without modifying scientific inputs.
