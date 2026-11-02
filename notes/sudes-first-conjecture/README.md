# Sude's First Conjecture

*Mira-Cult research note · 2 November 2026*

Can the first $`n^2`$ odd primes be placed in an $`n\times n`$ square so that every row, column, and both main diagonals have prime sums?

The current proposed unconditional theorem answers yes for **every odd $`n\ge2^{4320}`$**. The full conjecture for every positive odd order is still open. This index preserves three stages of the proof as separate manuscripts, so that the qualitative argument and the initial explicit bound remain readable in their original form.

## Three manuscripts

1. **[I. Eventual existence](proof.md).** Every sufficiently large odd order works. This is the original qualitative argument: it constructs a placement but does not provide an effective numerical threshold. Supporting manuscripts: [centered controller](controller.md) and [prime targets with an exact total](prime-targets.md).
2. **[II. The initial published explicit bound](explicit-bound.md).** Every odd $`n\ge2^{2^{40}}`$ works. This separate quantitative proof replaces the ineffective analytic inputs and pays all construction costs. Supporting manuscripts: [classical prime supplies](classical-primes.md), [finite controller](explicit-controller.md), and [exact prime targets](explicit-targets.md). This manuscript is preserved as the initial public numerical result.
3. **[III. The optimized explicit bound](optimized-bound.md).** Every odd $`n\ge2^{4320}`$ works. The improvement changes the analytic estimates, reservoir allocation, graph degree, and target window together. Its full composition and linked supporting proofs are published here.

These are conventional mathematical arguments with internal review and exact arithmetic checks. They are not end-to-end proof-assistant formalizations or claims of external peer acceptance. [Provenance](PROVENANCE.md#optimized-bound) identifies the scientific snapshot, review scope, and verification limits; [References](REFERENCES.md) identifies the classical imports.

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

## Current theorem and remaining range

**Optimized-threshold theorem.** For every odd integer

```math
\boxed{n\ge2^{4320}},
```

there is a bijective placement of exactly the first $`n^2`$ odd primes in an $`n\times n`$ square for which all $`2n+2`$ required line sums are prime.

The theorem covers the entire odd-order tail, not a subsequence. The line sums may repeat. The bound is sufficient and is not claimed optimal. There are finitely many smaller odd orders, but the remaining range is far beyond naive exhaustive checking; isolated examples do not settle it.

## How the optimized proof works

The proof reserves disjoint reversible moves inside the prescribed pool, chooses compatible nearby prime sums, and uses the moves to attain those targets without replacing or repeating any entry.

- **Uniform prime supplies.** A density and matching argument finds many disjoint pairs with one common even gap. Explicit arithmetic-progression estimates supply the additional primes at each actual scale. The analysis keeps the sign of a possible exceptional-zero contribution, retains the constants in the original zero-sum integrals, and proves the domain needed for their use.
- **Cheaper disjoint reservoirs.** Delicate residue and prefix gadgets are reserved first. Wider reservoirs then use all reduced residue classes, with every deletion charged against the aggregate remaining stock. Reflected interval bins keep pair midpoints close to the pool mean even though the supply bands are wide.
- **Lower-degree routing.** A degree-10 multigraph still supports the full integral row and column correction range. The reduced degree lowers reservation, placement, and centering costs. Independent rectangle trades handle both diagonals while preserving the row and column sums.
- **A constant relative target window.** With $`X=p_{n^2+1}`$ and $`y=(\sum_{p\in P_n}p)/n`$, the selected parameters are $`K=\lfloor n/1308\rfloor`$ and $`D=y/1370`$. A finite repeated-target construction produces row and column prime lists with the exact pool total. Repeated target values are allowed; repeated entries are not.
- **One coupled calculation for every larger order.** The final proof checks prime-supply scales, all reservations, floors and ceilings, centering, target size, and correction capacity together. Pointwise estimates and monotone envelopes establish persistence throughout the infinite tail.

The [optimized composition](optimized-bound.md) supplies the exact dependency graph. Its most direct supporting arguments are the [constant-window analytic estimates](optimized/cutoff_constant_window_analytic.md), [constant-window controller](optimized/cutoff_constant_window_controller.md), [degree-10 graph](optimized/cutoff_degree10_graph.md), [seed and target-modulus refinement](optimized/cutoff_seed_density_refinement.md), and [finite target lemma](optimized/cutoff_target_optimization.md). Earlier quantitative lemmas remain linked where they supply a proof dependency; their historical numerical profiles are not substituted into the final theorem without checking their hypotheses.
