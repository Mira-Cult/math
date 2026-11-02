# Sude's First Conjecture

*Mira-Cult research note · 2 November 2026*

Can the first $n^2$ odd primes be placed in an $n\times n$ square so that
all row sums, column sums and both main diagonal sums are prime?
Sude's First Conjecture says yes for every positive odd $n$. This note records
our proof for **every sufficiently large odd $n$**, together with its full
combinatorial and analytic components. It does not yet prove the assertion
for every positive odd order.

## The conjecture

Let $p_j$ be the $j$-th prime, with $p_1=2$, and set

$$
P_n=\{p_2,p_3,\ldots,p_{n^2+1}\}.
$$

**Sude's First Conjecture.** For every positive odd integer $n$, there is an
$n\times n$ array containing every element of $P_n$ exactly once such that
every row, every column and each of the two main diagonals has a prime sum.

The pool is prescribed: it is exactly the first $n^2$ odd primes, beginning
with 3. No entry can be omitted, repeated or replaced. The **line sums** need
not be equal, need not be distinct, and may equal an entry. There is no extra
requirement that the sum of all entries be prime.

The odd-order restriction is necessary. For even $n\ge2$, each line sum is
an even integer greater than 2 and therefore composite. At $n=1$, the square
$[3]$ works; the row, column and both diagonal labels all refer to that same
single entry.

## A small example

At order three the prescribed entries are
$3,5,7,11,13,17,19,23,29$. One successful square is

|  |  |  | Row sum |
|---:|---:|---:|---:|
| 7 | 5 | 19 | **31** |
| 13 | 11 | 29 | **53** |
| 17 | 3 | 23 | **43** |
| **37** | **19** | **71** | Column sums |

The two diagonal sums are $7+11+23=41$ and $19+11+17=47$.
All eight required sums are prime. Exact order-three examples predate this
note; see the [example reference](REFERENCES.md#order-three-example).

## What is proved

**Eventual-existence theorem.** There is an integer $n_0$ such that every odd
$n\ge n_0$ satisfies Sude's First Conjecture.

The theorem uses the exact initial pool for each order. It is not restricted
to a subsequence of successful orders, and it does not extend one small square
inductively. The construction is carried out afresh inside each prescribed
pool.

The proof is an **internally reviewed conventional mathematical research
proof**, presented here for public scrutiny. Internal reviews found no
remaining blocking mathematical gap in the controller, prime-target lemmas or
their composition. This is not a claim of formal verification, external peer
acceptance or novelty. The source revisions and review boundary are recorded
in [PROVENANCE.md](PROVENANCE.md).

No numerical value of $n_0$ is supplied. Consequently the theorem alone does
not settle every positive odd order: it leaves an unspecified finite range.
A finite list of successful examples cannot bridge that range without a
certified threshold. Deriving one would require explicit bounds throughout
the analytic estimates and the construction, not merely choosing a very large
number.

## How the proof works

The difficulty is to meet many coupled conditions without changing the entries.
Changing a cell affects its row and column, and sometimes a diagonal. The
proof first builds a sparse collection of reversible moves that control the
line sums, then chooses prime sums within the range those moves can reach.

### 1. Reserve switches inside the prescribed pool

If two primes $p,p+d$ occupy one column in different rows, exchanging them
transfers $d$ between those two row sums while leaving the column sum unchanged.
A transposed pair transfers between columns while preserving rows. Using
pairwise disjoint entries makes these switches commute.

A quantitative consequence of Maynard's sieve supplies many disjoint prime
pairs with one common even gap $g\le600$ at **every sufficiently large scale**.
This is the starting point for bundles whose subset sums contain every multiple
of $g$ in a long interval. Further pairs enlarge those intervals, while their
midpoints are chosen to keep the reserved entries balanced.

Bounded-degree networks organize the row and column transfers. An integral
flow argument realizes all balanced correction vectors of the needed size;
the exact-total dependency between rows, and separately between columns, is
built into that argument. Four-cell rectangle trades control each diagonal
without changing any row or column. The supports of these controls are
embedded disjointly.

### 2. Obtain a centered baseline with usable residues

Write $X=p_{n^2+1}$, $T=\sum_{p\in P_n}p$, $\mu=T/n$ and
$K=\lceil n^{2/3}\rceil$. After reserving the controls, place the unused
entries by a permutation chosen to balance all required lines. Sampling
without replacement gives a simultaneous concentration bound. Separate
bounded-size switches repair the residues, making every line sum coprime to
$g$.

The resulting [controller theorem](controller.md#u-the-centered-universal-controller)
has a baseline within $KX/10$ of $\mu$. It can reach every integer target
within $KX/2$ of its baseline coordinate, provided each target has the same
residue modulo $g$ and each of the row and column target vectors sums exactly
to $T$.

### 3. Choose prime targets with the exact total

The [analytic component](prime-targets.md) derives a prescribed-residue
version of the Matomäki–Maynard–Shao theorem on three almost-equal primes.
The modulus is fixed; prime powers in it and the costs of residue filtering
are treated explicitly.

To choose $n$ prime row targets, select primes just above or below $\mu$ in
the required classes, always correcting the current discrepancy. This keeps
the cumulative discrepancy bounded independently of $n$. Finish the last
three targets with the ternary theorem, obtaining **exactly** the total $T$.
Repeat for columns and choose the two diagonal targets individually.
All target primes lie within $\mu^{3/5}$ of $\mu$.

These targets fit inside the controller's range. Applying the switches gives
a permutation of the original entries with every required line sum prime.
The [synthesis proof](proof.md#proof-of-theorem-p) checks the capacities,
congruences, exact totals and eventual quantifier.

## Reading the full argument

- [Proof of eventual existence](proof.md): the theorem and its composition.
- [Centered controller](controller.md): complete seed-supply, transfer,
  placement, residue-repair and centering arguments.
- [Nearby prime targets with an exact total](prime-targets.md): the analytic
  source contract and complete proofs of A1–A4.
- [References](REFERENCES.md): primary sources, versions and theorem locators.
- [Provenance](PROVENANCE.md): source pins and the limits of internal review.
