# Sude's First Conjecture

*Mira-Cult research note · 2 November 2026*

Can the first $`n^2`$ odd primes be placed in an $`n\times n`$ square so that
all row sums, column sums and both main diagonal sums are prime?
Sude's First Conjecture says yes for every positive odd $`n`$. This note records
a proposed unconditional proof for **every odd $`n\ge2^{2^{40}}`$**, together
with its supporting combinatorial and analytic arguments. It does not yet
prove the assertion for every positive odd order.

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

## What is proved

**Explicit-threshold theorem.** Every odd integer



```math
\boxed{n\ge N_0=2^{2^{40}}=2^{1099511627776}}
```



satisfies Sude's First Conjecture.

The theorem applies to **every** odd order at or above the bound, not merely
a subsequence. The construction is performed afresh inside each exact initial
pool. The bound is sufficient, not claimed optimal or practically usable.
The finitely many odd orders below $`N_0`$ remain unresolved by this theorem;
known small examples do not close that range.

This is a **proposed unconditional conventional mathematical proof**, using
the stated classical prime-distribution estimates. Its source has undergone
internal reviews by reviewers other than the component authors. Internal
review and arithmetic checks are not formal verification or external peer
acceptance. No novelty claim is made. See [Provenance](PROVENANCE.md) for
the pinned sources and precise review boundary.

## How the explicit proof works

The difficulty is to meet many coupled conditions without changing the entries.
Changing one cell affects its row and column, and sometimes a diagonal.
The proof first reserves disjoint reversible moves, then chooses prime sums
within the range those moves can reach.

### 1. Find a numerical supply of switches

Write $`X=p_{n^2+1}`$ and $`E=\lceil\log_2X\rceil`$. Pair consecutive primes
inside $`[X/4,3X/4]`$. An elementary density and pigeonhole argument gives
at least $`\lfloor X/(2048E^3)\rfloor`$ disjoint pairs with a common even
gap $`g\le16E`$ and a common reduced lower-endpoint residue modulo $`g`$.
The gap may change with $`n`$, so the progression estimates are uniform in it.

[Classical explicit estimates](classical-primes.md) supply the additional
prime pairs needed to enlarge these switches. Their quantitative range is
checked at every scale used by the construction, including its shorter
entry-reservoir intervals.

### 2. Build a controller with all costs paid

With $`K=\lfloor n/E^3\rfloor`$ and
$`\mu=(\sum_{p\in P_n}p)/n`$, the [finite controller](explicit-controller.md)
produces a baseline whose required sums are units modulo $`g`$ and within
$`KX/10`$ of $`\mu`$. Bounded-degree networks transfer amounts between rows
or columns. Four-cell rectangle trades control each diagonal while preserving
all rows and columns. Separate switches repair the residues.

All supports use distinct pool entries. The proof pays the complete global
reservation cost before each prime-supply selection, as well as cell loads,
centering errors, integer floors and both diagonal families. The controller
can realize every compatible target vector within $`KX/2`$ of its baseline,
with row and column totals each exactly equal to the total of the pool.

### 3. Choose nearby prime sums with the exact total

Set $`\ell=\lceil\log_2\mu\rceil`$ and $`D=\mu/\ell^4`$.
The [finite target lemma](explicit-targets.md) constructs $`n`$ prime targets
in $`[\mu-D,\mu+D]`$, in their assigned residue classes, with the exact
required total. It uses repeated prime targets to build a complete interval
of attainable sums on an arithmetic grid; a balancing step then finishes
with an exact correction. Repetition is legal for line sums, not for entries.
Apply it separately to rows and columns and choose the two diagonal targets
independently.

The [composition proof](explicit-bound.md) checks that all supplies and
finite inequalities hold for every odd $`n\ge N_0`$. In particular,
$`D/(KX)\le2/E<1/10`$, so the prime targets fit inside the controller's range.
The final operations only permute the original $`n^2`$ primes.

## Reading the full argument

### Explicit bound

- [The bound and its complete composition](explicit-bound.md): theorem,
  dependency graph, numerical ledger and uniform-tail checks.
- [Classical prime supplies](classical-primes.md): pool size and mean,
  common-gap matching, the primitive-character explicit formula, and the
  specialized strong and weak progression estimates.
- [Finite controller and numerical regime](explicit-controller.md): complete
  transfer, placement, depletion, residue-repair and centering proofs.
- [Exact prime target lists](explicit-targets.md): complete finite target lemma.

### Original qualitative proof

The earlier [eventual-existence proof](proof.md),
[centered controller](controller.md) and
[nearby prime-target arguments](prime-targets.md) are retained as the original
qualitative proof. That argument did not compute a threshold. The explicit
supplement above changes the quantitative construction and supplies the new
bound; it is not merely a large number inserted into the earlier proof.

[References](REFERENCES.md) records primary sources, versions and locators.
[Provenance](PROVENANCE.md) records source revisions and the limits of review.
