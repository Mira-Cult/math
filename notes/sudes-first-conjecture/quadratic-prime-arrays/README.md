# Gaussian and Eisenstein prime squares and cubes

*Mira-Cult research note · 2 November 2026*

Arrange a prescribed initial segment of prime elements into a square or cube,
using every element exactly once. Can every full row, column, and diagonal
have a prime-element sum?

**The proposed unconditional conventional theorem answers yes for every
sufficiently large odd Gaussian order, and for every sufficiently large
Eisenstein order—both parities, including multiples of three.** The proof gives
no evaluated cutoff: its thresholds are ineffective. It does not assert that
every small order works.

The Eisenstein contrast is real, not a change of input convention. Order-six
Eisenstein squares already work, whereas orders two and four do not; full
Eisenstein cubes of orders two and three do not work. All of these use the
same canonical pool. The eventual theorem is a conventional research proof
with internal mathematical review, not a kernel-checked theorem or a claim of
external peer acceptance or novelty. [Provenance](PROVENANCE.md) distinguishes
proof, finite certificates, and review.

## The theorem

There are constants $`n_G,n_E`$ such that:

| Ring and shape | Orders covered | Required sums |
|---|---|---|
| Gaussian square | Every odd $`n\ge n_G`$ | All $`2n+2`$ rows, columns, and two diagonals |
| Gaussian cube | Every odd $`n\ge n_G`$ | All $`3n^2+6n+4`$ full signed-coordinate lines |
| Eisenstein square | Every integer $`n\ge n_E`$ | All $`2n+2`$ required lines |
| Eisenstein cube | Every integer $`n\ge n_E`$ | All $`3n^2+6n+4`$ required lines |

Every even Gaussian order $`n\ge2`$ is impossible. The singleton arrays work
in both rings. The line counts in the table apply to $`n\ge2`$; singleton line
labels deduplicate to one line.

For a cube the line family consists of all $`3n^2`$ axis lines, the two
long diagonals in each coordinate-parallel square slice ($`6n`$ lines), and
the four body diagonals. “Signed” describes coordinate directions, **not
negative coefficients in a sum**. Every line sums its $`n`$ entries positively.
There is no requirement that an entire square section have prime sum, nor
that different line sums be distinct. No entries may be repeated or replaced.

## Exactly which primes?

Let $`\omega^2+\omega+1=0`$ with $`\mathrm{Im}\,\omega\gt0`$.

- **Gaussian:** $`a+bi\in\mathbb Z[i]`$, in the sector $`a\gt0,b\ge0`$.
  The norm is $`a^2+b^2`$. Omit the associate class of $`1+i`$.
- **Eisenstein:** $`a+b\omega\in\mathbb Z[\omega]`$, in the sector
  $`a\gt b\ge0`$. The norm is $`a^2-ab+b^2`$. Omit the associate class of
  $`1-\omega`$.

Retain one representative of each remaining prime-element associate class,
with conjugate classes kept separately. **Include inert rational primes:**
3 is a Gaussian prime element of norm 9, while 2 and 5 are Eisenstein prime
elements of norms 4 and 25. Prime element does not mean prime norm.

Sort by the lexicographic key $`(N(z),a,b)`$, and take **exactly the first
$`n^2`$ or $`n^3`$ elements**. An initial segment can stop partway through a
conjugate norm tie. No post-selection rotations or conjugations are allowed.
[The frozen problem specification](PROBLEM.md) gives the complete conventions.

## Why Eisenstein orders behave differently

In the Gaussian ring every allowed element has residue 1 modulo $`1+i`$.
An even-length line sum is therefore divisible by $`1+i`$; its positive real
part rules out a ramified prime associate. Thus every even order fails.

In the Eisenstein ring reduction modulo $`1-\omega`$ has three residue classes.
Allowed entries have residues $`+1`$ or $`-1`$. A line containing $`k`$ plus
entries has residue $`2k-n\pmod3`$. This imposes a genuine coloring constraint,
but not an eventual parity or divisibility-by-three restriction.

The proof uses the **actual counts** in the canonical pool, including inert
primes and the final incomplete norm tie. For the sufficiently large theorem,
local arithmetic, compatible prime targets, and a physical permutation
controller all have to work together. A local square-coloring lemma starts at
$`n\ge40`$; **40 is not a cutoff for prime squares or cubes**.

Changing to “primary” representatives all in one ramified residue class would
be a different problem and would destroy this particular comparison.

## Small exact examples

A Gaussian order-three square is

```math
\begin{pmatrix}
2+5i&2+3i&3\\
1+2i&1+4i&5+2i\\
2+i&4+i&3+2i
\end{pmatrix}.
```

Its row sums are $`7+8i,7+8i,9+4i`$; column sums are
$`5+8i,7+8i,11+4i`$; diagonal sums are $`6+11i,6+5i`$.
Their norms, in that order, are $`113,113,97,89,113,137,157,61`$,
all rational primes. [Exact certificate](inputs/gaussian_square3.json).

An Eisenstein order-three square is

```math
\begin{pmatrix}
5&6+\omega&2\\
3+\omega&4+3\omega&5+3\omega\\
3+2\omega&4+\omega&5+2\omega
\end{pmatrix}.
```

Its row sums are $`13+\omega,12+7\omega,12+5\omega`$; columns are
$`11+3\omega,14+5\omega,12+5\omega`$; diagonals are
$`14+5\omega,9+5\omega`$. Their norms are
$`157,109,109,97,151,109,151,61`$, all rational primes.
The prescribed pool includes $`6+\omega`$ but not $`6+5\omega`$ at the
norm-31 tie. [Exact certificate](inputs/eisenstein_square3.json).

### Finite successes and obstructions

| Ring | Verified square orders | Verified cube orders |
|---|---|---|
| Gaussian | 1, 3, 5 | 1, 3 |
| Eisenstein | 1, 3, 5, **6** | 1 |

The [order-six Eisenstein square](inputs/eisenstein_square6.json) simultaneously
demonstrates an even order and an order divisible by three. No nontrivial
positive Eisenstein cube example is claimed by this finite certificate packet.

The Eisenstein square obstructions at orders two and four have complete
residue proof trees. For the order-three cube the stronger statement holds:
**every two-coloring of its 27 cells has a monochromatic full signed line**.
Such a three-entry line has zero ramified residue. The certificate checks all
49 required lines and needs no prescribed total color count. Order-two cubes
fail because every pair of distinct vertices is a required line and the
prescribed pool contains both residue classes: an opposite-color pair has
zero ramified residue. These are proofs of
impossibility, not failed searches. See [local arithmetic](manuscripts/local_arithmetic.md).

## Complete proof manuscripts

1. **[Architecture and comparison with ordinary primes](manuscripts/ordinary_architecture.md).**
   What transfers from the rational-prime square/cube proof, and what must be replaced.
2. **[Canonical pools, local obstructions, and compatibility](manuscripts/local_arithmetic.md).**
   Exact associate conventions, inert entries, residue counts, local square construction,
   cube integer-image conditions, and the even-order extension.
3. **[Analytic prime inputs and exact-total targets](manuscripts/analytic_inputs.md).**
   Prime elements in small boxes and residue classes; retained exceptional-zero terms;
   a fixed three-form completion rather than a growing prime-pattern system;
   actual repeated-gap pairs and their supplies.
4. **[Physical rank-two controller and Theorem QPA](manuscripts/vector_controller.md).**
   Two independent actual gap directions, a finite multiscale prefix, centered
   reservoirs, joint deletion budget, and a permutation attaining compatible targets.

The controller must move whole prime elements: separate scalar adjustments to
real and imaginary coordinates would not preserve the prescribed pool. Its
additive correction lattice need not be an ideal. A multiscale prefix and a
centered zonotope provide a physically attainable correction region rather
than merely a formal lattice span.

The complete public mathematical dependency chain includes the earlier
[ordinary-prime squares and cubes](../README.md).
The [references](REFERENCES.md) name the external analytic theorems. The
Eisenstein all-order conclusion uses the local manuscript's even-order
compatibility extension and the controller's even-order physical geometry;
it does not follow from the initial odd-order cube interface alone.

## Reproduce the finite evidence

The [code guide](code/README.md) gives all commands. Python 3.11 or later and
only the standard library are required. From this repository's root:

```sh
python3 -B notes/sudes-first-conjecture/quadratic-prime-arrays/code/check_certificate.py --negative-controls notes/sudes-first-conjecture/quadratic-prime-arrays/inputs/gaussian_*.json notes/sudes-first-conjecture/quadratic-prime-arrays/inputs/eisenstein_*.json
python3 -B notes/sudes-first-conjecture/quadratic-prime-arrays/code/local_audit.py --self-test
python3 -B notes/sudes-first-conjecture/quadratic-prime-arrays/code/vector_trade_fixture.py verify notes/sudes-first-conjecture/quadratic-prime-arrays/inputs/vector_trade_*.json --negative-controls
```

The first checker independently reconstructs each pool, line family, sums,
and prime-element tests without importing the producer. The physical-trade
fixtures have a separate verifier and are **not all-prime cube certificates**.
Finite replay does not establish the eventual analytic or controller bounds.
The Python programs and intentional JSON inputs are published unchanged;
[the source map](source-map.json) binds their bytes and the adapted manuscripts.

## What remains open here

An explicit numerical threshold, complete finite exception sets, efficient
large-instance construction, and proof-assistant formalization remain open.
This note makes no claim for growing dimension, Gaussian even orders,
arbitrary slopes, or sums of higher-dimensional sections.
