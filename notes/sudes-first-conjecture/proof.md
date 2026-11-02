# Proof of eventual existence

**Theorem P.** There is an integer $n_0$ such that, for every odd integer
$n\ge n_0$, the first $n^2$ odd primes can be arranged in an $n\times n$
square whose rows, columns and two main diagonals all have prime sums.
Each prescribed entry is used once. The line sums need not be equal or distinct.

This is an internally reviewed conventional research proof, presented for
public scrutiny. No explicit $n_0$, formal verification, external peer
acceptance or novelty claim is asserted. The stronger assertion for every
positive odd $n$ is [Sude's First Conjecture](README.md#the-conjecture).

Write $p_j$ for the $j$-th prime, including $p_1=2$, and put
$P_n=\{p_2,\ldots,p_{n^2+1}\}$. The proof combines two components:

1. [The centered controller](controller.md) constructs disjoint switches
   inside the exact pool. It realizes a box of integer row, column and
   diagonal targets with specified residues and exact row and column totals.
2. [The prime-target theorem](prime-targets.md) supplies primes in that box,
   with those individual residues and exact totals. Its threshold is uniform
   in the number of targets.

The full component proofs, not only their statements, are included in the
linked files. All analytic systems used have fixed complexity; the growing
array is handled by the finite construction and balancing arguments below.

## Proof of Theorem P

Put

$$
 X=p_{n^2+1},\qquad T=\sum_{p\in P_n}p,\qquad
 \mu=T/n,\qquad K=\lceil n^{2/3}\rceil.
$$

The prime number theorem and partial summation give

$$
 X\sim2n^2\log n,\qquad T\sim n^4\log n,\qquad
 \mu\sim n^3\log n.
$$

Fix $\theta=3/5$. In particular,

$$
 \mu^{3/5}/X
 \asymp n^{-1/5}(\log n)^{-2/5}\longrightarrow0.       \tag{P1}
$$

For all sufficiently large odd $n$, apply [Theorem U](controller.md#u-the-centered-universal-controller) to the exact pool
$P_n$. It gives an even integer $g$, with $2\le g\le600$, and
a baseline permutation having row sums $A_i$, column sums $B_j$,
and diagonal sums $D_+,D_-$. Each baseline sum is a unit modulo $g$
and lies within $KX/10$ of $\mu$. The baseline is an actual
permutation, so

$$
 \sum_i A_i=\sum_j B_j=T.                            \tag{P2}
$$

Apply [A3](prime-targets.md#a3-prime-vectors-with-exact-total-uniformly-in-their-length) with $q=g$, $k=n$, total $T$, and the residue vector
$(A_i\bmod g)_{i=1}^n$. Its hypotheses hold: the classes are reduced,
their sum is $T\pmod g$ by (P2), and $\mu$ eventually exceeds
the required threshold. Thus there are primes $a_i$ satisfying

$$
 a_i\equiv A_i\pmod g,\qquad
 \sum_i a_i=T,\qquad |a_i-\mu|\le\mu^{3/5}.
$$

Independently apply A3 to the column residues. It gives primes $b_j$
with $b_j\equiv B_j\pmod g$, $\sum_jb_j=T$, and
$|b_j-\mu|\le\mu^{3/5}$. Apply the [bracketing statement A2](prime-targets.md#a2-bracketing-primes-in-every-requested-class) to
each of $D_+,D_-\pmod g$, choosing a prime $d_+,d_-$ within
$\mu^{3/5}$ of $\mu$ in its respective class. All these target
primes are positive. Repetitions among them are permitted by the problem.

There are only 300 possible even moduli $g\le600$. A3's threshold
is independent of the vector length $k$, and the maximum of the finitely
many thresholds in A2 and A3 is finite. The fact that the selected $g$
may change with $n$ therefore causes no subsequence restriction.

The capacity comparison can be checked without an additional asymptotic
threshold. Since $\mu\le nX$, $X\ge n^2$ and $K\ge n^{2/3}$,

$$
 \frac{\mu^{3/5}}{KX}
 \le \frac{n^{3/5}}{KX^{2/5}}
 \le n^{-13/15}<\frac25 \qquad(n\ge3).
$$

The last inequality follows from $3^{13}>(5/2)^{15}$ and monotonicity.
Thus every target coordinate satisfies

$$
 |a_i-A_i|,\ |b_j-B_j|,\ |d_\pm-D_\pm|
 \le KX/10+\mu^{3/5}<KX/2. \tag{P3}
$$

The differences are integer multiples
of $g$; the row and column target totals are exactly $T$. These
are precisely the hypotheses of Theorem U. Apply its simultaneous target
assertion to obtain a permutation of exactly $P_n$ with line sums
$a_i,b_j,d_+,d_-$, all prime. This proves Theorem P. $\square$

The quantifier is every sufficiently large odd integer, not an unbounded
subsequence. No inductive extension of one square to a larger square is used;
the construction is performed directly inside each full initial pool.

## Quantifiers and imported results

All constants are fixed before increasing $n$: the 105-tuple, the gap
bound 600, the graph degree 64, the midpoint width $\delta=10^{-7}$,
and the target exponent $3/5$. The modulus and reduced class selected
from the seed supply vary only over finite sets. Every supply and placement
inequality holds eventually for each member of those finite sets, so one
threshold handles all choices. The scale separations used are

$$
 n\log^2X=o(X^{3/4}),\quad nK=o(n^2),\quad
 \log^2X=o(K),\quad\sqrt{n\log n}=o(K),\quad
 \mu^{3/5}=o(X).
$$

The two non-elementary imports beyond the fixed-progression prime number
theorem are pinned in [REFERENCES.md](REFERENCES.md):

- Maynard, *Small gaps between primes*, arXiv:1311.4600v3,
  Propositions 4.1 and 4.3, the proof of Proposition 4.2, and (5.9).
  The quantitative seed consequence is proved in [controller Lemma S](controller.md#s-a-supply-of-common-bounded-gaps-for-every-sufficiently-large-pool).
- Matomäki, Maynard and Shao, *Vinogradov's theorem with almost equal
  summands*, arXiv:1610.02017v2, Theorem 2.1, Proposition 3.1, its proof
  on printed pages 5–6, and Section 5. The additional fixed-class conclusion
  is proved in [A1](prime-targets.md#a1-almost-equal-ternary-primes-in-prescribed-fixed-classes), with all bounded filtering costs recorded.


## Scope of the conclusion

The argument is unconditional: its analytic inputs are the published results
specified above, with the needed extensions proved in the component files.
It is an existence proof and supplies neither a numerical threshold nor a
practical running-time guarantee for constructing large examples. Establishing
a particular numerical threshold would require explicit bounds for every
analytic supply and target-selection threshold, as well as the placement and
centering conditions. The elementary estimate (P3) alone does not supply one.

In particular, this theorem does not settle the finitely many odd orders below
its unspecified threshold and therefore does not prove the full conjecture.
See the [main note](README.md) for the exact statement, an example and a guide
to the proof, and [provenance](PROVENANCE.md) for the source revisions.
