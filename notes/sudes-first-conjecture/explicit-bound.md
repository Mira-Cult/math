# Explicit bound for Sude's First Conjecture

Define the exact integer
$$
\boxed{N_0=2^{2^{40}}=2^{1099511627776}.} \tag{F0}
$$

**Explicit-threshold theorem.** For every odd integer $n\ge N_0$, the
first $n^2$ odd primes admit an $n\times n$ arrangement whose rows,
columns and both main diagonals all have prime sums. Each prescribed entry
occurs exactly once. The line sums may repeat.

This is a **proposed unconditional conventional proof**, using the stated
classical Rosser–Schoenfeld, Bennett–Martin–O'Bryant–Rechnitzer and McCurley
imports. The supporting local proofs are included below and in this note's
linked components. Internal review is not formal verification or external
peer acceptance; see [Provenance](PROVENANCE.md). The finitely many odd
orders below $N_0$ remain unresolved by this theorem.

The explicit construction uses a logarithmically growing seed gap, a
quantified controller, and a repeated-target reservoir. It is a separate
quantitative composition, not a numerical substitution into the
[original qualitative proof](proof.md).

## 1. Parameters and proof dependencies

Write

$$
 X=p_{n^2+1},\quad P_n=\{p_2,\ldots,p_{n^2+1}\},\quad
 T=\sum_{p\in P_n}p,\quad m=T/n^2,\quad y=\mu=T/n,
$$
$$
 E=\lceil\log_2X\rceil,\qquad e=\lceil\log_2y\rceil,
 \qquad K=\lfloor n/E^3\rfloor,\qquad D=y/e^4.
                                                               \tag{F1}
$$

Here $e$ is an integer parameter, not Euler's number. Analytic logarithms
are natural. The exact pool is defined in [the main note](README.md#the-conjecture).

| Obligation | Fixed numerical choice or bound | Canonical proof |
|---|---|---|
| Index and entry mean | $n^2\le X<n^3$, $2X/5<m<3X/5$ | [M0.1–M0.2](classical-primes.md#elementary-size-and-mean-bounds), RS62; starts n>=64, X>=2^256 |
| All-scale disjoint seeds | $\lfloor X/(2048E^3)\rfloor$, some even $g\le16E$ and common reduced class | [E1](classical-primes.md#e1-a-numerical-all-scale-seed-supply-from-consecutive-primes), X>=2^32 |
| Strong progression windows | $q\le32\lceil\log_2Y\rceil$, length at least $Y/(\log Y)^5$, count at least $H/(2\varphi(q)\log(2Y))$ | [S40-S](classical-primes.md), every Y>=N_0 |
| Weak progression windows | $q\le(\log Y)^3$, same length, count at least $H/(2\varphi(q)(\log Y)^6\log(2Y))$ | [S40-W](classical-primes.md), every Y>=N_0 |
| Strong source parameters | $Z=8,\kappa_1=1,\kappa_2=\kappa_3=2^{20}$ | BMOR Proposition 6.16, all conditions evaluated in S40 |
| Endpoint logarithms | $\log x>2^{39}$ for $x\in[Y/2,2Y]$ | S40.3, including the lower endpoint |
| Controller domain | $n\ge2^{2^{40}}, E\ge2^{40}, n\ge E^{204}$ | [PC3](explicit-controller.md#6-a-fully-evaluated-controller-regime-pc3) and Section 2 |
| Macro half-width | $\delta=1/10^7$ | Unchanged FC/PC3 |
| Remaining counts | $M=\lfloor X/(128E^2)\rfloor$, $H_c=\lfloor X/(640000000E^2)\rfloor$ | PC3, after charging the entire reserved pool |
| Prefix and reserved entries | $P\le5120E^3$, $B=(128n+8)(P+7K)+4(n+1)(g/2-1)$ | [FC](explicit-controller.md), PC3 |
| Whole depletion | $E^2B/n^2\le696384/E^{199}+952/E<1/640000000$ | PC3 for E>=2^40 |
| Exact target-list domain | $n\ge54000e^{11}$, $D\ge2^{20}e^{11}$, $D\le y/4$ | [Finite target lemma](explicit-targets.md) and Section 4 |
| Final order cutoff | $\max\{N_{\rm PC3},Y_{\rm S40-W},Y_{\rm S40-S}\}=2^{2^{40}}$ | Sections 2--5 |

All finite inequalities in the ledger are evaluated in these linked proofs.
No unknown constant or unevaluated analytic threshold occurs in the cutoff.

~~~mermaid
flowchart TD
  RS["RS62 prime bounds"] --> Seed["All-scale matching and pool mean"]
  Classical["BMOR and primitive explicit formula"] --> AP["S40 progression windows"]
  Seed --> Control["FC and PC3 controller"]
  AP --> Control
  AP --> Targets["Exact prime target lists"]
  Control --> Square["Every odd n at least 2^(2^40)"]
  Targets --> Square
~~~

## 2. Uniform domain for every larger order

Fix any odd integer $n\ge N_0$. The index and mean bounds apply: their
finite starting points are dominated by (F0). Set $v=\log_2n$. Then
$v\ge2^{40}$, and

$$
 2v\le E\le3v+1\le4v.                                  \tag{F2}
$$

At $v_0=2^{40}$, $v_0>204\cdot42$, so
$2^{v_0}>(4v_0)^{204}$. The logarithmic derivative of
$2^v/(4v)^{204}$ is $\log2-204/v>2/3-204/v>0$
throughout this tail. Therefore

$$
 n\ge E^{204},\qquad E\ge2^{40}.                        \tag{F3}
$$

Since $X<y\le nX\le X^{3/2}$, ceilings give

$$
 E\le e\le2E.                                          \tag{F4}
$$

The actual analytic scales are $X$, $y$, and the entry-reservoir
centers $Y_-=m-X/4$, $Y_+=m+X/4$. The mean bounds imply

$$
 X/8<3X/20<Y_-<Y_+<17X/20<X.
$$

Thus each scale is at least $n$, since $X/8\ge n^2/8\ge n$.
S40 applies uniformly to every one of them and every permitted modulus;
there is no silently fixed choice of $g$. For each such scale, with
$u=\log Y$,

$$
 u>2^{39},\qquad
 \log(Y/2)\ge(2^{40}-1)\log2
 >\tfrac23(2^{40}-1)>2^{39}.                            \tag{F5}
$$

The same lower bound persists for all larger orders and scales.

## 3. All controller supplies after complete depletion

E1 supplies the seed matching with some even $2\le g\le16E$ and a
common reduced lower-endpoint class $a\pmod g$. Every endpoint is an
odd prime at most $X$, so it is in the required pool.

Apply S40-S at scale $X$ to $(X/2,X]$. Its length condition holds
because $(\log X)^5\ge2$. As $\log(2X)\le E$ for $E\ge3$,
every reduced class modulo $g$ has at least

$$
 \frac{X}{4\varphi(g)\log(2X)}\ge\frac{X}{64E^2}         \tag{F6}
$$

entries available before reservations.

For the two macro intervals

$$
 I_\pm=[m\pm X/4-\delta X,m\pm X/4+\delta X],
 \qquad \delta=10^{-7},                                \tag{F7}
$$

use scale $Y_\pm$. Both intervals lie in $(1,X)$ and in
$[Y_\pm/2,2Y_\pm]$. Their length $2\delta X$ is at least
$Y_\pm/(\log Y_\pm)^5$, since $(2^{39})^5>5000000$.
The modulus fits because

$$
 \lceil\log_2Y_\pm\rceil\ge E-3,
 \qquad 16E\le32(E-3) \quad(E\ge6).
$$

Using the weaker convenient bound $\log(2Y_\pm)\le2E$, each reduced
class in either macro interval contains at least

$$
 \frac{2\delta X}{2\varphi(g)\log(2Y_\pm)}
 \ge\frac{X}{320000000E^2}.                            \tag{F8}
$$

This supplies all the selected classes $a,-1,1$, including coincidences
between them. Counts in overlapping classes are not added as independent
stocks: PC3 subtracts the entire global reservation cap $B$ from every
raw supply before every selection. Its remaining counts are exactly the
$M,H_c$ in the ledger. The complete bounds on seeds, fresh equal-gap
pairs, extension steps, bandwidth, rectangle placement, prefix load and
diagonal supplies therefore apply as stated.

In particular, [FC](explicit-controller.md) yields a baseline square whose
required line sums are units modulo $g$ and within $KX/10$ of $y$.
It realizes every compatible row and column target vector with exact
totals $T$, and independently any two diagonal targets, provided their
individual displacements from the baseline are at most $KX/2$.

All finite existence choices have explicit search specifications. For example,
FC enumerates 32-tuples of permutations to find its two degree-at-most-64
expansion graphs; the proved union bound makes this finite search terminate.
Its completion uses all remaining pool entries. No efficient running time is
claimed or needed for this existence theorem.

## 4. Exact prime target vectors of length n

Use the baseline row residues and, separately, column residues modulo $g$.
They are units and each vector sums to $T\pmod g$, because each family
partitions the exact pool. The finite target lemma preserves this actual
integer total, not a rounded or approximate one.

Its numerical size hypotheses hold throughout the tail. From (F3)--(F4),

$$
 \frac{n}{e^{11}}\ge\frac{E^{193}}{2^{11}}\ge54000.
                                                               \tag{F9}
$$

Also $y>(2/5)nX\ge(2/5)n^3$, so

$$
 D=\frac{y}{e^4}\ge\frac{(2/5)n^3}{16E^4}
 \ge2^{20}e^{11},                                     \tag{F10}
$$

where it suffices that $(2/5)E^{597}\ge2^{35}$, already true at
$E=2^{40}$. These are increasing positive-power comparisons. Clearly
$D\le y/4$ because $e^4\ge4$.

For the prime supplies needed by the target lemma put $u=\log y$.
The elementary bounds $u\le e\le2u$, together with (F5), imply

$$
 D/500\ge y/u^5 \quad(u\ge8000),\qquad
 128e^2\le512u^2\le u^3 \quad(u\ge512).                \tag{F11}
$$

Thus S40-S supplies the lemma's strong count in every needed interval
and class modulo $g$, since $g\le16E\le16e$ and
$2\varphi(g)\log(2y)\le4ge$. S40-W supplies its weak count for every lifted
modulus $q\le128e^2$. Explicitly its denominator is no larger than
the allowed one:

$$
 2\varphi(q)u^6\log(2y)\le4qe^7\le4qe^9.              \tag{F12}
$$

The finite target lemma therefore gives $n$ prime row targets, all in
$[y-D,y+D]$, in their assigned classes and with exact sum $T$.
Apply it again to obtain the column targets with that same total. Its
repeated target primes do not consume pool entries; they specify line sums.
The number of controlled target coordinates is bounded by $3332e^{10}$,
and the hypothesis (F9) was proved uniformly for the actual length $n$.

For each diagonal residue, the strong count in a central interval of length
$D$ is positive, supplying a prime diagonal target in the same window.
The two targets are chosen independently and need not be distinct.

## 5. Final transfer and all-tail conclusion

The floor defining $K$ retains at least half of $n/E^3$, since
$n\ge E^{204}\ge2E^3$. Hence

$$
 \frac{D}{KX}
 \le\frac{nX/E^4}{(n/(2E^3))X}
 =\frac2E<\frac1{10}.                                 \tag{F13}
$$

Each desired prime target is within $D<KX/10$ of $y$; each baseline
sum is within $KX/10$ of $y$. The combined correction is therefore
less than $KX/5<KX/2$, inside FC's transfer box. The row and column
targets satisfy both exact-total constraints. FC's independent diagonal
trades meet the two remaining targets while preserving rows and columns.

Every operation permutes reserved entries, and every unused entry was placed
in the completion. The final array therefore uses exactly $P_n$, once
each, with all $2n+2$ required sums prime. No subsequence, alternative
pool, replacement entries, distinct-sum condition or proper prime powers
enter the conclusion. Sections 2--4 prove every comparison for all larger
orders by explicit monotonicity or signed powers. This proves the theorem.


## 6. What the bound does and does not certify

The bound is a sufficient existence threshold, not an optimized threshold,
an efficient algorithm, or a verification of all smaller odd orders. The
symbolic integer $2^{2^{40}}$ need not be expanded in decimal. Sections 2–5,
the numerical controller regime, and the progression proofs include the
endpoint and monotonicity arguments for **every larger order**, rather than
only a calculation at one enormous value.

The source record includes exact-arithmetic checks of the displayed finite
comparisons, but those checks are not substituted for any mathematical
argument or imported analytic theorem here. This public exposition supplies
the proof in readable form and does not distribute or claim a standalone
machine-checkable certificate. Its review boundary is recorded in
[Provenance](PROVENANCE.md).
