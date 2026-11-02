# Logarithmic gain and a smaller paid controller

## Scope and precise dependence

This is an additive specialization of the unchanged finite controller
[FC](../explicit-controller.md). It replaces no baseline file and allocates no
permanent claim identifier. Its labels CG1--CG4 are local. Review of this
source must be recorded at its exact scientific revision; authorship and a
successful arithmetic run are not independent review.

The statements below are conventional finite implications with explicit prime
supply hypotheses. They are **not standalone prime-square cutoff theorems**.
The analytic producer must establish the indicated supplies at the actual
scales, and the target producer must establish exact-total prime vectors.
The coordinator's composition supplies those two separate arguments.

Use the exact pool and line family from [PROBLEM.md](../README.md), with


```math
X=p_{n^2+1},\quad T=\sum_{p\in P_n}p,\quad m=T/n^2,
 \quad y=T/n,\quad E=\lceil\log_2X\rceil,
 \quad e=\lceil\log_2y\rceil,\quad D=y/e^4.
```


The source freeze is scientific `c2118dfad1aeb660d66308dc6a94d6c959f5010c`,
delivery `38e1d98cd99eeddfb1f37ad3d140490418e632fc`.
FC's unchanged SHA-256 is
`f583772b0541407d92c3dd743b8849aa5fe51ad68b68e3ef9d54a0ce4b677dfd`.
The baseline parameter is $`K=\lfloor n/E^3\rfloor`$. CG4 explicitly
changes it to $`K=\lfloor2n/E^4\rfloor`$; the change is never silently
inserted into the old PC3 statement.

## 1. The lost prime-index logarithm

**CG1.** If $`X=p_{n^2+1}>\exp(3/2)`$, then


```math
\frac X{n^2}>\log X-\frac32
 >Q(E):=\frac{693E-2193}{1000}.                 \qquad\text{(CG1)}
```


The first inequality is the direct rearrangement of Rosser--Schoenfeld
(1962), Theorem 2, equation (3.4), printed p.69:
$`\pi(x)<x/(\log x-3/2)`$` for `$`x>\exp(3/2)`$.
Since $`\pi(X)=n^2+1`$, the extra 1 strengthens the bound.
For the second inequality, $`\log X>(E-1)\log2`$, including when
$`X`$ is a dyadic endpoint. Three positive terms of the elementary series
give


```math
\log2=2\sum_{j\ge0}\frac{1}{(2j+1)3^{2j+1}}
 >2\left(\frac13+\frac1{81}+\frac1{1215}\right)
 >\frac{693}{1000}.
```


The primary source was visually inspected at printed p.69, PDF page 6:
[RS62 original scanned paper](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf).
Its DOI is [10.1215/ijm/1255631807](https://doi.org/10.1215/ijm/1255631807).
The already-used RS62 Corollary 1, (3.6), would give the weaker bound
$`X/n^2>(E-1)\log2/1.25506`$. Thus the principal logarithmic gain
requires no modern prime-index theorem; the sharper denominator comes from
the same primary page. The program checks the rational consequences, not
the proof or computational inputs of RS62.

## 2. A common finite envelope

Let $`p\ge32`$ be even and suppose


```math
n\ge E^p,\quad n^2\le X\le n^3,
 \quad 2X/5<m<3X/5.                              \qquad\text{(CG2)}
```


Take a positive integer $`A>24`$`, put `$`\delta=1/A`$, and set


```math
M=\left\lfloor\frac{X}{128E^2}\right\rfloor,
 \qquad H=\left\lfloor\frac{X}{64AE^2}\right\rfloor.
                                                        \qquad\text{(CG3)}
```


There are two reservoir choices, both permitted by the arbitrary-integer-K
statement of FC:

| Regime | $`K`$` | Upper bound | Lower bound, when `$`n/E^k\ge2`$ |
|---|---|---|---|
| Preserved K | $`\lfloor n/E^3\rfloor`$` | `$`n/E^3`$` | `$`n/(2E^3)`$ |
| Smaller paid K | $`\lfloor2n/E^4\rfloor`$` | `$`2n/E^4`$` | `$`3n/(2E^4)`$ |

Write the upper coefficient and power as $`c,k`$, and the lower
coefficient as $`b`$`: respectively `$`(c,k,b)=(1,3,1/2)`$ or
$`(2,4,3/2)`$. In the second case the stronger floor estimate follows
from $`\lfloor2w\rfloor\ge2w-1\ge3w/2`$` for `$`w\ge2`$.
It is necessary for the final target fit; merely retaining half is insufficient.

Assume a reduced class $`a\pmod g`$`, with even `$`2\le g\le16E`$,
satisfies the following raw prime supplies in the exact pool:

1. At least $`\lfloor X/(2048E^3)\rfloor`$ vertex-disjoint gap-g pairs
   with lower endpoint in class a.
2. At least $`X/(64E^2)`$ pool primes in class a.
3. In each of the actual intervals
   $`I_\pm=[m\pm X/4-X/A,m\pm X/4+X/A]`$, at least
   $`X/(32AE^2)`$` pool primes in each needed class `$`a,-1,+1\pmod g`$.

Repeated classes represent the same requirement. These bounds neither add
overlapping supplies nor presume independence of later adaptive choices.
The wider interval count is exactly the raw bound obtained from the same
strong analytic count as before: length $`2X/A`$,
$`\varphi(g)\le16E`$`, and `$`\log(2Y_\pm)\le2E`$ give
$`(2X/A)/(2\varphi(g)\log(2Y_\pm))\ge X/(32AE^2)`$.
Whether that analytic interface is available at those scales remains separate.

### Prefix and seed conditions

The same ceiling estimates, now re-derived from (CG3), give


```math
M\ge\frac X{256E^2},\quad H\ge\frac X{128AE^2},
 \quad s\le768E^2,\quad P\le5120E^3.                \qquad\text{(CG4)}
```


It suffices respectively that $`E^{2p-2}\ge256`$ and
$`E^{2p-2}\ge128A`$ for the two floor estimates.
Indeed $`s\le512E^2+1`$ and the added growth-prefix length is at most
$`4096E^3+1`$. Multiplying the unrounded definition of s by g gives
$`sg\le1024E^2+16E\le1040E^2`$.

All remaining prefix and seed comparisons reduce to


```math
\begin{gathered}
 E^{2p-2}\ge1040,\quad gM/(16X)\le1/(128E)\le1,\\
 E^{2p-4}\ge1572864,\quad E^{2p-4}>(128A)^2,\\
 E^{2p-3}\ge4096,\quad E^{p-5}\ge213909504.
                                                        \qquad\text{(CG5)}
\end{gathered}
```


These prove $`sg\le X`$`, `$`M^2g\ge48X`$,
$`H^2>X\ge\lceil X/g\rceil`$, and seed demand
$`(64n+4)s\le52224nE^2\le X/(4096E^3)`$.
The seed floor loses at most a factor two. Every ordinary seed and both
physical pairs in each diagonal seed group are included.

### The reservation-to-supply ratio, with the logarithm retained

Use the original exact reservation formula without replacing its first
factor by 136n:


```math
B=(128n+8)(P+7K)+4(n+1)(g/2-1).
```


Substituting (CG4), $`K\le cn/E^k`$`, and `$`g\le16E`$ gives


```math
\frac{E^2B}{n^2}\le U(E):=
 \left(128+\frac8{E^p}\right)
 \left(\frac{5120}{E^{p-5}}+\frac{7c}{E^{k-2}}\right)
 +\frac{32}{E^{p-3}}\left(1+\frac1{E^p}\right).
                                                        \qquad\text{(CG6)}
```


This keeps the exact leading reservation coefficient 896, or 1792 for the
smaller K choice. The sole discarded term in the residue contribution is
negative. CG1 now yields the sufficient depletion inequality


```math
\boxed{\frac{E^2B}{X}<\frac{U(E)}{Q(E)}
       \le\frac1{64A}.}                              \qquad\text{(CG7)}
```


The dominant decay is $`896/(E Q(E))=O(E^{-2})`$ in the preserved-K
regime, and $`1792/(E^2Q(E))=O(E^{-3})`$ for the smaller K.
The old invoice had dominant term $`952/E`$.

After subtracting the **whole** B, the global supply leaves at least M,
because $`1/64-1/(64A)\ge1/128`$` for `$`A\ge2`$; each interval/class
leaves at least H because $`1/(32A)-1/(64A)=1/(64A)`$.
This remains valid under overlapping classes/windows and adversarial adaptive
selection: no allocation-specific improvement is claimed.

The exact-pool occupancy condition requires a separate check:


```math
B/n^2\le U(E)/E^2<1/2.                            \qquad\text{(CG8)}
```


It does **not** follow merely from a bound for B/X, because X is larger
than n squared. This separate inequality is explicitly verified.

### Placement, centering, and capacity

The original L and J remain unchanged. The six separately embedded pair
passes and the joint placement of both diagonal rectangle families follow
from


```math
\begin{split}
 (4L+8)/n&\le3932360/E^{p-3}+5376c/E^k<1,\\
 4J/n&\le40960/E^{p-3}+56c/E^k+64/E^{p-1}<1.
\end{split}                                             \qquad\text{(CG9)}
```


Also $`KX\ge bn^3/E^k\ge32E\ge2g`$ follows from
$`bE^{3p-k-1}\ge32`$.
Dividing FC's complete centering invoice by K gives


```math
\boxed{\frac{6000}{A}
 +\frac{576\cdot5120}{bE^{p-k-3}}
 +\frac{242}{bE^{p-k-1}}
 +\frac3{bE^{p/2-k-1}}<\frac1{10}.}                \qquad\text{(CG10)}
```


For the fluctuation term, use $`\log n\le E`$,
$`\sqrt E\le E`$`, and `$`\sqrt n\ge E^{p/2}`$.
The residue numerator uses $`10g+82\le242E`$. Thus every term, including
prefixes, midpoint width, residue repair, and random-completion fluctuation,
is included. The endpoint comparisons
$`3/20-1/A>2^{-32}`$` and `$`17/20+1/A<1`$ place the two intervals in
$`(1,X)`$`, once `$`X\ge2^{32}`$.

The bounded-degree graph, cut expansion 8, routing capacities, disjoint
rectangle supports, and independent diagonal operations are precisely FC's
proved construction. Reducing K changes the capacities through FC's stated
parameter, with no infrastructure sharing or reuse of entry positions.

### Target fit

From (CG2), $`X<y\le nX\le X^{3/2}`$` and hence `$`E\le e\le2E`$.
The old finite target lemma's conditions already follow from


```math
E^{p-11}>54000\,2^{11},\qquad
 (2/5)E^{3p-15}>2^{35},\qquad E^4\ge4.              \qquad\text{(CG11)}
```


These are only numerical conditions: the target prime supplies must still
be established. For any actual targets within D of y,


```math
\frac D{KX}\le\frac{3}{5bE^{4-k}}\le\frac25.       \qquad\text{(CG12)}
```


In the smaller-K regime the last bound equals 2/5; the actual mean bound
is strict. FC's baseline radius is **strictly** less than KX/10, so the
combined displacement is strictly below KX/2 even with the non-strict
2/5 envelope. Row and column target totals must still both equal T,
and the two diagonal targets still retain their separate prescribed residues.

## 3. Evaluated regimes and all-tail proof

**CG2--CG4 (evaluated FC corollaries).** Under (CG2), the raw supplies above,
and the exact initial prime pool, all FC hypotheses and (CG11)--(CG12) hold
in each of the following four parameter regimes:

| Regime | A | K | p | Sufficient minimum E |
|---|---:|---|---:|---:|
| Logarithmic gain only | 10000000 | $`\lfloor n/E^3\rfloor`$ | 204 | 1048576 |
| Wider midpoint windows | 100000 | $`\lfloor n/E^3\rfloor`$ | 32 | 131072 |
| Near centering limit | 64000 | $`\lfloor n/E^3\rfloor`$ | 32 | 80000 |
| Smaller paid reservoir | 100000 | $`\lfloor2n/E^4\rfloor`$ | 32 | 4096 |

Here CG2 denotes the first corollary, CG3 the two widened-window variants,
and CG4 the smaller paid reservoir. Their common proof is the full sequence
(CG4)--(CG12), evaluated by exact rational arithmetic in
[cutoff_controller_optimization.py](../PROVENANCE.md#optimized-bound).
Each regime passes 32 finite checks. Ten negative controls reject damaged
parameter choices and empty, enlarged, malformed, or mismatched source maps.

At the fourth endpoint, $`U/Q`$ is enclosed by


```math
0.000000037658289108127213
 < U(4096)/Q(4096)
 <0.000000037658289108127214,
```


against allowed $`1/6400000=0.00000015625`$.
The complete centering upper bound is below
$`0.060000000000000000000001`$, against 1/10.
These decimals are presentation only; all decisions use rational arithmetic.

Every positive-power condition in (CG5), (CG11), and the floor/capacity
checks persists with E. Every nonconstant term in U, the placement ratios,
and the centering ratio is a positive decreasing power of E, since
$`p\ge32`$` and `$`k\le4`$. Q is positive and increasing on these
domains, so U/Q decreases. Thus all inequalities hold for **every integer
E above the stated endpoint**, regardless of jumps in E or K. K itself
is never assumed monotone: the proved two-sided floor envelope is reapplied
separately at each n and E.

For example, the smaller-K corollary's purely combinatorial domain follows
from $`n\ge2^{2048}`$, provided its index and mean assumptions hold:
writing $`v=\log_2n`$`, `$`2v\le E\le3v+1\le4v`$.
At $`v=2048`$`, `$`v>32\log_2(4v)=416`$, and
$`v-32\log_2(4v)`$ is increasing thereafter because
$`1-32/(v\log2)>0`$`. This proves `$`n\ge E^{32}`$ across every ceiling
jump. The analytic scale thresholds can be much larger; $`2^{2048}`$
is not presented as a cutoff for the conjecture.

An exact search of the decreasing depletion invoice alone finds first integer
ceilings 909658, 90968, 72775, and 2550 for the four rows, respectively.
These describe sufficient-estimate sensitivity, not lower bounds for the
mathematical problem. The rounded thresholds above are used for the clean
corollaries. The actual order cutoff must take the coupled analytic scales,
target requirements, and the $`n`$-versus-E envelope into account.

## 4. Architectural experiments and their limits

The logarithmic gain is decisive because the reserved entry count is naturally
proportional to n squared, whereas the analytic interval supply is proportional
to X. Replacing n squared by X before comparing them discards a logarithm.
Retaining the original factor 128n+8 also removes unnecessary padding from
the coefficient, but that is a smaller improvement.

Widening the macro intervals by 100 improves their raw supply by 100 while
raising the dominant centering term from .0006 to .06. This is a jointly
charged choice, not a supply gain with a frozen centering estimate. Taking
A=64000 uses still more centering budget (.09375); taking A=60000 fails
because the dominant term already equals 1/10, leaving no allowance for
the other positive terms. This failure is a limitation of FC's sufficient
centering invoice.

The K change is a second structural gain: the baseline pays reservoir width
n/E cubed even though target radius is of order nX/e to the fourth. Reducing
the paid width retains enough transfer capacity by (CG12) and removes another
power from the depletion ratio. It reduces both ordinary and diagonal
reservation counts, and improves placement, while the smaller K worsens the
prefix and concentration ratios. Those worsened terms are explicitly paid
in (CG10). No target overhead is omitted.

Executable replay details are recorded in [Provenance](../PROVENANCE.md#optimized-bound).

The script is standard-library-only, checks the exact required FC source
set and SHA-256, uses integer/rational arithmetic, and labels its analytic
and formal-proof limits. The coordinator's complete manifest must additionally
bind this new source, the new verifier, analytic and target sources, and the
composition proof. No inaccessible private artifact is introduced as a new
mathematical input.

[Manuscript index](../README.md) · [Optimized theorem](../optimized-bound.md) · [Source and review record](../PROVENANCE.md#optimized-bound)
