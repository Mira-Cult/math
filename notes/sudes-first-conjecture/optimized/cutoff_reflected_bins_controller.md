# Reflected bins: a controller for the linear target window

The target radius becomes D=y/e and the reservoir parameter becomes
K=floor(101n/(100E)). The actual midpoint tolerance remains 1/64000.
The intervals supplying wide pairs are wider than that tolerance, but are
partitioned into reflected bins. Pairs taken from matched bins have the
required midpoint. This separates the supply width from the centering error.

## 1. A reflected-stock lemma with adaptive deletions

Let X be positive, g even, m real, delta positive, and N a positive integer.
Put w=N delta and suppose the two bands


```math
(m-X/4-wX,m-X/4+wX],\qquad
 (m+X/4-wX,m+X/4+wX]                         \qquad\text{(RB1)}
```


are disjoint subsets of (1,X). Divide the lower band into the N disjoint
half-open bins


```math
A_j=(a_j,a_j+2\delta X],\quad
 a_j=m-X/4-wX+2j\delta X,\quad0\le j\lt N.
```


Match A_j to


```math
C_j=(2m-a_j-2\delta X,2m-a_j].                \qquad\text{(RB2)}
```


The upper bins are also a disjoint half-open partition, in the reverse
order. Their centers reflect about m. Endpoint openness is chosen to make
both partitions disjoint; a set-theoretic reflection of the half-open
interval is not being asserted. If p is in A_j and q in C_j, then


```math
\left|\frac{p+q}{2}-m\right|\le\delta X,
 \qquad (1/2-2w)X\le q-p\le(1/2+2w)X.         \qquad\text{(RB3)}
```


Suppose every bin initially has at least W pool primes in every reduced
class modulo g. After any set of at most B reserved pool entries, write
L_jr and H_jr for the remaining stocks in A_j and C_j in class r. Put


```math
S=\sum_{j,r}\min(L_{jr},H_{jr}).
```


A deleted entry belongs to at most one bin on at most one side and to
at most one reduced class. If l_jr and h_jr are the corresponding deletion
counts, min(L_jr,H_jr) is at least W-l_jr-h_jr, even if that expression
is negative. Consequently


```math
S\ge N\varphi(g)W-B.                         \qquad\text{(RB4)}
```


This is one budget for actual deleted entries. It is valid for adversarial
and adaptive selections and does not assume independence among stocks.
The number of same-class pairs within matched bins is at least


```math
\sum_{j,r}L_{jr}H_{jr}
 \ge\sum_{j,r}\min(L_{jr},H_{jr})^2
 \ge\frac{S^2}{N\varphi(g)}.                  \qquad\text{(RB5)}
```


If S squared exceeds NX, this is greater than X/g, since phi(g) is at most g.
Every pair has a positive difference divisible by g and less than X.
There are at most floor(X/g) possible differences. Two distinct pairs
therefore share a difference. They have disjoint endpoints: with a fixed
positive difference, either endpoint determines the other, and no lower
endpoint is an upper endpoint because the bands are disjoint.

The two pairs may come from different bins and different reduced classes.
Each pair separately satisfies (RB3), and their differences agree. These
are precisely the properties used by the main diagonal rectangle identity.
No common lower residue or common exact midpoint is required.

## 2. The finite controller implication

Use FC's exact initial pool, odd n at least three, even g, reduced seed
class a, positive integers K,M,H and its definitions of s and P. Retain
its conservative load bounds


```math
L=192P+1344K+3g-4,\qquad
 J=2(P+7K+g/2-1).                              \qquad\text{(RB6)}
```


Choose either FC's degree-64 graph, or G1's degree-12 multigraph. Put G=128
for the first choice and G=24 for the second. There are at most Gn/2
ordinary reservoirs in total across the row and column networks. Define


```math
B_0=(Gn+8)P+4(n+1)(g/2-1),\qquad
 B=B_0+(Gn+8)7K.                               \qquad\text{(RB7)}
```


There are two main diagonal reservoirs, each needing a double pair per
stage. Their entry coefficient 8 is unchanged. The narrow intervals for
residue repairs are (m-X/4-delta X,m-X/4+delta X] and the corresponding
upper interval. They are used only in the first reservation phase.

Assume these supply conditions for the actual pool:

1. At least (64n+4)s disjoint seed pairs of gap g and lower class a exist.
   For degree 12 only the actual (12n+4)s or fewer needed pairs are reserved.
2. At least B0+M pool primes lie in class a.
3. Each narrow residue interval has at least B0+H primes in each of the
   required classes -1 and +1 modulo g.
4. Each bin of (RB2) in every reduced class has at least W pool primes,
   and S0=N phi(g) W-B is positive with S0 squared greater than NX.

Assume the bands lie inside (1,X), w at least delta, 0<delta<1/24, and


```math
7(1/2-2w)\ge2,\qquad1/2+2w\lt 1.                \qquad\text{(RB8)}
```


Also retain all of FC's numerical hypotheses with B from (RB7), namely


```math
\begin{gathered}
 X\ge g,\quad sg\le X,\quad gM\le16X,
 \quad M^2g\ge48X,\quad H^2\gt \lceil X/g\rceil,\\
 2B\le n^2,\quad n\gt 4J,\quad n\gt 4L+8,\quad KX\ge2g,\\
 6000\delta K+576P+10g+82+3\sqrt{n\log n}\lt K/10.
                                                        \qquad\text{(RB9)}
\end{gathered}
```


**Theorem RBC.** Under these hypotheses, FC's entire controllability
conclusion holds. There is a baseline permutation of exactly the first
n squared odd primes, all required line sums are units modulo g and
strictly within KX/10 of y. Every compatible integer target vector within
KX/2 of the baseline, whose row and column totals both equal the actual T,
is realized by a permutation of the same pool. Both diagonal targets remain
independent, and target values may repeat.

### Selection phases and complete grids

First reserve all actually needed seed pairs. Complete every ordinary and
diagonal growth prefix, stopping at its first crossing of total difference X.
Throughout this phase only B0 entries can be consumed and the global class
retains M primes. FC's counting proof applies without change: the full g-grid
is covered, at most P stages suffice, and the final prefix sum R satisfies
X at most R at most 2X.

Next reserve all residue-path pairs and all residue rectangles on both
diagonals from the narrow intervals. The phase-one supply leaves H primes
in each required interval and class after all prior reservations. The
H-squared pigeonhole argument supplies the diagonal double pairs. These
gadgets are selected now but their final orientations are chosen only after
the actual baseline is known. For g=2 the residue families are empty.

Every class-specific gadget is now complete. For a wide stage, apply
(RB4)--(RB5) to the bins after all previous reservations. Their total never
exceeds B, so a fresh equal-difference double pair exists. An ordinary stage
uses one pair; a diagonal stage uses both. Pairs considered but not selected
do not consume entries. Each positive difference d is divisible by g and
at most (1/2+2w)X<X, hence at most the current R. Appending d preserves
complete coverage of all g-multiples from zero through R+d.

Every wide stage increases R by at least (1/2-2w)X. After 7K stages its
increase alone is at least 2KX by (RB8). Thus a reservoir reaches R at least
2KX using at most 7K wide stages. This replaces the old X/3 lower bound;
the number seven is proved again for the new difference interval rather
than inherited without checking. It proves the full entry cap (RB7).

### Placement, centering and transfers

The original six placement passes still have maximum degrees at most
64P,64P,448K,448K,2(g/2-1),2(g/2-1). Degree 12 only lowers the actual first
four degrees. Thus the original L in (RB6) remains a valid conservative
bound. All main and residue rectangles on both diagonals are placed jointly
with distinct rows and columns. The hypotheses n>4J and n>4L+8 give the
same disjoint supports, and all ordinary pairs avoid both diagonals.

The centering bound uses each wide pair's midpoint, not its membership
in one common narrow interval. Equation (RB3) supplies exactly the same
delta X error for every selected pair. Prefix counts, residue counts,
midpoint rounding and rectangle counts are unchanged or smaller. In a
diagonal rectangle the two pair midpoints need not be equal: each fixed
row or column sum is their sum, and each midpoint has the required error.
FC's complete centering invoice, completion by a random permutation of
unused entries, and subsequent residue repairs therefore give the strict
baseline radius in (RB9). That probabilistic existence argument is part of
the conventional proof, not a heuristic about successful squares.

All main-pair differences are multiples of g, so varying their lower classes
does not affect residue preservation. Residue paths can repair the actual
reference sums, and later main switches preserve those repaired residues.
For the degree-64 graph FC's original flow argument applies. For degree 12,
put C=floor(KX/g). A required integral demand coordinate divided by g has
absolute value at most floor(KX/(2g))=floor(C/2). G1 has every cut boundary
at least half the smaller side, so C times its boundary bounds the cut
demand. Integral max-flow/min-cut realizes the full required row/column box.
The equality of row and column target totals to T gives zero-sum demands.
Diagonal reservoirs retain the unchanged symmetric transfer range, and
their trades do not change rows, columns or the opposite diagonal.

Every selection uses unused primes. Every operation permutes entries on
disjoint supports, and the completion uses every remaining pool prime once.
This proves RBC while preserving the exact pool and both diagonals.

## 3. Two evaluated linear-window profiles

Let


```math
X=p_{n^2+1},\quad T=\sum_{p\in P_n}p,\quad
 m=T/n^2,\quad y=T/n,\quad
 E=\lceil\log_2X\rceil,\quad e=\lceil\log_2y\rceil.
```


Analytic logarithms are natural; e here is an integer scale parameter.
Suppose n is odd, n at least E to the power 32 and at least 2 to the power
4096, and n squared at most X at most n cubed with 2X/5<m<3X/5. Use the
smaller-gap seed conclusion 2 at most g at most E and its weaker matching
bound floor(X/(2048E cubed)). Set


```math
\begin{gathered}
 A=64000,\quad\delta=1/A,\quad N=6080,\quad w=N/A=19/200,\\
 K=\left\lfloor\frac{101n}{100E}\right\rfloor,
 \quad D=y/e,\quad
 M=\left\lfloor\frac X{4E^2}\right\rfloor,
 \quad H=\left\lfloor\frac X{AE^2}\right\rfloor,
 \quad W=\frac X{A\varphi(g)E}.                 \qquad\text{(RB10)}
\end{gathered}
```


The profiles are G=128,E at least 14400 and G=24,E at least 8192. Require
raw global count X/(2E squared) in the seed class, and raw count W in
every reduced class of every narrow residue interval and every reflected
bin. These are explicit analytic inputs. The controller does not prove
them by running its arithmetic program.

The bands lie in (1,X): their smallest possible endpoint is greater than
(3/20-w)X=(11/200)X, and their largest is less than (17/20+w)X<X.
Differences lie between .31X and .69X, so seven stages per K suffice.
Every bin lies in [Y/2,2Y] about its own center Y; it is enough that
2 delta at most 3/20-w. Its length 2X/A is at least Y/50000 since Y<X.
These facts identify the scale and interval length for the analytic import.
The same estimates cover the narrow residue intervals. The proof uses
half-open intervals throughout, matching the analytic theta-difference
interface, so no endpoint prime is counted twice or silently discarded.

### Prefix, phase budgets and geometry

The [small-gap prefix calculation](cutoff_small_gap_controller.md) suggests
the following estimates, which we rederive from the present hypotheses
because its literal E at least 10000 premise does not cover the degree-12
endpoint here:


```math
M\ge X/(8E^2),\quad H\ge X/(2AE^2),\quad
 s\le24E^2,\quad P\le160E^3,\quad sg\le33E^2.
                                                        \qquad\text{(RB11)}
```


Indeed X at least E to the power 64 makes X/(4E squared) at least two
and X/(AE squared) at least two, so each floor retains half its argument.
Then s at most 16E squared plus one is at most 24E squared, while the
second ceiling in P is at most 128E cubed plus one; their sum is at most
160E cubed. Also sg at most 4X/M+g is at most 33E squared. Thus these
estimates include the floors and ceilings without using an older numerical
corollary. We have gM at most X/(4E), M squared g at least X squared
divided by 32E to the fourth, and H squared at least X squared divided by
4A squared E to the fourth. The checked comparisons E to the power 60 at
least 1536 and strictly greater than 4A squared give the two double-pair
hypotheses; H squared greater than X is stronger than H squared greater
than ceil(X/g). The prefix fitting bound follows from E to the power 62
at least 33. The seed invoice is at most 1632nE
squared, while floor(X/(2048E cubed)) is at least X/(4096E cubed); it is
enough that E to the power 27 exceed 6684672. The weaker old degree-64
seed demand can therefore be retained for both profiles, provided only the
actual seeds needed by the chosen graph are reserved.

The Rosser--Schoenfeld lower bound on the prime index, derived in the
[first optimization](cutoff_controller_optimization.md) from their 1962
Theorem 2, inequality (3.4), gives


```math
\frac X{n^2}\gt Q(E):=\frac{693E-2193}{1000}\gt 0.     \qquad\text{(RB12)}
```


Its domain is X>exp(3/2). The rational ln 2 lower bound used here follows
from three positive terms of its convergent atanh series. Define


```math
\begin{split}
 U_0(E)&=\left(G+\frac8{E^{32}}\right)\frac{160}{E^{27}}
       +\frac2{E^{29}}\left(1+\frac1{E^{32}}\right),\\
 V(E)&=\left(G+\frac8{E^{32}}\right)
       \left(\frac{160}{E^{28}}+\frac{707}{100}\right)
       +\frac2{E^{30}}\left(1+\frac1{E^{32}}\right).
\end{split}                                           \qquad\text{(RB13)}
```


These bound E squared B0/n squared and EB/n squared, respectively.
The exact entry cap, including the +8 and n+1 terms, gives


```math
\frac{E^2B_0}{X}\lt \frac{U_0(E)}{Q(E)}\le\frac1A,
 \qquad
 \frac{EB}{X}\lt \frac{V(E)}{Q(E)}\le\frac{91}{1000}.
                                                        \qquad\text{(RB14)}
```


As phi(g) is at most E/2, W is at least 2X/(AE squared). The first budget
therefore leaves H in every narrow phase-one class, and the global supply
leaves M. The second is an aggregate budget over all reflected bins, giving


```math
S_0=N\varphi(g)W-B\ge(w-91/1000)X/E=X/(250E).
                                                        \qquad\text{(RB15)}
```


Thus S0 squared exceeds NX if X>6080 times 250 squared E squared. This
follows from n at least E to the power 32 and the checked inequality
E to the power 62 greater than 6080 times 250 squared. Separately,
B/n squared is at most V(E)/E<1/2; occupancy is not inferred from B/X.

The original conservative placement comparisons become


```math
\frac{4L+8}{n}\le\frac{122892}{E^{29}}
                  +\frac{5376(101/100)}E\lt 1,
 \qquad
 \frac{4J}{n}\le\frac{1280}{E^{29}}
                  +\frac{56(101/100)}E+\frac4{E^{31}}\lt 1.
                                                        \qquad\text{(RB16)}
```


Write b=1009/1000. As n/E is at least 1000, the floor in K gives
K at least bn/E. The centering invoice divided by K is bounded by


```math
\frac{6000}A+
 \frac{576\cdot160}{bE^{28}}+
 \frac{92}{bE^{30}}+
 \frac3{bE^{14}}\lt \frac1{10}.                    \qquad\text{(RB17)}
```


For the fluctuation term, log n/n decreases for n>exp(1), and
32 log E at most 32E at most E squared at these endpoints. This proves the
displayed bound for every n at least E to the power 32, rather than only
at equality. The reservoir range KX at least 2g follows from bE to the
power 94 at least two. The remaining floor, interval, seed and double-pair
comparisons are explicit in the accompanying program.

Here are outward decimal bounds produced from exact rational arithmetic:

| Profile | E minimum | EB/X upper bound | (4L+8)/n upper bound | Centering/K upper bound |
|---|---:|---:|---:|---:|
| Original degree 64 | 14400 | 0.090704556987882237628981 | 0.377066666666666666666667 | 0.093750000000000000000001 |
| Degree 12 | 8192 | 0.029900281293134301215730 | 0.662812500000000000000001 | 0.093750000000000000000001 |

The budget for EB/X is .091 and the load budget is one. Degree 12 is useful
when the analytic floor falls below the degree-64 depletion floor; it is not
claimed that either sufficient controller endpoint is an obstruction to the
mathematical problem.

### Linear target radius and integer ceiling coupling

The already proved prime-index upper bound X<4n squared log n holds for
n at least 64. With v=log2 n it implies


```math
E\lt 2v+\log_2v+3,\qquad e\gt 3v-2.
```


For v at least 4096,


```math
\frac{167}{250}(3v-2)-(2v+\log_2v+3)
 =\frac v{250}-\log_2v-\frac{542}{125}\gt 0.       \qquad\text{(RB18)}
```


At 4096 this equals 6/125. Its derivative is positive, because
1/250-1/(v log 2)>1/250-3/(2v)>0. These pointwise integer-ceiling
envelopes prove E/e<167/250 for the full order tail. They do not
differentiate through a ceiling jump.

Using m<3X/5, K at least bn/E and D=y/e now gives


```math
\frac D{KX}\lt \frac{(3/5)(167/250)}{1009/1000}
 =\frac{2004}{5045}\lt \frac25.                    \qquad\text{(RB19)}
```


The strict baseline radius adds less than KX/10, so all target coordinates
at distance at most D from y lie inside RBC's complete KX/2 box. This uses
the actual scale relationship; treating E and e as independent would lose
the linear-window conclusion at this choice of K.

For the optimized exact-total target construction, its convenient sufficient
size conditions n at least 680e to the fourth and D at least 2048e to the
fourth follow from e at most 2E, n at least E to the power 32 and


```math
E^{28}\gt 680\cdot16,\qquad (2/5)E^{91}\gt 2^{16}.
```


Also e at least four gives D at most y/4. Prime supply for those target
intervals, and the target construction itself, remain separate dependencies.
In particular, a fixed relative-length analytic interface for the bins must
not automatically be reused for the shrinking target interval y/e at every
larger e. Composition must verify the applicable target interface.

## 4. Whole-tail certification and reproducibility

All inequalities in (RB11)--(RB17) use envelopes valid at the actual integer
E,n,g and the actual floors. Every nonconstant term of U0 and V is positive
and decreasing, Q is positive and increasing, and the placement and centering
error envelopes decrease. Lower power bounds increase. The two endpoint
evaluations thus prove all integer E above each stated endpoint. The separate
n at least E to the power 32 and v at least 4096 hypotheses are checked
pointwise by the outer composition proof. Changes in E,e,K,P,M,H do not
invalidate these bounds: no smooth interpolation of a rounded quantity is
used. Equation (RB18) differentiates only an unrounded envelope valid on
both sides of every jump.

Run from the repository root:

```sh
python problems/prime-line-sums/code/cutoff_reflected_bins_controller.py
```

The standalone checker verifies 36 exact finite comparisons in each profile,
24,320 explicit endpoint controls for the 6080 matched bins, and a separate
actual-prime ten-bin selection fixture. That fixture deletes an entire
bin/class stock, then produces ten equal-gap double-pair stages with forty
distinct prime entries; primality is independently checked by trial division.
It tests the selection lemma, not a finite square of the theorem's order.
Negative controls reject an insufficient degree-64 budget, an excessive
midpoint tolerance, an excessive band width, and missing, empty or malformed
source maps. The exact required source set and SHA-256 bindings are embedded;
missing, empty, nonregular or mismatched source files also fail closed.

The program verifies finite arithmetic and the stated finite controls.
Universal graph existence, adaptive stock selection, finite controller
geometry and flows, prime-index facts and raw analytic counts remain
mathematical arguments or imported theorems. This is not a kernel-checked
proof and does not by itself certify a complete numerical theorem for
Sude's conjecture. The coordinator must compose these conditional statements,
freeze the exact source, and obtain independent review before announcing a
record cutoff.

[Manuscript index](../README.md) · [Optimized theorem](../optimized-bound.md) · [Source and review record](../PROVENANCE.md#optimized-bound)
