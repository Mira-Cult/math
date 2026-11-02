# A centered controller for the exact initial prime pool

## Scope and status

This is the full combinatorial component of the [eventual-existence proof](proof.md).
Write $`p_j`$ for the $`j`$-th prime, with $`p_1=2`$, and let
$`P_n=\{p_2,\ldots,p_{n^2+1}\}`$ be the first $`n^2`$ odd primes.
The status and scope of the result are stated in the [main note](README.md).

The main result of this note is a **centered universal-controller theorem**:
for every sufficiently large odd order, the exact initial pool admits an
arrangement whose line sums are all units modulo one bounded even integer and
whose row, column and diagonal sums can then be prescribed throughout a large
lattice box, subject only to the two total-sum constraints. This removes the
prescribed-pool and simultaneous-control obligations from the analytic target
selection. The [prime-target lemmas](prime-targets.md) supply the targets at the end.
The construction does not add, omit or replace entries.

The arithmetic inputs are an unconditional quantitative consequence of
Maynard's sieve and the prime number theorem in each of finitely many fixed
progressions. The seed argument needs a quantitative count at every sufficiently large
scale; an assertion of infinitely many bounded gaps alone would not suffice.

Write



```math
X=p_{n^2+1},\qquad T=\sum_{p\in P_n}p,\qquad
 m=T/n^2,\qquad \mu=T/n=nm,\qquad K=\lceil n^{2/3}\rceil.
```



The prime number theorem gives $`X\asymp n^2\log n`$ and
$`m/X\to1/2`$. The scale $`KX`$ is deliberately larger than the random
completion error $`X\sqrt{n\log n}`$, while $`K=o(n)`$ keeps the controls sparse.

## S. A supply of common bounded gaps for every sufficiently large pool

**Lemma S.** For every fixed $`\varepsilon>0`$, every sufficiently large $`X`$
contains at least $`c_\varepsilon X^{1-\varepsilon}`$ vertex-disjoint prime
pairs $`(p,p+g)`$ with the same even gap $`2\le g\le600`$, and with all lower
endpoints in one reduced class $`a\pmod g`$. The choices $`g,a`$ may depend
on $`X`$. All endpoints may be required to lie in $`[X/4,3X/4]`$.

**Primary import.** James Maynard, *Small gaps between primes*,
[arXiv:1311.4600v3, 28 October 2019](https://arxiv.org/abs/1311.4600v3),
Propositions 4.1 and 4.3, the proof of Proposition 4.2, equation (5.9), and
footnote 2 on printed page 6. The fixed 105-element admissible tuple has
diameter 600. Proposition 4.3 gives $`M_{105}>4`$; Proposition 4.1 supplies
positive sieve surplus, and (5.9) bounds the coefficients. These are the exact
source locators used here; the admissible tuple is printed in that footnote.

**Proof of the quantitative consequence.** Choose the fixed smooth function
in Maynard's construction with a strict positive margin above one prime. For
all sufficiently large $`N`$, his nonnegative weights satisfy



```math
S_2-S_1\gg
 \frac{\varphi(W)^{105}N(\log R)^{105}}{W^{106}},
 \qquad
 w_t=\left(\sum_{d_i\mid t+h_i}\lambda_{d_1,\ldots,d_{105}}\right)^2,
```



where $`t\in[N,2N)`$, $`R=N^c`$ for a fixed positive $`c`$, and
$`W=\prod_{p\le\log\log\log N}p=N^{o(1)}`$. His coefficient estimate is
$`\max|\lambda|\ll(\log R)^{105}`$, the smooth function being fixed.
For each fixed $`\eta>0`$, the elementary divisor bound
$`\tau(u)\ll_\eta u^\eta`$, applied with sufficiently small exponents to
the 105 factors, therefore gives $`\max_t w_t\ll_\eta N^\eta`$.
The displayed surplus is $`\gg_\eta N^{1-\eta}`$.

Let $`G_N`$ be the bases having at least two prime values among the tuple.
Terms outside $`G_N`$ contribute nonpositively to $`S_2-S_1`$, while each
term inside contributes at most $`104\max w_t`$. Thus
$`|G_N|\gg_\eta N^{1-2\eta}`$. Taking $`\eta<\varepsilon/2`$ and
$`N=\lceil X/3\rceil`$ proves the required power lower bound. The tuple
endpoints lie in $`[X/4,3X/4]`$ for all sufficiently large $`X`$.

Choose one prime pair from each good base. A fixed prime belongs to at most
105 bases, since it must equal $`t+h_i`$. Consequently the resulting
multigraph of pairs has maximum degree at most 105. Greedy matching retains
at least a $`1/209`$ fraction of its edges. Partition this matching by its
even difference $`g\le600`$ and lower endpoint modulo $`g`$. There are only
finitely many classes, and every endpoint exceeds 600 eventually, so the
selected class is reduced. Pigeonhole proves the lemma. No one particular gap
is asserted to occur with this frequency for every $`X`$. $`\square`$

Taking $`\varepsilon=1/4`$ supplies more than the $`O(n\log X)`$ seed pairs
needed below. The inequality is uniform through all sufficiently large orders,
since $`n\log^A X=o(X^{3/4})`$ for every fixed $`A`$.

## C. Complete sequences from global density

**Lemma C1 (interval extension).** Suppose positive multiples
$`d_1,\ldots,d_s`$ of $`g`$ have subset sums containing every multiple of
$`g`$ in $`[0,R]`$. Appending a multiple $`d`$ with $`0<d\le R+g`$
extends coverage to $`[0,R+d]`$. In particular, $`k`$ copies of $`g`$
start the interval $`[0,kg]`$.

The two covered intervals are $`[0,R]\cap g\mathbb Z`$ and
$`[d,R+d]\cap g\mathbb Z`$; their grid points touch or overlap. This also
gives an exact representation algorithm: process the appended differences
backwards, selecting a difference precisely when the remaining target exceeds
the previous endpoint.

**Lemma C2 (one pair).** Let $`A\subset[1,X]\cap(a+g\mathbb Z)`$ have
$`M`$ elements. If $`4X/M\le R\le X`$, partition $`[1,X]`$ into
$`\lceil X/R\rceil\le2X/R`$ intervals of length at most $`R`$. One contains
at least $`MR/(2X)`$ elements. Its extremes give a difference



```math
\frac{gMR}{4X}\le d\le R.
```



Indeed, the interval has at least two elements and the span of $`s`$ points
in one $`g`$-class is at least $`g(s-1)\ge gs/2`$.

**Lemma C3 (two disjoint equal-gap pairs).** Under the same hypotheses, if
$`M^2g\ge48X`$, there are two vertex-disjoint pairs in $`A`$ with a common
difference satisfying



```math
\frac{gMR}{16X}\le d\le R.
```



To prove this, let $`m_j`$ be the bin counts. The number of pairs within
bins is at least



```math
\frac12\left(\frac{M^2}{\lceil X/R\rceil}-M\right)
 \ge\frac{M^2R}{4X}-\frac M2\ge\frac{M^2R}{8X}.
```



Put $`h=gMR/(16X)`$. For each lower endpoint, fewer than $`h/g`$ possible
upper endpoints have a positive difference below $`h`$. Deleting those
pairs leaves at least $`M^2R/(16X)`$ pairs. There are at most $`R/g`$
possible differences, so one difference occurs at least
$`M^2g/(16X)\ge3`$ times. The graph of pairs of one positive difference
has maximum degree two and no cycles; any three edges contain two disjoint
edges. This proves the claim.

**Consequence C4.** If the available prime set in class $`a\pmod g`$ has
size $`\gg_g X/\log X`$, $`O_g(\log X)`$ common-gap seeds start a complete
interval to which C2 or C3 applies. Each subsequent stage increases its
endpoint by a factor at least $`1+c_g/\log X`$. Thus
$`O_g(\log^2X)`$ fresh pairs, or fresh equal-gap double pairs, suffice to
reach an endpoint between $`X`$ and $`2X`$.

Only a global residue-class count is used. There is no short-interval prime
number theorem at these intermediate scales and no prescribed large prime
difference.

## M. Macroscopic extension with controlled midpoints

Fix $`0<\delta<1/24`$. Use the two intervals



```math
I_-=[m-X/4-\delta X,m-X/4+\delta X],\qquad
 I_+=[m+X/4-\delta X,m+X/4+\delta X].
```



They lie inside $`(1,X)`$ for all sufficiently large $`n`$. The fixed-modulus
prime number theorem gives $`\gg_{g,\delta}X/\log X`$ primes in each
prescribed reduced class within either interval. The input may be taken from
KOUK in [the references](REFERENCES.md#prime-number-theorem-in-fixed-progressions), specialized to fixed moduli; no
growing-modulus uniformity is needed. Since $`g\le600`$, taking the maximum
of finitely many thresholds makes all constants uniform in the selected gap.

Pair any fresh low and high primes of the same class $`a\pmod g`$. Their
positive difference lies between $`X/3`$ and $`2X/3`$, and their midpoint
is within $`\delta X`$ of $`m`$. Once the complete interval reaches $`X`$,
all these differences are admissible in C1. At most $`6K+1\le7K`$ such
pairs extend the interval beyond $`2KX`$.

For diagonal controls one needs two pairs of the same difference. There are
$`\gg_{g,\delta}X^2/\log^2X`$ low-high pairs but only $`O(X/g)`$
differences. One difference therefore has many representations. Those
representations are automatically vertex-disjoint: for fixed positive $`d`$,
each low prime has only one possible high partner, and conversely. This gives
two pairs with the same bounds on difference and midpoint, and the same
$`7K`$ stage bound.

These selections remain possible after $`O(nK+n\log^2X)=o(n^2)`$ earlier
entries have been reserved, because each fixed interval and reduced class
initially contains $`\gg_{g,\delta}n^2`$ entries. The deletion bound is global,
so it applies even if all deleted entries were concentrated in one such class
or interval. Reserve the entire seed supply in S first, including one pair
per ordinary seed and two disjoint equal-gap pairs per diagonal seed. Only
then select the growth and macroscopic pairs. Supply is not a heuristic
independence claim.

## F. Independent row and column controls

For a row edge $`u,v`$, put each pair $`(p_j,p_j+d_j)`$ in one column at
rows $`u,v`$. Choosing which endpoint receives the larger member transfers
$`d_j`$ between the two row sums and leaves the column sum unchanged.
Put $`R=\sum_jd_j`$. The insertion construction covers every point of
$`[0,R]\cap g\mathbb Z`$; here $`R`$ is the total difference, not a
smaller endpoint inside a possibly larger subset-sum range. Choosing a subset
of sum $`q`$ gives endpoint contributions



```math
\sum_jp_j+R-q,\qquad \sum_jp_j+q.
```



Choose the baseline $`q_0=g\lfloor R/(2g)\rfloor`$. Both contributions
differ from the sum of the pair midpoints by at most $`g/2`$. Every signed
transfer $`gz`$, with $`|z|\le\lfloor R/(2g)\rfloor`$, is then available
relative to this baseline. This is a whole-bundle statement; individual pair
orientations need not be balanced.

**Lemma F1 (a bounded-degree network for every order).** For every $`n\ge2`$
there is an undirected multigraph on $`n`$ vertices with degree at most 64 and



```math
|\partial S|\ge8\min(|S|,n-|S|)
```



for every vertex set $`S`$.

Take 32 independent uniform permutations and retain the undirected edge
$`v,\pi_j(v)`$ for every $`j,v`$, with multiplicity, discarding loops. Fix
$`|S|=s\le n/2`$ and write $`p=s/n`$. The probability that specified
$`k`$ domain points in $`S`$ all map into $`S`$, within one permutation,
is $`(s)_k/(n)_k\le p^k`$. Independence between permutations gives the
same bound for a specified collection of domain points among all 32 copies.
If fewer than $`4s`$ directed edges leave $`S`$, at least $`28s`$ of
the $`32s`$ images stay in $`S`$. A union bound gives probability at most
$`\binom{32s}{28s}p^{28s}`$. Hence the union over all sets is bounded by



```math
\sum_{s=1}^{\lfloor n/2\rfloor}
 \left[e\exp\{32H(1/8)\}\,2^{-27}\right]^s<1,
```



where $`H(t)=-t\log t-(1-t)\log(1-t)`$; the bracket is below $`0.004`$.
For each permutation, equally many edges enter and leave a cut, so the
undirected boundary has at least $`8s`$ edges. The degree bound is 64.

**Lemma F2 (integral box of demands).** On a graph with this cut bound, give
each edge all integral transfers in $`[-C,C]`$. Every integral demand vector
$`b`$ satisfying $`\sum_vb_v=0`$ and $`|b_v|\le8C`$ is realizable.

For every cut,
$`|\sum_{v\in S}b_v|\le8C\min(|S|,n-|S|)\le C|\partial S|`$.
The integral max-flow/min-cut theorem, applied with capacity $`C`$ in both
directions on every edge, produces the desired integral flow. Cancel opposing
flows on each edge. It then lies in $`[-C,C]`$. There is no independent-repair
assumption: the zero-sum dependencies are exactly those handled by the flow.

Give each edge a disjoint reservoir reaching $`R\ge2KX`$. F2 realizes any
zero-sum row correction on the $`g`$-grid of magnitude at most
$`8g\lfloor KX/g\rfloor`$ per coordinate. A second, disjoint copy transposed
controls the columns while preserving every row sum. Both supports avoid the
two diagonals.

## D. Two diagonal controls preserving every row and column

Suppose two disjoint prime pairs have a common difference $`d`$. The trade



```math
\begin{pmatrix}a&a+d\\b+d&b\end{pmatrix}
 \longleftrightarrow
 \begin{pmatrix}a+d&a\\b&b+d\end{pmatrix}
```



preserves both row sums and both column sums. Place the rectangle so that
its top-left cell is the only cell on the chosen diagonal and no cell lies on
the other diagonal. The trade changes exactly the chosen diagonal by $`d`$.
It does not change it by $`2d`$: that factor would arise from a different
rectangle meeting the diagonal twice.

C3 and M give a complete $`g`$-grid of diagonal changes through $`2KX`$,
using $`O_g(\log^2X)+7K`$ rectangles. The midpoint subset gives a symmetric
range at least $`[-KX+g,KX-g]\cap g\mathbb Z`$. Its diagonal contribution
differs from the sum of the relevant pair midpoints by at most $`g/2`$.

There are $`O(K)=o(n)`$ rectangles in total, including both these main
reservoir rectangles and the residue-correction rectangles in R below.
Allocate all of them together, using distinct row indices and distinct column
indices across both diagonal families and both purposes. For a main
rectangle choose rows $`i,j`$ and columns $`i,k`$; exclude the center,
previously used indices, $`j=k`$, and the finitely many equations causing
an unwanted anti-diagonal cell. For an anti rectangle use columns
$`n-1-i,k`$ and impose the analogous exclusions. At each choice only
$`O(K)`$ indices and a fixed number of additional values are forbidden.
This proves greedy placement for all sufficiently large $`n`$.

Every row and column then contains at most two rectangle cells. Their fixed
row and column sums are sums of two pair midpoints; this fact will also
control the baseline means.

## E. Embedding without concentrating the uncontrolled prefixes

Each ordinary edge reservoir consists of an uncontrolled prefix of length
$`O_g(\log^2X)`$, followed by at most $`7K`$ centered macroscopic pairs.
Embed these two parts in separate passes. Embed residue controls, described
below, in a third pass. This separation is necessary: an embedding controlling
only total load could concentrate $`\Theta(K)`$ uncontrolled prefix pairs
in one column.

For any one row-pair pass, its multigraph has maximum degree $`D`$, at most
$`nD/2`$ edges, and $`D=o(n)`$. Assign each edge a column, allowing at most
$`D`$ edges of this pass in one column. At most $`n/2`$ columns are full.
The two incident rows exclude only $`O(K)`$ columns through cells already
occupied in earlier passes or earlier edges, and four further columns through
the diagonal conditions. A free column therefore exists eventually.

For a column-pair pass transpose the argument. The previous load caps ensure
that every earlier row and column has only $`O(K)`$ occupied cells. This
allows all passes to avoid one another and the diagonal rectangles. Pair
switches and rectangle trades then act on disjoint entries and commute.

In the prefix passes, every line sees only $`O_g(\log^2X)`$ uncontrolled
entries. In the macroscopic passes, a row's own edge bundles contain at most
$`64\cdot7K=448K`$ pairs, and the orthogonal pass contributes at most
$`2\cdot448K`$ entries in that row. The same bounds hold for columns.

## R. Correcting residues at bounded numerical cost

The main reservoirs preserve all line sums modulo $`g`$. It would be a gap
to assume their baseline residues were automatically units. The following
separate controls solve this problem using the actual initial-segment supply
in two different reduced residue classes.

Put $`h=g/2`$. Choose fresh prime pairs with lower member in
$`-1\pmod g`$ and upper member in $`+1\pmod g`$, using $`I_-`$ and
$`I_+`$. Every difference is $`2\pmod g`$. On each edge of a spanning path
of rows reserve $`h-1`$ such pairs. In the reference orientation on the
directed path edge $`i\to i+1`$, put every larger member at $`i`$.
Selecting the first $`k`$ pairs,
$`0\le k<h`$, realizes every even residue transfer modulo $`g`$, irrespective
of the different integer gaps. More explicitly, divide the even desired
corrections by two modulo $`h`$, obtaining $`b_i`$ of total zero.
On edge $`i\to i+1`$, select $`k_i\equiv-\sum_{j\le i}b_j\pmod h`$
pairs, with $`0\le k_i<h`$. Its flow has residue $`k_i`$ after division
by two, giving exactly the required vertex demands. A separate column path
does the same for columns. Both supports avoid the diagonals.

Every row or column belongs to at most two path edges, so the numerical
change to its sum is at most $`2(h-1)X=O_g(X)`$. Row corrections preserve
columns exactly and column corrections preserve rows exactly.

To choose the desired unit residues, observe that for odd $`n\ge3`$ and odd
$`T`$, there are $`n`$ units modulo every even $`g`$ summing to $`T`$.
Take $`n-3`$ ones and let $`A=T-(n-3)`$. Choose a triple of units summing
to $`A`$. For every odd prime divisor $`q\mid g`$, choose a nonzero
$`y\pmod q`$ different from $`A-1\pmod q`$. Modulo the power of 2 choose
$`y`$ odd. The Chinese remainder theorem produces such a unit modulo $`g`$,
and $`1,y,A-1-y`$ are the required units, with prime powers handled by
lifting these classes. Apply this independently to the row and column totals.

For each diagonal reserve $`h-1`$ extra rectangles whose equal gaps are
$`2\pmod g`$. They exist by the low-high difference pigeonhole argument
from M, now using class $`-1`$ below and class $`+1`$ above. Their gaps
all have the required residue. Selecting the first $`k`$ rectangles realizes
every even diagonal correction. Since each diagonal sum is odd, it can be
set to $`1\pmod g`$, preserving every row, column and the other diagonal.
The numerical change is at most $`(h-1)X`$.

When $`g=2`$, these paths and extra rectangles have length zero: all required
line sums are already odd units. The small primes dividing $`g`$ may occur
anywhere in the remaining pool; the correction argument accounts for their
contributions and does not discard them.

The exact initial pool supplies both reduced classes $`-1,+1\pmod g`$
with positive density, as well as the common-gap seeds and macroscopic
controls. These are arithmetic properties of the prescribed entries.

## B. Centered completion by sampling without replacement

Reserve the seed pairs first, then all growth and macroscopic pairs and all
residue controls, always with distinct entries. The total number reserved is
$`O(nK+n\log^2X)=o(n^2)`$. Place them as above. Set every main reservoir
at its exact midpoint subset; put the residue controls in their all-off
reference orientations for now.

For every required line $`L`$, let $`r_L`$ be its number of reserved cells
and $`C_L`$ the sum of their entries. The midpoint identities, separate
prefix load caps and centered macro pairs give



```math
|C_L-r_Lm|\le 2000\delta KX+C_gX\log^2X.                 \qquad\text{(B1)}
```



The constant 2000 is deliberately generous: ordinary row and column controls
contribute at most $`(448+896)\delta KX`$; each row or column meets at most
one diagonal rectangle; diagonal midpoint sums require only $`7K`$ macro
terms. Prefix entries, bounded-gap rounding and all residue controls are
absorbed in the second term. The finite maximum over $`g\le600`$ is allowed.

Let $`M_0`$ be the remaining pool size and $`m_0`$ its mean. Summing (B1)
over the rows, and using $`M_0\ge n^2/2`$, gives



```math
|m_0-m|\le\frac2n\bigl(2000\delta KX+C_gX\log^2X\bigr).
```



Uniformly permute the remaining entries into the remaining cells. For each
required line,



```math
|\mathbb E S_L-\mu|
 \le3\bigl(2000\delta KX+C_gX\log^2X\bigr).             \qquad\text{(B2)}
```



This expectation calculation is why controlling the sum of the reserved
entries, rather than merely their number, matters.

For completeness, the concentration step has no independence assumption.
A line's $`t\le n`$ unfilled entries form a uniform sample without
replacement. Reveal them successively and take the conditional expectation
of their final sum. The martingale increment at reveal $`j`$ is



```math
(Z_j-\bar Z_{j-1})\frac{M_0-t}{M_0-j},
```



whose absolute value is at most $`X`$. The bounded-increment exponential
martingale estimate therefore gives



```math
\Pr(|S_L-\mathbb E S_L|>u)
 \le2\exp\{-u^2/(2nX^2)\}.
```



With $`u=3X\sqrt{n\log n}`$, a union bound over the $`2n+2`$ required
lines is below one for all sufficiently large $`n`$.

Choose, for example, $`\delta=10^{-7}`$, and then take $`n`$ sufficiently
large. Since $`\log^2X=o(K)`$ and $`\sqrt{n\log n}=o(K)`$, (B2) and this
concentration statement give a completion whose every line differs from
$`\mu`$ by less than $`KX/20`$. Apply the residue repairs R; their
$`O_g(X)`$ changes leave every line within $`KX/10`$ of $`\mu`$.

## U. The centered universal controller

**Theorem U.** For every sufficiently large odd $`n`$, there
are an even $`2\le g\le600`$ and a permutation of the exact pool $`P_n`$
with baseline row sums $`A_i`$, column sums $`B_j`$ and diagonal sums
$`D_+,D_-`$ such that:

1. Every baseline sum is a unit modulo $`g`$ and lies within $`KX/10`$
   of $`\mu=T/n`$.
2. Every integer target vector $`(A'_i,B'_j,D'_+,D'_-)`$ having the same coordinate
   residues modulo $`g`$, satisfying
   $`\sum_iA'_i=\sum_jB'_j=T`$, and differing from its baseline coordinate
   by at most $`KX/2`$, is realized by another permutation of exactly $`P_n`$.

All quantifiers concern every sufficiently large odd order. The modulus may
vary among a fixed finite set. The simultaneous target assertion follows by
F2 for rows and columns, and D for diagonals, on mutually disjoint supports.
The row and column target totals are necessary and sufficient for these
control networks; the diagonals impose no additional total constraint.

**Prime-target interface.** To finish the original theorem using U, it suffices
to have the following independently proved analytic statement for each bounded
even $`g`$: if $`u_1,\ldots,u_n`$ are units modulo $`g`$, and
$`\sum_i u_i\equiv T\pmod g`$, then one can choose primes
$`q_i\equiv u_i\pmod g`$ with $`\sum_iq_i=T`$ and
$`\max_i|q_i-T/n|=o(X)`$. One also needs one prime in each of the two
prescribed diagonal unit classes within $`o(X)`$ of $`T/n`$.

This interface concerns prime targets, separately from the array arrangement.
It is proved in [A1–A4](prime-targets.md). Applying that result twice for rows
and columns, and applying the bracketing lemma to the diagonals, falls strictly
inside U's box. The [synthesis proof](proof.md#proof-of-theorem-p) checks the
exact totals, residue conditions, capacities and common eventual threshold.
