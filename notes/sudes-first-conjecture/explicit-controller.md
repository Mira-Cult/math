# The finite controller and its numerical parameter regime

Theorem FC is a finite implication for the exact prime pool, with every
supply, deletion, placement, centering and transfer requirement displayed.
Corollary PC3 verifies those finite inequalities with
$`K=\lfloor n/\lceil\log_2X\rceil^3\rfloor`$ for every
$`n\ge2^{2^{40}}`$. The [explicit-bound proof](explicit-bound.md) supplies
its prime-count hypotheses from [the classical estimates](classical-primes.md)
and chooses compatible prime targets using [the finite target lemma](explicit-targets.md).
This file alone is not a prime-square theorem: prime supplies and prime
targets are substantive inputs, not numerical assumptions certified by notation.

## FC: a finite controller theorem

Use the exact pool and line family from [the main note](README.md#the-conjecture). Let


```math
X=p_{n^2+1},\qquad T=\sum_{p\in P_n}p,\qquad
 m=T/n^2,\qquad \mu=T/n.
```


Let $`n\ge3`$ be odd, $`K,M,H`$ positive integers, $`g\ge2`$ even, and
$`a`$ a reduced residue modulo $`g`$. Take a rational
$`0<\delta<1/24`$, and define


```math
\begin{split}
 \ell&=\lceil\log_2X\rceil,\qquad h=g/2,\\
 s&=\left\lceil\frac{4X}{gM}\right\rceil,\qquad
 P=s+\left\lceil\frac{32X\ell}{gM}\right\rceil,\\
 B&=(128n+8)(P+7K)+4(n+1)(h-1),\\
 L&=192P+1344K+3g-4,\\
 J&=2(P+7K+h-1).
\end{split}                                                    \qquad\text{(FC1)}
```


Here $`B`$ bounds the **entire number of reserved entries**, $`L`$ bounds
the number of reserved cells on each row or column, and $`J`$ bounds all
diagonal rectangles, including residue repairs. The definitions are finite;
there is no unspecified constant hidden in $`P,B,L,J`$.

Put


```math
I_\pm=[m\pm X/4-\delta X,\ m\pm X/4+\delta X].             \qquad\text{(FC2)}
```


Assume the following supply statements for this very pool:

1. There are at least $`(64n+4)s`$ vertex-disjoint prime pairs
   $`(p,p+g)`$, all with lower endpoint in class $`a\bmod g`$.
2. The pool contains at least $`B+M`$ members in class $`a\bmod g`$.
3. Each of $`I_-,I_+`$, in each required class
   $`a,-1,+1\bmod g`$, contains at least $`B+H`$ pool members.
   Repeated classes denote the same condition. These are lower bounds in
   the actual intervals centered at the actual rational number $`m`$.

The analytic producer is responsible for these counts, including the
common gap and the reduced class chosen by its seed matching. Supplying
only a positive density before uncharged deletions is insufficient.

Assume also the following finite inequalities:


```math
\begin{gathered}
 X\ge g,\quad I_-\cup I_+\subset(1,X),\quad sg\le X,\quad gM\le16X,\\
 M^2g\ge48X,\qquad H^2>\lceil X/g\rceil,\\
 2B\le n^2,\qquad n>4J,\qquad n>4L+8,\qquad KX\ge2g.
\end{gathered}\qquad\text{(FC3)}
```




```math
6000\delta K+576P+10g+82+3\sqrt{n\log n}<K/10.             \qquad\text{(FC4)}
```


All logarithms except $`\log_2`$ are natural.

**Theorem FC.** Under these hypotheses there is a permutation of exactly
$`P_n`$ whose row sums $`A_i`$, column sums $`C_j`$, and diagonal sums
$`D_+,D_-`$ are units modulo $`g`$ and satisfy


```math
|A_i-\mu|,\ |C_j-\mu|,\ |D_\pm-\mu|<KX/10.
```


Every integer target vector in the same coordinate residue classes, with
row and column totals both exactly $`T`$, and with every coordinate at
distance at most $`KX/2`$ from its baseline, is realized by a permutation
of exactly the same pool.

The diagonal targets have no extra total constraint. The target values may
repeat. This statement is a numerical controllability theorem; it does not
say that a prime target vector exists.

## 1. Prefix length and complete intervals

Reserve **all** seed pairs first. There are at most $`32n`$ edges in each
of the two degree-64 control graphs, hence at most $`64n`$ ordinary
reservoirs. Each uses $`s`$ seeds. Each of the two diagonal reservoirs uses
two seed pairs per stage, so four further seed-pair copies are required.
The total is at most $`(64n+4)s`$, exactly as in FC.

The supply inequalities charge the complete eventual deletion bound $`B`$.
Consequently, during every later choice there are still at least $`M`$
unreserved primes in class $`a`$, and at least $`H`$ in every required
interval and class. This includes all seeds allocated to reservoirs that
have not yet been completed.

Start each ordinary reservoir with $`s`$ gap-$`g`$ pairs; start each
diagonal reservoir with $`s`$ groups, each consisting of two gap-$`g`$
pairs. The total difference is initially $`R=sg`$, and its subset sums
contain every multiple of $`g`$ from 0 to $`R`$.

The complete finite counting input is as follows. If $`A\subset[1,X]\cap(a+g\mathbb Z)`$, $`|A|\ge M`$, and
$`4X/M\le R\le X`$, first restrict $`A`$ to any $`M`$ points, then divide
$`[1,X]`$ into at most $`2X/R`$ intervals.
The within-bin pair count is at least


```math
\frac{M^2R}{4X}-\frac M2\ge\frac{M^2R}{8X}.
```


Pairs with positive difference below $`gMR/(16X)`$ number less than
$`M^2R/(16X)`$. There are at most $`R/g`$ possible remaining differences,
so one occurs at least $`M^2g/(16X)\ge3`$ times. The graph of one fixed
positive difference is a disjoint union of paths. Any three of its edges
contain two vertex-disjoint edges. Thus a fresh double pair exists with


```math
\frac{gMR}{16X}\le d\le R.                               \qquad\text{(FC5)}
```


One such pair suffices for an ordinary reservoir. No prime in a specified
short interval is requested during these prefix stages.

Appending a positive $`g`$-multiple $`d\le R+g`$ preserves complete
coverage from 0 through $`R+d`$: the two translated intervals touch or
overlap on the $`g`$-grid. Here $`R`$ is the **sum of all differences
already used**, not a smaller claimed coverage radius.

Write $`t=gM/(16X)\le1`$. Each growth step before reaching $`X`$ multiplies
$`R`$ by at least $`1+t`$. The elementary inequality
$`\log(1+t)\ge t/2`$, $`0\le t\le1`$, gives


```math
\left(1+t\right)^{\lceil32X\ell/(gM)\rceil}
 \ge \exp(\ell)\ge X.
```


The last inequality uses $`\ell\ge\log X`$, since $`\log2<1`$.
As $`sg\ge1`$, at most this many growth stages are needed. The first
crossing has $`X\le R\le2X`$, since each appended difference is at most
the old $`R`$. Therefore at most $`P`$ stages per reservoir suffice.
This pays every growth iteration and every diagonal double-pair cost.

## 2. Macroscopic extension and remaining supplies

Any lower prime from $`I_-`$ and upper prime from $`I_+`$ have difference
between $`X/3`$ and $`2X/3`$, and their midpoint is within $`\delta X`$
of $`m`$. Primes in the same class yield a positive multiple of $`g`$.
Once $`R\ge X`$, all such differences satisfy the insertion inequality
$`d\le R+g`$.

Starting at $`R\ge X`$, at most $`6K+1\le7K`$ such stages reach
$`R\ge2KX`$. This deliberately coarse bound is valid for every integer
$`K\ge1`$; it does not require $`K=n^{2/3}`$.

For a diagonal stage, the $`H^2`$ low--high pairs have differences in one
residue modulo $`g`$, with at most $`\lceil X/g\rceil`$ possible values.
By $`H^2>\lceil X/g\rceil`$, some difference has two representations.
Since the low and high intervals are disjoint, two representations of the
same difference are vertex-disjoint. This proves the required double-pair
supply after all prior reservations.

The same argument with class $`-1`$ below and $`+1`$ above gives double
pairs of difference $`2\bmod g`$ for the diagonal residue repairs.
Ordinary residue repairs require only one low--high pair at a time.
This uses the same global deletion charge $`B`$, including all future
diagonal reservations. No independence or random allocation of primes
is assumed.

The exact count of reserved entries is bounded as follows.

| Purpose | Number of entries, bounded above |
|---|---:|
| At most $`64n`$ ordinary reservoirs, $`P+7K`$ pairs each | $`128n(P+7K)`$ |
| Two main diagonal reservoirs, $`P+7K`$ double pairs each | $`8(P+7K)`$ |
| Row and column residue paths | $`4(n-1)(h-1)`$ |
| Both diagonal residue families | $`8(h-1)`$ |
| Total | $`B=(128n+8)(P+7K)+4(n+1)(h-1)`$ |

The input counts $`B+M,B+H`$ are intentionally conservative: even if every
already reserved entry belonged to the currently needed class and interval,
the relevant supply still remains.

## 3. Graph, rectangles and placement

### The expander constant is a finite calculation

Take 32 independent uniform permutations of $`n`$ vertices. Retain every
undirected edge $`v,\pi_j(v)`$ with multiplicity and discard loops. The degree
is at most 64. For a fixed set $`S`$ of size $`s\le n/2`$, put $`p=s/n`$.
The probability that any specified $`k`$ domain points in one copy of $`S`$
all map into $`S`$ is $`(s)_k/(n)_k\le p^k`$; independence gives the
same bound across the 32 permutations. If fewer than $`4s`$ directed edges
leave $`S`$, at least $`28s`$ of its $`32s`$ images stay inside. A union bound
therefore bounds this event by $`\binom{32s}{28s}p^{28s}`$.
Using $`\binom ns\le(en/s)^s`$ and
$`\binom{32s}{28s}\le\exp(32s\mathcal H(1/8))`$, where
$`\mathcal H(t)=-t\log t-(1-t)\log(1-t)`$, the total failure probability is
at most $`\sum_{s=1}^{\lfloor n/2\rfloor}r^s`$, with


```math
r=e\,e^{32\mathcal H(1/8)}2^{-27}
   =e\,\frac{2^{69}}{7^{28}}.                             \qquad\text{(FC6)}
```


Since $`e<3`$ and $`250\cdot3\cdot2^{69}<7^{28}`$, one has
$`r<1/250`$ and $`r/(1-r)<1/249<1`$. The entropy identity is
$`e^{32\mathcal H(1/8)}=8^{32}/7^{28}`$.
Thus some choice has at least $`4s`$ directed edges leaving every such $`S`$.
Each permutation has equally many edges entering and leaving a cut, so the
undirected edge boundary has size at least $`8\min(s,n-s)`$.
This establishes the graph for every $`n\ge2`$, independently of the prime supplies.

A finite construction specification is enough for existence: enumerate
32-tuples of permutations of $`\{0,\ldots,n-1\}`$, compute all cuts with
multiplicities, and stop at the first passing graph. The positive counting
argument proves this finite search terminates. No efficiency is claimed.

### Joint rectangle placement

There are at most $`J`$ rectangles. Use mutually distinct rows and mutually
distinct columns across all main and residue rectangles on both diagonals.
After placing $`t`$ rectangles, exactly $`2t`$ rows and $`2t`$ columns are
used. For the next rectangle, let its designated diagonal map be
$`f(i)=i`$ or $`n-1-i`$, and the other map be $`h_*(i)=n-1-f(i)`$.

Choose its designated cell $`(i,f(i))`$. At most $`4t+1`$ choices of $`i`$
are excluded by used rows, used columns, and the center. Choose the second
row $`j`$ avoiding the used rows and $`i,n-1-i`$; at most $`2t+2`$
choices are excluded. Choose the second column $`k`$ avoiding used columns
and the at most four values
$`f(i),f(j),h_*(i),h_*(j)`$. At most $`2t+4`$ choices are excluded.
The condition $`n>4J`$ makes each choice possible, including $`J=1`$.

The designated cell is the only cell on its chosen diagonal, and no cell
is on the opposite diagonal. Every row and column meets at most one
rectangle, hence at most two rectangle cells.

The equal-gap trade is


```math
\begin{pmatrix}a&a+d\\b+d&b\end{pmatrix}
 \longleftrightarrow
 \begin{pmatrix}a+d&a\\b&b+d\end{pmatrix}.
```


It preserves both row sums and both column sums and changes the designated
diagonal by exactly $`d`$. Its fixed row/column sums are sums of pair
midpoints. The second diagonal is unchanged.

### Ordinary pairs in separate passes

Embed row prefixes, column prefixes, row wide pairs, column wide pairs,
row residue-path pairs, and column residue-path pairs in separate passes.
The corresponding multigraph degrees are at most


```math
64P,\quad64P,\quad448K,\quad448K,\quad2(h-1),\quad2(h-1).
```


For a row-pair pass of degree at most $`D`$, assign each edge to a column,
using at most $`D`$ edges in that column. There are at most $`nD/2`$
edges in the pass, so at most $`n/2`$ columns are full. The two endpoint
rows rule out at most $`2L`$ columns through occupied cells. At most four
further columns put an endpoint on a diagonal. Thus
$`n/2>2L+4`$, which is exactly implied by $`n>4L+8`$, guarantees a
legal column. Transpose for a column-pair pass.

This global cap is valid during each pass because the final row and column
loads are bounded by


```math
\underbrace{192P}_{\text{prefixes}}+
 \underbrace{1344K}_{\text{wide pairs}}+
 \underbrace{6(h-1)}_{\text{residue paths}}+
 \underbrace{2}_{\text{rectangles}}
 =L.                                                     \qquad\text{(FC7)}
```


For example, a row contains at most $`64P`$ endpoints from its own prefix
pass and at most $`2\cdot64P`$ entries from the transposed pass. Separating
prefix and wide passes is essential: a bound on their combined load would
not control how many uncontrolled prefix entries land in one line.

All supports are disjoint, and all ordinary pairs avoid both diagonals.
The operations commute as permutations of disjoint entries.

## 4. Exact transfers and residues

For any completed ordinary reservoir, write $`R`$ for its total difference.
Every $`q\in[0,R]\cap g\mathbb Z`$ is a subset sum. The two endpoint
contributions are


```math
\sum p_j+R-q,\qquad \sum p_j+q.
```


Taking $`q_0=g\lfloor R/(2g)\rfloor`$ puts each within $`g/2`$ of the sum
of the pair midpoints, since $`R/g`$ is an integer. It leaves every signed
transfer of magnitude at most $`g\lfloor KX/g\rfloor`$ available.

Give each graph edge the integral capacity $`C=\lfloor KX/g\rfloor`$.
Every zero-total integer demand vector with coordinates at most $`8C`$
in absolute value satisfies all cut inequalities: for every $`S`$,
$`|\sum_{v\in S}b_v|\le8C\min(|S|,n-|S|)\le C|\partial S|`$.
Use capacity $`C`$ in both directions on each edge. Integral max-flow/min-cut
realizes the demands; cancel opposing flows to obtain one signed integral
flow in $`[-C,C]`$ on each edge. Because $`KX\ge2g`$, each required row or column
correction of magnitude at most $`KX/2`$, divided by $`g`$, is within
this box. Row switches preserve columns; column switches preserve rows.

Each diagonal reservoir has the analogous complete grid. Its midpoint
configuration provides the symmetric range
$`[-KX+g,KX-g]\cap g\mathbb Z`$, which contains every required diagonal
correction of magnitude at most $`KX/2`$.

It remains to make the baseline residues units. With $`h=g/2`$, put
$`h-1`$ difference-$`2\bmod g`$ pairs on each edge of a directed path.
The reference orientation has the larger entry at the source. For desired
even residue corrections, write $`b_i`$ for their halves modulo $`h`$;
their total is zero. On edge $`i\to i+1`$, swap the first


```math
k_i\equiv-\sum_{j\le i}b_j\pmod h,\qquad0\le k_i<h
```


pairs. At vertex $`i`$ this gives $`k_{i-1}-k_i=b_i\bmod h`$.
Thus all residue demands are realized. Each row or column changes in
absolute value by at most $`2(h-1)X=(g-2)X`$.

There are $`n`$ unit residues with sum $`T\bmod g`$. Take $`n-3`$ ones
and put $`A=T-(n-3)`$, which is odd. For each odd prime divisor $`q\mid g`$,
choose $`y\not\equiv0,A-1\pmod q`$, and choose $`y`$ odd modulo the
power of 2. The Chinese remainder theorem gives three units
$`1,y,A-1-y`$. Apply the path construction separately to rows and columns.

Each diagonal has $`h-1`$ residue rectangles. Swapping the first $`k`$
of them gives every even residue correction, so each odd diagonal sum
can be made $`1\bmod g`$, at cost at most $`(h-1)X`$.
For $`g=2`$, all residue families are empty. Small prime factors of $`g`$
that belong to the original pool are still placed in the unreserved cells;
no entry is deleted from the problem.

## 5. Centering with an evaluated error

Put every main reservoir at its midpoint subset. Initially leave all residue
controls in the reference orientation. Let $`r_Q`$ be the reserved cell
count on line $`Q`$ and $`C_Q`$ their sum. Then


```math
|C_Q-r_Qm|\le eX,\qquad
 e=2000\delta K+192P+3g+28.                              \qquad\text{(FC8)}
```


Here is the complete invoice.

| Contribution on a row or column | Bound after division by $`X`$ |
|---|---:|
| Own and perpendicular uncontrolled prefixes | $`192P`$ |
| Own and perpendicular wide midpoints | $`1344\delta K`$ |
| Midpoint rounding on at most 64 own bundles | $`32g/X\le32`$ |
| Residue-path entries before repair | $`6(h-1)=3g-6`$ |
| At most one rectangle | $`2`$ |

Their sum is at most $`1344\delta K+192P+3g+28`$, which is bounded
by (FC8). A diagonal has at most
$`P+7\delta K+(h-1)+g/(2X)`$ in the same units, also bounded by (FC8).
The constant 2000 leaves slack in both bounds.

There are at least $`n^2/2`$ unreserved entries. Their mean $`m_0`$
satisfies $`|m_0-m|\le2eX/n`$: sum (FC8) over rows, then divide the
total reserved deviation by the remaining pool size. Uniformly permute
the remaining entries into the remaining cells. Each line then satisfies


```math
|\mathbb E S_Q-\mu|\le3eX.                              \qquad\text{(FC9)}
```



A line's unreserved entries are a sample without replacement. Reveal them
successively; the conditional-expectation martingale has increments of
absolute value at most $`X`$. The bounded-increment estimate gives


```math
\Pr(|S_Q-\mathbb E S_Q|>u)
 \le2\exp[-u^2/(2nX^2)].
```


With $`u=3X\sqrt{n\log n}`$, the union bound over $`2n+2`$ lines is
$`(4n+4)n^{-9/2}<1`$ for **every $`n\ge2`$**. Indeed,
$`4n+4\le6n`$, and $`6n^{-7/2}<1`$ follows from
$`36<n^7`$, valid already at $`n=2`$.

Some completion therefore has all deviations at most
$`3eX+3X\sqrt{n\log n}`$. Residue repairs add at most $`(g-2)X`$.
Substituting (FC8) gives exactly (FC4). The universal transfer statement
then follows from the disjoint networks and rectangles in Section 4.
This proves Theorem FC.


## 6. A fully evaluated controller regime: PC3

Continue to use the exact pool, notation and definitions in
[the main note](README.md#the-conjecture) and FC:


```math
X=p_{n^2+1},\quad T=\sum_{p\in P_n}p,\quad
 m=T/n^2,\quad \mu=T/n,\quad E=\lceil\log_2X\rceil .
```



**Corollary PC3.** Suppose $`n`$ is odd and


```math
n\ge2^{\,2^{40}},\qquad n^2\le X\le n^3,\qquad
 2X/5\le m\le3X/5.
```


Put


```math
\delta=10^{-7},\qquad K=\lfloor n/E^3\rfloor,\qquad
 I_\pm=[m\pm X/4-\delta X,\ m\pm X/4+\delta X].
```


Suppose that for some even $`2\le g\le16E`$ and reduced class $`a\bmod g`$:

1. $`P_n`$ contains at least $`\lfloor X/(2048E^3)\rfloor`$ disjoint
   pairs $`(p,p+g)`$ with lower endpoint in class $`a\bmod g`$.
2. The number of pool primes in class $`a\bmod g`$ is at least
   $`X/(64E^2)`$.
3. Each $`I_-,I_+`$, in each needed class $`a,-1,+1\bmod g`$, contains
   at least $`X/(320000000E^2)`$ pool primes.

Then FC's complete conclusion holds for this $`K,g`$: there is a baseline
permutation of exactly $`P_n`$, all required sums are units modulo $`g`$
and within $`KX/10`$ of $`\mu`$, and every compatible integer target vector
within $`KX/2`$ of that baseline is realized. Row and column target totals
must both equal the actual $`T`$; the two diagonal targets are independently
prescribed.

The hypotheses are uniform in the class and gap selected by the seed source.
The exact pool, both diagonal constraints, and both exact-total constraints
are retained.

### 6.1 Domain, floors and prefix quantities

Set $`v=\log_2n`$. From $`n^2\le X\le n^3`$ one has


```math
E\ge2v,\qquad E\le3v+1\le4v.
```


At $`v_0=2^{40}`$,


```math
v_0>204\log_2(4v_0)=204\cdot42.
```


The function $`v-204\log_2(4v)`$ is increasing for $`v\ge v_0`$,
because $`\log2>2/3`$ and $`v_0>306`$. Consequently the entire domain
of PC3 satisfies


```math
\boxed{E\ge2^{40},\qquad n\ge E^{204}.}                 \qquad\text{(I1)}
```


This proves the tail while allowing the ceiling defining $`E`$ to jump.
No monotonicity of the floor defining $`K`$ is assumed.

Define exactly as in FC


```math
M=\left\lfloor\frac{X}{128E^2}\right\rfloor,\qquad
 H=\left\lfloor\frac{X}{640000000E^2}\right\rfloor,
```




```math
s=\left\lceil\frac{4X}{gM}\right\rceil,\qquad
 P=s+\left\lceil\frac{32XE}{gM}\right\rceil .
```


Since $`X\ge n^2\ge E^{408}`$, each quantity being floored is at least 2,
and


```math
M\ge\frac{X}{256E^2},\quad
 H\ge\frac{X}{1280000000E^2},\quad
 s\le768E^2,\quad P\le5120E^3.                           \qquad\text{(I2)}
```


The derivations of these numerical prefix bounds use only $`X,E,g,M`$,
not $`K`$. For example
$`s\le512E^2+1`$ and
$`\lceil32XE/(gM)\rceil\le4096E^3+1`$, which imply (I2).
These are direct inequalities from FC.

All prefix, double-pair and seed conditions are unchanged:


```math
sg\le1040E^2\le X,\qquad
 \frac{gM}{16X}\le\frac1{128E}\le1,
```




```math
M^2g\ge\frac{X^2}{32768E^4}\ge48X,\qquad
 H^2>X\ge\lceil X/g\rceil.                              \qquad\text{(I3)}
```


The sufficient positive-power comparisons are


```math
E^{406}\ge1040,\quad E^{404}\ge1572864,\quad
 E^{404}>(1280000000)^2.
```


They hold at $`E=2^{40}`$ and persist.

The seed matching contains at least $`X/(4096E^3)`$ pairs, after paying its
floor. The demand is at most


```math
(64n+4)s\le52224nE^2.
```


Thus $`n\ge213909504E^5`$, implied by
$`E^{199}\ge213909504`$ and (I1), supplies every ordinary seed and both
physical pairs in each diagonal seed group.

The enlarged reservoir parameter satisfies


```math
\frac{n}{2E^3}\le K\le\frac n{E^3},                     \qquad\text{(I4)}
```


because $`n/E^3\ge E^{201}\ge2`$. The total-difference capacity is still
obtained by at most $`7K`$ macro stages per bundle, by FC's bound for every
positive integer $`K`$.

### 6.2 Complete reserved-pool depletion

FC's full count is unchanged:


```math
B=(128n+8)(P+7K)+4(n+1)(g/2-1).
```


Using (I2)--(I4), $`128n+8\le136n`$, and $`g\le16E`$,


```math
B\le696384nE^3+952nK
 \le696384nE^3+\frac{952n^2}{E^3}.
```


Therefore


```math
\frac{E^2B}{n^2}
 \le\frac{696384E^5}{n}+\frac{952}{E}
 \le\frac{696384}{E^{199}}+\frac{952}{E}
 \le\frac1{640000000}.                                 \qquad\text{(I5)}
```


The upper-bound expression $`696384/E^{199}+952/E`$ decreases with $`E`$.
At $`E=2^{40}`$ it is strictly below
$`1/640000000`$, as the following exact integer comparisons show:


```math
5\cdot952\cdot640000000<3\cdot2^{40},\qquad
 5\cdot696384\cdot640000000<2\cdot2^{40\cdot199}.
```


The two summands therefore contribute less than $`3/5`$ and $`2/5`$ of the
allowed bound, respectively. This proves (I5) on the entire domain.

It follows that


```math
B\le\frac{n^2}{640000000E^2}
 \le\frac{X}{640000000E^2},\qquad B<n^2/2.               \qquad\text{(I6)}
```


The raw global count leaves at least $`M`$, because


```math
\frac1{64}-\frac1{640000000}\ge\frac1{128}.
```


Each raw interval/class count leaves at least $`H`$, because


```math
\frac1{320000000}-\frac1{640000000}
 =\frac1{640000000}.
```


Thus every supply used by FC is available after the **entire** reserved pool
has been charged, including both kinds of diagonal rectangles, both residue
paths, all prefix entries, and every wide pair. Enlarging $`K`$ has not
silently depleted a rare class or an interval.

### 6.3 Placement, centering and capacity

FC's line-load and joint rectangle bounds remain


```math
L=192P+1344K+3g-4,\qquad
 J=2(P+7K+g/2-1).
```


They now give


```math
\frac{4L+8}{n}
 \le\frac{3932360}{E^{201}}+\frac{5376}{E^3}<1,          \qquad\text{(I7)}
```




```math
\frac{4J}{n}
 \le\frac{40960}{E^{201}}+\frac{56}{E^3}
       +\frac{64}{E^{203}}<1.                          \qquad\text{(I8)}
```


These inequalities certify every separate pair pass and the joint placement
of all main and residue rectangles. The geometric argument itself is FC's
unchanged proof. Both rational expressions decrease for $`E\ge2^{40}`$.

Also


```math
KX\ge\frac{n^3}{2E^3}\ge\frac{E^{609}}2\ge32E\ge2g,
```


where $`E^{608}\ge64`$ suffices. Hence the signed reservoirs still contain
the entire required correction box, including both diagonals.

The only centering condition in FC is


```math
6000\delta K+576P+10g+82+3\sqrt{n\log n}<K/10.
```


Divide by $`K`$ and use (I1)--(I4). The prefix and residue terms satisfy


```math
\frac{576P}{K}\le\frac{5898240}{E^{198}},\qquad
 \frac{10g+82}{K}\le\frac{484}{E^{200}}.
```


Since $`\log n\le E`$, the fluctuation term satisfies


```math
\frac{3\sqrt{n\log n}}K
 \le\frac{6E^3\sqrt E}{\sqrt n}
 \le\frac6{E^{98}}.
```


Consequently the complete invoice is


```math
\boxed{\frac3{5000}
       +\frac{5898240}{E^{198}}
       +\frac{484}{E^{200}}
       +\frac6{E^{98}}<\frac1{10}.}                    \qquad\text{(I9)}
```


At $`E=2^{40}`$ each of the three nonconstant terms is less than $`1/1000`$,
so the left side is less than $`3/5000+3/1000<1/10`$. Each term decreases. This pays the increased reservation and every
centering contribution without changing the concentration argument.

The mean range still puts $`I_\pm`$ inside $`(1,X)`$: their extreme
normalized endpoints lie between $`3/20-\delta`$ and $`17/20+\delta`$.
All finite hypotheses of FC have now been proved from PC3's stated inputs.
Applying FC proves Corollary PC3.
