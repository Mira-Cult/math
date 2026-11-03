**Public reading copy.** Presentation and links have been normalized. Historical status statements below belong to their source revisions; see the [current publication status](../../README.md#review-and-verification-status). The matching original bytes are in the [source archive](../../originals/manuscripts/incidence.md).

# Incidence, integer compatibility, and quantitative numeric capacity

This manuscript contains the incidence component of the prime-array assembly.
The results here concern integer arrays, with signed entries allowed. They do
**not** assert that their integer lifts are permutations of a prescribed pool.
The permutation realization is a separate obligation. All arguments below are
self-contained; the accompanying code uses exact rational arithmetic.

## 1. Axis marginals and their integer image

Write $`V=\mathbb Z^{[n]}`$, and let $`\epsilon:V\to\mathbb Z`$ sum the
coordinates. The axis-line map is


```math
M=(S_1,\ldots,S_D):V^{\otimes D}\longrightarrow
       \bigoplus_{d=1}^D V^{\otimes([D]\setminus\{d\})},
```


where $`S_d`$ sums coordinate $`d`$. A proposed line vector is
$`y=(y_1,\ldots,y_D)`$, where $`y_d`$ is indexed by the other coordinates.

### Axis-image theorem

For every $`D,n\geq1`$, an integer vector $`y`$ lies in the image of $`M`$
if and only if


```math
S_e y_d=S_d y_e\qquad(d\ne e).                 \qquad\text{(1)}
```


The equations are equalities of arrays on the remaining $`D-2`$ coordinates.
Consequently the integer image is saturated, and


```math
\mathrm{rank}_{\mathbb Q}M=n^D-(n-1)^D,
 \qquad \ker_{\mathbb Z}M=(\ker\epsilon)^{\otimes D}. \qquad\text{(2)}
```


**Proof.** Necessity follows by commuting sums. Set $`e=e_n`$ and
$`K=\ker\epsilon`$. Since $`\epsilon(e)=1`$, there is an integral direct sum
$`V=K\oplus\mathbb Ze`$. Tensoring gives one summand for each subset
$`I\subseteq[D]`$: factors in $`I`$ are in $`K`$, and the others are in
$`\mathbb Ze`$. The $`d`$-th marginal retains exactly the summands with
$`d\notin I`$. Equation (1) says that the copy of such a summand read from
any available marginal is the same. Assign this common component to the
corresponding summand of the full array, for every proper $`I`$; assign zero
to the all-$`K`$ summand. This is an integral preimage. The all-$`K`$ summand
is exactly the kernel. Its rank is $`(n-1)^D`$, proving (2). Since the image
is defined by integer homogeneous equalities, it is saturated. $`\square`$

For a cube, put
$`A_{jk}=\sum_i x_{ijk}`$, $`B_{ik}=\sum_j x_{ijk}`$, and
$`C_{ij}=\sum_k x_{ijk}`$. The complete compatibility equations are


```math
\sum_jA_{jk}=\sum_iB_{ik},\quad
 \sum_kA_{jk}=\sum_iC_{ij},\quad
 \sum_kB_{ik}=\sum_jC_{ij}.                       \qquad\text{(3)}
```


There are $`3n`$ displayed equations with exactly one linear dependency,
so their rank is $`3n-1`$. In particular, matching just the three grand
totals omits $`3n-3`$ independent conditions. With a fixed entry-pool total
$`T`$, add $`\sum A=T`$; the other grand totals then equal $`T`$.

An integral basis of the kernel consists of the $`2^D`$-cell checkerboards


```math
(e_{i_1}-e_n)\otimes\cdots\otimes(e_{i_D}-e_n),
 \qquad i_1,\ldots,i_D\lt n.                         \qquad\text{(4)}
```


These preserve all line sums; they are not themselves a supply of useful
prescribed-pool swaps.

### Congruence refinement

For integers $`a`$ and $`m\geq1`$, an axis target has a lift with every
entry congruent to $`a\pmod m`$ exactly when (1) holds and every line
target is congruent to $`na\pmod m`$. Apply the theorem to
$`(y_d-na)/m`$, then set $`x=a+mz`$. Thus for odd $`n`$, odd targets have
an odd integer lift. This removes no exact-pool or positivity obligation.

## 2. Balanced lifting with dimension-only rounding loss

The anchored direct-sum proof can place a large correction in a few cells.
The next result supplies a quantitative lift throughout the complete grid.
Write $`\|\cdot\|_\infty`$ for the largest absolute coordinate.

### Bounded integer lifting theorem

Let $`D\geq2`$, and let compatible integer axis targets satisfy
$`\max_d\|y_d\|_\infty\leq\delta`$. There is an integer array $`x`$ with
those targets and


```math
\|x\|_\infty \lt  (2^D-1)\delta/n+C_D,             \qquad\text{(5)}
```


where one may use $`C_2=1`$, $`C_3=2`$, and
$`C_D=2\cdot5^{D-3}`$ for $`D\geq3`$. More generally, every real array
whose axis marginals are integers has an integer array with exactly the
same marginals at coordinatewise distance less than $`C_D`$. Rational
inputs admit a finite algorithm using rational arithmetic and bipartite
integer flows.

The constants are convenient bounds, with no claim of optimality.

#### Balanced rational preimage

For nonempty $`J\subseteq[D]`$, let $`y_J`$ denote the common marginal
obtained from any $`y_d`$, $`d\in J`$, by summing the coordinates in
$`J\setminus\{d\}`$. Compatibility makes this well-defined. Extend it
constantly in the coordinates in $`J`$, divided by $`n^{|J|}`$. Then


```math
x^{\rm rat}=\sum_{\varnothing\ne J\subseteq[D]}
       (-1)^{|J|+1}\frac{y_J}{n^{|J|}}             \qquad\text{(6)}
```


has all the desired marginals. In a marginal $`S_d`$, terms indexed by
$`J\not\ni d`$ cancel against those indexed by $`J\cup\{d\}`$, leaving
$`y_d`$. Also $`\|y_J\|_\infty\leq n^{|J|-1}\delta`$, so every term in
(6) has norm at most $`\delta/n`$. This proves the rational part of (5).

#### Matrix rounding lemma

If a real matrix has integral row and column sums, it can be rounded to
an integer matrix with the same margins, each entry rounded to its floor
or ceiling. Subtract entrywise floors. The remaining fractional matrix
is a feasible flow in a bipartite network: source-to-row capacities are
the required integer row sums; fractional positions have capacity one;
column-to-sink capacities are the required integer column sums. An
integer maximum flow attains the same total. For completeness, repeatedly
augment an integral flow along a residual source-to-sink path; if no such
path exists, reachable vertices give a cut proving maximality. Since the
fractional feasible flow attains the prescribed total, the final integral
flow does also. Adding floors proves the assertion, with error less than
one in each entry.

#### Balanced splitting of a zero-margin matrix

If an integer matrix $`R`$ has zero row and column sums and $`m\geq1`$,
it is a sum of $`m`$ integer zero-margin matrices, each entry equal to
$`\lfloor R_{ij}/m\rfloor`$ or $`\lceil R_{ij}/m\rceil`$.

To see this, put $`a_{ij}=\lfloor R_{ij}/m\rfloor`$ and
$`b=R-ma`$. The row and column sums of $`b`$ are $`m`$ times the
nonnegative integer demands $`-\sum_j a_{ij}`$ and $`-\sum_i a_{ij}`$.
Round $`b/m`$ by the matrix lemma. The resulting $`0/1`$ matrix $`E`$
has those demands. Subtract $`E`$ from $`b`$ and replace $`m`$ by
$`m-1`$. Entries that were at either endpoint zero or $`m`$ are forced
correctly by the rounding; hence the remaining entries lie between zero
and $`m-1`$. Repeat. Every $`a+E`$ has zero margins, and their sum is
the original $`R`$.

#### Cube rounding with error less than two

Let $`x`$ be a real cube whose three families of line sums are integral.
Round each fixed-$`k`$ matrix slice using the matrix lemma. Call the
result $`z`$. Its first two directional families are correct, and
$`|z_{ijk}-x_{ijk}|\lt 1`$. The third-family residual


```math
R_{ij}=\sum_k(x_{ijk}-z_{ijk})
```


is an integer zero-row/column matrix with $`|R_{ij}|\lt n`$. Split it into
$`n`$ zero-margin matrices by the preceding lemma. Every resulting
entry lies in $`\{-1,0,1\}`$. Add one piece to each slice of $`z`$.
This corrects the third family without changing the first two, and total
rounding error is strictly less than two. Formula (6) then gives
$`\|x^{\rm int}\|_\infty\lt 7\delta/n+2`$.

#### General-dimensional rounding

Suppose integer-margin rounding with error less than $`C`$ is available
for $`(D-1)`$-arrays. First note a splitting consequence. Any integer
zero-margin $`(D-1)`$-array $`R`$ can be split into $`m`$ integer
zero-margin arrays, each at distance less than $`3C`$ from $`R/m`$.
Recursively split a node assigned $`k`$ pieces into groups of sizes
$`\lfloor k/2\rfloor`$ and $`\lceil k/2\rceil`$. Round the first
proportional share while preserving its zero margins; assign the residual
to the second group. The local allocation error has norm less than $`C`$.
Its contribution to a final leaf is at most $`C/l`$, where $`l`$ is
the number of leaves in the chosen child. Along any root-to-leaf path,
the reciprocals of child sizes sum to less than three: read backwards,
the sizes start with 1, are next at least 2, and subsequently grow at
least by $`s\mapsto2s-1`$, giving
$`1+\sum_{j\geq0}(2^j+1)^{-1}\lt 3`$. This proves the splitting bound.

Now round each slice of a $`D`$-array separately, with error less than
$`C`$. The remaining last-direction residual is an integer zero-margin
$`(D-1)`$-array of norm less than $`nC`$. Split it into $`n`$ pieces
as above. Each piece has norm less than $`4C`$; adding the pieces to the
slices gives total error less than $`5C`$. Starting with the cube result
proves the stated $`C_D`$, and completes the theorem. $`\square`$

### Numeric interior consequence

If a real solution has every entry in $`[L+C_D,U-C_D]`$, the theorem
produces an integer solution in $`[L,U]`$, with unchanged margins.
This is a useful sign and capacity statement. It still provides neither
distinct entries nor membership in a specified prime pool.

## 3. Sparse graph products and checkerboard capacity

A correction that changes only directional family $`d`$, preserving all
other families, must have zero margins in each coordinate of its target
$`(D-1)`$-array. Conversely, each elementary tensor of differences in
those coordinates can be realized numerically on one perpendicular
section. In a cube this is an ordinary four-cell checkerboard rectangle.
The following result gives bounded coefficients using only a sparse
family of such rectangles.

### Tensor-expander coefficient theorem

Let $`G`$ be a connected loopless undirected multigraph on $`n\geq2`$
vertices, of maximum degree at most $`\Delta`$; parallel edges are
allowed and counted in degrees.
Orient its edges arbitrarily and let $`B`$ be the $`n`$-by-$`m`$
incidence matrix with one $`+1`$ and one $`-1`$ per column. Let
$`P=I-BB^{\mathsf T}/(2\Delta)`$ be the symmetric lazy stochastic
matrix, and suppose its spectral gap on the zero-sum subspace is at
least $`\gamma\gt 0`$. Set


```math
\tau=\left\lceil\frac{\log n}{2\gamma}\right\rceil,
 \qquad L=\frac{2\tau+1/\gamma}{\Delta}.           \qquad\text{(7)}
```


For every integer $`n`$-by-$`n`$ matrix $`D`$ with zero row and column
sums and $`\|D\|_\infty\leq\delta`$, there is an integer
$`m`$-by-$`m`$ matrix $`F`$ such that


```math
BFB^{\mathsf T}=D,
 \qquad \|F\|_\infty\leq
 L^2\delta+\tfrac12+\frac{\Delta^2n^2}{8}.        \qquad\text{(8)}
```


Thus a bounded-degree, fixed-gap graph provides $`O(n^2)`$ checkerboard
types with coefficient capacity $`O(\delta\log^2n+n^2)`$. This theorem
is conditional on the stated graph hypothesis; it does not assert a
graph family or an associated supply of prime gadgets.

**Proof.** Put $`J=\mathbf1\mathbf1^{\mathsf T}/n`$. The convergent
operator


```math
R=\frac1{2\Delta}B^{\mathsf T}\sum_{t\geq0}(P^t-J)
```


satisfies $`BR=I-J`$, because
$`BB^{\mathsf T}=2\Delta(I-P)`$. The row-sum norm satisfies


```math
\|P^t-J\|_{\infty\to\infty}
 \leq \min\{2,\sqrt n(1-\gamma)^t\}.
```


Indeed, the first bound follows from stochasticity and the second from
the spectral bound followed by Cauchy--Schwarz on each row. Summing the
first bound up to $`\tau-1`$, then the geometric tail, gives
$`\sum_t\|P^t-J\|_{\infty\to\infty}\leq2\tau+1/\gamma`$.
Since $`\|B^{\mathsf T}\|_{\infty\to\infty}=2`$,
$`\|R\|_{\infty\to\infty}\leq L`$.

The real coefficient array $`F_0=RDR^{\mathsf T}`$ satisfies
$`BF_0B^{\mathsf T}=D`$ and has norm at most $`L^2\delta`$.
Round every entry of $`F_0`$ to a nearest integer, obtaining $`F_1`$.
The integer residual $`H=D-BF_1B^{\mathsf T}`$ has zero margins and
$`\|H\|_\infty\leq\Delta^2/2`$, since each matrix entry sees at most
$`\Delta^2`$ rounding errors of magnitude at most one half.

Choose a spanning tree, rooted arbitrarily. The tree flow operator
$`S`$ maps a zero-sum vector to its signed subtree sums, giving
$`BSv=v`$ on zero-sum vectors. Embed it into all graph edges by zero
on non-tree edges. Then $`SHS^{\mathsf T}`$ is an integer correction.
Every coefficient is a signed sum of $`H`$ over the product of two
tree cuts. Because $`H`$ has zero row and column sums, either side of
each cut may be used, up to sign; choose the smaller sides. Each has
size at most $`n/2`$. Hence


```math
\|SHS^{\mathsf T}\|_\infty
 \leq \frac{n^2}{4}\|H\|_\infty
 \leq \frac{\Delta^2n^2}{8}.
```


Set $`F=F_1+SHS^{\mathsf T}`$. This proves (8). $`\square`$

The same proof for a $`k`$-tensor $`D`$ with every coordinate marginal
zero gives integer coefficients on $`E(G)^k`$, using
$`B^{\otimes k}F=D`$, with


```math
\|F\|_\infty\leq L^k\delta+\tfrac12
                     +\frac{(\Delta n)^k}{2^{k+1}}. \qquad\text{(9)}
```


There are $`m^k=O_\Delta(n^k)`$ generator types. Rounding creates
residual at most $`\Delta^k/2`$; the tree-product correction uses the
smaller side of each cut. The degree and spectral-gap hypotheses matter.

### From edge expansion to the required spectral gap

Suppose every set of at most $`n/2`$ vertices has at least $`h|S|`$
edges leaving it, counting multiplicity. Then the above symmetric lazy
walk has spectral gap at least


```math
\gamma=\frac{h^2}{4\Delta^2}.                  \qquad\text{(9a)}
```


Here is a direct proof. For a nonnegative function $`f`$ supported on
at most half the vertices, summing boundaries of level sets of $`f^2`$
gives


```math
h\sum_v f_v^2\leq\sum_{uv\in E}|f_u^2-f_v^2|
 \leq\left(\sum_{uv\in E}(f_u-f_v)^2\right)^{1/2}
       \left(2\Delta\sum_vf_v^2\right)^{1/2}.
```


Thus its Dirichlet energy is at least
$`h^2/(2\Delta)\sum_vf_v^2`$. For a zero-mean real function $`v`$,
subtract a median and apply this bound to the positive and negative
parts. Each is supported on at most half the vertices. Their energies
sum to at most the energy of $`v`$, whereas their squared norms sum
to $`\sum(v-\mathrm{med}v)^2\geq\sum v^2`$. Hence
$`\lambda_2(BB^{\mathsf T})\geq h^2/(2\Delta)`$. Dividing by
$`2\Delta`$ proves (9a). The walk has nonnegative spectrum because
$`\sum_{uv}(v_u-v_v)^2\leq2\Delta\sum_vv_v^2`$.

In particular, the combination $`\Delta=64`$, $`h=8`$ permits
$`\gamma=1/256`$,


```math
L\leq4\log n+129/32\leq5\log n+5,
 \qquad \Delta^2n^2/8=512n^2.                    \qquad\text{(9b)}
```


This verifies the coefficient theorem's hypotheses for any graph with
those two combinatorial bounds; the graph's existence and physical
placement remain separate inputs.

### Physical meaning and remaining obligations

For a perpendicular $`(D-1)`$-dimensional checkerboard, an integer
coefficient multiplied by a gap $`g`$ can be effected by simultaneously
swapping $`2^{D-2}`$ disjoint equal-gap pairs, with appropriate signs.
Every such pair contributes one positive and one negative corner. The
coefficient theorem itself does not supply those pairs, their signs,
their disjoint placement, or enough reusable capacity for its coefficients.
Those are pool and packing hypotheses of the physical controller.

## 4. Signed-coordinate line and section counts

For $`n\geq3`$, an $`r`$-dimensional signed-coordinate section is
specified canonically by: the set of $`k`$ varying coordinate positions;
a partition of those positions into $`r`$ nonempty parameter blocks;
relative signs within each block (normalize its least coordinate to
positive); and a fixed value in $`[n]`$ for every remaining coordinate.
Consequently the number of distinct sections is


```math
N_{D,r}(n)=\sum_{k=r}^D {D\choose k}
       n^{D-k}\,\left\{\!{k\atop r}\!\right\}\,2^{k-r}, \qquad\text{(10)}
```


where the braces denote Stirling numbers of the second kind. The
representation is unique: a coordinate projection reveals whether it is
fixed; two varying coordinates belong to one parameter block exactly
when their joint projection is an equality or reversed-equality graph,
rather than all of $`[n]^2`$. Relative signs are then recovered.

In particular the signed-line count is


```math
N_{D,1}(n)=\frac{(n+2)^D-n^D}{2}.
```


For a cube this is $`3n^2+6n+4`$; the two-dimensional section count
is $`3n+6`$. The $`3n`$ axis slices include all interior slices. The
six others are diagonal squares, each with two independent parameters;
they are not body diagonals. Summing (10) for $`1\leq r\lt D`$ gives
$`O_D(n^{D-1})`$ distinct proper sections. This counts constraints and
does not assert their prime feasibility.

## 5. Cyclic windows: the whole integer image and an exact box test

Put $`N=n^2`$, index cells cyclically by $`0,\ldots,N-1`$, and define
$`w_i=\sum_{j=0}^{n-1}x_{i+j}`$, with indices modulo $`N`$. Write
$`P_r=\sum_{k=0}^{n-1}w_{r+kn}`$ for $`0\leq r\lt n`$.

### Window-image theorem

The integer image consists exactly of the vectors satisfying


```math
P_0=P_1=\cdots=P_{n-1}.                          \qquad\text{(11)}
```


It is saturated, has rational rank $`N-n+1`$, and has kernel precisely
the period-$`n`$ vectors whose one-period sum is zero.

**Proof and reconstruction.** Necessity follows because each offset
partition sums all cells. The difference equations are


```math
x_{i+n}-x_i=w_{i+1}-w_i.                         \qquad\text{(12)}
```


For each residue $`r`$, put $`h_r(0)=0`$ and


```math
h_r(k)=\sum_{j=0}^{k-1}(w_{r+jn+1}-w_{r+jn}),
 \quad 1\leq k\lt n.                               \qquad\text{(13)}
```


Equation (11) gives consistency when a track closes. All lifts are


```math
x_{r+kn}=b_r+h_r(k),\qquad \sum_rb_r=w_0.         \qquad\text{(14)}
```


The base values make window zero correct; (12) then makes every other
window correct. This proves sufficiency and the kernel description.
Rank follows. $`\square`$

For integer cell bounds $`L\leq x_i\leq U`$, (14) gives an exact
additional criterion. Define


```math
\ell_r=L-\min_k h_r(k),\qquad
 u_r=U-\max_k h_r(k).
```


A bounded integer lift exists if and only if (11) holds, every
$`\ell_r\leq u_r`$, and


```math
\sum_r\ell_r\leq w_0\leq\sum_r u_r.             \qquad\text{(15)}
```


These conditions are sufficient because sums of integer intervals fill
their entire integer sum interval. For a prescribed pool, one needs the
much stronger requirement that the translated tracks in (14) partition
that exact pool. Equation (15) alone does not establish it.

### A quantitative obstruction, already for two offset partitions

For odd $`n=2m+1\geq3`$, choose $`f_k`$ to be $`+1`$ for $`m`$
successive indices, then $`-1`$ for $`m`$, then zero. Set
$`w_{kn}= -f_k`$, $`w_{kn+1}=f_k`$, and all other $`w_i=0`$.
Every partition total is zero and $`\|w\|_\infty=1`$. Yet (13) for
$`r=0`$ has range $`2m=n-1`$. Every integer or real lift therefore
has $`\|x\|_\infty\geq(n-1)/2`$. Only the equations at starts
$`kn`$ and $`kn+1`$ were used, so the same obstruction holds for
two adjacent offset partitions, whose maximum cell degree is only two.
Small target errors, bounded degree, and a saturated image do not imply
a uniformly bounded inverse. The repair is to impose the track-range
and interval-sum capacity tests, not merely (11).

For any fixed set of $`1\leq s\leq n`$ offsets, the restricted window map has rank
$`s(n-1)+1`$, and its integer image is exactly equal totals among
those $`s`$ partitions. To prove this, extend the missing offset
vectors to have the same total, apply the full theorem, and observe
that its only row dependencies are differences of partition totals.

If every window target is the same number, (12) forces period $`n`$,
so an array with $`N\gt n`$ distinct entries is impossible. Even two
adjacent offset partitions with the same constant target force the
entire residue-zero track to repeat one entry. This is a failure of
that target choice, not an impossibility theorem for prime windows.

## 6. All affine lines over a finite field

Let $`q`$ be a prime power, and consider all $`q(q+1)`$ affine lines
on $`\mathbb F_q^2`$. With incidence matrix $`A`$, every point is on
$`q+1`$ lines and every pair of distinct points shares exactly one.
Hence


```math
A^{\mathsf T}A=qI+J_{q^2},                      \qquad\text{(16)}
```


where $`J_{q^2}`$ is the all-ones matrix. Thus $`A`$ has full column
rank $`q^2`$. Its rational image consists exactly of equal totals
$`T`$ in the $`q+1`$ parallel classes. For such a line vector $`y`$,
the unique preimage is


```math
x_p=\frac{\sum_{L\ni p}y_L-T}{q}.              \qquad\text{(17)}
```


Indeed, summing the numerator over a line gives $`q y_L`$: that line
contributes $`q y_L`$, and the $`q`$ other directions contribute
$`qT`$, which cancels the subtraction of $`qT`$. Therefore the exact
integer image requires, in addition to equal class totals,


```math
\sum_{L\ni p}y_L\equiv T\pmod q
 \quad\hbox{for every point }p.                 \qquad\text{(18)}
```


Unlike the axis and cyclic-window maps, this image need not be
saturated. For example, at $`q=3`$, assign target one to the four
lines $`x=0`$, $`y=0`$, $`y=x`$, and $`y=2x+1`$, and zero to all
other lines. Every parallel-class total is one, but three chosen
lines pass through $`(0,0)`$, so (17) reconstructs $`x_{(0,0)}=2/3`$.
This violates (18) and demonstrates nonsaturation without relying
on a Smith-form computation.

For a fixed pool, (17) must reconstruct precisely that pool, once each.
This is substantially stronger than choosing nearby compatible primes.
The statement concerns finite-field geometry; it does not apply to all
slopes modulo a general composite integer.

## 7. A localized modular obstruction at the required edge size

Let $`n\geq3`$ be odd, and let $`q\mid n`$ be prime. Among distinct
prime entries, at most one is zero modulo $`q`$. On any fixed


```math
m=(q-1)(n-1)+2
```


cells, at least $`(q-1)(n-1)+1`$ entries have nonzero residue modulo
$`q`$. Some nonzero residue occurs at least $`n`$ times. The sum of
those $`n`$ odd primes is divisible by $`q`$ and is greater than
$`q`$, hence composite. Consequently the fixed hypergraph of all
$`n`$-subsets of those $`m`$ cells is unsatisfiable under every
assignment of the first $`n^2`$ odd primes. Here


```math
m\leq(n-1)^2+2=n^2-2n+3\leq n^2.
```


Thus requiring all $`n`$-subsets of the full pool is impossible for
every odd $`n\geq3`$. This is an explicit upper bound
$`{m\choose n}`$ for the size of an unsatisfiable family in this
particular class, not a sharp extremal theorem.

### Stronger obstruction by zero-sum selection

In fact one can replace the displayed cell count by


```math
m_*=n+q-1\leq2n-1.                              \qquad\text{(20)}
```


This follows from the classical Erdős--Ginzburg--Ziv zero-sum theorem;
only its prime case is needed here. The original source is P. Erdős,
A. Ginzburg and A. Ziv, *Theorem in the additive number theory*,
Bull. Res. Council Israel **10F** (1961), 41--43,
[original-paper reprint](https://combinatorica.hu/~p_erdos/1961-25.pdf),
[accessible mirror](https://nonagon.org/ExLibris/sites/default/files/pdf/Erdos-Ginzburg-Ziv-Theorem-1961.pdf).
This is a new application/bound within the present project, not a claim
that the underlying zero-sum theorem is new.

Here is a self-contained proof of the needed prime case. Sort $`2q-1`$
residues as $`a_1\leq\cdots\leq a_{2q-1}`$ in $`\{0,\ldots,q-1\}`$.
If $`a_i=a_{i+q-1}`$ for some $`1\leq i\lt q`$, the intervening $`q`$
equal residues have sum zero. Otherwise the $`q-1`$ disjoint pairs
$`\{a_i,a_{i+q-1}\}`$ all have two distinct residues. Starting from
$`\{a_{2q-1}\}`$, add these pairs successively. Each addition increases
the sumset size unless it is already all of $`\mathbb F_q`$: a proper
nonempty set cannot be invariant under a nonzero translation. After
$`q-1`$ additions every residue occurs, including zero. Its representation
uses exactly one entry of every pair and the final entry, hence exactly
$`q`$ entries.

From $`m_*`$ given entries, repeatedly remove a zero-sum block of size
$`q`$, a total of $`n/q`$ times. Before the last removal at least
$`m_*-(n/q-1)q=2q-1`$ entries remain. The union of the removed blocks
has exactly $`n`$ entries and sum divisible by $`q`$. For entries at
least three this sum exceeds $`q`$, so it is composite. Therefore the
fixed hypergraph consisting of all $`n`$-subsets of any $`m_*`$ cells
is unsatisfiable, for **any** entry pool with entries at least three.
Primality, oddness, and distinctness of the pool are not used in this
stronger obstruction. For the problem's odd $`n`$, the first odd-prime
pool meets these hypotheses. The resulting upper bound on the minimum
size of an unsatisfiable $`n`$-uniform family is
$`{n+q-1\choose n}`$.

The cell threshold in this single-modulus zero-sum statement is sharp:
$`n-1`$ copies of residue 1 and $`q-1`$ copies of residue 2 form a
sequence of length $`n+q-2`$ with no zero-sum $`n`$-subset modulo $`q`$.
Every such subset uses between one and $`q-1`$ copies of residue 2, so
its sum is nonzero modulo $`q`$. This is not sharpness for the minimum
unsatisfiable hypergraph of the actual prescribed prime pool: other
divisors and arithmetic obstructions may apply.

### Equal edge counts with opposite feasibility

For $`n=3`$, the family of all ten triples of five fixed cells is
unsatisfiable by (20), using $`q=3`$. There is also a feasible,
geometrically specified ten-edge family on the same nine cells: take
the three rows, three columns, two main diagonals, and the two corner
L-triples


```math
\{(0,0),(0,1),(1,0)\},\qquad
 \{(2,2),(2,1),(1,2)\}.
```


The constraints were specified before searching the arrangement. An
exact certificate using the first nine odd primes is


```math
\begin{pmatrix}3&5&23\\11&19&13\\29&17&7\end{pmatrix}.
```


Its row, column, diagonal, and L-triple sums, in that order, are


```math
31,43,53;\quad43,41,43;\quad29,71;\quad19,37,
```


all prime. Thus equal edge count and equal edge size do not determine
feasibility, already for one fixed prescribed pool. This is a finite
example, not a uniform theorem obtained by selecting successful subsets
after an assignment.

## 8. Why numeric feasibility is not permutation feasibility

Let $`Q`$ be reserved cells with prescribed distinct values, let the
pool diameter be $`W`$, and let each cell belong to at most $`\Delta`$
constraints. Any permutation confined to $`Q`$ has correction vector
$`c`$ satisfying


```math
|c_E|\leq W|E\cap Q|,
 \qquad \|c\|_1\leq\Delta |Q|W.                 \qquad\text{(19)}
```


More generally every real dual weighting of constraints bounds the
correction by the extrema of the corresponding weighted assignment
problem on $`Q`$, computed by sorting weights and reserved values.
These are necessary capacity bounds, not sufficient exact permutation
tests. Even a single three-cell constraint on the first nine odd
primes cannot attain target 17: its smallest possible sum is 15 and
the next is 19. Yet 17 is prime, has the correct parity, and lies in
the convex attainable interval. Fine disjoint permutation gadgets are
needed to pass from an integer image or a convex capacity region to
the exact-pool theorem.

## Reproducible evidence and scope

`../code/incidence.py` implements independent constraint generation,
exact axis lifting and rounding, cyclic reconstruction and box tests,
and integer graph-product coefficients. `../code/verify_incidence.py`
checks these with deterministic rational and integer fixtures, including
the cyclic capacity obstruction. These checks support implementation
correctness on their stated inputs; the proofs above carry the
universal claims. No asymptotic prime-array theorem is inferred from
a rank calculation, a numerical lift, or a finite experiment.
