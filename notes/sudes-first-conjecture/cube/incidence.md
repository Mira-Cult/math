# Incidence, integer compatibility, and quantitative numeric capacity

This manuscript contains the incidence component of the prime-array assembly.
The results here concern integer arrays, with signed entries allowed. They do
**not** assert that their integer lifts are permutations of a prescribed pool.
The permutation realization is a separate obligation. The proofs below give the active integer and quantitative lifting lemmas used by the cube construction.

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
\operatorname{rank}_{\mathbb Q}M=n^D-(n-1)^D,
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
to $`\sum(v-\operatorname{med}v)^2\geq\sum v^2`$. Hence
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

[Back to the four-manuscript index](../README.md).
