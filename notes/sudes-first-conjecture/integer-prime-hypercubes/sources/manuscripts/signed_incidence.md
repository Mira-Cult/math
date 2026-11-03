**Public reading copy.** Presentation and links have been normalized. Historical status statements below belong to their source revisions; see the [current publication status](../../README.md#review-and-verification-status). The matching original bytes are in the [source archive](../../originals/manuscripts/signed_incidence.md).

# Full signed-line incidence: the integer image and bounded cuboid coefficients

Author: `/root/incidence`. Labels in this manuscript are local; no permanent
claim IDs are allocated. This is new source extending the incidence results
at scientific revision `aba3397991165103c2bebca3a898a4b30d79fcb2` without
changing that source. The arguments below concern signed integer arrays.
Their use for permutations of the prescribed prime pool requires the separate
[physical trade and packing argument](signed_trades.md). Independent review
of this new source is pending.

## 1. Coordinates and the exact compatibility equations

Let $`n=2m+1\ge3`$, and use centered coordinates


```math
I=\{-m,\ldots,m\},\qquad R(t)=-t.
```


For an integer array $`a:I^3\to\mathbb Z`$, write its axis sums as


```math
U(y,z)=\sum_x a(x,y,z),\quad
 V(x,z)=\sum_y a(x,y,z),\quad
 W(x,y)=\sum_z a(x,y,z).
```


The six families of face diagonals have targets


```math
F_{xy}^{\sigma}(z)=\sum_ta(t,\sigma t,z),\quad
 F_{xz}^{\sigma}(y)=\sum_ta(t,y,\sigma t),\quad
 F_{yz}^{\sigma}(x)=\sum_ta(x,t,\sigma t),\qquad \sigma\in\{+1,-1\}.
```


The four body targets are


```math
b_{\sigma,\tau}=\sum_ta(t,\sigma t,\tau t),
 \qquad (\sigma,\tau)\in\{+1,-1\}^2.
```


These are the deduplicated full signed-coordinate lines: there are


```math
M=3n^2+6n+4.
```


A face diagonal is a line lying in an axis slice; it is not a
two-dimensional section. The six families together sweep out the six
diagonal squares, which themselves are not required to have prime sums here.

Every target vector satisfies the axis plane identities


```math
\begin{aligned}
  \sum_yU(y,z)&=\sum_xV(x,z)&& (z\in I),\\
  \sum_zU(y,z)&=\sum_xW(x,y)&& (y\in I),\\
  \sum_zV(x,z)&=\sum_yW(x,y)&& (x\in I),
 \end{aligned}                                                    \qquad\text{(1)}
```


and the six diagonal-square identities


```math
\begin{aligned}
  \sum_z F_{xy}^{\sigma}(z)&=\sum_tW(t,\sigma t),\\
  \sum_y F_{xz}^{\sigma}(y)&=\sum_tV(t,\sigma t),\\
  \sum_x F_{yz}^{\sigma}(x)&=\sum_tU(t,\sigma t)
 \end{aligned}
 \qquad(\sigma\in\{+1,-1\}).                              \qquad\text{(2)}
```


Both sides of each equation (2) partition one diagonal square into lines.
No equation is obtained merely by adding the four body lines: their union
is not one of the sections on the right of (1) or (2).

When the total of the entry pool is a specified integer $`T`$, also require


```math
\sum_{y,z}U(y,z)=T.                                      \qquad\text{(3)}
```


Equation (1) then makes the other two directional totals equal to $`T`$.
In particular, matching three grand totals alone omits the plane identities.

<a id="full-signed-line-integer-image"></a>
## 2. Full signed-line integer-image theorem

**Theorem SI.** For every odd $`n\ge11`$, an integer target vector for all
$`M`$ signed lines is the line-sum vector of an integer array if and only
if it satisfies (1) and (2). The image lattice is saturated in
$`\mathbb Z^M`$. There is no additional congruence or body-target relation.
The rational rank and the integer-kernel rank are respectively


```math
\mathrm{rank}L=3n^2+3n-1,\qquad
 \mathrm{rank}\ker_{\mathbb Z}L=n^3-3n^2-3n+1.        \qquad\text{(4)}
```


There are $`3n+5`$ independent rational relations: $`3n-1`$ from (1) and
six more from (2). With (3) fixed, the attainable affine space has
dimension $`3n^2+3n-2`$.

More generally, fix integers $`r`$ and $`q\ge1`$. A compatible integer
target has a lift with every entry congruent to $`r\pmod q`$ if and only
if every line target is congruent to $`nr\pmod q`$. In particular, for
odd $`n\ge11`$, every compatible vector of odd targets has a lift by
odd integers. This does not assert positivity or use of any prescribed pool.

### The integral axis kernel

The [axis-image theorem](incidence.md#axis-image-theorem) supplies an
integer lift of $`U,V,W`$ whenever (1) holds. Its rank is
$`3n^2-3n+1`$. We recall an integral basis of its kernel, since an
arbitrary rational kernel basis would not suffice here.

Put $`V_{\mathbb Z}=\{v\in\mathbb Z^I:\sum_tv(t)=0\}`$.
The vectors $`e_t-e_0`$, $`t\ne0`$, form a basis, and


```math
\mathbb Z^I=\mathbb Ze_0\oplus V_{\mathbb Z}.
```


In the induced tensor decomposition, contraction of one coordinate by
the sum functional kills precisely the summands having a
$`V_{\mathbb Z}`$ factor in that coordinate. Consequently the joint
kernel of all three axis maps is exactly


```math
V_{\mathbb Z}^{\otimes3},                               \qquad\text{(5)}
```


with basis


```math
(e_i-e_0)\otimes(e_j-e_0)\otimes(e_k-e_0),
 \qquad i,j,k\ne0.                                      \qquad\text{(6)}
```


No denominator or finite-index sublattice enters (5).

### Cuboids with isolated face images

For distinct endpoints in each coordinate, call


```math
C=(e_{x_0}-e_{x_1})\otimes(e_{y_0}-e_{y_1})
                       \otimes(e_{z_0}-e_{z_1})           \qquad\text{(7)}
```


a unit cuboid. It has eight entries, each $`+1`$ or $`-1`$, and all
axis-line sums zero. Its coefficient may later be any signed integer.

Fix distinct levels $`u,v\in I`$. At most two nonzero reflection
orbits meet $`\{u,v\}`$. Since $`m\ge5`$, choose three distinct
positive representatives $`t,a,b\in\{1,\ldots,m\}`$ from orbits not
meeting $`\{u,v\}`$. Then


```math
C_{xy,+;u,v}=(e_t-e_a)\otimes(e_t-e_b)\otimes(e_u-e_v)    \qquad\text{(8)}
```


has signed-line image


```math
F_{xy}^+\longmapsto e_u-e_v,                            \qquad\text{(9)}
```


and zero image on every other face family and every body line. Indeed,
the only common value of the first two endpoint sets is $`t`$, and
there is no equality after negating one of those sets. The reflection
orbits of the third-coordinate endpoints are disjoint from every orbit
used by the first two coordinates, so no $`xz`$, $`yz`$, or body line
meets a nonzero entry in the required pattern. The two surviving
$`xy,+`$ entries have coefficients $`+1,-1`$.

Reflecting an entire coordinate and permuting entire coordinates preserves
the complete constraint family. These operations turn (8) into an isolated
unit transfer in any of the six face families. They are global symmetries
of the instance; they do not independently relabel individual constraints.

### Cuboids controlling the body lines

Choose distinct positive representatives $`t,a,b,c`$ in four nonzero
reflection orbits. The cuboid


```math
D=(e_t-e_a)\otimes(e_t-e_b)\otimes(e_t-e_c)               \qquad\text{(10)}
```


has body image $`b_{+,+}=1`$, with the other three body coordinates
zero. Its only nonzero face images are


```math
F_{xy}^+=e_t-e_c,\qquad
 F_{xz}^+=e_t-e_b,\qquad
 F_{yz}^+=e_t-e_a.                                      \qquad\text{(11)}
```


All first, second, and third endpoint sets share exactly the orbit of
$`t`$. Thus the body assertion and the three displayed pairwise
intersections follow by direct inspection of (10). Each of the three
face images has total zero. Subtract three cuboids of type (8) to cancel
(11). The resulting sum of at most four cuboids has image a single unit
body coordinate and zero image on every other signed line. Reflecting
the second and third coordinates gives all four body unit vectors.

### Completion of the proof

Lift the axis targets integrally. Subtracting that lift leaves zero axis
targets. Equation (2) says that the remaining vector in each of the six
face families has total zero; the four body targets remain arbitrary.
Every zero-total integer $`n`$-vector is an integer combination of
$`e_u-e_v`$. Equations (8)--(11) therefore lift all these remaining
targets by axis-neutral cuboids. This proves sufficiency and explicitly
exhibits every integer direction of the extra image.

That extra image is


```math
\left\{f\in\mathbb Z^n:\sum_if_i=0\right\}^{6}
          \oplus\mathbb Z^4,                            \qquad\text{(12)}
```


of rank $`6(n-1)+4`$. Adding the axis rank gives (4). Equations
(1)--(2) define the full integer image as the integer points of a
rational subspace, hence the image is saturated. Equation (3) is one
additional independent affine condition.

For the congruence refinement, subtract the constant array $`r`$, whose
every line sum is $`nr`$, and divide all targets by $`q`$. The resulting
integer target still satisfies the homogeneous identities (1)--(2).
Lift it by the already proved theorem, multiply the array by $`q`$, and
add $`r`$ entrywise. Necessity follows by summing $`n`$ entries. QED.

<a id="bounded-coefficient-solvers"></a>
## 3. Bounded coefficient solvers

The previous proof is constructive but does not by itself give disjoint
prime swaps. The following bound is the numeric interface used by the
physical construction. Coefficients, not cell values or permutation
distances, are bounded.

Let the axis targets already be zero. Let $`f_1,\ldots,f_6\in\mathbb Z^n`$
have total zero and let $`b_1,\ldots,b_4\in\mathbb Z`$. Put


```math
F=\max_j\|f_j\|_\infty,\qquad
 B=F+\sum_{i=1}^4|b_i|.                                 \qquad\text{(13)}
```


**Theorem BC.** For odd $`n\ge11`$, first use four cuboids of type
(10), with coefficients $`b_i`$, to correct the body coordinates.
Then the remaining face vectors have total zero and norm at most $`B`$.
They can be corrected as follows.

1. On the path with vertices $`0,\ldots,n-1`$, each face family needs
   at most $`n-1`$ cuboid types, whose coefficients have magnitude at
   most $`\lfloor n/2\rfloor B`$.
2. Let $`G`$ be any loopless undirected graph on $`n`$ vertices with
   edge expansion
   
```math
|\partial S|\ge h\min(|S|,n-|S|)\quad
     (\varnothing\ne S\ne V(G)),\qquad h\gt 0.
```

   On one cuboid type (8) for each oriented graph edge and face family,
   there is an integer correction with coefficient magnitude at most
   $`\lceil B/h\rceil`$.

Thus a graph of bounded maximum degree uses $`O(n)`$ numeric cuboid
types. If every initial face and body error has magnitude at most
$`\delta`$, the face coefficient bound is at most
$`\lceil5\delta/h\rceil`$. The constants do not depend on $`n`$.

**Proof.** Each cuboid (10) contributes at most one in magnitude to a
given face coordinate, and has zero total in each face family. This
gives (13), including for arbitrary signs of the body coefficients.
For a remaining face vector $`d`$, orient a path from $`0`$ to $`n-1`$
and give edge $`(i,i+1)`$ coefficient $`\sum_{j=0}^id_j`$.
Its divergence is $`d`$. Since $`\sum_jd_j=0`$, this prefix has
magnitude at most $`\min(i+1,n-i-1)B`$, proving the path bound.

For the graph version, put $`C=\lceil B/h\rceil`$. Replace each
undirected edge by arcs in both directions, each of capacity $`C`$.
Attach a source to every positive-demand vertex, with capacity $`d_v`$,
and every negative-demand vertex to a sink, with capacity $`-d_v`$.
For every vertex set $`S`$,


```math
\left|\sum_{v\in S}d_v\right|
 \le B\min(|S|,n-|S|)\le C|\partial S|.                 \qquad\text{(14)}
```


The source--sink cut conditions therefore permit a flow saturating every
demand. The usual augmenting-path proof of max-flow/min-cut uses only
integer augmentations here, so that a maximum flow is integral.
Subtract the two directed flows on each edge to obtain a signed integer
coefficient in $`[-C,C]`$ with divergence $`d`$. Replace each oriented
edge by its isolated cuboid (8), independently for the six face families.
They preserve the body targets and all axes. QED.

This one-dimensional flow bound needs no Green-function estimate or
rounding correction. The tensor-expander result in
[the baseline incidence manuscript](incidence.md#tensor-expander-coefficient-theorem)
remains relevant to the two-index correction of axis lines. The new face
vectors require ordinary graph flows only.

There is an exact capacity criterion for a supplied graph and integer
capacity $`C\ge0`$: an integer flow with $`|f_e|\le C`$ exists if and
only if the cut inequalities


```math
\left|\sum_{v\in S}d_v\right|\le C|\partial S|
 \quad\text{for every }S\subseteq V(G)                  \qquad\text{(15)}
```


hold. Necessity follows by summing divergence over $`S`$; the same
integer network proves sufficiency. This states sign and capacity
conditions, not merely rank or a gcd condition.

**Physical boundary.** The cuboids just proved need not have disjoint
supports. One coefficient may represent many physical stages. Arbitrary
signed-integer addition changes entries and is not an allowed operation
on a prescribed pool. The separate physical proof must realize each
stage with four equal-gap pairs, reserve distinct entries and cells,
control line loads, and keep the scalar coefficient inside the
reservoir's attainable interval. Nothing in Theorems SI or BC supplies
those properties automatically.

## 4. Constructive even-modulus residue routing

**Lemma SR-I.** Let $`n\ge11`$ be odd and $`g=2h\ge2`$. Suppose axes
have already been corrected modulo $`g`$. Let the desired changes on
the six face vectors and four body coordinates be even residues modulo
$`g`$, with each face-family total zero modulo $`g`$. They can be
realized by axis-neutral cuboids whose scalar steps are $`2\pmod g`$.
At most


```math
4+6(n-1) (historical reference; not supplied in this package)=(6n-2)(h-1)                            \qquad\text{(16)}
```


individual cuboids are needed. Four equal-gap pairs per individual
cuboid would consume at most four times this many pairs, provided the
physical realization is separately available. If $`g=2`$, no cuboid is
needed.

**Proof.** Divide the even residues by two in $`\mathbb Z/h\mathbb Z`$.
For each body coordinate choose its coefficient in
$`\{0,\ldots,h-1\}`$ and use that many cuboids of type (10). Their
face-family totals are zero. Recompute the six residual face vectors.
For each path edge, use the prefix sum of that residual vector, reduced
to $`\{0,\ldots,h-1\}`$. The divergence equations hold modulo $`h`$,
including at the last vertex because the family total is zero.
Isolated face cuboids do not disturb corrected bodies or other face
families. Restoring the scalar factor two gives the claimed result
modulo $`g`$, and counting the available stages gives (16). QED.

The individual body stages may use different allowed orbit labels.
Their exact face drifts can be measured after all body residues have
been corrected; each still has total zero in each family. The path
argument then applies unchanged. Likewise a physical gap congruent
to $`2\pmod g`$, rather than numerically equal to two, has the same
residue effect. This lemma contains no assertion that suitable prime
pairs exist.

## 5. Small odd orders: rational rank does not determine the lattice

The exact diagnostic reduces to the map in (12) on the integral basis
(6). Drop the center coordinate in each face vector, recovering it as
minus the other coordinates. This is an integral isomorphism for every
zero-total face vector. Keep the four body coordinates. The resulting
integer matrix $`Q_n`$ has size


```math
[6(n-1)+4]\ \text{ by }\ (n-1)^3.                      \qquad\text{(17)}
```


Its entries are obtained by intersecting each anchored eight-corner
cuboid with each remaining line. They are small signed integers;
no elimination or division has been used to form this matrix.

[The exact checker](../../originals/code/verify_signed_incidence.py) performs Smith
reduction with a log containing only integer row/column additions,
swaps, and row sign reversals. A separate replay verifies every allowed
operation and the final diagonal and divisibility chain. It obtains:

| $`n`$ | Shape of $`Q_n`$ | Rank of $`Q_n`$ | Full line-map rank | Nonunit Smith factors of $`Q_n`$ |
|---|---:|---:|---:|---|
| 3 | $`16\times8`$ | 8 | 27 | $`3,3,3,6`$ |
| 5 | $`28\times64`$ | 28 | 89 | $`5,5,15`$ |
| 7 | $`40\times216`$ | 40 | 167 | none |
| 9 | $`52\times512`$ | 52 | 269 | none |
| 11 | $`64\times1000`$ | 64 | 395 | none |

The full rank adds the axis rank $`3n^2-3n+1`$. At order three the
full map has zero kernel; it has eight additional rational relations
beyond (1)--(2). At order five, (1)--(2) are all rational relations,
but they are not the complete integer compatibility conditions. The
finite checks at seven and nine exhibit saturation at those two
orders. Theorem SI has its elementary proof for every odd $`n\ge11`$
independently of the finite Smith computations.

### An explicit order-five obstruction

For an axis-zero integer array on $`\{-2,-1,0,1,2\}^3`$, let


```math
B=\sum_{\sigma,\tau}b_{\sigma,\tau},\qquad
 S=\sum_{\sigma}\bigl(F_{xy}^{\sigma}(0)
                  +F_{xz}^{\sigma}(0)+F_{yz}^{\sigma}(0)\bigr).
```


Then


```math
B\equiv7S\pmod {15}.                                  \qquad\text{(18)}
```


To prove this without Smith reduction, it suffices by (6) to use one
anchored cuboid with nonzero endpoints $`i,j,k`$. Let $`I_{ij}`$ be
one if $`|i|=|j|`$, and zero otherwise, and let $`I_*=1`$ if all
three absolute values are equal. The only body contributions are the
noncentral corner, if its three orbits coincide, and the center,
which lies in all four bodies with coefficient $`-1`$. Thus


```math
B=I_*-4,\qquad S=-(I_{ij}+I_{ik}+I_{jk})-6.             \qquad\text{(19)}
```


There are only two nonzero reflection orbits. If all three endpoints
use the same orbit, $`(B,S)=(-3,-9)`$. Otherwise precisely one pair
shares an orbit, giving $`(B,S)=(-4,-7)`$. The differences $`B-7S`$
are respectively $`60`$ and $`45`$, both divisible by fifteen. This
proves (18) on the integral basis and hence on every axis-zero array.

In particular, zero axes, zero face targets, and body target
$`(1,0,0,0)`$ satisfy every displayed rational compatibility equation
but have no integer lift. Even the pure numerical generalization
"the equations alone suffice at every odd order at least five" is
therefore false. Scaling this example by two and adding the constant
one array gives compatible odd targets that cannot be lifted by odd
integer entries; positivity of targets does not remove the obstruction.

### The other two order-five congruences

Put


```math
H_{xy}=\sum_{t=-2}^{2}t^2
          (F_{xy}^{+}(t)+F_{xy}^{-}(t)),
```


and define $`H_{xz},H_{yz}`$ analogously, weighting their fixed
coordinate. Every axis-zero order-five integer array also satisfies


```math
H_{xy}\equiv H_{xz}\equiv H_{yz}\pmod5.                \qquad\text{(20)}
```


For an anchored cuboid these three quantities are


```math
k^2(I_{ij}+2),\quad j^2(I_{ik}+2),\quad i^2(I_{jk}+2).
```


Modulo five the two possible orbit squares are $`1`$ and $`-1`$.
If all orbits agree the displayed quantities agree; otherwise the
quantity using the distinct orbit is $`-3a\equiv2a`$, and the other
two are $`2a`$. This proves (20) by the same integral-basis argument.

The two independent differences in (20), together with (18), give a
surjective homomorphism from the free target group in (17) onto


```math
(\mathbb Z/5\mathbb Z)^2\oplus\mathbb Z/15\mathbb Z.
```


Indeed each of $`H_{xy},H_{xz},H_{yz}`$ can be changed independently
modulo five using a face value at level one and its compensating center
value, and one body coordinate then adjusts (18) independently modulo
fifteen. The kernel has index $`375`$. The certified Smith factors
give the same index for the actual image. Consequently (18)--(20)
are also sufficient for an axis-zero order-five target. For arbitrary
axis targets, subtract an integral axis lift first. The resulting
congruence test is independent of that choice, because differences of
axis lifts are actual axis-zero arrays satisfying (18)--(20).

This finite exact compatibility result is not an assertion about
permuting the first $`125`$ odd primes. It explains why the large-order
integer-image theorem requires proof beyond a rank calculation.

## 6. Code, finite evidence, and scope

[signed_incidence.py](../../originals/code/signed_incidence.py) supplies the explicit
keyed line sets, compatibility checker, cuboid generators, full integer
lift, optional entry-congruence lift, path/graph corrections, residue
routing, anchored-kernel matrix, Smith producer, and elementary-operation
certificate replay. The coordinate convention in code is
$`\{0,\ldots,n-1\}`$, obtained from this manuscript by translation.

Run from the repository root:

```sh
python3 -B problems/prime-arrays-beyond-square/code/verify_signed_incidence.py
```

The verifier uses a separately written full-line generator, checks the
isolated face and body effects, checks integer and congruence lifts,
replays all five Smith certificates, and tests the order-five
congruences and the forbidden unit body target. It also includes
capacity and certificate-corruption negative controls. Integer
arithmetic is exact; no numerical rank threshold is used.

These finite checks support the explicit formulas and detect coding
errors. The all-order proofs of SI, BC, and SR-I are the arguments
above. They do not infer bounded disjoint prime-pair supplies, reservoir
survival, or an exact-pool permutation from integer-lattice saturation.
Those are separate obligations of the physical controller.
