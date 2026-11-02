# Canonical pools, local obstructions, and the additive correction lattice

All result labels in this manuscript are local. The frozen pools and
line families are defined in [PROBLEM.md](../PROBLEM.md). The statements below
are mathematical lemmas, not a claim that prime targets or physical reservoir
capacities have been supplied. In particular, a lift by arbitrary ring elements
is not a permutation of the prescribed primes.

The scalar geometric source is the public
[signed-incidence manuscript](../../sudes-first-conjecture/cube/signed_incidence.md),
Theorems SI/BC and the cuboids in equations (8)--(11). Its physical boundary
is preserved explicitly here.

## 1. Prime-element and associate bookkeeping

Write an element as the integer coefficient pair `(a,b)` in the basis
`(1,i)` or `(1,omega)`. These are coefficient coordinates; Eisenstein Euclidean
coordinates are `(a-b/2,sqrt(3)b/2)`. All lattice indices below use coefficient
coordinates.

In the Gaussian ring, an element is prime if and only if its norm is a rational
prime, or it is an associate of a rational prime `p=3 mod 4`. In the Eisenstein
ring the corresponding inert congruence is `p=2 mod 3`. Thus a test accepting
only rational-prime norms incorrectly rejects the required inert entries.
In arbitrary coordinates an inert Gaussian associate lies on `a=0` or `b=0`;
an inert Eisenstein associate lies on `a=0`, `b=0`, or `a=b`.

For completeness, these criteria follow from Euclidean unique factorization.
If a prime element divides its integer norm, it divides one rational prime
factor of that norm. Reduction of `X^2+1` modulo odd rational primes gives the
split/inert alternatives `p=1/3 mod 4`; reduction of `X^2+X+1` gives
`p=1/2 mod 3`. The exceptional rational primes 2 and 3 ramify, respectively.
Factoring a split rational prime gives two nonassociate prime factors of norm
`p`; an inert rational prime remains prime and has norm `p^2`. The units give
exactly the axis lists just stated. Conversely, prime integer norm precludes a
factorization into two nonunits because the norm is multiplicative.

### Canonical pairs and norm ties

Every nonramified split Gaussian class has a representative `(a,b)` with
`a,b>0`; its conjugate class has representative `(b,a)`. These are distinct:
equality would force norm `2a^2`, whose only prime case is the excluded
ramified class. The inert representative is `(p,0)`, `p=3 mod 4`.

For Eisenstein elements the conjugate of `a+b omega` is
`a-b-b omega`. Multiplication by the unit `1+omega` gives


```math
(1+\omega)\overline{a+b\omega}=a+(a-b)\omega.
```


Consequently the two canonical split representatives are `(a,b)` and
`(a,a-b)`, with `0<b<a`. Equality would give norm `3a^2/4`, whose prime
case is precisely the excluded class `(2,1)`. The inert representative is
`(p,0)`, `p=2 mod 3`.

The two members of a split pair have equal norm and are consecutive in the
specified `(norm,a,b)` ordering. There are no other ties: a split norm is a
rational prime, whereas an inert norm is a rational-prime square. A prefix
therefore contains complete conjugate pairs, its included inert entries,
and at most one unpaired final split representative. The half-open sectors
give exactly one associate per class, including the positive-real-axis
boundary. They do not identify the two conjugate classes.

Let `M` be the prefix length, `R` the largest absolute value, `T=(T_a,T_b)`
the exact pool sum, and `I` its number of inert entries. If an orphan split
representative exists, write it `(a_*,b_*)`; otherwise all orphan terms below
are zero. The exact identities are


```math
\begin{array}{ll}
\mathbb Z[i]:& T_a-T_b=\displaystyle\sum_{p\ {\mathrm{inert}},\ p\le R}p
                   +(a_*-b_*),\\[3pt]
\mathbb Z[\omega]:&T_a-2T_b=\displaystyle\sum_{p\ {\mathrm{inert}},\ p\le R}p
                   +(a_*-2b_*).
\end{array}                                                    \qquad\text{(1)}
```


Thus the actual average is not identically on the sector bisector.
Replacing it by a bisector point without accounting for (1) loses an exact
vector constraint.

For a complete norm cutoff `B`, the numbers of retained classes are exactly


```math
\begin{split}
 A_G(B)&=2\pi(B;4,1)+\pi(\sqrt B;4,3),\\
 A_E(B)&=2\pi(B;3,1)+\pi(\sqrt B;3,2).
\end{split}                                                     \qquad\text{(2)}
```


The ramified class is absent from both formulas. The usual fixed-modulus
prime number theorem, or the fixed-field prime-element theorem in the analytic
note, gives `A_K(B)~B/log B`. The possible half-pair at the boundary changes
this by at most one. Hence, for `M=n^D`,


```math
B\sim M\log M,\qquad R\sim\sqrt{M\log M},\qquad
 I\sim\frac{\sqrt M}{\sqrt{\log M}}.                    \qquad\text{(3)}
```


No estimate in (3) asserts distribution in a thin box or a fixed row.

## 2. Ramified residues and size exclusions

### Gaussian obstruction

Modulo `lambda=1+i`, the residue of `(a,b)` is `a+b` in `F_2`.
Every pool entry has residue 1. An even-length line therefore has sum divisible
by `lambda`. If that sum were prime, it would be an associate of `lambda`.
But every canonical entry has real part at least 1, so a line of length
`n>=2` has real part at least 2, whereas every associate of `lambda` has real
part at most 1. This is impossible.

**Lemma G-even.** Every even order `n>=2` is impossible for the Gaussian
square and full signed-line cube baselines. This is an exact obstruction,
not only an eventual one. The singleton is the prime `[1+2i]`.

For odd `n`, every line automatically has nonzero residue modulo `lambda`,
whatever the arrangement. This checks the ramified prime only.

### Eisenstein residue counts

Modulo `lambda=1-omega`, the residue of `(a,b)` is `a+b` in `F_3`.
The two members `(a,b),(a,a-b)` of a split pair have opposite nonzero
residues, because `2a-b=-(a+b) mod 3`. Every inert representative has
residue `p=-1 mod 3`.

Let `N_+` and `N_-` be the actual numbers of the two residues. If `epsilon`
is the residue `+1` or `-1` of the possible orphan, and zero if absent, then


```math
N_++N_-=M,\qquad N_+-N_-=-I+\epsilon,\qquad
 T\equiv-I+\epsilon\pmod\lambda.                        \qquad\text{(4)}
```


For a line containing exactly `k` positive-residue entries, its residue is
`2k-n`. It avoids the ramified ideal exactly when


```math
k\not\equiv -n\pmod3.               \qquad\text{(5)}
```


All canonical nonramified Eisenstein primes have real part at least 2.
Every sum of one or more such entries therefore has real part at least 2,
exceeding the absolute value `sqrt(3)` of a ramified prime. Accordingly a
line violating (5) is composite, with no exceptional small-associate escape.
The singleton is `[2]`, an inert prime of norm 4.

There is no inference from (5) to `3 does not divide n` or to oddness.
For example the independently checked exact-pool square of order 6 in
[the retained certificate](../inputs/eisenstein_square6.json) has all fourteen
required prime-element sums. That finite construction excludes both proposed
conditions as necessary conditions for this baseline.

### A constructive odd-order ramified audit

**Lemma E-residue-square.** Let `n=2m+1>=3`. For every integer
`K=nm+k`, `1<=k<=n-1`, there is a binary `n` by `n` array with exactly
`K` ones for which every row, column, and both long diagonals have
`2*(number of ones)-n` nonzero modulo 3.

**Proof.** Use indices `0,...,n-1` and put a one at `(i,j)` exactly when
`j-i mod n` belongs to `{1,...,m}`. Each row and column has `m` ones.
The main diagonal has zero; the other diagonal has `m`, since multiplication
by 2 permutes the residues modulo odd `n`. Write `c=(n-1)/2`.

Choose `q` from `{k,k-1}` with `q not equal to -n mod 3`; two consecutive
integers cannot both be forbidden. If `q=k`, add ones at any `k` main-diagonal
positions excluding `(c,c)`. If `q=k-1`, add `q` such diagonal positions,
leaving `c` and at least one other index `v` unused. Exactly one of `(c,v)`
and `(v,c)` is zero in the original array; add a one there. Its row and
column were not used for diagonal additions. It lies on neither long
diagonal, since `v!=c`.

The resulting row and column counts are `m` or `m+1`, so their signed sums
are `-1` or `+1`. The anti-diagonal still has `m` ones. The main diagonal
has `q`, which was chosen to avoid (5). The total number of additions is
`k` in both cases. QED.

For the actual square pool, (3)--(4) give
`K=N_+=(n^2-I+epsilon)/2`, so `k=(n-I+epsilon)/2` lies in the stated range
for every sufficiently large odd `n`. Assign the positive-residue entries
bijectively to the ones and the negative-residue entries to the zeros.
This proves ramified-ideal feasibility on that entire tail. It does not
assert prime line sums or simultaneous feasibility at other prime ideals.
The next construction includes even orders as well.

### All-order ramified square feasibility

**Lemma E-residue-square-all.** For every `n>=40` and every integer
`K` with `n^2/4<=K<=3n^2/4`, a binary square with exactly `K` ones
passes the ramified test on every row, column, and both diagonals.
Consequently the actual canonical Eisenstein square pool passes this
necessary test for every sufficiently large order, with no congruence
restriction on that order.

**Proof.** The proof uses constant `3` by `3` blocks, each of which
can be changed from zero to one at a cost of nine ones. A line meeting
such a block in three cells sees no change modulo three. The following
boundary patterns ensure that both diagonals also meet free blocks
in zero or three cells. Detailed integer code is in
[local_audit.py](../code/local_audit.py), function `residue_square`.

First let `n=3m+r`, where `r=1` or `2`. Partition the first `3m`
indices into consecutive triples. The bottom `r` rows and rightmost
`r` columns initially consist entirely of ones. Among the interior
`3` by `3` blocks, protect every block meeting the anti-diagonal and
set it identically one. There are at most `2m` protected blocks.
All other interior blocks are free and initially zero. Interior rows
and columns have signed sums congruent to `r` or `-r`, independently
of the free blocks. The main diagonal receives complete interior
triples and `r` final ones, hence is nonzero. The anti-diagonal is
identically one and is also nonzero.

For `r=1`, flip `h` entries of the last column and `g` entries of
the last row from one to zero, avoiding both endpoints of the
anti-diagonal and the bottom-right corner. Choose
`h,g` in `{0,1,3,4}`. Each interior row/column still has its single
boundary sign, so remains nonzero. The last column and last row have
signed sums `n-2h` and `n-2g`, respectively; neither vanishes modulo
three because neither count is `2 mod 3`. The sums `h+g` cover every
residue modulo nine (indeed every integer from zero through eight
occurs). Hence this boundary adjustment can put the total number
of ones in any prescribed residue class modulo nine.

For `r=2`, flip both right-boundary entries in each of `h` interior
rows, and both bottom-boundary entries in each of `g` interior
columns. Avoid the first two row/column indices, which carry the
anti-diagonal endpoints. Choose `h,g` in `{0,2,3,5}`. Each affected
interior line changes its two equal boundary signs simultaneously,
so it still has signed sum `+2` or `-2` modulo three. The two
boundary columns have sums `n-2h`, and the two boundary rows have
sums `n-2g`; these are nonzero because neither count is `1 mod 3`.
The residues of `2(h+g)` cover all of `Z/9Z`. Neither diagonal has
been affected. Again the total can be placed in any residue modulo
nine.

After selecting the appropriate boundary adjustment, fill any desired
number of the free blocks with ones. The minimum available total is
at most `8n-7` for `r=1` and at most `10n-16` for `r=2`, before
the subtractive adjustment; the maximum is at least `n^2-8` and
`n^2-20`, respectively. Every integer of the chosen residue between
these endpoints is obtained, in steps of nine. For `n>=40`, the
whole interval `[n^2/4,3n^2/4]` lies inside these capacity bounds.

It remains to treat `3|n`. Put `n=3m+3`; the first `3m` indices are
again partitioned into triples, and now the boundary has width three.
For each triple of interior rows, set its right boundary to three
copies of one fixed nonmonochromatic binary triple. For each triple
of interior columns do the analogous thing on the bottom boundary.
Use `(1,1,0)` for the first row group and first column group, and
`(1,0,0)` for the other groups initially. The bottom-right `3` by `3`
corner starts with ones at `(0,0),(1,2),(2,1)` in local coordinates.
It has three ones, every row and column has one, and its main diagonal
has one. It may receive zero, one, or two extra ones, in that order
at `(0,1)` and `(1,0)`; all its rows and columns then have one or two
ones and its main diagonal still has one.

All full rows and columns reduce modulo three to their nonmonochromatic
boundary triple. The main diagonal reduces to the corner's main
diagonal. Reflection respects the triple partition because `3|n`.
The anti-diagonal's interior contributions are therefore multiples
of three, and its two boundary triples both have signed sum `1`;
its residue is `2`, which is nonzero. The corner is disjoint from
the anti-diagonal.

Changing the right-boundary pattern in one of the second and third
row groups from `(1,0,0)` to `(1,1,0)` adds three ones. Do this in
zero, one, or two groups, independently of the zero/one/two extra
corner ones. The nine choices cover every residue modulo nine and
preserve all the just-checked line residues. The initial boundary
contains `2n+3` ones, so its nine alternatives have between `2n+3`
and `2n+11` ones. All `m^2` interior blocks are free. Filling them
gives a maximum of at least `n^2-4n+12`, in steps of nine. These
capacities again contain the stated interval when `n>=40`.

Finally (3)--(4) imply that the actual count `N_+` is asymptotic to
`n^2/2`, so it eventually lies in this interval. Map the actual prime
entries to the two binary color classes. This proves the final
assertion and only the ramified test. QED.

## 3. Sharp finite Eisenstein failures

These are exceptions to an eventual-existence target, not refutations of it.

### Order two, both dimensions

For an order-two square every pair of cells is a required line. The same is
true for the order-two signed cube: any two distinct vertices specify which
coordinates vary and their signs. Both exact pools contain `(2,0)` and
`(3,1)`, whose opposite residues force their sum `(5,1)` to have norm 21.
Thus both baseline instances are impossible. Equivalently, all required
two-entry lines could avoid zero in `F_3` only if every entry had the same
nonzero residue, which these pools do not.

### Order-four square

The first sixteen Eisenstein representatives, in the frozen order, are


```math
\begin{split}
 &(2,0),(3,1),(3,2),(4,1),(4,3),(5,2),(5,3),(5,0),\\
 &(6,1),(6,5),(7,3),(7,4),(7,1),(7,6),(9,4),(9,5).
\end{split}                                                     \qquad\text{(6)}
```


They have exactly seven residues `+1` and nine residues `-1`.
A length-four line has zero residue exactly when it contains two `+1`s.
Suppose there were a placement avoiding this in all ten lines, and mark
the seven positive residues with ones. Row degrees avoid 2, so their
multiset must be one of


```math
(4,3,0,0),\quad(3,3,1,0),\quad(4,1,1,1).        \qquad\text{(7)}
```


The first case has three columns of degree 2. In the second, the two
degree-three rows overlap in at least two columns; the singleton can
increase at most one such column, leaving another of degree 2. In the
third, a full row contributes one to every column. The three singleton
rows must place all their ones in one column: any distribution `2+1`
or `1+1+1` leaves a column with exactly two ones. Thus the seven ones
form the union of one full row and one full column.

The two long diagonals of a four-square are disjoint. At least one avoids
the intersection of that row and column; that diagonal meets the full row
and full column in two distinct cells and has exactly two ones. This is
again forbidden. The contradiction proves impossibility. The certificate
[eisenstein_square4_obstruction.json](../inputs/eisenstein_square4_obstruction.json)
independently checks the same finite residue problem; the argument above
does not depend on search exhaustion.

### Order-three full signed cube

In a length-three line, residues in `{+1,-1}` sum to zero precisely when
the line is monochromatic. The 49-line hypergraph on `[3]^3` has no
two-coloring without a monochromatic line. Here this finite combinatorial
fact is proved by the retained exhaustive binary decision-tree certificate
[eisenstein_cube3_obstruction.json](../inputs/eisenstein_cube3_obstruction.json),
whose verifier independently regenerates the line sets, checks both
children at every branch, replays each forced assignment, and validates
the displayed monochromatic line at each contradiction leaf. No bound on
the color counts is used.

Consequently the order-three Eisenstein signed cube is impossible for any
canonical-sector pool of nonramified primes, in particular for the actual
first 27 representatives. This is a finite proof by exhaustive cases;
it supplies no asymptotic obstruction.

## 4. Other prime ideals and all additive compatibility equations

For a fixed prime ideal `p` of norm `Q`, precisely one prime-element associate
class generates `p`. The pool therefore contains either zero or one entry
with residue zero modulo `p`; it is wrong to assume that all entries avoid
every small ideal. Every other pool entry has nonzero residue there.

If a prime line sum has residue zero modulo `p`, it must generate `p`, hence
have absolute value `sqrt(Q)`. The positive-sector lower bounds exclude this
when `n>sqrt(Q)` in the Gaussian case and `2n>sqrt(Q)` in the Eisenstein case.
In those ranges, all required line sums must be nonzero in `O/p`. Their
parallel-family totals and intersecting-family identities below must hold
in that quotient. These are necessary tests; residue counts alone are not
a proof that a simultaneous residue arrangement exists.

### Squares

Rows `r_i`, columns `c_j`, and the two diagonals `d_+,d_-` satisfy


```math
\sum_i r_i=\sum_j c_j=T.               \qquad\text{(8)}
```


For every `n>=5`, (8) is the complete compatibility condition for a lift
by arbitrary ring elements. First lift the rows and columns using an
anchored last row/column. The zero-margin rectangle with row endpoints
`1,2` and column endpoints `1,3` has signed main-diagonal sum 1 and
anti-diagonal sum 0, since all its coordinate sums are at most 5 while
`n+1>=6`. Its column-reflection has the opposite diagonal effect.
Arbitrary coefficients of these two rectangles set both diagonal sums.
The argument uses only addition and subtraction and works over every
abelian group, including all ideal quotients.

### Cubes, including even order

Use indices `1,...,n`, reflection `rho(t)=n+1-t`, and axis targets


```math
U(y,z)=\sum_x a(x,y,z),\quad
 V(x,z)=\sum_y a(x,y,z),\quad
 W(x,y)=\sum_z a(x,y,z).
```


The axis identities are


```math
\begin{aligned}
 \sum_yU(y,z)&=\sum_xV(x,z) &&\text{for each }z,\\
 \sum_zU(y,z)&=\sum_xW(x,y) &&\text{for each }y,\\
 \sum_zV(x,z)&=\sum_yW(x,y) &&\text{for each }x.
\end{aligned}                                                    \qquad\text{(9)}
```


There are six face families, indexed by a varying pair `xy,xz,yz` and
a sign `sigma` equal to the identity or reflection. They satisfy


```math
\begin{aligned}
 \sum_zF_{xy}^{\sigma}(z)&=\sum_tW(t,\sigma(t)),\\
 \sum_yF_{xz}^{\sigma}(y)&=\sum_tV(t,\sigma(t)),\\
 \sum_xF_{yz}^{\sigma}(x)&=\sum_tU(t,\sigma(t)).
\end{aligned}                                                    \qquad\text{(10)}
```


Also require `sum_{y,z}U(y,z)=T`. Equations (9) make all three directional
totals equal. The four body targets have no further additive identity
in the following range.

**Lemma rank-two-SI.** For every `n>=10`, equations (9)--(10) are the
complete compatibility conditions for the full signed-line map over
either ring, and indeed over any abelian group. Over the integers the
map has saturated image and rank `3n^2+3n-1`. Its two-coordinate ring
version has integer rank `2(3n^2+3n-1)`. Specifying `T` reduces the
integer affine rank by two for ring-valued targets.

**Proof and even-order extension.** The axis lifting theorem works with
any anchor index, not only a central one. Its joint kernel is generated
integrally by the cuboids


```math
(e_i-e_o)\otimes(e_j-e_o)\otimes(e_k-e_o),
```


where `o` is an arbitrary index. There are `floor(n/2)>=5` noncentral
reflection orbits for every `n>=10`. Given two face-family levels `u,v`,
at most two of these orbits meet them, so choose three remaining distinct
orbit representatives `t,a,b`. Then


```math
(e_t-e_a)\otimes(e_t-e_b)\otimes(e_u-e_v)                \qquad\text{(11)}
```


has face image `e_u-e_v` in the `xy,+` family and zero in the other
five face families and all body lines. Coordinate permutations and
reflections give all six versions. Four distinct noncentral orbits with
representatives `t,a,b,c` give


```math
(e_t-e_a)\otimes(e_t-e_b)\otimes(e_t-e_c),               \qquad\text{(12)}
```


whose only body effect is a unit at the `(+,+)` body, and whose three
face effects are zero-total transfers. Cancel those by (11); reflect
coordinates for the other bodies. These calculations do not use a
central index or oddness. After lifting the axes, (10) says each residual
face family has total zero, so these transfers lift it; (12) lifts the
four independent body residuals. This proves sufficiency over every
abelian group without any division.

The axis rank is `3n^2-3n+1`; the extra image has rank
`6(n-1)+4`, giving the stated rank. The equations describe the entire
integer image, so it is saturated. Finally both rings are free abelian
groups on the displayed two-element basis, so the calculation applies
to each coordinate. This proves an algebraic lift, not a legal
coordinatewise permutation of prescribed entries. QED.

At smaller orders, further relations or torsion may occur. The scalar
source explicitly documents such effects at orders 3 and 5. They cannot
be dismissed by a rational-rank computation.

## 5. The additive difference group and unit-difference routing

Set


```math
D_G=(1+i)\mathbb Z[i]
     =\{(x,y)\in\mathbb Z^2:x+y\equiv0\pmod2\},
 \qquad D_E=\mathbb Z[\omega].                           \qquad\text{(13)}
```


Every difference of Gaussian pool entries lies in `D_G`. By the seventh
entry this upper bound is attained: the disjoint pairs


```math
(1,2)\to(2,1),\qquad (3,0)\to(4,1)
```


have increments `(1,-1)` and `(1,1)`, of determinant 2. Thus the additive
group of all pool differences is exactly `D_G` for every prefix length
at least seven. In particular it is larger than `2 Z^2`.

For Eisenstein primes the disjoint pairs


```math
(2,0)\to(3,1),\qquad (3,2)\to(5,3)
```


already have increments `(1,1),(2,1)` with determinant `-1`, so the
full additive difference group is `D_E` by prefix length seven. If one
requires both endpoints to have the same ramified residue, the disjoint
pairs `(2,0)->(3,2)` and `(3,1)->(5,2)` have increments `(1,2),(2,1)`
of determinant `-3`; these generate precisely `(1-omega)O`. These
finite witnesses prove spanning only, not a repeated-gap supply.

**Lemma unit-difference.** For either ring, any nonzero ideal `q`, and
any `v` in the corresponding group `D_K` in (13), there are reduced
residue classes `u,u+v` modulo `q`.

**Proof.** Factor `q` into prime powers. In each residue field choose
`u` different from 0 and `-v`, and lift this class modulo the prime
power. A field of size at least three always permits the choice. The
only residue field of size two in either ring is the Gaussian field
modulo `(1+i)`. There `v=0`, so there is only one forbidden value and
the nonzero class works. Chinese remaindering finishes the proof.
For Eisenstein primes above 2 the residue field has four elements,
not two. QED.

For Gaussian moduli divisible by `(1+i)`, every difference of units
lies in its residue kernel. Thus `D_G` is the exact obstruction, not
an arbitrarily strengthened congruence. For other moduli its image is
the full quotient. There is no corresponding size-two obstruction in
the Eisenstein ring.

Let `Gamma` be any full-rank additive sublattice of `O`, of index `d`.
The elementary finite-group theorem applied to `O/Gamma` gives


```math
dO\subseteq\Gamma,
            \qquad dD_K\subseteq\Gamma.                 \qquad\text{(14)}
```


Choose the bases `(1,1),(1,-1)` for `D_G` and `(1,0),(0,1)` for `D_E`.
Modulo `dD_K`, each of these two basis increments is the difference
of two reduced residue classes by the preceding lemma. In fact their
endpoint residues can be chosen uniformly in the modulus using actual units:


```math
1+i=1-(-i),\quad 1-i=1-i;
 \qquad 1=(1+\omega)-\omega,\quad
 \omega=(1+\omega)-1.                                  \qquad\text{(15a)}
```


If suitable
actual disjoint equal-gap prime tuples in these endpoint classes are
supplied analytically, the ordinary incidence paths and cuboids can
route each basis coefficient modulo `d`. The remaining error lies
in `dD_K`, hence in `Gamma` by (14).

The last paragraph is a precise algebraic interface. It does not
infer actual prime pairs from the Chinese remainder theorem. It also
does not assume that an additive sublattice is an ideal or that a
gap can be multiplied or rotated physically. The groups `dD_K` used
as analytic moduli are actual ideals, while the correction lattice
`Gamma` may be only a `Z`-module.

## 6. Two independent repeated directions from density alone

The following elementary lemma supplies true disjoint pairs and uses no
fixed-gap prime conjecture. It is useful for seeds; it does not supply
the large-increment stages of a complete reservoir.

**Lemma two-direction-seeds.** Let `S` be a set of `m` integer points
in a rectangle containing at most `L` integer coordinate values in
each direction. Suppose `m>=8L`. Put


```math
H=\left\lceil\frac{8L^2}{m}\right\rceil,
 \qquad k=\left\lfloor\frac{m}{16H}\right\rfloor.
                                                               \qquad\text{(15)}
```


There are `k` pairwise disjoint pairs with one common horizontal
increment `(g_1,0)`, and `k` further pairs with one common vertical
increment `(0,g_2)`, all endpoints distinct, where `1<=g_j<=H`.
For `k>=1` their generated additive lattice is exactly
`g_1 Z x g_2 Z`, of index `g_1*g_2`.

**Proof.** In each horizontal row join consecutive points of `S`.
There are at least `m-L` edges. The sum of all their lengths is less
than `L^2`, by telescoping within each row. At most `m/8` edges have
length greater than `H`, so there are at least `3m/4` short edges.
Some integer gap `g_1<=H` occurs at least `3m/(4H)` times. Its graph
is a disjoint union of paths: its edges increase the first coordinate
by a fixed positive integer. Alternating edges in each path gives a
matching containing at least half of all its edges. Retain exactly
`k` edges and delete their endpoints.

At least `m/2` points remain, since `2k<=m/(8H)<=m/8`.
Joining consecutive points in vertical columns now gives at least
`m/2-L>=3m/8` edges; their total length is again less than `L^2`.
Deleting at most `m/8` long edges leaves at least `m/4` short edges.
One vertical gap occurs at least `m/(4H)` times and has a matching
of at least `m/(8H)>=k` edges. Its endpoints are fresh by construction.
The lattice and determinant statements are immediate. QED.

This argument is valid in Eisenstein coefficient coordinates, where
the two displayed directions have angle 120 degrees in the plane.
It does not rotate any prime or move an endpoint out of the fixed pool.
In the Gaussian case both gaps are automatically even; the resulting
rectangular lattice may have larger index than the full difference
group `D_G`, and the routing step (14) is still needed.

There is also a transparent deletion invoice. If an original set has
`m_0` points in this rectangle and at most `Q<=m_0/2` have already
been reserved elsewhere, apply (15) to the surviving set, which has
`m>=m_0/2`. In particular `m_0>=16L` suffices, and one may use
`H_0=ceil(16L^2/m_0)` and guarantee
`floor(m_0/(32H_0))` pairs in each direction. All removals, including
the first direction, have already been charged in this calculation.

If an analytically certified box of side comparable to `L` contains
`m_0>=c L^2/log R` available pool primes, the lemma gives
`g_j=O(log R)` and `Omega(L^2/log^2 R)` pairs per direction, after
deletion of at most half that box's supply. Grouping four disjoint
pairs of a direction gives an actual eight-cell cuboid trade; only
the integer part of one quarter of the matching count can be used.
Geometric placement and competition with all other reservoir families
remain separate demands.

For a narrow square of width `W=R/log^c R`, the displayed inference
is valid only after the analytic theorem proves the box count with
the enclosing-radius error paid. It cannot be applied to a polynomially
shrinking box from a whole-sector count. Nor do the short seed gaps
alone provide corrections of size `R`: a complete reservoir needs a
separate multiscale growth argument and a bounded nonnegative-choice
decoder.

## 7. Normalization alternatives and current admissibility boundary

The canonical Eisenstein inert representative `2` has residue `-1`
modulo `1-omega`. It proves that the sector convention and a demand
that every representative have residue `+1` cannot be imposed
simultaneously. Any nontrivial unit rotation leaves the chosen
half-open sector; it changes the input element and all sums containing
it. A primary convention is therefore a different pool theorem.

Moreover the condition `z=1 mod (1-omega)` alone leaves three unit
associates, since three of the six units map to 1. It is not by itself
a unique representative convention. A deterministic additional rule
must be supplied. In a pool normalized to that residue, a line of
length divisible by three would have to equal a ramified associate
if it were prime. A size or total-sum argument is still needed when
unit choices permit cancellation; the present positive-sector size
proof does not transfer automatically to such a modified pool.

The unconditional local conclusions currently established here are:

| Ring and family | Proven obstruction or feasibility statement |
|---|---|
| Gaussian square and signed cube | Every even order fails; the ramified test is automatic at every odd order |
| Eisenstein square | Orders 2 and 4 fail; every sufficiently large order passes the ramified test for the actual counts; order 6 gives an exact even, divisible-by-three prime example |
| Eisenstein signed cube | Orders 2 and 3 fail; no eventual congruence classification is proved solely by this local audit |
| Either ring, square `n>=5` | Exact additive target identities are (8), coordinatewise |
| Either ring, signed cube `n>=10` | Exact additive target identities are (9)--(10), coordinatewise; even order is included |

There is no circular definition of admissibility here. Gaussian oddness
is a proved necessary infinite-tail condition. For Eisenstein arrays,
all sufficiently large orders remain the desired target; neither
oddness nor `3 does not divide n` is inserted as an assumption. Passing
ramified, small-ideal, or integer-image checks is not promoted to
global feasibility. The analytic target construction and complete
physical correction theorem must close that gap.
