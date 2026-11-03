# A physical axis controller for the exact four-dimensional prime pool

Author: `/root/hyper_axis`. This is new successor-lane source; the author did
not write the inherited PR79 incidence or cube-controller manuscripts. Labels
below are local to this manuscript. The result is a conventional proof, subject
to the successor lane's independent review. It is neither a kernel-checked
theorem nor a numerical threshold assertion.

## 1. Source boundary, statement, and choice of architecture

The frozen starting point is PR79 scientific revision
`a2445962ec6e06b2a893980fb7a183057eb9bcee`, delivered at
`cdb7879e358f93afa54b685027a27692d22635a9`. The imports are exactly:

* [incidence.md, Sections 1--3](incidence.md): the saturated axis image, odd
  lifting statement, and the tensor-expander coefficient theorem, including
  its dimension-dependent rounding term;
* [cube_controller.md, Sections 2--3](cube_controller.md): the elementary
  growing common-gap selection, the repeated-difference argument, and the
  degree-64 graph. The graph existence input is baseline controller Lemma F1
  at scientific revision `4ac266e7c4994a8502eb2a0c57d6b1d3fbd801c5`;
* [cube_targets.md, imported interfaces](cube_targets.md#imported-interfaces-and-their-exact-boundary):
  the printed Thorner--Zaman short-interval progression consequence. Its
  threshold is ineffective. No older fixed-gap or ternary target interface is
  substituted for it.

The packing, depletion, physical realization, and five-level composition in
this manuscript are new arguments. In particular, the general target theorem
CT and the general integer axis lift are not physical-controller imports.

Write the coordinates as `(x,y,z,w)`. Let `A_d` be the tensor of sums on lines
parallel to coordinate `d`. For example, `A_x(y,z,w)` sums over `x`.
For a tensor indexed by all coordinates except `d`, write `S_e` for summation
over its coordinate `e`. The exact compatibility equations are

`S_e A_d = S_d A_e` for every distinct `d,e`.                 (AC)

Both sides are arrays indexed by the two remaining coordinates. In addition,
the sum of each complete directional target tensor is the fixed total `T`.
These are integer equations, not merely equations modulo an auxiliary gap.

For odd `n`, let `P_n={p_2,...,p_(n^4+1)}`, `X=max P_n`,
`T=sum P_n`, `m=T/n^4`, and `mu=nm=T/n^3`. Put

`K_j=ceil(n^((15+j)/25))` for `0<=j<=4`, `delta=n^(-1/5)`.    (S)

Thus the five exponents are `.60,.64,.68,.72,.76`.

**Theorem U4 (physical axis universality).** There is an integer `N_U4` such
that, for every odd `n>=N_U4` and every four-tuple of odd integer target tensors
`A'_d` satisfying (AC), directional total `T`, and

`|A'_d(u)-mu|<=K_0 X` for every direction and index,           (TB)

there is a bijection from `P_n` to `[n]^4` having exactly these four axis-target
tensors. The threshold and constants are uniform in the entire target tuple.
Targets need not be prime or distinct.

The proof first establishes U4 on its own. Sections 5 and 7 also give the
interfaces needed to reserve a later signed-line controller: the axis supports
can be packed around any pre-reserved set of axis load `o(n)`, avoid every full
four-coordinate diagonal, have separate prefix and macro-pass caps on every
other signed line, and have whole-reservoir contribution range at most `2X`.
These combinatorial interfaces do not assert that arbitrary pre-reserved
values can be centered; their centering must satisfy the explicit conditions
in Section 7.3.

Two architectures were compared. Calling the three-dimensional theorem
separately in the `w`-slices does not solve the problem: those slice pools are
not its prescribed pools, their totals have not been corrected, and the
`w`-lines couple all slices. A direct tensor right inverse supplies numeric
arrays but supplies no disjoint prime swaps. The chosen hybrid uses staged
hyperplane and plane totals, ordinary line transfers, then the proven bounded
tensor inverse on ranks two and three. Each coefficient is paid for by its
own pre-packed physical reservoir. Separate correction levels are retained
because their increasingly larger incidental drifts enter the next level.

## 2. Fresh prime supplies, including grouped equal-gap pairs

The prime number theorem gives

`X~4n^4 log n`, `m~X/2`, and `mu~2n^5 log n`.                 (PS)

Set

`F=ceil(100 log X)`,
`P=ceil(4096 F^2)+32F ceil(log_2 X)`,
`Q_*=2^40 n^3 K_4`.                                        (PQ)

Here `Q_*` is a global deletion allowance, not a claim that all those entries
are used. Section 4 gives the smaller actual axis invoice. Other controllers
may consume the difference only if their own invoice is proved.

### 2.1 Uniform progression counts after worst-case deletion

The selected gap below satisfies `2<=g<=16ceil(log_2 X)` and is even. For all
reduced classes modulo any such `g`, every fixed positive-length proportion
of `[X/4,3X/4]` contains `>>X/(g log X)` primes. Define

`I_-=[m-X/6-delta X,m-X/6+delta X]`,
`I_+=[m+X/6-delta X,m+X/6+delta X]`.

They lie in `[X/4,3X/4]` eventually. Each reduced class has
`>>delta X/(g log X)` primes in each interval, uniformly in `g` and the class.
To check the analytic import, `log(delta X)/log X ->19/20`; one may fix any
exponent strictly between `7/12` and `19/20` and then the source's positive
power slack dominates its polylogarithmic modulus factor. Endpoints are all
comparable to `X`. Consequently the quoted progression consequence applies
throughout the large odd tail with uniform, ineffective constants.

In the worst allowed modulus, the smaller supply has order at least a
constant times `n^(19/5)/log n`. The deletion allowance has order
`n^(94/25)`. Since `19/5-94/25=1/25>0`,

`Q_*=o(delta X/(g log X))` uniformly in the selected gap.      (D)

Thus deletion of any at most `Q_*` previously reserved endpoints leaves at
least half every stated supply eventually. This charges all previous
allocations even if all of them lie in one requested interval and class.

### 2.2 Seed selection precedes all other prime allocation

The elementary selection in cube_controller.md, Section 2.1, applies at this
new value of `X`: pair consecutive primes in `[X/4,3X/4]`, pigeonhole the
`O(log X)` short even gaps, then pigeonhole the lower class modulo the chosen
gap. It supplies an even `g` in the stated range and
`>>X/log^3 X` mutually disjoint pairs `(p,p+g)` in one reduced lower class
`r mod g`. No fixed-gap conjecture or prime-constellation input is used.

Select and reserve all required seed pairs now. The axis demand is
`O(n^3 P)=O(n^3 log^2 X)`, and

`n^3 log^2 X=o(X/log^3 X)`.

This comparison holds for every sufficiently large `n`. It remains true if
`O(n^2 P)` extra fixed-size compound stages are included. Every seed endpoint
is thereafter charged to (D). An unselected prime, including any last member
unpaired by the selection procedure, remains in `P_n` for final filling.

### 2.3 A finite grouped-pair growth lemma

Suppose a fresh set `S` in one residue class modulo `g` lies in an interval
of length at most `X`, with `|S|>=X/(gF)` and `F>=4`. If

`4096gF^2<=R<=X`,

there are at least **40 mutually disjoint pairs** with a common actual gap
`d`, divisible by `g`, and

`R/(32F)<=d<=R`.                                            (G40)

Indeed partition the interval into at most `2X/R` bins of length at most `R`.
One has `s>=R/(2gF)` points. At least `s^2/4` unordered pairs have distance
at least `gs/16`: fewer than `s^2/16` can have smaller positive distance on
the `g`-grid, and `s` is large enough to absorb the diagonal term. There are
at most `R/g` possible positive differences. One difference therefore has
at least `R/(16gF^2)>=256` edges. Its graph has maximum degree two, so greedy
matching selects at least a third as many edges; in particular 40 disjoint
pairs. Its gap is at least `gs/16>=R/(32F)`.

After the entire deletion allowance, the common reduced class in the long
interval still has at least `X/(8g log X)>X/(gF)` primes eventually. Thus
(G40) applies afresh at every request. Selecting only the one, two, or four
pairs needed for an axis stage leaves all other candidate pairs unreserved.
The larger constant also permits a later compound stage requiring at most
40 pairs; it does not waive that stage's geometry proof.

Begin each scalar reservoir with `ceil(4096F^2)` seed stages of gap `g`.
For a checkerboard stage use the required number of distinct seed pairs.
Its subset sums cover the complete `g`-grid interval from zero to
`R>=4096gF^2`. If `R<X`, append a stage from (G40). Since `d<=R`, its two
translated subset-sum intervals overlap on the grid. Their union covers the
grid to `R+d`, and `d>=R/(32F)` gives multiplicative growth. The inequality
`log(1+1/(32F))>=log(2)/(32F)` proves that at most
`32F ceil(log_2 X)` stages suffice. The final endpoint is at most `2X`.
Thus `P` bounds the entire uncontrolled prefix, including all actual seed and
growth stages. This proves a complete bounded subset-sum interval, not just
a gcd assertion.

### 2.4 Macro stages, residues, and two-sided capacity

After arbitrary prior deletion, the fresh lower and upper sets in `I_-` and
`I_+`, in class `r`, each have `>>delta X/(g log X)` members. Pigeonhole their
pair differences, of which at most `X/g+1` are possible. Some difference has
`>>delta^2 X/(g log^2 X)` representations. For a fixed positive difference
these are already a matching because the two endpoint intervals are
disjoint. This quantity tends to infinity uniformly in `g`, so 40 such pairs
are available eventually at each request. Every chosen gap is in `[X/4,X/2]`
and every pair midpoint is within `delta X` of `m`.

The same argument with reduced lower class `-1` and reduced upper class `+1`
supplies any required group of at most 40 pairs having the same actual gap
`2 mod g`. These are the separate residue stages. The total target of an
aggregate may be nonunit; neither this supply nor the residue repair asks for
primes in a nonunit class. Pool primes dividing `g` remain in the unused pool.

Append `J_j=ceil(32K_j)<=33K_j` macro stages to each level-`j` reservoir.
Its total scalar gap `R_b` obeys

`8K_jX<=R_b=O(K_jX)`.

The prefix already reaches `X`, so these appendages preserve complete grid
coverage. Choose a subset with scalar sum
`q_b=g floor(R_b/(2g))`, and alternatively its complement. These are two
legal reference configurations on the same distinct entries and cells. Their
scalar sums differ by at most `g`, and from either configuration every
multiple of `g` of signed magnitude at most `3K_jX` is attainable eventually.
Each stage switches all of its pairs together. The independent random
objects in Section 7 will be these two whole-reservoir choices, not cells or
individual stages.

## 3. Physical shapes and the five preserved-data contracts

Fix a loopless undirected multigraph `G` on `[n]`, with separately labeled
parallel edges, maximum degree `Delta=64`, and

`|partial S|>=8 min(|S|,n-|S|)`.

The cited Lemma F1 supplies such a graph for every sufficiently large order;
there is no prime-power or subsequence restriction. Write `B` for an arbitrary
oriented incidence matrix; it has one `+1` and one `-1` per edge. There are at
most `32n` edges.

For `k=1,2,3`, a stage on `k` selected oriented coordinate pairs `(u_i,v_i)`
changes the array by the tensor product `d tensor_(i=1)^k(e_(u_i)-e_(v_i))`,
embedded with all other coordinates fixed. Equivalently, at the vertex
indexed by bits `epsilon in {0,1}^k`, its change is

`d (-1)^(epsilon_1+...+epsilon_k)`.                            (CB)

It has a physical realization using `2^(k-1)` disjoint equal-gap pairs. Pair
the vertices along the last selected coordinate. At its bit-zero endpoint,
put the lower prime when the sum of the other bits is even and the upper
prime when that sum is odd. Put its partner at the bit-one endpoint. Swap
all pairs. This gives (CB) cell by cell. Pairs in different stages are also
disjoint. Hence every operation is a permutation of the prescribed entries.

The levels are the following. A reservoir means its complete prefix and all
macro stages; position restrictions apply across both, not just within a pass.

| Level | Types and multiplicity | Physical stage | Native correction | Exactly preserved |
|---|---|---|---|---|
| 0 | Each `w`-edge, `n^2` reservoirs | Pair at `(x,y,z,w)` and `(x,y,z,w')`; each reservoir uses distinct `x`, distinct `y`, distinct `z` across its stages | Totals of the two `w` hyperplanes | Every `w`-axis sum |
| 1 | Each fixed `w`, each `z`-edge, `n` reservoirs | Pair at common `(x,y)`; each reservoir uses distinct `x` and distinct `y` | Totals of the two `(z,w)` planes | Every `z`-axis sum; all `w`-hyperplane totals |
| 2 | Each `(z,w)` plane, two separate copies of `G` | `x`-edge pairs at distinct free `y`, and transposed `y`-edge pairs at distinct free `x` | The `y`-axis targets, respectively the `x`-axis targets | The other horizontal family, and all `(z,w)` plane totals |
| 3 | Each fixed `w`, every ordered pair of `x,y` graph edges | Four-cell `x,y` checkerboards, two equal-gap pairs, distinct free `z` | The `z`-axis target matrix in that `w` slice | Every `x`- and `y`-axis sum |
| 4 | Every ordered triple of `x,y,z` graph edges | Eight-cell `x,y,z` checkerboards, four equal-gap pairs, distinct free `w` | The `w`-axis target three-tensor | Every `x`-, `y`-, and `z`-axis sum |

For instance, the last level is **not** a formal four-dimensional increment
or an eight-pair full hypercuboid. Its eight cells at one chosen `w` alter
eight `w`-axis sums by `d B_e tensor B_f tensor B_h`; each old axis sees either
zero cells or a cancelling pair. The later signed-line controller may need
16-cell/eight-pair shapes, which are outside this axis proof.

Each level-0 graph edge has complete signed scalar capacity at least
`3n^2K_0X`, by adding its `n^2` reservoir intervals; level 1 similarly has
`3nK_1X`. Level 2 has `3K_2X` per edge. Levels 3 and 4 have `3K_3X` and
`3K_4X` per edge pair and edge triple. Sums of intervals on the same `g`-grid
are complete intervals on that grid. Thus both signs and every integer grid
coefficient are provided, with no assumption of continuous or fractional
switching.

## 4. Exact resource invoice

The numbers of main reservoirs are at most

`32n^3, 32n^3, 64n^3, 1024n^3, 32768n^3`

at levels `0,...,4`. Counting `2,2,2,4,8` entries per stage, respectively,
the entire prefix invoice is `266496 n^3 P`. The macro invoice is at most

`2112n^3K_0 + 2112n^3K_1 + 4224n^3K_2`
`+ 135168n^3K_3 + 8650752n^3K_4`.                              (I)

Section 6 adds fewer than `10n^3g` entries. Once `P,g<=K_4`, the sum is
strictly less than `2^24 n^3K_4`, hence less than `Q_*`. In particular it is
`o(n^4)`, and no use of a single prime endpoint has been counted twice.

These are upper bounds on **reserved pool entries**. At every later supply
request all entries already selected, including unused switch options, are
deleted from the fresh pool. Geometry is planned first; values are then
allocated to its finitely many stages under this invoice.

## 5. Packing, exceptional axes, and protected signed lines

For `s in [n]`, put `bar s=n+1-s`, and let the reflection orbit of `s` be
`{s,bar s}`. A full signed line whose varying-coordinate set is `S` contains
only points whose coordinates in `S` share a reflection orbit. This elementary
observation is used for avoidance; it does not identify different lines.

**Packing lemma AP4.** Suppose a previously reserved set `R` has at most
`M_R=o(n)` cells on each axis line. All axis stages in Sections 3 and 6 can
be packed disjointly from `R` and from one another. In each separate pass
with at most `L` stages per reservoir, every axis or nonaxis signed line has
at most `cL` new cells, where one may take `c=10^15`. Every axis support
avoids all eight full four-coordinate diagonals. Every other nonaxis signed
line meets any one entire axis reservoir in at most one stage, and in at most
two cells of that stage.

There is a separate prefix pass for each level and each level-2 orientation,
a separate macro pass for each such shape, and separate residue-shape passes.
Each pass is allowed the
constant `c`; summing the finitely many passes preserves the stated big-O
bounds. One does not charge all earlier stages at the largest exponent when
estimating the drift of an earlier correction level.

### 5.1 Orbit restrictions and persistence across passes

Use these restrictions when selecting a stage's free coordinates:

* Level 0: choose `x,y,z` in pairwise distinct noncentral reflection orbits,
  all outside the orbits of both `w` endpoints. Such a stage avoids every
  nonaxis signed line.
* Level 1: choose `x,y` in distinct noncentral orbits, both outside the orbits
  of `z,z',w`. Only signed lines varying `z,w` can meet its endpoints.
* Level 2, `x`-edge orientation: choose free `y` outside the orbits of
  `x,x',z,w`. Only signed lines varying a subset of `{x,z,w}` can meet it.
  Transpose for the other orientation.
* Level 3: choose free `z` outside the orbits of both `x` endpoints, both
  `y` endpoints, and fixed `w`. Only subsets of `{x,y,w}` can vary on a
  signed line through a support cell.
* Level 4: choose free `w` outside the orbits of all six `x,y,z` endpoints.
  Only subsets of `{x,y,z}` can vary.

Thus every level avoids full four-coordinate diagonals, even when native
endpoints are centers, reflect one another, or coincide with endpoints in a
different coordinate. Such coincidences are permitted and are accounted for
by caps. This explicitly covers axes lying entirely in a diagonal section;
blanket avoidance of every extra-line cell is never required.

The free coordinate in the last three levels is fixed on each surviving
extra line. Its distinct-position rule across the complete reservoir implies
that such a line meets at most one stage. At level 1 the surviving line fixes
`x,y`, and their partial-matching rule has the same consequence. A signed line
meets a Cartesian checkerboard in at most two vertices: any varying
coordinate has only two possible endpoint values. Ordinary pairs have at most
two vertices as well. This proves the asserted whole-reservoir intersection
bound, conditional only on successful packing.

### 5.2 Greedy placement and explicit saturation counts

Induct on stages. Reject an otherwise permitted placement if it exceeds the
current pass's cap `cL` on a nonnative axis or signed line. A stage contributes
at most two cells to such a line. Therefore a rejected line already has at
least `cL-2>=cL/2` cells. At levels 2--4 the native controlled axis loads
are bounded by `Delta^k L`, where `k<=3`, and are below the cap automatically.
Levels 0--1 control aggregates, and every axis family is capped explicitly.
The occupied axis load after
any bounded number of earlier passes is

`M <= M_R+O(K_4+P+g)=o(n)`.                                  (OL)

All implicit constants here are fixed, including `c`.

For clarity, the following table bounds the number of candidates rejected by
occupied cells and by cap saturation. It treats `Delta=64` symbolically to
show every leading constant used. The partial-matching and orbit exclusions
in the last column are separate from occupied cells.

| Level | Free-candidate count | Already occupied exclusions | Saturation exclusions | Matching/orbit exclusions |
|---|---:|---:|---:|---:|
| 0 | `n^3` | `2n^2 M` | `16 Delta n^3/c` | `o(n^3)` |
| 1 | `n^2` | `2n M` | `32 Delta n^2/c` | `o(n^2)` |
| 2, one orientation | `n` | `2M` | `64 Delta n/c` | `o(n)` |
| 3 | `n` | `4M` | `128 Delta^2 n/c` | `o(n)` |
| 4 | `n` | `8M` | `128 Delta^3 n/c` | `o(n)` |

Here is a derivation of the saturation columns, independent of any uniformity
of previously chosen positions.

At level 0, a fixed `w` hyperplane has at most `Delta n^2 L` planned cells
in the pass. For its three horizontal axis families and the two endpoint
hyperplanes, at most `12 Delta n^3/c` triples are excluded. The total planned
cells are at most `Delta n^3L`; capped `w`-axes therefore exclude at most
`2 Delta n^3/c` triples. No extra line is touched. The sum is bounded by
the displayed `16 Delta n^3/c`.

At level 1, a fixed `(z,w)` plane has at most `Delta nL` planned cells; a
fixed `z` or fixed `w` hyperplane has at most `Delta n^2L`. The two `z`
endpoint planes' `x,y` axis caps cost at most `8 Delta n^2/c`. The `z` caps
within fixed `w` cost `2 Delta n^2/c`; the `w` caps at the two fixed `z`
endpoints cost `4 Delta n^2/c`. In either diagonal section `z=w` or
`z=bar w`, each fixed `w` has at most `Delta nL` planned cells, so the two
possible extra-line families cost at most `4 Delta n^2/c`. Their total is
at most `18 Delta n^2/c`, below the table's bound.

At level 2, the native `y`-axes have load at most `Delta L`. The planned
load in a `(z,w)` plane or in a section with fixed `x,w` or fixed `x,z`
is at most `Delta nL`. The transverse `x` cap and the two possible `z` and
two possible `w` caps therefore cost at most `10 Delta n/c` free `y`
choices. There are at most twelve surviving extra-line candidates as `y`
varies: four `zw` candidates (two signs and two fixed `x` endpoints), two
`xz`, two `xw`, and four `xzw`. For each such candidate family, the union
over all free `y` has planned load at most `2 Delta nL`. Indeed sum over
its signed-line parameter: each specified native `x` value has at most
`Delta` incident graph edges, while the other fixed or signed coordinates
determine the relevant plane. Consequently each candidate family rejects
at most `4 Delta n/c` choices. Adding gives at most `58 Delta n/c`.

At level 3, the native `z`-axes have load at most `Delta^2L`. For each of
the eight nonnative axis candidates (two `x`, two `y`, four `w`), the union
over free `z` has planned load at most `Delta^2 nL`. Their cap cost is at
most `16 Delta^2 n/c`. There are at most fourteen extra candidates: two
`xy`, four `xw`, four `yw`, and four `xyw`. For each candidate family the
union over free `z` has planned load at most `2 Delta^2 nL`. To see this,
sum over its one signed parameter; specified native endpoints have at most
`Delta^2` incident edge pairs. Their total cost is at most
`56 Delta^2 n/c`, giving `72 Delta^2 n/c` in all.

At level 4, the native `w`-axes have load at most `Delta^3L`. Each of the
twelve nonnative axis candidates has union load at most `Delta^3 nL`,
costing `24 Delta^3 n/c`. There are sixteen extra candidates: for each of
the three native coordinate pairs, two signs and two fixed third-coordinate
endpoints, and the four native triple directions. For each such candidate
family the free-`w` union load is at most `2 Delta^3 nL`, by the same
signed-parameter/incident-edge count. Their total cost is at most
`64 Delta^3 n/c`. The sum `88 Delta^3 n/c` is below the table's bound.

These union-load counts are valid at every intermediate stage because they
bound the entire planned pass, not its average occupancy. Separately labeled
parallel edges are counted in `Delta`, so cause no omitted multiplicities.
Residue stages use paths, a subcase of these counts with degree at most two
and fewer copies at levels 0 and 1.

The occupied-cell column follows by partitioning the relevant two hyperplanes
or planes into axes, or using the two, four, or eight native fibers directly.
The orbit exclusions remove only `O(n^2)`, `O(n)`, or `O(1)` candidates at
levels 0, 1, or later levels. A reservoir has at most `P+J_j=o(n)` stages
across its passes, so its previous free labels remove respectively `o(n^3)`,
`o(n^2)`, or `o(n)` candidates. With `c=10^15` every saturation fraction is
less than `1/4`; all other excluded proportions tend to zero. A legal choice
exists at each step. This completes the induction and proves AP4.

## 6. A separate five-level residue repair

Put `h=g/2`. When `h=1`, all current and target axis sums are odd and already
congruent modulo `g`; reserve no residue stages. Otherwise use these additional
bundles, each with `h-1` stages, with actual gaps `2 mod g` supplied by
Section 2.4. Their reference state is the unswitched state in (CB).

1. Along a path on the `w` labels, one ordinary bundle per edge controls
   `w`-hyperplane total residues. Only one copy is needed, not `n^2`.
2. In each fixed `w`, a path on `z`, one ordinary bundle per edge, controls
   the `(z,w)` plane total residues. Only one copy is needed, not `n`.
3. In every `(z,w)` plane, independent `x` and `y` paths control both
   horizontal axis-target lists.
4. In each fixed `w`, one rectangle bundle for every pair of `x,y` path
   edges controls the `z`-axis residual matrix.
5. One eight-cell checkerboard bundle for every triple of `x,y,z` path
   edges controls the `w`-axis residual tensor.

The gaps of distinct stages need not be equal to one another; all are `2`
modulo `g`, and the pairs within any one stage have exactly the same gap.

Every desired aggregate correction is even because all relevant section
sizes and all axis targets are odd. Divide corrections by two in `Z/hZ`.
At the first two levels, the already-matched enclosing total ensures the
path demand has total zero. Prefix sums supply its edge coefficients in
`Z/hZ`. At the third level the plane totals just matched give zero-total
row and column demands; the two passes preserve one another exactly.

After that, compatibility (AC) gives zero margins for each `z` residual
matrix, in `Z/hZ`. Double prefix sums give coefficients on path-edge pairs.
After those rectangles, all three old axis families have their target
residues, so the last tensor has zero marginal in each coordinate. Triple
prefix sums give coefficients on path-edge triples. These prefix identities
hold over any commutative ring, so no field or division by a nonunit is used.
For each coefficient choose its representative in `[0,h-1]`, and switch
that many of its bundle's stages. The stipulated number of stages pays every
coefficient with a nonnegative selection of distinct stages.

This procedure has all the exact preservation contracts in Section 3. Its
entry invoice is less than

`ng+n^2g+2n^3g+2n^3g+4n^3g < 10n^3g`.

By AP4 every required axis or signed line changes numerically by at most
`O(gX)`, not just modulo `g`. It avoids full four-coordinate diagonals.
The main reservoirs are untouched and still have both signed capacities.
All subsequent main gaps are multiples of `g`, so they preserve the residue
of every signed line, whether or not that line has yet been corrected.

## 7. Centering a genuine exact-pool baseline

### 7.1 Whole-reservoir random choices

After planning disjoint supports and allocating all their fresh prime values,
choose independently for each main reservoir one of its two complementary
reference configurations from Section 2.4 with probability one half. Residue
stages stay at their fixed reference state. Every macro cell has expected
value equal to its actual prime-pair midpoint, within `delta X` of `m`.
Prefix and residue cells have arbitrary error at most `X`.

The separate AP4 caps imply, for any full signed line `L` with `r_L` reserved
cells,

`|E C_L-r_Lm|=O(delta K_4X+PX+gX)`.                           (CE)

The contribution range of one entire random reservoir to any axis line is
at most `X` eventually. A nonnative axis either meets at most one stage and
one noncancelling cell, or has cancelling paired contributions. A native
axis receiving stages from the whole reservoir has fixed tensor sign, so
its two complementary scalar sums differ by at most `g`. At levels 0 and 1,
the partial-matching restrictions also prevent many isolated contributions
on a nonnative axis. Thus independence is never falsely assigned to cells.

For nonaxis signed lines AP4 gives the uniform range `2X`: a line meets at
most one stage of that reservoir and at most two vertices. Full four-coordinate
diagonals meet no axis-reserved cell. There are at most `O(K_4+P)` relevant
random reservoirs on any line, since each one uses a reserved cell there.
A bounded-independent-variable inequality, with a sufficiently large fixed
constant and a union bound over `4n^3+12n^2+16n+8=O(n^3)` lines, therefore
gives simultaneous deviation

`|C_L-r_Lm|<=E`,
`E=O(delta K_4X+PX+gX+X sqrt((K_4+P)log n))`.                 (E)

This is an existential choice of legal reservoir orientations. Both choices
retain every later two-sided capacity.

### 7.2 Completion without replacement and the shifted unused mean

At least `n^4/2` unused primes remain eventually. Let their number be `M_0`
and their mean `m_0`. Sum (E) over a single partition into `n^3` axis lines.
Using the exact pool total, not an assumed unchanged mean, yields

`|m_0-m|<=n^3E/M_0<=2E/n`.

Randomly biject the unused primes onto the unused cells. Every full signed
line has `n` cells, so its expected completed sum differs from `mu` by at
most `3E`. Sampling without replacement from `[0,X]` has the estimate

`Pr(|S_L-E S_L|>u)<=2 exp(-u^2/(2nX^2))`.

For example `u=4X sqrt(n log n)` makes the union bound over all signed
lines tend to zero. Choose a completion with all these bounds. Every element
of `P_n`, including small primes dividing `g`, now occurs exactly once.

The hierarchy (S) gives

`delta K_4=o(K_0)`, `P+g=o(K_0)`,
`sqrt((K_4+P)log n)=o(K_0)`, `sqrt(n log n)=o(K_0)`.

All signed line sums, in particular all axis sums, are therefore
`mu+o(K_0X)`. Apply Section 6 for the chosen axis target tuple. Its actual
`O(gX)` error is absorbed by the same bound, and all main reservoirs remain
available with every axis difference divisible by `g`.

### 7.3 Exact integration conditions for other reserved controllers

The geometric AP4 lemma allows previously reserved supports of arbitrary
shape with axis load `o(n)`. To use the same centering proof with their prime
values, additionally require: disjoint fresh allocation within the common
`Q_*` allowance; `O(P+g)` uncontrolled entries per signed line; `O(K_*)`
macro entries per signed line with pair midpoints within `delta X` of `m`;
independent whole-bundle complementary choices whose contribution ranges are
`O(X)` on every signed line; and `delta K_*=o(K_0)`,
`sqrt(K_*log n)=o(K_0)`. A fixed `K_*=ceil(n^.79)` meets these numerical
conditions, but that observation does not prove the other controller's
packing, supply invoice, or contribution ranges. With those hypotheses
checked, replace `K_4` by `K_*` in (CE)--(E); the mean-shift and completion
arguments are unchanged.

## 8. Exact corrections and quantitative margins

Integral max flow on the graph with expansion eight implies: if each edge
permits integer transfers in `[-C,C]`, every zero-total integer demand of
coordinate size at most `8C` is realizable. Indeed every cut demand is at
most `8C min(|S|,n-|S|)`, while its edge capacity is at least that amount;
integrality is the ordinary integral max-flow property. For a `g`-grid,
divide both the demands and the available complete interval by `g`, retaining
integer endpoint floors. Those floors cost at most `g` per scalar reservoir,
which is absorbed by the displayed capacities.

### 8.1 Hyperplane totals, plane totals, and the first two axis families

Let `U_w` be the target total of a fixed `w` hyperplane, obtained by summing
any one of the `x,y,z` target families over its `n^2` lines there.
Compatibility (AC) makes these three definitions equal, and their grand sum
is `T`. From Section 7 and (TB), its initial discrepancy is at most
`(1+o(1))n^2K_0X`. The level-0 graph edge interval has capacity at least
`3n^2K_0X`, so the integral cut-flow condition holds, with room for grid
rounding. Distribute each edge coefficient among its `n^2` complete reservoir
intervals. This fixes every `U_w` exactly and preserves all `w`-axis sums.
By the separate level-0 cap every axis line has changed by `O(K_0X)`.

In each fixed `w`, let `V_(z,w)` be the target total of the `(z,w)` plane.
Summing the `x` targets over `y` or the `y` targets over `x` gives the same
integer by (AC). Its discrepancy is now `O(nK_0X)`. The discrepancies sum
to zero in that `w` hyperplane because its total was fixed at level 0.
Level-1 edge capacity `3nK_1X` suffices since `K_0=o(K_1)`. This fixes all
plane totals, preserves each `w` hyperplane total and every `z`-axis sum,
and changes each other axis sum by `O(K_1X)`.

Within every `(z,w)` plane, both desired horizontal line lists now have the
correct exact total. Their coordinate errors are `O(K_1X)`. The two level-2
graph systems have capacity `3K_2X`; use integral flow first for one list,
then the other. Their physical pairs preserve one another's sums exactly.
Both `x` and `y` target families are now exact. All other axis errors are
`O(K_2X)` by that pass's separate cap.

### 8.2 The rank-two correction inside each slice

For each fixed `w`, let
`D_(x,y)=A'_z(x,y,w)-A_z(x,y,w)`. Its row and column margins vanish as
integers by (AC) and the already exact `x,y` families. Its entries are
multiples of `g`. Apply the inherited tensor-expander theorem with `k=2`
to `D/g`. For this graph it gives integer coefficients with physical scalar
size at most

`(5log n+5)^2 ||D||_infinity + g/2 +512gn^2`
`=O(K_2X log^2 n)+O(gn^2)=o(K_3X)`.                          (C3)

Every coefficient is within its level-3 reservoir's complete signed interval.
Use the actual four-cell/two-pair switches. They preserve all `x,y` targets
exactly and fix the `z` target family in every `w` slice. Their incidental
effect on any `w`-axis line is at most `O(K_3X)` by AP4.

### 8.3 The rank-three fourth-direction correction

Now put `D_(x,y,z)=A'_w(x,y,z)-A_w(x,y,z)`. Summing in any of `x,y,z`
and applying (AC) expresses the result as the discrepancy of an already
fixed axis family. Thus every coordinate marginal is **zero as an integer**.
Again `g` divides every entry. Apply the same theorem with `k=3` to `D/g`.
The exact inherited rounding term is

`(Delta n)^3/2^4 =16384n^3`,

not the square-stage `512n^2`. The resulting physical scalar coefficients
are bounded by

`(5log n+5)^3 ||D||_infinity +g/2+16384gn^3`
`=O(K_3X log^3 n)+O(gn^3)=o(K_4X)`.                          (C4)

This last estimate uses `X~4n^4log n` and `g=O(log n)` as well as
`K_3 log^3 n=o(K_4)`. Every coefficient is attained by the reserved eight-cell,
four-pair checkerboards. They preserve the three exact old families and set
the `w` family exactly. Every chosen operation consists solely of swaps
between previously assigned distinct elements of `P_n`. This proves U4.

## 9. Consolidated invoice and the signed-line handoff

All constants implicit in this table are absolute, with graph degree and
packing cap fixed above. Local bounds refer to any single required signed
line; native capacity is separately scaled for aggregate levels.

| Item or pass | Reserved entries / available supply | Local occupancy or drift | Required coefficient / margin |
|---|---|---|---|
| Seed selection | Demand `O(n^3P)` pairs; available `>>X/log^3X` disjoint pairs in one class | Prefix caps `O(P)` | Ratio tends to zero |
| Arbitrary prior endpoint deletion | At most `Q_*=2^40n^3K_4` | May concentrate in one class/window | `Q_*=o(delta X/(g log X))` |
| Fresh grouped growth | Matching at least 40 pairs for `R>=4096gF^2` | At most `P=O(log^2X)` stages per reservoir | Complete `g`-grid to at least `X` |
| Fresh balanced macro/residue tuples | `>>delta^2X/(g log^2X)` disjoint equal-gap pairs at every request | Pair midpoint error at most `delta X` | Tends to infinity, hence fixed tuple sizes supplied |
| Prefixes and residues | `266496n^3P+<10n^3g` entries | `O((P+g)X)` drift | `o(K_0X)` |
| Level 0 | `2112n^3K_0` entries | `O(K_0X)`; no extra signed line touched | Demand `(1+o(1))n^2K_0X`; edge capacity `3n^2K_0X` |
| Level 1 | `2112n^3K_1` entries | `O(K_1X)` | Demand `O(nK_0X)=o(nK_1X)` |
| Level 2 | `4224n^3K_2` entries | `O(K_2X)` | Demand `O(K_1X)=o(K_2X)` |
| Level 3 | `135168n^3K_3` entries | `O(K_3X)` | (C3), with genuine `512gn^2` rounding cost |
| Level 4 | `8650752n^3K_4` entries | `O(K_4X)` | (C4), with genuine `16384gn^3` rounding cost |
| All axis reserves | `<2^24n^3K_4=o(n^4)` | Axis load `O(K_4+P+g)=o(n)` | Leaves at least half the pool unused eventually |
| Balanced orientation | Independent whole reservoirs, range at most `2X` | `O(delta K_4X+PX+gX+X sqrt((K_4+P)log n))` | `o(K_0X)` |
| Unused completion | Sampling without replacement from exact remaining pool | `O(X sqrt(n log n))`; unused mean shift explicitly paid | `o(K_0X)` |
| Full four-coordinate diagonals | No axis-reserved cells | Every axis correction preserves each exactly | Initial error remains `o(K_0X)` |
| Pair/triple signed lines | Per-pass caps; at most two cells per whole reservoir | Total old-controller drift `O(K_4X)` | Input error for a later larger controller |

No assertion of primality for extra lines follows from U4. The exact handoff
is: after a jointly centered baseline and compatible residue repair, the five
axis passes finish all axis targets, preserve every signed-line residue
modulo `g`, preserve every full four-coordinate diagonal numerically, and
leave pair/triple signed-line discrepancies at most `O(K_4X)` whenever their
initial target discrepancies were `O(K_0X)`. The hidden constant here is
fixed; any genuinely proved later capacity of exponent strictly larger than
`.76` absorbs it. A later controller must still prove all of its own coupled
compatibility, geometry, integral coefficients, and preservation claims.

Every threshold used above depends only on fixed exponents, degree, cap,
analytic slack, and the source's uniform progression threshold. Their maximum
is an eventual threshold for **all** larger odd `n`. Ineffectivity enters the
progression count; no square or cube numerical cutoff is transferred.

## 10. Source-bound finite controls and their scope

The companion [hyper4_axis_controls.py](../code/hyper4_axis_controls.py) checks
four-dimensional signed-line enumeration; grouped-pair physical checkerboards
using distinct entries of an exact first-prime pool; the separate preservation
contracts and orbit avoidance; whole-bundle intersections; exact integer
rank-three tensor rounding and repair; and rejecting malformed pool, support,
orientation, and residue inputs. Its optional certificate output records the
actual initial permutation and every paired switch for independent replay.

These are finite controls of the arguments' delicate interfaces. A control
whose target tensor is not entirely prime is explicitly a controller
certificate, not a signed-prime hypercube arrangement. Finite success is not
used to prove the eventual packing or analytic supply. The uniform arguments
are Sections 2, 5, 7, and 8 above.
