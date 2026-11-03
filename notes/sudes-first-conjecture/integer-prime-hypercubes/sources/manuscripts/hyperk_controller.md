**Public reading copy.** Presentation and links have been normalized. Historical status statements below belong to their source revisions; see the [current publication status](../../README.md#review-and-verification-status). The matching original bytes are in the [source archive](../../originals/manuscripts/hyperk_controller.md).

# Physical controllers in fixed dimension

Author: `/root/controller`. The general axis construction and its packing
proof and majority-coordinate extension are new work in the all-dimensions
workspace. The full signed-line extension in Section 9 has a separately
stated missing generator hypothesis;
an integer lift is never treated as a permutation. All labels are local.
Independent review must exclude the author of this source and its controls.

## 1. Exact interfaces and source boundary

Fix an integer `k>=2` before allowing the odd integer `n=2m+1` to grow.
Coordinates lie in `I={-m,...,m}`. Put

`P={p_2,...,p_(n^k+1)}`, `X=max P`, `T=sum P`,
`b=T/n^k`, and `mu=nb=T/n^(k-1)`.

For each coordinate `i`, `A_i` is the tensor of sums over that coordinate.
The axis compatibility equations are the integer identities

`S_j A_i = S_i A_j` for `i!=j`.                         (AX)

They are equalities of arrays on the other `k-2` coordinates, not merely
equalities of grand totals. The saturated axis image, its parity refinement,
and the sparse tensor-expander inverse are proved in the frozen
[incidence source](incidence.md), Sections 1--3. The source is inherited from
PR79 scientific `a2445962ec6e06b2a893980fb7a183057eb9bcee`, delivered at
`cdb7879e358f93afa54b685027a27692d22635a9`. Its graph hypothesis is supplied
by the degree-64, expansion-eight graph used in the frozen
[four-dimensional axis source](hyper4_axis.md). The latter is read at
scientific `b837e307fc41975d0fb332c8215d6835ba47a271`, with the review
boundary recorded in [the four-dimensional handoff](../HYPER4_HANDOFF.md).
Neither its dimension-four packing lemma nor its five levels are being
assumed in arbitrary dimension.

Write `D=2k-4`. Choose increasing fixed exponents

`a_j=3/5+3j/[20(D+1)]`, `K_j=ceil(n^a_j)` for `0<=j<=D`,
`delta=n^(-1/5)`.

Thus `3/5<=a_j<3/4`, and every consecutive gap is positive for each fixed
`k`. A longer finite hierarchy can use the same formula with its actual
depth in place of `D`. Constants below may depend on `k`, and are fixed
before `n` grows.

**Theorem U(k), physical axis universality.** For each fixed `k>=2` there
is `N_axis(k)` such that for every odd `n>=N_axis(k)`, every collection of
odd integer axis tensors satisfying (AX), directional total `T`, and

`|A'_i(u)-mu|<=K_0 X`

is attained by a permutation of the exact pool `P`. The target tuple need
not consist of primes. The threshold is uniform in that tuple.

The proof uses the grouped-pair supply and joint-centering interface stated
in Section 6. Those are numerical and probabilistic inputs; Sections 2--5
prove the new geometric and exact algebraic obligations in arbitrary fixed
dimension. In particular, U(k) does not invoke lower-dimensional prime-array
theorems on slices with different prescribed pools.

## 2. Physical tensors and their complete line signature

For each coordinate choose a vector `v_i` which is either a point mass or a
difference of two distinct point masses. Let `C=tensor_i v_i`. For a full
signed line varying on `A`, with normalized signs `sigma`, and fixed
coordinates `c_j`, substitution in the defining sum gives exactly

`(A_(k,n) C)_(A,sigma,c)`
` = [sum_(t in I) product_(i in A) v_i(sigma_i t)]`
`   * product_(j notin A) v_j(c_j)`.                    (SIG)

The formula holds at central coordinates and at repeated or opposite
endpoints. It has no generic-position proviso. A line meets a Cartesian
product of two-point coordinate sets in at most two vertices unless it is
disjoint, because any one varying coordinate restricts its parameter to at
most two values. Point masses can only decrease this intersection bound.

**Lemma CB(k), physical checkerboards.** A tensor with `s>=1` difference
factors and all other factors point masses can be realized as an actual
array change `dC` using `2^(s-1)` disjoint prime pairs of common positive
gap `d`. The stage uses `2^s` distinct cells and entries.

Pair vertices along the last difference coordinate. For an edge whose other
bits have even parity, put its lower prime at bit zero; for odd parity, put
the upper prime there. Put the partner at bit one. Swapping every pair gives
`d(-1)^(sum bits)` at each vertex. This is precisely `dC`. The proof concerns
actual values and a simultaneous switch configuration, not formal signed
increments. Reflecting coordinates preserves it.

In particular a full alternating hypercuboid uses `2^(k-1)` equal-gap pairs,
preserves every axis, and has all its other images given by (SIG). It does
not generally isolate one signed line. A common central vertex belongs to
all body directions; a tensor repeating the same pair in every coordinate
has body coefficient `1+(-1)^k`, not a unit body control.

## 3. The `2k-3` axis levels

Fix an oriented loopless multigraph `G` on `I`, with degree at most
`Delta=64`, cut expansion at least eight, and at most `32n` edges. Parallel
edges remain separately labeled. Its incidence columns are
`B_e=e_u-e_v`. Each main reservoir has a complete bounded scalar prefix,
then at most `33K_j` macro stages. The scalar gaps of its stages may differ,
but every pair within a stage has the same gap. From either of two legal
central reference states it realizes every multiple of a common even gap
`g` in `[-3K_jX,3K_jX]`. Section 6 gives the supply contract.

### 3.1 Nested aggregate passes

For `d=k,k-1,...,3`, in that order, and for each fixed outer tuple
`z=(x_(d+1),...,x_k)`, take `n^(d-2)` reservoirs per edge `(u,v)` of the
`d`-coordinate graph. One stage occupies

`(x_1,...,x_(d-1),u,z)` and `(x_1,...,x_(d-1),v,z)`.

The first `d-1` coordinates are free. Their values are in distinct,
noncentral reflection orbits, avoiding all the orbits of `u,v,z`. Within
one whole reservoir, every individual free coordinate value is fresh across
all its stages, including prefix and macro stages. This is a partial matching
in the free coordinate tuple, not just a distinct-cell rule.

The stage transfers `d_stage` between the two `(d-1)`-dimensional sections
with those `d` labels and fixed outer tuple. It preserves every axis sum
parallel to coordinate `d` and every enclosing section total already fixed.
There are at most

`32 n * n^(k-d) * n^(d-2)=32 n^(k-1)`

reservoirs in each aggregate pass. At fixed outer tuple the combined scalar
capacity per graph edge is `3 n^(d-2) K_j X`.

### 3.2 The two horizontal families

After all two-dimensional section totals have been corrected, in each fixed
outer tuple `(x_3,...,x_k)` use two separate copies of `G`. One uses pairs
along coordinate 1 and a free coordinate 2; the other interchanges 1 and 2.
The free coordinate avoids every orbit among the native endpoints and fixed
outer coordinates and is fresh across its whole reservoir.

The first pass adjusts coordinate-2 axis sums and preserves coordinate-1
axis sums; the second does the reverse. Each preserves its section total.
The two passes share one capacity level and do not disturb each other's
native outputs. They use at most `64 n^(k-1)` reservoirs in total.

### 3.3 Successively higher tensor passes

For `d=3,4,...,k`, use one reservoir for each fixed outer tuple
`(x_(d+1),...,x_k)` and ordered tuple of graph edges in coordinates
`1,...,d-1`. Its stage is

`B_(e1) tensor ... tensor B_(e_(d-1)) tensor e_u tensor e_z`,

where `u` is the free coordinate-`d` value. This requires `2^(d-2)` actual
equal-gap pairs. Choose `u` in a noncentral orbit outside every endpoint and
outer-coordinate orbit, and fresh across its complete reservoir.

The stage changes the coordinate-`d` axis tensor by the native graph product
and preserves every axis in coordinates `1,...,d-1` exactly. It has at most

`32^(d-1) n^(d-1) n^(k-d)=32^(d-1) n^(k-1)`

reservoir types. All earlier enclosing section totals are then preserved as
well, since they can be recovered from an already fixed axis family.

There are `k-2` aggregate levels, one horizontal level, and `k-2` tensor
levels: `2k-3` in total, indexed `0,...,2k-4`. For `k=2`, only the horizontal
level remains. For `k=4`, the order is exactly the five-level pattern in U4,
but the proof below has `k` as a variable.

## 4. Packing with caps for every signed line

The following is the essential geometric extension. It keeps maximum load,
not only total reserved volume, small. A pass means one fixed shape and one
of prefix, macro, or residue use. There are finitely many passes for fixed
`k`. A pass has at most `L=o(n)` stages per reservoir; aggregate passes have
the stated `n^(d-2)` copies per edge, or fewer.

**Lemma AP(k).** Suppose a previously reserved set has maximum axis load
`M_R=o(n)`. All the axis stages above, including the residue versions in
Section 5, can be placed disjointly from it and one another. Each pass uses
at most `H_k L` cells on every full signed line, with

`H_k=2^(6k+12) 3^k Delta^k`

as one deliberately generous choice. Every stage avoids every full body
diagonal. Any nonaxis signed line meets one whole reservoir in at most one
stage and at most two cells. Every other individual axis-line contribution
is either native with fixed coefficient, identically zero, or meets at most
one stage. Thus its whole-reservoir reference range is at most `2X`, apart
from native scalar ranges at most `g`, which also obey that bound.

### 4.1 One-free-coordinate passes

This includes both horizontal orientations and every tensor pass. Temporarily
delete the free coordinate. The remaining footprint of a stage is a product
of at most `k-1` graph edges, with all remaining coordinates fixed. Any one
native point belongs to at most

`C_k=Delta^(k-1)`

footprints, because each prescribed edge endpoint belongs to at most `Delta`
labeled graph edges. Consequently, across the entire planned pass, at most
`C_k L` stage cells project to a given native point. This count is valid for
every intermediate choice of free labels; it is not an averaging claim.

The native free-coordinate axes therefore have load at most `C_k L`
automatically. Any other line a permissible stage can meet excludes the free
coordinate from its varying set: a line varying it with another coordinate
would require a forbidden equality of reflection orbits. For a possible
nonnative line, vary the free label over all `n` choices. The union of these
`n` lines projects to one line of `n` native points. Its entire planned load
is at most `C_k nL`. If the cap `H_k L` would be violated, that line already
has at least `H_k L-2^k>=H_k L/2` cells, for large `n`. Hence at most
`2C_k n/H_k` free labels are forbidden for this particular potential line.

There are at most `2^(k-1) (3^k-1)/2` potential support-vertex/direction
pairs: for each nonempty varying set and relative signs, at most one line
of that direction passes through a given vertex. Overcounting coincidences
only enlarges the bound. Thus all cap rejections exclude at most

`2^k 3^k C_k n/H_k < n/8`

candidate free labels. The chosen constant also covers the horizontal
shape, which has fewer native factors.

For each support vertex, varying the free label follows its native axis.
Current total occupied axis load is

`M=M_R+O_k(P+K_D+g)=o(n)`.

At most `2^(k-1) M=o(n)` labels hit an occupied cell. A reservoir's earlier
free labels exclude `O(P+K_D+g)=o(n)` values; the finitely many generic orbit
conditions exclude `O_k(1)` further values. Therefore some permitted label
remains. Add the support and continue. This proves packing and caps for all
one-free-coordinate passes.

### 4.2 Aggregate passes: the required section counts

Fix an aggregate pass at coordinate `d`, and put `r=d-1>=2`. Its candidates
are `n^r` free inner tuples. By construction, with coordinate `d` and all
outer coordinates fixed, the total planned support in that `r`-dimensional
section is at most

`Delta n^(r-1)L`.                                      (P1)

This follows from the at most `Delta` incident native edges and
`n^(r-1)` copies per edge. With only the outer tuple fixed and coordinate
`d` varying, the corresponding count is at most

`Delta n^r L`.                                         (P2)

These bounds include every prefix or macro stage of this pass and hold
regardless of earlier placements.

Consider the cap exclusions for the two native endpoints of the proposed
stage. For an inner-coordinate axis `i<=r`, (P1) shows that at most
`2Delta n^(r-1)/H_k` axes in that section are saturated. Each forbids at
most `n` free tuples, giving `2Delta n^r/H_k` exclusions. For coordinate
`d`, (P2) gives at most `2Delta n^r/H_k` saturated axes, each with one free
tuple label. For an outer-coordinate axis, sum (P1) over its `n` labels;
the same bound `Delta n^r L` and the same exclusion count result.

The generic orbit restrictions exclude nonaxis lines containing any inner
coordinate in their varying set. Thus a surviving nonaxis line varies only
within coordinates `d,...,k`. In the union of its candidate placements over
all inner tuples, each of its `n` parameter values determines coordinate `d`
and the outer coordinates. Summing (P1) over those values gives at most
`Delta n^rL` planned cells. This remains valid if `d` is fixed on that
direction. At most `2Delta n^r/H_k` line labels are saturated, each forbidding
one free inner tuple. Central and opposite endpoints are included: the
number of possible directions is overcounted by `(3^k-1)/2` uniformly.

Adding the two endpoint possibilities, all axes and all signed directions
gives at most

`4Delta (k+3^k)n^r/H_k < n^r/8`

cap rejections. The cap allowance `2^k` above is more than the two cells
this shape adds.

For occupied cells, partition each native endpoint section into axes in one
inner direction. At most `n^(r-1)M` cells are already occupied there. Both
endpoints therefore exclude at most `2n^(r-1)M=o(n^r)` tuples. Requiring
each free coordinate to be fresh across the complete reservoir excludes
`O_k((P+K_D+g)n^(r-1))=o(n^r)` tuples. Pairwise orbit disjointness and
avoidance of native/outer orbits exclude `O_k(n^(r-1))` more. A legal tuple
remains. This proves the greedy induction for all aggregate passes.

### 4.3 Preservation and the whole-reservoir range

All supports have a free coordinate whose orbit is different from every
other coordinate at that point, so no full body diagonal is touched. For
one-free-coordinate stages, every possible nonnative signed line fixes that
coordinate; freshness permits at most one stage of the reservoir. For
aggregate stages, a possible nonaxis line fixes every inner coordinate, and
the partial matching gives the same conclusion. An inner axis in an
aggregate pass fixes at least one other inner coordinate, since `r>=2`;
again it meets at most one stage. The native transfer-direction axes have
zero image. Outer axes fix all inner coordinates.

For one-free-coordinate native axes, every stage has the same coefficient
`0,+1,-1`; the two central scalar values differ by at most `g`. Axes canceled
by a checkerboard have zero range. All remaining lines meet at most two
cells in at most one stage and hence have contribution range at most `2X`.
This proves the claimed range and completes AP(k).

The argument allows an already reserved controller of arbitrary support
shape, provided its maximum axis occupancy is `o(n)`. Its values require
their own centering contract; small occupancy alone is not such a contract.

## 5. Residue repair and exact numerical correction

### 5.1 Residues over an arbitrary composite ring

Let `h=g/2`. Use separate stages with actual gaps congruent to 2 modulo `g`.
For every graph copy replace the graph by a path. Aggregate levels need only
one reservoir per path edge, not `n^(d-2)` copies. Horizontal and tensor
levels use the path and its tensor products. Give each reservoir `h-1`
stages. If `h=1`, no residue stages are needed.

Every desired aggregate discrepancy is even: actual sections have an odd
number of odd entries, and the prescribed aggregate is an odd number of odd
line targets. Divide each discrepancy by 2 in `Z/hZ`. At an aggregate
level, the enclosing total has already been matched, so the path demand
has total zero. Its edge coefficients are signed prefix sums in that ring.
The two horizontal lists then have the correct plane total and are corrected
independently. At direction `d>=3`, (AX) and already corrected earlier axes
give a target `(d-1)`-tensor whose every coordinate marginal is zero in
`Z/hZ`. Repeated prefix summation gives its coefficients on path-edge
products. These are identities over the integers and hence over every
commutative ring; no division by `n` or another nonunit occurs.

Choose each coefficient in `{0,...,h-1}` and switch that many distinct
stages. The stage contracts from Section 3 preserve every already corrected
quantity. The invoice is `O_k(n^(k-1)g)` entries. AP(k) gives actual signed
line drift `O_k(gX)`, not merely matched residues. Every main stage gap is
divisible by `g`, so all later main switches preserve the residue of every
signed line, including those not numerically corrected by U(k).

### 5.2 Aggregate and horizontal numerical passes

Assume the centered exact-pool baseline of Section 6. After residue repair,
every axis discrepancy is a multiple of `g` and has size at most
`(1+o(1))K_0X`. At the first aggregate level `d=k`, the target total of a
section is obtained by summing, for instance, its coordinate-1 line targets.
Equation (AX) makes all possible definitions agree. Its discrepancy is at
most `(1+o(1))n^(k-2)K_0X` and has total zero across the `k` labels, since
the pool total is exactly `T`.

Integral cut flow on the expansion-eight graph supplies the transfer:
complete signed edge capacity `3n^(k-2)K_0X` exceeds the required
coordinate demand divided by eight, with room for grid floors. Distribute
each edge coefficient among its `n^(k-2)` scalar intervals by ordinary
integer interval addition. All resulting switches are actual reserved pairs.

Inductively, before the aggregate level at `d`, all enclosing section totals
are exact. Its section error is `O_k(n^(d-2)K_(j-1)X)`; the desired
corrections sum to zero in each enclosing section. The next complete edge
capacity is `3n^(d-2)K_jX`, and `K_(j-1)=o(K_j)`. Its integral flow fits.
AP(k)'s separate pass cap bounds the incidental movement of every axis and
signed line by `O_k(K_jX)`, including the prefix since `P=o(K_j)`.

Once all plane totals are exact, each horizontal target list has the correct
integer total and entry errors `O_k(K_(j-1)X)`. The two graph systems at the
horizontal level correct the lists and preserve one another. For `k=2`,
this is the first level; the initial error `(1+o(1))K_0X` fits the level-zero
flow directly. Both first axis families are now exact.

### 5.3 Tensor numerical passes, including rounding cost

At direction `d=3,...,k` and fixed outer tuple, let `D_d` be its residual
axis tensor on coordinates `1,...,d-1`. By (AX), summing it in an earlier
coordinate equals a sum of discrepancies of that already exact axis family.
Every such marginal is zero as an integer. Also `D_d` is divisible by `g`.

Apply the inherited tensor-expander coefficient theorem to `D_d/g`, with
rank `r=d-1`. It gives integer graph-product coefficients whose physical
scalar magnitudes are at most

`(5log n+5)^r ||D_d||_infinity + g/2`
`                                  + g(Delta n)^r/2^(r+1)`. (FLOW)

The rounding term depends on the current rank; it is not the rank-two
constant reused in every dimension. Since `||D_d||=O_k(K_(j-1)X)`, the
right side is `o(K_jX)`: consecutive powers absorb every fixed power of
`log n`, and `r<=k-1`, `g=O(log n)`, `X~k n^k log n` imply
`g n^r=o(K_jX)`. Each coefficient lies in its reserved scalar interval.
Use CB(k) to realize it. All earlier axes remain fixed exactly. Separate
pass caps bound the remaining axes' error by `O_k(K_jX)` for the next pass.

The last direction fixes the entire axis target tuple. Every operation is
a permutation of disjoint preassigned pairs, and the global exact-pool
bijection survives. Subject to the verified Section 6 supply/centering
interface, this proves U(k).

## 6. Supply, reserve invoice, and centering interface

This section states all numerical inputs consumed by the geometric proof.
The elementary grouped-gap proof from U4 Section 2 has arbitrary fixed tuple
size: if at most `J_k` disjoint pairs are required in one stage, replace its
growth threshold `4096gF^2` by `C(J_k)gF^2`, where, for example,
`C(J_k)=128(J_k+1)`. The bin argument then supplies at least
`8(J_k+1)` edges of one difference; a maximum-degree-two graph gives a
matching exceeding `J_k`. For the axis construction `J_k=2^(k-2)`.
The unchanged seed supply, macro pigeonhole argument and arbitrary-deletion
contract apply because `J_k` is fixed. The resulting prefix length is
`P_k=O_k(log^2X)` and the common gap has `g=O(log X)`.

The number of main reservoirs is at most `R_k n^(k-1)`, where one may take

`R_k=32(k-2)+64+sum_(r=2)^(k-1) 32^r`.

The displayed sum is empty at `k=2`. Every stage uses at most `2^(k-1)`
entries. Thus the axis reserve, including all prefixes, macros and residue
stages, is at most

`C_k' n^(k-1)(P_k+g+K_D)=O_k(n^(k-1)K_D)`,

for some explicit finite `C_k'`, for instance
`C_k'=100 * 2^k (R_k+k)` once `P_k,g<=K_D`.
There is no reuse of a prime endpoint between reservoirs or stages.

With `delta=n^(-1/5)` and `a_D<3/4`, the least requested reduced-class
midpoint supply has size comparable from below to
`delta X/(g log X)`. Its exponent is `k-1/5`, whereas the complete reserve
has exponent less than `k-1/4`. Consequently arbitrary deletion of the
entire invoice leaves the stated fresh supplies eventually. The seed demand
`O_k(n^(k-1)P_k)` is `o(X/log^3X)`. Macro repeated-gap multiplicity is
`>>delta^2X/(g log^2X)` and tends to infinity, so it exceeds fixed `J_k`.
These comparisons apply for all sufficiently large odd `n`, not a chosen
subsequence. The short-interval prime input is the same pinned ineffective
input as U4; dimension is fixed before its asymptotics are used.

AP(k) supplies `O_k(P_k+g)` uncontrolled entries and `O_k(K_D)` centered
macro entries on every required signed line. Independently choose one of
the two complementary central states of each whole main reservoir. Its
contribution range is at most `2X` by AP(k), and each macro cell has its
actual pair midpoint as its expectation, within `delta X` of `b`. A union
bound over `L_k(n)=O_k(n^(k-1))` full signed lines gives reserved-sum error

`E_k=O_k(delta K_D X+(P_k+g)X`
`                   +X sqrt((K_D+P_k)log n))`.

This is concentration of whole reservoirs, not independent cells. At least
`n^k/2` entries remain unused. Summing the reserved error over one axis
partition and using the exact pool total bounds the changed unused mean
by `2E_k/n`. A uniform bijection of unused primes therefore has expected
line sums within `3E_k` of `mu`. The without-replacement bound

`Pr(|S-E S|>u)<=2 exp(-u^2/(2nX^2))`

with `u=sqrt(2(k+3)) X sqrt(n log n)` allows a union bound over all lines.
Both the reserved and completion errors are `o(K_0X)`, because

`delta K_D=o(K_0)`, `sqrt(K_D log n)=o(K_0)`,
`P_k+g=o(K_0)`, and `sqrt(n log n)=o(K_0)`.

The completed baseline is a genuine bijection using every prescribed prime
once. This establishes the numerical interface used in Section 5 and
completes the conventional proof of U(k). Replacing the depth by a larger
fixed finite depth leaves all these strict margins available.

## 7. What the recursive architecture has achieved

The exact first-prime pool can therefore be controlled in every fixed
dimension for all axis families, with correct coupled marginals. Combining
U(k) with the inherited general-dimensional compatible prime-target theorem
CT in [cube_targets.md](cube_targets.md) yields the eventual all-axis prime
array theorem for every fixed `k>=2`.

The architecture is a global permutation controller: the aggregate stages
correct the totals of the subpools actually assigned by the common baseline,
and later stages couple slices with the same global reservoirs. It does not
stack independently solved lower-dimensional prime arrays. All cross-slice
axis lines are corrected by the higher tensor stages.

Every full body diagonal is preserved by the axis controller. All other
signed-line sums remain within `O_k(K_DX)` of their initial targets, by the
separate pass caps. Every signed-line residue is preserved by the main
stages after a separate complete residue repair, if such a repair has been
supplied by an extra controller. U(k) alone repairs only axis residues and
does not assert the full signed-line prime theorem.

## 8. A proved signed-line family in every fixed dimension

Write `r_*=floor(k/2)+1`. Define the family `mathcal H_k` to consist of every axis and every
full signed line whose varying-coordinate set has size at least `r_*`.
For `k=2,3` this is the entire signed-line family. For `k>=4`, it omits
precisely the nonaxis families of sizes `2,...,floor(k/2)`.

**Theorem UM(k), nearby compatible majority-coordinate targets.** For
each fixed `k>=2`, every sufficiently large odd order admits a physical
exact-pool controller for odd targets on `mathcal H_k` within `ceil(n^(3/5))X`
of `mu`, provided the axis targets satisfy (AX) with total `T` and each
nonaxis target tensor has the prescribed single-coordinate marginals
imposed by its signed-section partition identities with the axes.

The compatibility condition is explicit. If `A` is a varying block and
`j` is outside `A`, summing the `A`-line target tensor over coordinate `j`
must equal the sum of coordinate-`j` axis targets along the signed `A`
parameter, with all other coordinates fixed. The full-body case `A=[k]`
has no such condition. Among two distinct majority blocks there are no
disjoint pairs, so there are no additional shared complementary-block
identities within `mathcal H_k`. The proof does not assert that the displayed
conditions are the complete integer image for arbitrary omitted families.

### 8.1 Native controls and their triangular preservation

After the axes are exact, fix a varying block `A` of size `r>=r_*` and
one of its `2^(r-1)` normalized sign patterns. Put `F=[k]\A` and
`d=|F|=k-r<r`. The residual target tensor `D_A` on `F` has every axis
marginal zero, by the displayed compatibility and the already exact axes.
When `d=0` it is simply one scalar with no margin restriction.

For each ordered tuple of graph edges in the `d` fixed-coordinate
directions, use a reservoir with stage

`U_A tensor B_(e1) tensor ... tensor B_(ed)`,             (MAJ)

where

`U_A=tensor_(i in A)(e_(sigma_i a)-e_(sigma_i b_i))`.

All `r+1` positive selector labels `a,b_i` lie in distinct noncentral
reflection orbits, disjoint from every coordinate label in the native
graph footprint. They are fresh across the complete reservoir. The
selector has native contraction exactly one. Formula (SIG) shows:

* every axis is preserved, since every coordinate factor has sum zero;
* a line varying in both `A` and `F` meets no support cell;
* contractions within `F` have size at most `d<r`;
* a contraction within `A` has size at most `r`, with equality only for
  the intended native block and sign pattern.

Thus the only affected family of varying-set size at least `r` is the
native family, with image exactly the graph-product tensor on `F`.
Every stage has `2^k` cells and is realized by `2^(k-1)` genuine equal-gap
prime pairs. If `d=0`, there is one scalar reservoir for that full body.

Process `r=k,k-1,...,r_*`. Families at one `r` preserve one another and
all previously corrected higher families. This is a strict triangular
argument because `k-r<r`; it is precisely the inequality that fails for
the omitted small varying sets.

### 8.2 General packing for a selector times a bounded-load footprint

Here is a reusable placement lemma. On the fixed-coordinate set `F`, let
`M_alpha` be bounded-support templates, with each target cell contained in
at most `B` templates and each template using at most `s` cells. Keep `r`
and `B,s` fixed. A stage on `A` is `U_A tensor M_alpha`; for the present
application, `M_alpha` is a graph-product checkerboard, `s=2^d`, and
`B=Delta^d`. The selector orbit exclusions above are imposed, and each
reservoir has at most `L=o(n)` stages in one pass.

Every line varying only within `A` fixes one native `F` cell. Across the
entire pass, at most `2^r BL` support cells lie above that native cell.
Consequently all such line loads are bounded directly by `2^r BL`, even
for native or exceptional centered lines. No distribution of the chosen
selector labels is being assumed.

Now fix a potential line varying only within `F`, with its remaining `F`
coordinates prescribed by one support point of `M_alpha`. The union over
every possible selector position projects to the corresponding native line
of exactly `n` points. Its entire planned load is at most

`2^r BnL`.                                              (MP)

This includes canceled support on that line. With a separate pass cap
`H(k,B,s)L`, at most `2^(r+1)Bn/H(k,B,s)` of these line keys can already
be saturated. Each key contains every selector coordinate. Select
`a,b_i` successively; test a potential key when its last free variable is
assigned. It is injective in that variable. Over-testing all potential
support-vertex/direction keys is harmless, and the finite number of tests
is at most `2^r s (3^k-1)/2`. A cap such as

`H(k,B,s)=2^(4k+10)3^k(B+1)(s+1)`

therefore excludes fewer than `n/8` positive-label candidates at each
choice. The allowance of `2^r s` cells per future support pays coincidences
between already tested keys. Mixed `A,F` lines are excluded by orbit
separation. Lines within `A` have the direct bound above.

For occupied cells, vary the last free variable of a proposed vertex. Its
occurrences in the selector coordinates are all that variable or its
negative, with every other coordinate fixed. Thus it follows one full
signed line. Previously packed extra passes have maximum signed-line load
`o(n)` by these same caps, so only `o(n)` choices hit occupied cells.
Freshness across the reservoir excludes `o(n)` further labels, and its
native footprint excludes only `O_k(s)` orbits. Among `(n-1)/2` positive
labels a legal choice remains. No supports are committed until all tests
of all vertices are complete. This proves greedy disjoint placement.

Plan these extra stages before the axis controller. Their axis load is
`o(n)`, so AP(k) subsequently places every axis stage around them. There is
no circular reliance on unknown axis geometry. This proof needs bounded
native point degree and local line projections (MP); global volume alone
would not suffice.

### 8.3 Bundle ranges, residues, and numerical coefficients

Each native `A` line sees its fixed `0,+1,-1` graph-product coefficient
times the scalar value of the whole reservoir, so its two central states
differ by at most `g`. A nonnative line varying in a proper subset of `A`
fixes at least one selector coordinate; a line varying within `F` fixes all
selector coordinates. Freshness therefore permits at most one stage of
the reservoir. A line intersects that stage in at most two cells. The
whole-reservoir contribution range is at most `2X` on every full signed
line, including the omitted families.

Residues are repaired after the axis residue passes and before any main
numerical pass. For `d>=1`, the native tensor has zero margins over
`Z/(g/2)Z`. Use path-product prefix coefficients and separate stages of
actual gap `2 mod g`, as in Section 5.1. For `d=0`, use its one scalar
coefficient. All representatives are in `0,...,g/2-1`; no nonunit division
is used. The contracts of (MAJ) preserve the earlier larger families and
all axes. After finishing the descending residue pass, all targets in
`mathcal H_k` are matched modulo `g`. Total numerical residue drift per full
signed line is `O_k(gX)` by the proved caps.

Run the main axis controller next. Its gaps are divisible by `g` and hence
preserve all these residues. All nonaxis errors are then `O_k(K_DX)`,
and body errors remain at their centered scale because axes avoid bodies.
For each descending numerical majority level, apply the tensor-expander
inverse of rank `d` to the residual divided by `g`. Its physical scalar
bound is

`(5log n+5)^d E + g/2 + g(Delta n)^d/2^(d+1)`

when `d>=1`, where `E` is the current maximum native error; for `d=0`,
the required coefficient is the scalar itself. Use a strictly larger next
scale for each value of `r`. The exponent ladder with total level count

`(2k-3) + (k-floor(k/2))`

has a positive gap between consecutive scales for every fixed `k`, and
still has final exponent below `3/4`. Explicitly use
`D_M=3k-floor(k/2)-4` and `a_j=3/5+3j/[20(D_M+1)]`
for `0<=j<=D_M`, including the axis levels. Thus the flow coefficients fit their
reservoirs, including all rank-dependent rounding terms. Each pass's actual
incidental drift is paid as `O_k(K_jX)` before the next level. At one fixed
`r`, the finitely many block/sign families preserve one another exactly.

The extra reservoir count at block size `r` is at most

`binom(k,r) 2^(r-1) (32n)^(k-r)`.

Each uses `2^k` entries per stage. Hence its full seed, macro and residue
invoice is `O_k(n^(k-r_*)(P_k+g+K_final))`, below
`O_k(n^(k-1)K_final)`. The supply, deletion, centering, unused-mean and
capacity inequalities in Section 6, or the common
[resource ledger](hyperk_resources.md), apply with this larger fixed depth
and tuple size `2^(k-1)`. The two-sided capacities and exact pool are
preserved at every switch. This proves UM(k).

**Corollary PM(k), prime targets on the proved family.** For each fixed
`k>=2` there is `N_M(k)` such that for every odd `n>=N_M(k)`, the exact
first `n^k` odd primes admit a bijective arrangement with every axis and
every full signed line varying more than `k/2` coordinates prime. Apply
UM(k) to the compatible prime prescription in
[hyperk_targets.md](hyperk_targets.md); its displacement is `o(X)` and its
partition equations include all the single-coordinate margins required
here. This corollary uses the separately owned target theorem KPT as an
explicitly identified mathematical input. The physical
proof above does not reprove KPT, and the independent-review statuses of
the two sources remain separate. It does not claim the omitted families
or the full endpoint at `k>=4`.

## 9. The full signed-line architecture and its remaining generator issue

Let `W=ker(sum:Z^I->Z)`. After all axes are exact, corrections lie in
`W^(tensor k)`. For a signed block `A` with at least two coordinates, let
`C_A` be the signed equality contraction appearing in (SIG). A collection
of disjoint signed blocks `pi` has rank

`r(pi)=sum_(A in pi)(|A|-1)`.

A generic unit selector for one signed block is

`U_A=tensor_(i in A)(e_(sigma_i a)-e_(sigma_i b_i))`,

where `a` and every `b_i` occupy different noncentral reflection orbits.
It has `C_A U_A=1`. Selectors on disjoint blocks can use disjoint orbit
sets. With a residual tensor `M` on the unused coordinates, and selector
orbits disjoint from every coordinate value in `supp M`, mixed contractions
across different selector blocks or into `M` vanish. A surviving contraction
inside one selector block has the selector's compatible signs and leaves
the remaining difference factors. Thus the section-contraction images form
a triangular system on signed block partitions ordered by rank. At equal
rank, only the intended partition survives, provided `M` is annihilated by
all its own nontrivial signed contractions.

This exposes the invariant behind the body, triple, common-pair-trace and
pure-pair stages in four dimensions. Their rank order is the first
nontrivial instance of this partition filtration. A finite number of types
for fixed `k` is not itself a bounded physical controller.

The direct compatible-generator architecture would need the following
additional statement, beyond the ordinary axis tensor inverse:

**Required bounded-kernel lemma BK(d).** For fixed `d`, tensors in
`K_d={M in W^(tensor d): C_A M=0 for every signed A, |A|>=2}` admit an
integral decomposition into `O_d(n^d)` templates of bounded support, with
coefficients `O_d(E log^(c_d)n+n^d)` for input norm `E`, and uniformly
bounded template incidence at every target cell. The placement proof in
Section 8.2 then supplies the necessary local line-load bounds; no
unproved uniform spatial distribution is substituted for it. The same
identities must hold over arbitrary
residue rings, with bounded-degree residue templates. Templates must admit
an actual grouped-pair implementation, or a proved bounded disjoint
checkerboard refinement. Neither signed coefficients nor a rational right
inverse substitute for this last condition.

For `d=0,1` the kernel condition is trivial or ordinary zero-sum flow. For
`d=2`, MP4 supplies the needed bounded-load marker construction. A local
projection of one compact tensor into `K_d` can be built using finitely many
fresh selectors, but selecting independent markers for many tensors leaves
a marker residual. Selecting the same fixed markers for all tensors may
make those residuals cancel algebraically, while concentrating physical
occupancy on a few lines. The latter violates the required per-line reserve
and cannot be charged merely to global volume.

The arbitrary-`d` bounded marker relocation/decomposition has not been
proved in this source. Consequently, the partition architecture is a
precise continuation interface, not a theorem that all signed lines have
already been physically realized. The numerical ladder is not its current
obstruction: any finite depth has strict slack by Section 1. The obstruction
is the coefficient-and-support statement BK(d), including its residue and
physical implementation requirements.

## 10. Controls, negative controls, and status

The companion [hyperk_controller.py](../../originals/code/hyperk_controller.py) checks
complete signed-line signatures, arbitrary-rank checkerboard orientations,
axis preservation, generic selector behavior, and the variable-dimensional
axis correction recurrence. It also checks every block and sign of the
majority-coordinate preservation contract through dimension six, and retains
a concrete complementary spill at `k=6,r=3` that falsifies applying that
contract outside its strict range. It compares the sparse signature formula to an
independent full line enumeration on feasible instances. Exact pool primes
used in partial physical stages are checked independently by trial division;
those stages are not full array certificates. Numeric tensor controls are
not prime permutations. The program rejects duplicate endpoints, wrong gap,
wrong signs, nongeneric selectors, and false full-arrangement labels.

Retained genuine partial trades at dimensions five and six use sixteen and
thirty-two disjoint equal-gap pairs, respectively:

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyperk_controller.py
python3 -B problems/prime-arrays-beyond-square/code/hyperk_controller.py --verify problems/prime-arrays-beyond-square/inputs/hyperk-controller-k5-stage.json
python3 -B problems/prime-arrays-beyond-square/code/hyperk_controller.py --verify problems/prime-arrays-beyond-square/inputs/hyperk-controller-k6-stage.json
```

Reproduce either retained input with `--write-physical PATH --dimension 5`
or `--dimension 6`. The files carry the kind `partial-prime-controller`;
mislabeling one as a full arrangement is a checked negative control.

The proof uses `k` as a variable. Tests at `k=5,6` diagnose its implementation;
they do not establish the universal quantifier. Conventional proof status,
independent review, local test success, remote CI, and kernel verification
are recorded separately by the owner. At this source revision, U(k) and
UM(k) are author conventional proofs; BK(d) and the full signed-line controller remain
open in the explicitly stated form.
