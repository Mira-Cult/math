# Physical signed-line corrections in four dimensions

Author: `/root`, with numeric generator and marker-projection contributions
from `/root/hyper_incidence`. This source owns the extra-controller packing,
physical stages, whole-reservoir bounds and descending correction. The axis
controller is separately proved in [hyper4_axis.md](hyper4_axis.md); the exact
integer image and bounded matrix decomposition are in
[hyper4_incidence.md](hyper4_incidence.md). These authorship overlaps must be
excluded from any purported independent review. Manuscript-local labels only.

All assertions below are for every sufficiently large odd order, with fixed
constants independent of the order. No computation is used to infer that tail.
The initial checkpoint is an author proof pending independent review.

## 1. Physical tensors and all their signed-line images

Use centered coordinates `I={-m,...,m}`, `n=2m+1`, and the line labels of SI4.
An orbit means `{a,-a}`; free orbit representatives are positive and noncentral.
For four ordered pairs of distinct endpoints write

\[
 v_i=e_{a_{i,0}}-e_{a_{i,1}},\qquad C=v_1\otimes v_2\otimes v_3\otimes v_4.
                                                        \tag{PT1}
\]

Every axis sum of `C` vanishes. Its full image on the family varying `S`,
with normalized signs `epsilon`, is exactly

\[
 \left(\sum_{t\in I}\prod_{i\in S}v_i(\epsilon_i t)\right)
       \bigotimes_{j\notin S}v_j.                       \tag{PT2}
\]

This identity includes central and repeated-orbit cases. It follows by
substituting each point of a defining line, so there is no generic-position
assumption in the formula itself.

**Eight-pair physical lemma.** Given eight mutually disjoint pairs of actual
pool primes, all of difference `d>0`, assign one pair to each of the eight
edges parallel to the fourth coordinate in (PT1). At its bit-zero endpoint
put the lower prime when the sum of the first three endpoint bits is even,
and the upper prime otherwise. Swap every pair. The change at vertex
`(a_(1,b1),...,a_(4,b4))` is exactly `d(-1)^(b1+...+b4)`.
Thus the swaps realize `dC`, preserve every axis, and permute sixteen distinct
prescribed entries. Reflecting or permuting entire coordinates preserves the
assertion. Formal increments are not used in place of these swaps.

We also need a compound version. Let `M` be a zero-row/column matrix whose
nonzero entries are `+1` or `-1`, at most twenty in number. Let

\[
 A_\sigma=(e_a-e_b)\otimes(e_{\sigma a}-e_{\sigma c}),
                                                        \tag{PT3}
\]

where `a,b,c` are different noncentral orbits, outside every orbit appearing
in either coordinate of the support of `M`. Pair along the first coordinate
of `A_sigma`. For each support cell of `M` there are two such edges. Orient
the lower/upper primes according to the sign of `A_sigma tensor M` there.
At most forty mutually disjoint equal-gap pairs then implement exactly
`d A_sigma tensor M`. All its entries change by `+d` or `-d`; no pair has to
have difference `2d`, and no cell or prime is reused. If both signed traces
of `M` vanish, (PT2), extended linearly, shows that this stage affects only
the native pair family, with image `dM`. Its other pair, triple and body
images, and all its axis images, are zero.

The latter support may meet a complementary pair line even though its net
change on that line is zero. The occupancy proof below counts those cells.

## 2. Four types of extra reservoirs and their preservation contracts

The scalar grid gap `g`, prefix bound `P`, midpoint width `delta X`, and
fresh-pair supplies are those proved in U4, Section 2. In particular the
growth lemma there supplies forty pairs after the full common deletion
allowance; no new prime-constellation theorem is assumed. Put

\[
 K_5=\lceil n^{77/100}\rceil,\quad
 K_6=\lceil n^{78/100}\rceil,\quad
 K_7=\lceil n^{79/100}\rceil.                           \tag{PT4}
\]

Every main scalar reservoir consists of at most `P` prefix stages and
`ceil(32K_j)` macro stages at its specified level. Each stage has a single
actual difference, shared by all its pairs. Differences of different stages
may differ. All main differences are multiples of `g`.

The U4 subset-sum proof gives a complete grid and two complementary
reference states whose native scalar values differ by at most `g`. From
either state every scalar in `g Z` of magnitude at most `3K_jX` is attainable.
This provides both signs using the same set of reserved entries. It does not
postulate negative capacities or share endpoints between opposite choices.

### 2.1 Eight body reservoirs

For the all-positive body, a stage is

\[
 (e_a-e_b)\otimes(e_a-e_c)\otimes(e_a-e_d)\otimes(e_a-e_e),
                                                        \tag{PT5}
\]

with five different noncentral orbits. Coordinate reflections give the other
seven body directions. Its body image is the corresponding unit vector.
Its triple images are the four vectors `e_a-e_bj` with the appropriate
reflections; its pair images are the six products of the remaining two
factors. All other images vanish. Every surviving extra line meets this
support in one cell. Use capacity level `K_5`.

Across the whole reservoir, including prefix and macro passes, all five
free orbits at a new stage are fresh for that reservoir. Hence a fixed triple
or pair line meets at most one stage and one cell of this entire reservoir.
The native body meets many stages, with constant coefficient one. This will
bound both incidental drift and the random reference range.

### 2.2 Triple-family transfer reservoirs

For each of the sixteen triple families, place one reservoir per labeled edge
`(u,v)` of the degree-64, expansion-eight graph on its fixed-coordinate labels.
Its stage, before the requested coordinate reflections, is

\[
 (e_a-e_b)\otimes(e_a-e_c)\otimes(e_a-e_d)\otimes(e_u-e_v),
                                                        \tag{PT6}
\]

with the three varying factors placed in their native coordinates. The four
free noncentral orbits are different and avoid the orbits of `u,v`; this is
possible also when `u,v` are central or opposite. It transfers one unit between
the native triple targets, changes no other triple or body target, and spills
only into the three contained pair families. Each spill is a zero-margin
rectangle whose two coordinate-orbit sets are disjoint, so both signed traces
vanish. Use capacity level `K_5`.

The four free orbits are fresh across the whole reservoir. A pair line met
by its spill has one fixed coordinate among these free values and its other
fixed coordinate equal to `u` or `v`. Thus any fixed pair line meets at most
one stage and one cell per reservoir. Across all triple reservoirs it can
meet at most `8 Delta` reservoirs: choose the third varying coordinate in
two ways, choose its compatible sign in at most four ways, and choose a
graph edge incident to the other fixed coordinate in at most `Delta` ways.
This deliberately loose bound is independent of `n` and `K_5`. Consequently
the total numerical pair drift from this entire correction is `O(X)`, not
`O(K_5X)` and not `O(nK_5X)`.

### 2.3 Twelve common pair traces

For a partition `ij | kl` and signs `sigma,tau`, use a stage

\[
 A_\sigma\otimes B_\tau,                              \tag{PT7}
\]

where each factor is a generic unit-trace rectangle (PT3), and all six free
orbits are different. It has precisely two pair images: `B_tau` in family
`ij,sigma`, and `A_sigma` in family `kl,tau`. It changes their common trace
by one, every other common trace by zero, and every triple/body/axis by zero.
Use `n` scalar reservoirs of capacity level `K_6` for each of the twelve
identities. A trace error as large as `nE` is split into `n` grid integers
each at most `E+g` in magnitude. The division is ordinary quotient/remainder
division; it does not invert `n` modulo a modulus.

All six free orbits are fresh across each complete reservoir. Any fixed pair
line therefore meets that reservoir in at most one stage and one cell. Bounds
across the `12n` reservoirs require the packing caps in Section 3; freshness
within one reservoir alone would not give those caps.

### 2.4 Pure pair kernels with bounded marker load

For each of the twelve pair families use the templates of MP4. Every template
`M` has zero margins and both traces zero and is a sum of at most five
cell-disjoint signed rectangles. Thus it has at most twenty entries, all
`+1` or `-1`. Put one reservoir of capacity level `K_7` on `A_sigma tensor M`
using the compound physical lemma. Its three free native selector orbits are
fresh across the whole reservoir and avoid all coordinate orbits of `M`.
It affects exactly its native pair family, with the fixed matrix image `M`.

Here are the exact structural inputs from MP4 used in placement. With
`Delta=64`, `L_*=256 Delta^2`, one may take

\[
 B=\Delta^2+321L_*,\qquad E_*=1282\Delta^2.             \tag{PT8}
\]

There are `O_Delta(n^2)` templates, each target matrix cell belongs to at most
`B` of them, and at most `E_* n` templates meet the union of the two signed
diagonals. The last bound includes graph rectangles with cancelling trace
but nonempty diagonal support. It also includes every marker-flow template.
These support counts, not merely the zero trace equations, are necessary.
The separate path/tree residue templates obey the same bounds after enlarging
these fixed constants if needed; their coefficients are reduced modulo `g/2`.

## 3. Disjoint support packing, with local section bounds

**Lemma EP4.** All the extra supports above, including their residue versions,
can be planned pairwise disjointly. In each separate prefix, macro or residue
pass, with at most `L=o(n)` stages per reservoir, each required signed line
and each axis has `O(L)` reserved cells. The implied constant is absolute.
The distinct-orbit rules hold across complete main reservoirs. Extra supports
can be planned before the axis supports; AP4 then places all old supports
around them. No cell is shared between the two controllers.

**Proof.** There are finitely many passes and families. Plan bodies, triples,
common traces and pure pair families successively, keeping separate load caps
for each pass/family. Let `H` be a fixed constant sufficiently large for all
the finite coefficients below; for example any constant larger than
`2^80(B+E_*+Delta+1)` suffices. Cap new loads at `HL`, apart from native
loads already bounded directly by incidence. A support adds at most eighty
cells and at most eighty cells to a line. Reject a placement if it exceeds
the cap. At rejection the old load is at least `HL/2` eventually. Previous
passes have total load `O(P+K_7+g)=o(n)` on every required line.

The body, triple and trace groups each have `O(n)` reservoirs and constant
stage size. A cell lies on at most forty required lines: for each nonempty
varying set and normalized signs there is at most one such line through it.
Hence their total planned line incidences in one pass are `O(nL)`. At most
`O(n/H)` lines can be saturated by this group. Native body loads are at most
`L`; native triple loads are at most `Delta L`. They need no avoidance.
Every other line a proposed stage can meet has a fixed coordinate containing
one of its free labels. Once its last free label is selected, its line label
depends injectively on that choice. Each saturated line therefore forbids at
most a fixed number of choices. There are only a fixed number of candidate
line types and support vertices, so these cap exclusions total `O(n/H)` at
each successive free-label choice.

Here is a precise convention for deferred cap tests. For each support-vertex
word and each of the forty directions, form its potential line key from its
fixed-coordinate words, even if the eventual varying coordinates fail the
incidence test. Test that key when its last free variable is assigned, and
require existing load plus eighty to be at most `HL`. A nonnative nonempty
key always contains a free variable. For triples the only fixed coordinate
without one is `u` or `v`, giving exactly the native triple lines. Body and
trace supports have all coordinates free. Full-body keys are empty, but only
the native body can meet a body support; triple and trace supports avoid all
bodies. Thus all unavoidable keys have the direct native bounds. The other
keys are injective in their last variable. Over-testing potential lines is
harmless. No support is committed until all free choices are made, so loads
stay fixed; the allowance eighty pays every eventual coincidence of vertices
on an already tested line. There are at most `16*40=640` potential tests in
one ordinary stage. This makes the rejection and saturation counts literal,
including lines whose incidence becomes known only at a later choice.

Occupied-cell exclusions are also controlled without averaging. As one free
label varies, each specified vertex follows a full signed line: its occurrences
in one or more coordinates are `a` or `-a`, and its other coordinates are
already fixed. Thus at most `O(P+K_7+g)=o(n)` choices hit previous occupied
cells, for each of the boundedly many newly determined vertices. At a partial
choice, defer this test until the last variable of a vertex has been chosen.
The same convention applies to line-cap tests. A cap whose line label is
already fixed by earlier choices was already tested then; native fixed lines
have the direct bounds just given. Finally, previous labels in this reservoir
exclude `O(P+K_7+g)=o(n)` reflection orbits, and generic restrictions exclude
only a fixed number. Among the `(n-1)/2` positive labels there is a choice:
fix `H` first, then take `n` large. This proves packing for these groups.

The pure pair groups have `O(n^2)` reservoirs. A global saturated-line count
would now lose a factor `n`; the following local counts replace it. Fix one
native family, with selector coordinates `i,j` and matrix coordinates `k,l`.
For each matrix cell `(k,l)`, at most `B` templates contain it. Consequently
its native pair line receives at most `BL` cells in this pass. An axis along
`i` or `j` through this matrix cell receives at most `2BL` cells. These native
bounds are automatic and are below `HL`.

For a fixed value `l=l_0`, the total planned support in that coordinate slice
is at most `4BnL`: sum the bound `B` over the `n` possible `k` cells, and
count the four selector vertices per stage. It follows that at most
`8Bn/H` axes along `k` in this slice can be saturated. The analogous bound
holds for axes along `l` with `k=k_0` fixed. A proposed template uses at most
twenty values of each coordinate, so these local counts cost `O(Bn/H)` free
selector choices. No uniform distribution of past choices is presumed.

Only the at most `E_* n` diagonal-touching templates can meet a complementary
pair line. Their entire planned complementary-line incidence is at most
`160E_* nL`, counting the central matrix cell on both signed diagonals.
Hence only `320E_*n/H` complementary lines can be saturated.
No mixed pair, triple or body line meets these supports, because every
selector orbit avoids every matrix-support orbit.

Choose the free selector labels in the order `a,c,b`. The corner
`(a,sigma*a)` determines the first inner-axis and complementary-line tests;
`(a,sigma*c)` determines the next; the two corners with first coordinate `b`
determine the last. In every test the relevant line label is injective in
the newly chosen variable. Thus the displayed local saturation counts remove
only `O((B+E_*)n/H)` choices at each step. For occupied cells, varying `a`
at a fixed matrix cell follows its native pair line, and varying `c` or `b`
follows an axis. The already established signed-line/axis load bounds remove
only `o(n)` choices. Freshness and orbit exclusion also cost `o(n)`. All
three choices therefore exist.

Apply the same argument to each of the twelve native families and to the
separate residue pattern collection. A fixed finite sum of the pass caps
gives the asserted `O(L)` bound and total maximum load `o(n)`. All chosen
supports are disjoint by the occupied-cell test. AP4 applies to their maximum
axis load and adds the old supports without collision. This proves EP4. QED.

The proof explicitly counts complementary diagonal support even where the
numeric change is zero. It never asks all axis controls to avoid the union
of extra lines, which would remove every slot from certain exceptional axes.

## 4. Fresh value allocation and the complete reserve

Plan all supports first. Select the common-gap seed supply and allocate all
seed endpoints before other prime requests, as in U4. The old axis seed
demand is `O(n^3P)` pairs, the new demand is `O(n^2P)` pairs, with at most
forty pairs per stage. Their sum is `o(X/log^3 X)`, so one matching supplies
all seeds without recycling a prime. For growth, macro and residue stages,
delete every endpoint previously reserved, including unused choices.

The extra prefix invoice is `O(n^2P)`. Body/triple macro stages use
`O(nK_5)` entries; common-trace macro stages use `O(nK_6)`; pure pair macro
stages use `O(n^2K_7)`. Residue stages use `O(n^2g)` entries. These constants
include the forty-pair compound stages, all marker edges and their repairs,
all signs and all twelve families. Thus

\[
 Q_{\rm extra}=O(n^2(P+g+K_7))=o(n^3K_4).              \tag{PT9}
\]

Together with the axis invoice `<2^24 n^3K_4`, this is below
`Q_*=2^40n^3K_4` for every sufficiently large order. Every prime request can
therefore use the worst-case depletion estimate in U4. Its smallest fresh
class supply is `>> n^(19/5)/log n`, whereas the deletion exponent is
`3+19/25=94/25<19/5`. The forty-pair growth and macro lemmas apply at each
request. Residue stages use lower class `-1` and upper class `+1 mod g`, both
reduced, giving actual common differences `2 mod g`. This works for every
even `g`, including those divisible by small odd primes. No target residue
is required to be a unit for the physical theorem.

All selected entries belong to the exact first-prime pool. Every unselected
entry remains available for the later random bijective completion. There is
no independent-pair hypothesis masquerading as a disjoint forty-tuple: each
request first obtains the repeated difference in the fresh set and then its
matching, and pays every endpoint immediately against `Q_*`.

## 5. Residues before the main corrections

Put `h=g/2`. After the old five-level residue repair, every axis target agrees
modulo `g`. The remaining target error is even, and divided by two its pair
margins, triple totals and complementary-pair identities hold in `Z/hZ`.
Here compatibility is inherited from the actual array and the chosen target
vector; it is not asserted for arbitrary independent extra residues.

Use separate stages of difference `2 mod g`, never the main reservoirs:

1. Correct each body residue by its unit template.
2. Correct each triple vector on a path, using its zero total in `Z/hZ`.
3. Correct each of the twelve common pair traces by its unit coupled template.
4. Correct the remaining zero-margin, zero-trace pair matrices by the residue
   version of MP4: tensor a tree incidence basis, project to the marker
   templates, and route the marker coefficients by a path with disjoint-support
   repairs.

All steps are integer identities over `Z/hZ`. In particular the tree incidence
columns are an integral basis of the zero-sum lattice, so reducing its prefix
coefficients requires no division by `n` or any nonunit. Every coefficient
has a representative in `{0,...,h-1}`; give its reservoir `h-1` stages and
switch that many distinct stages. The repaired marker path has bounded degree
and bounded target-cell load, as proved in MP4. For common traces one residue
reservoir per identity suffices. The additional `n-1` main copies need no
residue stages.

These corrections preserve every axis exactly, and preserve all already
corrected higher families modulo `g`; the displayed template contracts prove
this in the stated order. EP4 gives `O(g)` cells on any required line, hence
actual drift `O(gX)` throughout the entire extra residue repair. If `h=1`,
no residue stages are needed. Every subsequent old or new main stage has
difference divisible by `g`, so it preserves every signed-line residue.

## 6. Whole-reservoir ranges and descending numerical correction

No independence is assigned to cells. For initial centering, independently
choose one of the two complementary reference states of each entire main
reservoir. A macro cell has its pair midpoint as expectation, within
`delta X` of the exact pool mean. Prefix and fixed residue cells cost at most
`X` each.

On every axis the contribution range of an extra reservoir is zero. On a
body reservoir's native body, or a triple reservoir's native lines, the two
reference states differ by at most `g` in scalar value. A lower extra line
meets at most one stage and one cell by the full-bundle freshness rule, so its
range is at most `X`. The same rule bounds every pair-line range of a coupled
trace reservoir by `X`. A pure pair reservoir has native image equal to its
fixed template times the scalar; every template entry is `+1` or `-1`, so
its native range is at most `g`, and all other ranges are zero. Thus every
entire reservoir has range `O(X)` on every required line. This also proves
the extra part of U4's joint centering interface, rather than assuming it.

After joint centering and both residue repairs, run the old numerical axis
controller. Its supports avoid all full bodies, and its separate pass caps
bound every pair/triple drift by `O(K_4X)`. For nearby targets this leaves
body errors `O(K_0X)` and pair/triple errors `O(K_4X)`, all divisible by `g`.

**Body pass.** Each body error is `o(K_5X)`, within its scalar interval.
Correct all eight. Freshness bounds the total change on any lower line by
`8X`, independent of how many body stages are switched.

**Triple pass.** Compatibility makes each residual triple vector have zero
total as an integer, since the axes are exact. Its entries are `O(K_4X)`.
The expansion-eight integer flow has coefficients at most
`g ceil(O(K_4X)/(8g))=O(K_4X)+O(g)=o(K_5X)`. Correct these vectors with the
triple reservoirs. They preserve every body and axis, and change any pair
line by at most `8 Delta X` as established in Section 2.2. In particular the
remaining pair maximum is still `E=O(K_4X)`.

**Common-trace pass.** Pair margins now vanish by the exact axes. Each
common trace has size at most `nE` and is divisible by `g`. Split it among
the `n` reservoirs, with each scalar at most `E+g=o(K_6X)`. The coupled
images enforce both sides of its compatibility equation simultaneously and
preserve the other eleven traces and every higher family. EP4's separate
macro cap bounds the accumulated pair drift by `O(K_6X)`, including all
prefix stages as `P=o(K_6)`. Each final pair residual therefore has maximum
`O(K_6X)`, zero margins and both traces zero.

**Pure pair pass.** MP4 supplies integer coefficients in physical scalar
units bounded by

\[
 (5\log n+5)^2 O(K_6X)+g/2+512gn^2=o(K_7X).           \tag{PT10}
\]

Its marker-flow coefficients obey the same bound (indeed one eighth plus
rounding). Every coefficient is a multiple of `g` because MP4 is applied to
the residual divided by `g`. Every one lies inside its complete reserved
interval. Switch the compound stages to realize them. Each reservoir changes
only its native pair family. Thus all twelve residual matrices are corrected
without changing a single already fixed axis, triple or body target.

Every operation was a swap on distinct previously assigned prime pairs. The
global bijection survives, every required target is attained, and all capacity
claims have strict asymptotic margins. The joint baseline and final prime-target
application are composed explicitly in [hyper4_cube.md](hyper4_cube.md).

## 7. Failed local shortcuts retained as scope guards

A common central vertex in (PT5) lies on all eight bodies, so it cannot isolate
one. Repeating the same pair in all four directions gives body coefficient
two on its all-positive body, not a unit control. A formal product tensor
without eight disjoint equal-gap pairs is not a legal permutation. A single
two-coordinate target cannot be moved axis-neutrally with its margins fixed;
even separate zero-margin matrices must obey the twelve common-trace identities.
Fixed shared markers would overload a few native lines; the bounded-load
projection and marker graph repair this. A global saturation count for the
`O(n^2)` pure-pair bundles loses a factor `n`; EP4 uses fixed-coordinate slice
counts instead. These are obstructions to the listed shortcuts, not to the
eventual prime theorem.
