**Public reading copy.** Presentation and links have been normalized. Historical status statements below belong to their source revisions; see the [current publication status](../../README.md#review-and-verification-status). The matching original bytes are in the [source archive](../../originals/manuscripts/cube_controller.md).

# A triangular permutation controller for the exact prime cube

Authors: `/root` (triangular architecture and parameter schedule) and
`/root/cube_targets` (supply, embedding, centering, residue and composition
proof). The tensor-flow theorem is due to `/root/incidence` in the linked
canonical source. These are manuscript-local results; no permanent claim
IDs are allocated. Independent review is required before the handoff treats
the proposed composition as reviewed.

## 1. Statement and parameters

Write `A={p_2,...,p_(n^3+1)}`, `X=max A`, `T=sum A`, `m=T/n^3`,
and `mu=nm=T/n^2`. Coordinates of a cube are `(x,y,z)` in `[n]^3`.
Its axis sums are

`A_(y,z)=sum_x a_(x,y,z)`, `B_(x,z)=sum_y a_(x,y,z)`,
`C_(x,y)=sum_z a_(x,y,z)`.

The repeated letter `A` for the pool and its first directional array will
always be distinguished by a subscript. A target triple `(A',B',C')` is
compatible when its pairwise plane-margin equations hold and each of its
three grand totals is `T`; see
[the exact incidence theorem](incidence.md).

Put, with ceilings understood,

`K0=n^(3/5)`, `K1=n^(2/3)`, `K2=n^(3/4)`, `delta=n^(-1/5)`.

Every constant implicit below is absolute and fixed before `n` increases.
Changing a ceiling changes no limit. The useful separations are

`delta K2=n^(11/20)=o(K0)`, `sqrt(n log n)=o(K0)`,
`K0=o(K1)`, `K1 log^2 n=o(K2)`, `K2=o(n)`,
`n^2 K2=o(delta X/log^2 X)`,
`n^2 log^2 X=o(X/log^3 X)`.

Here the prime number theorem gives `X~3n^3 log n`, `m~X/2`.
In particular the supply inequality with the shrinking midpoint windows
has a positive power margin: `delta X/log^2 X` has order
`n^(14/5)/log n`, whereas total deletion has order `n^(11/4)`.

**Theorem U3 (universal odd compatible cube targets).** For every
sufficiently large odd `n`, every compatible triple of odd integer target
tensors `(A',B',C')` with grand total `T` and

`max(|A'_(y,z)-mu|,|B'_(x,z)-mu|,|C'_(x,y)-mu|)<=K0 X`

is realized by a permutation of exactly the first `n^3` odd primes.

The hypotheses do not assert a prime arrangement or a permutation controller.
They are integer plane-margin equations and an explicit box around the natural
mean. The proof constructs the controller from the prescribed pool. Its
intermediate gap `g` grows at most logarithmically; residue repair removes
any corresponding extra restriction from the final statement.

## 2. The two analytic supply facts actually needed

The prime counts used here follow from the short-interval progression
consequence of Thorner--Zaman, arXiv:2108.10878v2, Section 1.2, printed
page 3; its precise source contract and ineffective boundary are recorded
in [the target manuscript](cube_targets.md#imported-interfaces-and-their-exact-boundary).
The modulus range below is `g<=16ceil(log_2 X)`.

For each fixed `c>0`, uniformly in every reduced class modulo `g` and
every subinterval of `[X/4,3X/4]` of length at least `cX`, that
subinterval contains `>>_c X/(g log X)` primes. Also put

`I_-=[m-X/6-delta X,m-X/6+delta X]`,
`I_+=[m+X/6-delta X,m+X/6+delta X]`.

These intervals lie in `[X/4,3X/4]` eventually. Each contains
`>>delta X/(g log X)` primes in every reduced class. To check the
short-interval hypothesis, their lengths have logarithm ratio tending to
`14/15` relative to `X`, which exceeds `7/12`. All endpoints have size
comparable to `X`, and the logarithmic moduli are permitted. The constants
are uniform in the classes, in the selected `g`, and throughout the large
`n` tail. This is an asymptotic use, not a claim of an explicit cube cutoff.

At most `Q=2^20 n^2 K2` entries will be reserved in the entire construction
once `P,g<=K2`; this explicit upper bound is checked in Section 3.
The separation in Section 1 shows that deleting *any* at most `Q` entries
leaves at least half of each displayed supply eventually. This worst-case
deletion statement pays for all earlier allocations even if concentrated
in one residue class or one midpoint interval.

### 2.1 Disjoint common-gap seeds at every large scale

Inside `[X/4,3X/4]` there are `M~X/(2log X)` primes. Pair consecutive
members in their increasing list, discarding only one unpaired member from
this **selection procedure** if necessary; that prime remains in the pool.
The selected pairs are disjoint, and the sum of their gaps is at most `X/2`.
For large `X` there are at least `X/(5log X)` pairs. At most
`X/(16log X)` have gap greater than `8log X`, so a positive constant
times `X/log X` of them have even gap at most `8log X`.

Pigeonhole over these `O(log X)` gaps gives one even gap
`2<=g<=16ceil(log_2 X)` and `>>X/log^2 X` disjoint pairs with that
gap. Pigeonhole their lower endpoints modulo `g` once more. This gives
`>>X/log^3 X` disjoint pairs `(p,p+g)` in one common class `r mod g`.
The class is reduced because all these primes exceed `g`.

Only the needed `O(n^2 log^2 X)` seed pairs are now selected and reserved;
all other primes stay available. The supply comparison in Section 1 pays
this demand. This elementary all-scale argument replaces the old fixed-gap
Maynard input for the present cube controller. It does not prove bounded
gaps independent of the scale.

### 2.2 Repeated-gap growth after arbitrary previous deletions

The following finite lemma is convenient for both ordinary and rectangle
reservoirs. Let a fresh set `S` in one class modulo `g` lie in an interval
of length at most `X`, with

`|S|>=X/(gF)`, `F>=4`.

If `256gF^2<=R<=X`, there are two disjoint pairs from `S` with a
common difference `d`, an integer multiple of `g`, such that

`R/(32F)<=d<=R`.                                                   (G)

To prove this, partition the interval into at most `2X/R` bins of length
at most `R`. One bin contains `s>=R/(2gF)` points. In this bin, pairs
of distance less than `gs/16` number at most `s^2/16`: for each point
there are at most `s/16` possible larger points in that distance on the
`g`-grid. Since `s>=128F>=512`, at least `s^2/4` pairs remain.
Their differences lie between `gs/16>=R/(32F)` and `R` and take at
most `R/g` values. One difference therefore occurs on at least
`R/(16gF^2)>=16` pairs. The graph of pairs with a fixed positive
difference has maximum degree two; greedily selecting one edge and deleting
its at most two neighbours gives a matching of at least a third of its
edges. In particular two disjoint pairs exist. This proves (G).

Take `F=ceil(100 log X)`. On `[X/4,3X/4]`, the progression asymptotic
gives at least `X/(4g log X)` primes in the common reduced class `r`
eventually. The full deletion budget is `o(X/(g log X))`, uniformly in
the displayed modulus range, leaving at least `X/(8g log X)`.
This is larger than `X/(gF)`, so the finite hypothesis holds throughout
all allocations with this fixed choice of `F`.
Start each scalar reservoir with `ceil(256F^2)` copies of gap `g`:
one seed pair per copy for an ordinary reservoir and two disjoint seed
pairs per copy for a rectangle reservoir. Their subset sums cover every
multiple of `g` from zero to their total `R`.

If this interval currently ends at `R<X`, append a difference from (G).
The two intervals `[0,R]` and `[d,d+R]` overlap on the `g`-grid because
`d<=R`; thus the new subset sums contain the entire grid interval ending
at `R+d`. Each step increases the endpoint by a factor at least
`1+1/(32F)`. At most `32F ceil(log_2 X)` steps suffice to reach `X`,
and the final endpoint is at most `2X` eventually. The whole uncontrolled
prefix has length at most the following fixed quantity:

`P=ceil(256F^2)+32F ceil(log_2 X)=O(log^2 X)`.

All selected entries are fresh. In the ordinary case one of the two supplied
pairs is used; the unused second pair remains available. In the rectangle
case both are used. This proves actual disjoint paired-gap prefixes; a gcd
argument alone would not do so.

### 2.3 Macroscopic capacity and midpoint balance

Choose a fresh lower endpoint in `I_-` and a fresh upper endpoint in `I_+`,
both in class `r`. Their gap is a multiple of `g`, belongs to `[X/4,X/2]`
eventually, and their midpoint differs from `m` by at most `delta X`.

For a rectangle we need two *equal* gaps. The available lower and upper
sets have sizes at least `c delta X/(g log X)`. There are at most `X/g+1`
possible differences between these two sets in the common residue class.
Pigeonhole yields a difference supported by at least

`c' delta^2 X/(g log^2 X)`

pairs. This tends to infinity uniformly in `g<=16ceil(log_2 X)`.
For a fixed positive gap, the lower endpoints are distinct and their upper
partners distinct; the two endpoint intervals are disjoint. Thus all these
pairs already form a matching, and two can be selected. Both pair midpoints
have the required balance. The same argument with lower class `-1` and
upper class `+1` supplies equal-gap residue rectangles with `d=2 (mod g)`.

Append `J_t=ceil(32K_t)` macroscopic stages to each level-`t` reservoir.
Every new difference is at most `X` and the prefix already reaches `X`,
so complete grid coverage is maintained. Its total gap `R_b` satisfies

`R_b>=8K_t X`, `R_b=O(K_t X)`.

Choose a subset with sum `q_b=g floor(R_b/(2g))`. It is an actual
subset because the grid has been completed. Its complement has sum
`R_b-q_b`. Either reference orientation has distance at most `g/2` from
the exact midpoint, and either permits every signed grid transfer of
magnitude at most `g floor(R_b/(2g))>=3K_t X` eventually.

## 3. Physical gadgets and their distinct roles

Fix a loopless undirected multigraph `G` on `[n]` of maximum degree 64
with cut expansion

`|partial S|>=8 min(|S|,n-|S|)`.

Existence for every order, including odd orders, is proved by 32 random
permutations in baseline controller Lemma F1 at scientific revision
4ac266e7c4994a8502eb2a0c57d6b1d3fbd801c5. Its finite union bound is
also reproduced in the public
[controller](https://github.com/Mira-Cult/math/blob/4aaac8b416546d7e2fbc975faa960fe84d8e6f32/notes/sudes-first-conjecture/controller.md#f-independent-row-and-column-controls).
Parallel edges are separately labeled. The integral cut-flow consequence is:
if every edge permits `[-C,C]` integer transfers, all zero-total demands
of coordinate size at most `8C` can be met. This follows directly from
integral max flow and the displayed cut inequality.

All gadgets below use mutually disjoint cells and prime entries.

**Plane transfers (level 0).** For every edge `z,z'` of `G`, reserve
`n` ordinary reservoirs, each with `J_0` macro pairs and its prefix.
Each pair occupies `(x,y,z)` and `(x,y,z')` for a selected position `(x,y)`.
Within one reservoir these positions form a partial matching: all its
`x` labels are distinct and all its `y` labels are distinct. It moves
mass between the two whole `z`-planes and preserves every vertical sum
`C_(x,y)`. Each horizontal axis line meets at most one cell of a given
reservoir. The `n` reservoirs together give the plane edge a complete
grid interval of signed capacity at least `3nK0X`.

**Slice transfers (level 1).** Within each fixed `z`-plane, take two
independent copies of `G`, for row and column transfers exactly as in the
square controller. An ordinary pair between `x,x'` at one `y` changes
`B_(x,z),B_(x',z)` and preserves every `A` sum. Transpose to control
`A` while preserving `B`. Each edge has one level-1 reservoir of signed
capacity at least `3K1X`. Its distinct pairs occupy distinct free positions
on the transverse coordinate. A vertical line meets at most one cell of
each such reservoir.

**Vertical checkerboards (level 2).** For every ordered pair of graph
edges `e=(x,x')`, `f=(y,y')`, use one rectangle reservoir. A stage
with equal-gap pairs `(p,p+d)` and `(q,q+d)` occupies the four corners
in a common, freely chosen `z`-plane as

`[[p,p+d],[q+d,q]] <-> [[p+d,p],[q,q+d]]`.

The change in the four `C` entries is `d[[1,-1],[-1,1]]`, with an
orientation sign determined once for each graph edge. Every `A` and `B`
sum is preserved **as an integer**, not just modulo `g`. Distinct stages
of this reservoir use distinct `z` values. The signed scalar capacity of
each edge-pair reservoir is at least `3K2X`.

There are at most `32n^2` plane reservoirs, `64n^2` slice reservoirs,
and `1024n^2` rectangle reservoirs. Counting two entries per ordinary
stage and four per rectangle stage, their total is at most

`4288n^2P+2112n^2K0+4224n^2K1+135168n^2K2`.

Here the harmless bound `J_t<=33K_t` covers either convention for
rounding `K_t`. Section 5 adds at most `5n^2g` entries. Eventually
`P,g<=K2` and `K0,K1<=K2`, so the sum is less than
`2^20 n^2K2=Q`. These actual counts are the deletion budget used above;
they also show that fewer than half the pool entries are reserved
eventually.

## 4. Disjoint placement with separate prefix caps

Here are the complete occupancy obligations behind the preceding geometry.
They are combinatorial and do not assume random independent placement.
Treat the uncontrolled prefixes, each level's macro pairs, and residue
gadgets in separate passes. In a pass with at most `L` stages per
reservoir, impose caps `c_* L` for its contribution to each nonnative
axis line, with `c_*=10^9`. Native line loads are already bounded
by the graph degrees. All stages of a common reservoir retain the partial
matching or distinct-position rule across passes.
Reject a placement whenever its new contribution would exceed a cap.
Since a stage adds at most two cells to any line, such a rejected line
already has at least `c_*L-2>=c_*L/2` cells. The factor two in the
saturation counts below pays for this endpoint convention.

For vertical rectangles, each vertical line belongs to at most `64^2`
edge-pair types; its load in this pass is at most `64^2L`. Fix an `x`
or `y` coordinate. The planned total load in that coordinate plane is at
most a constant times `nL`. Consequently at most `O(n/c_*)` choices of
`z` have the relevant horizontal line saturated. There are four such
lines to check. Previously occupied cells exclude only `O(K2+P+g)=o(n)`
choices of `z` along the four vertical lines. The saturation exclusions
are at most `8*64^2 n/c_*<n/4`; a free `z` remains.

For a row-transfer edge in a fixed slice, choose its transverse `y`.
Its two native rows have only `O(K2+P+g)=o(n)` occupied cells. The
slice contains only `O(nL)` planned pair entries of this pass, so at most
`O(n/c_*)` transverse lines are saturated. For each of the two fixed
`x` values, the planned total across all slices is `O(nL)`; therefore
the cap on vertical lines excludes at most another `O(n/c_*)` choices
of `y`. Their total leading constant is at most `6*64`, so it is
strictly less than `n/4` with the stated `c_*`. Choose outside these
exclusions. Column passes are identical
with `x,y` transposed. This also controls their vertical load by `O(L)`.

For plane transfers, choose a position `(x,y)` simultaneously free in
its two prescribed `z`-planes. Each plane contains only `O(nK2+nP+ng)`
previously occupied cells, so these exclusions are `o(n^2)`. Within each
plane this pass has `O(nL)` planned entries; the horizontal line caps
exclude at most `O(n/c_*)` rows and columns in each plane. All vertical
lines together have `O(n^2L)` planned entries in this pass, so their
cap excludes at most `O(n^2/c_*)` positions. Finally the reservoir's
previous positions exclude `O(K0+P)=o(n)` rows and columns to maintain
its partial matching. With the stated `c_*`, the saturation exclusions
remove at most `(8*64+2*64)n^2/c_*<n^2/4` positions; the remaining set
has positive size eventually. The same argument covers the smaller plane-residue
pass with only one bundle per path edge.

These arguments are simultaneous induction on the placed stages. The
planned plane totals bound saturated lines at every intermediate time;
they do not depend on earlier placements being uniform. Earlier-pass
occupancy is bounded by the already established axis-line caps. The
separate prefix pass therefore gives `O(P)` prefix entries on **every**
axis line, while all macro and residue passes give `O(K2)` and `O(g)`
entries respectively. In particular no line contains a concentrated
`Theta(K_t)` collection of uncontrolled prefix values.

## 5. Residues: every compatible odd pattern is reachable

Put `h=g/2`. Reserve the following additional gadgets, all with fresh
entries, at most `O(n^2g)` in total and `O(g)` on any line by the
placement argument. Their lower endpoints are in class `-1 mod g`, their
upper endpoints in class `+1 mod g`, so their differences are `2 mod g`.
Use arbitrary fixed reference orientations at this stage. When `g=2`
there are no residue gadgets and every odd target is already compatible
with the baseline modulo `g`.

First use a spanning path on the `z`-planes, with `h-1` ordinary pairs
per edge, geometrically placed like the level-0 controls. Any even
plane-total correction vector of total zero modulo `g` is realizable:
divide by two modulo `h`, take prefix sums along the path to obtain its
edge flows modulo `h`, and choose their representatives in `[0,h-1]`.
Selecting that many pairs realizes each flow. This preserves every `C`.

After this step the two horizontal target lists in every `z`-plane
have the correct plane total modulo `g`. Use separate row and column
paths in each slice, with `h-1` pairs per edge, to set all `A` and `B`
residues. Each correction is even, and each list has total zero modulo
`g`, so the same prefix-sum proof applies. Row and column paths preserve
one another's sums exactly, and they preserve all plane totals.

The remaining desired change to `C`, divided by two modulo `h`, is an
`n` by `n` matrix with zero row and column sums modulo `h`. This follows
from the target compatibility equations and the now correct `A,B` residues.
Let `B_path` be the incidence matrix of the path `1,...,n`. Double prefix
sums give a coefficient matrix `Q` over `Z/hZ` with

`E=B_path Q B_path^t`.

Choose every coefficient in `[0,h-1]`. On each pair of path edges reserve
`h-1` checkerboard rectangles with equal actual gaps `2 mod g`, supplied
by Section 2.3. Selecting the required number realizes `2E mod g`,
while preserving all `A` and `B` sums exactly. Each vertical line meets
at most four edge-pair types, hence `O(g)` such entries.

Every line's actual numerical change during all residue steps is at most
`O(gX)`. This cost is paid; the procedure does not assume that a baseline
line is automatically coprime to `g`. Small primes dividing `g` remain
in the full pool and will be placed with the remaining entries.

## 6. Centering an actual baseline permutation

After selecting and embedding all main gadgets, set each reservoir at one
of its two complementary midpoint subsets from Section 2.3. Choose these
two possibilities independently with probability one half. Keep all residue
gadgets at their fixed reference orientations for now.

The expectation of each macro cell is the midpoint of its prime pair,
within `delta X` of `m`. A prefix or residue cell contributes an error
at most `X`. Thus every required axis line `L`, with reserved-cell count
`r_L`, satisfies

`|E C_L-r_L m|=O(delta K2 X+P X+gX)`.

The contribution of one reservoir to a line changes by at most `X` between
its two random choices. This assertion uses the physical geometry:

- a horizontal line meets at most one cell of a plane reservoir; a vertical
  line either misses it or receives a pair whose sum is fixed;
- a native slice-control line receives a whole midpoint bundle, whose two
  totals differ by at most `g`; a transverse horizontal line has fixed
  pair sums; a vertical line meets at most one cell;
- a native vertical line receives a whole midpoint checkerboard bundle,
  whose two totals differ by at most `g`; horizontal lines have fixed
  rectangle sums.

There are at most `O(K2+P)` relevant reservoirs on a line, by the cell
caps. A bounded-independent-variable inequality and a union bound over
`3n^2` lines therefore give an orientation with simultaneous error

`|C_L-r_Lm| <= E`,

`E=O(delta K2X+PX+gX+X sqrt(K2 log n))`.

No line-independence assumption is used; the independent objects are whole
reservoir orientation choices. Both choices retain the same later signed
control capacity.

Let `M0` unused primes remain and let `m0` be their mean. Since the
reserved cells are `O(n^2K2)=o(n^3)`, eventually `M0>=n^3/2`.
Sum the last deviation bound over one partition into `n^2` axis lines;
the fixed pool total gives

`|m0-m|<=2E/n`.

Uniformly permute the unused primes into the unused cells. Each line's
expected completed sum differs from `mu` by at most `3E`. Sampling
without replacement has the bounded-increment estimate

`Pr(|S_L-E S_L|>u)<=2 exp(-u^2/(2nX^2))`.

With `u=4X sqrt(n log n)`, a union bound over `3n^2` lines is below
one eventually. Choose such a completion. All entries have now been used
exactly once. Its line errors are

`O(delta K2X+PX+gX+X sqrt(K2 log n)+X sqrt(n log n))=o(K0X)`.

For any desired compatible odd target triple, run the separate residue
controls in Section 5. Their `O(gX)` cost preserves this `o(K0X)`
bound and makes every line congruent to its target modulo `g`. The main
controllers are untouched because their supports are disjoint.

## 7. Triangular exact correction and capacities

We now prove U3. After centering and residue repair, every line differs
from its target by at most `(1+o(1))K0X`, on the `g`-grid.

**Step 0: correct all `z`-plane totals.** Their demands have total zero
and each has magnitude at most `(1+o(1))nK0X`. Each graph edge has `n`
disjoint complete reservoirs and signed capacity at least `3nK0X`.
Rescale by `g` and apply the integral cut-flow lemma. An edge flow can
be split among its `n` reservoirs because the sum of integer grid intervals
is the full interval with the summed endpoint. All plane totals become
exact. Every `C` is unchanged. Every `A,B` line is altered by at most
`O(K0X)`, since it contains only `O(K0+P)` level-0 cells. Its remaining
target error is therefore `O(K0X)`.

**Step 1: correct all horizontal axis lines.** Within each `z`-slice,
each directional target list now has the correct exact plane total.
The differences in both lists are multiples of `g` with total zero.
Use its row and column graph reservoirs. Their per-edge capacity is at
least `3K1X`, and `K0=o(K1)`, so the integral cut-flow condition holds
eventually, including all the fixed occupancy constants. Row corrections
preserve columns, and column corrections preserve rows. Every `A,B`
line is now exactly at its target. A vertical line has only `O(K1+P)`
cells in this level, so its target error is `O(K1X)`.

**Step 2: correct the vertical tensor.** Let `D_(x,y)=C'_(x,y)-C_(x,y)`.
All entries are multiples of `g`, and every row and column sum is zero
**as an integer**: the other two directional tensors are already correct,
and both the current cube and the target satisfy the exact plane margins.

Apply the
[tensor-expander coefficient theorem](incidence.md#tensor-expander-coefficient-theorem)
to `D/g`. With the present graph, it supplies an integer matrix `F`
indexed by graph-edge pairs satisfying

`B_G F B_G^t=D/g`,

`||F||_infinity <= (5log n+5)^2 ||D/g||_infinity + 1/2 +512n^2`.

Multiplication by `g` gives scalar demands at most

`O(K1X log^2 n)+O(gn^2)=o(K2X)`.

The first term fits by `K1 log^2 n=o(K2)`. The second fits because
`g=O(log X)`, `X~3n^3log n`, so `gn^2/(K2X)->0`.
Every level-2 rectangle reservoir has capacity at least `3K2X`; choose
the corresponding subset for scalar change `gF_(e,f)`. Their physical
checkerboard effects are exactly `gB_G F B_G^t=D`. All `A,B` lines
are preserved, and all `C` lines reach their targets.

Every operation is a swap or the displayed two-swap checkerboard on
disjoint original entries. No scalar lifting is mistaken for a permutation:
the tensor-flow coefficients are consumed by the already packed equal-gap
rectangle reservoirs, with both signs, grid exactness, and their capacities
explicitly checked. This completes the proof of U3. QED.

## 8. Consequence and exact remaining boundary

Combine U3 with [Corollary CT](cube_targets.md#compatible-axis-targets-for-every-fixed-dimension)
at `D=3`. The compatible prime targets have grand total exactly `T` and
distance at most `mu^(3/5)=o(X)` from the natural mean, hence lie inside
U3's target box. They are odd since their size tends to infinity. Therefore:

**Theorem PC3.** For every sufficiently large odd `n`, the first `n^3`
odd primes admit a bijective placement in `[n]^3` with all `3n^2`
axis-parallel full line sums prime. Repeated line sums are allowed.

This is an asymptotic conventional proof. Its prime-count threshold is
ineffective in this presentation; no explicit numerical cube threshold is
claimed. It does not cover the extra `6n+4` signed-coordinate lines, any
square-section primality constraints, or growing dimension. Those additions
need new controller and/or compatible-target work. The proof's capacity
schedule has specifically been checked in dimension three.

## 9. Finite physical controls and their boundary

Run

```sh
python3 -B problems/prime-arrays-beyond-square/code/cube_controller_controls.py
```

The source selects disjoint gap-6 pairs from exactly the first `n^3` odd
primes for `n=5,7,9`, embeds every path-edge-product checkerboard by four
transverse colors, and fills all other cells with the unused prescribed
primes. Its independent sum loops and matrix-product calculation check
60 different selected-switch patterns: both horizontal directional tensors
stay fixed and the vertical change is exactly `6 B F B^t`. A separate
27-entry exact-pool fixture checks a centered two-stage rectangle reservoir
with all three signed changes `-6,0,6`. The producer uses a sieve; the
main fixture verifier regenerates the entry pools by trial division.

These are actual permutation controls on the stated prime pools, not just
signed integer lifts. Their baseline line sums are not asserted prime.
They test the physical consumer, the two signs, and exact-pool preservation;
they do not implement the asymptotic three-level construction or verify
the analytic supply on an infinite tail. A full finite controller certificate
can be emitted with `--certificate --n 5`.
