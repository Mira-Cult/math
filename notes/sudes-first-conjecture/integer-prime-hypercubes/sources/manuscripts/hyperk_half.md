**Public reading copy.** Presentation and links have been normalized. Historical status statements below belong to their source revisions; see the [current publication status](../../README.md#review-and-verification-status). The matching original bytes are in the [source archive](../../originals/manuscripts/hyperk_half.md).

# The half-coordinate signed-line family in every fixed dimension

Author: `/root/controller`. This is an additive strengthening of the
majority-coordinate controller UM(k), frozen at scientific source
`5692d37633ef4b509e8429cddf4ed762e7235d08`. Its
[controller source](hyperk_controller.md), code and inputs are unchanged.
All labels here are manuscript-local. This source is an author conventional
proof pending independent review; its author cannot independently review it.

## 1. Statement and exact missing families

Fix `k>=2`. For odd `n=2m+1`, use centered coordinates
`I={-m,...,m}` and the exact pool `P={p_2,...,p_(n^k+1)}`. Put
`X=max P`, `T=sum P`, and `mu=T/n^(k-1)`.

Let `Hhalf_k` contain every axis and every nonaxis full signed-coordinate
line whose varying set `A` satisfies `|A|>=ceil(k/2)`. Reversal of all
signs is identified. No shorter, shifted or arbitrary-slope line is added.

**Theorem UH(k), physical half-coordinate control.** For each fixed `k>=2`
there is a threshold such that, for every larger odd `n`, all odd integer
targets on `Hhalf_k` within `ceil(n^(3/5))X` of `mu` are realized by a
permutation of `P`, under these explicit integer conditions:

1. Axis targets satisfy their pairwise margin equations and every directional
   total is the same exact `T`.
2. For every nonaxis varying block `A` and every coordinate `j` outside it,
   summing its target tensor over `j` equals the corresponding signed-`A`
   aggregate of the coordinate-`j` axis targets.
3. If `k=2d` is even, each complementary partition `A|F` with `|A|=|F|=d`
   and each pair of normalized sign patterns has equal two partition sums.

At `k=2` the third item concerns only axes and adds nothing. If `k` is odd,
this is exactly UM(k), since `ceil(k/2)>k/2`. The new content is therefore
even `k=2d>=4`. It realizes every signed family of size at least `d` while
preserving the axes. The full signed-line target remains open in this
source for `k>=5`: the omitted sizes are

`2<=|A|<ceil(k/2)`.

**Corollary PH(k).** For every fixed `k>=2`, every sufficiently large odd
`n` admits a bijective placement of the exact first `n^k` odd primes whose
line sums are prime on `Hhalf_k`.

This follows from UH(k) and the separately proved target theorem KPT in
[hyperk_targets.md](hyperk_targets.md), whose vector satisfies every
two-block partition identity and lies within `mu^(3/5)=o(X)` of `mu`.
Repeated line sums are permitted. PH(k) is a genuine all-dimensions
intermediate theorem; it is not presented as the full endpoint in dimensions
at least five.

## 2. A bounded solver for zero margins and all body traces

The key new lemma generalizes MP4, the matrix solver in the frozen
[four-dimensional incidence source](hyper4_incidence.md), Section 3.1.
Only full-body traces of the inner tensor must vanish. Its other signed
contractions may be nonzero because they have size less than `d`, outside
the proved family in dimension `2d`.

Let `V=Z^I`, `W=ker(sum:V->Z)`, and fix `d>=2`. For a normalized sign
pattern `sigma=(1,sigma_2,...,sigma_d)`, define

`beta_sigma(M)=sum_(t in I) M(t,sigma_2 t,...,sigma_d t)`.

There are `s_d=2^(d-1)` traces. Write

`Bdy_d={M in W^(tensor d): beta_sigma(M)=0 for every sigma}`.

This is generally larger than the kernel of every signed contraction.
That distinction is necessary for the scope of the result.

Fix the inherited loopless graph `G` on `I`, maximum degree `Delta=64`
and expansion at least eight. For its oriented edge columns `B_e`, write

`R_e = B_(e1) tensor ... tensor B_(ed)`.

Every raw graph product has `2^d` distinct cells, coefficients `+1,-1`,
and zero axis margins. Every target cell belongs to at most `Delta^d`
raw products, including separately labeled parallel edges.

### 2.1 The complete integer coefficient bound

The general tensor-expander theorem in
[incidence.md](incidence.md), Section 3, states that for each integer
zero-margin `D` there are integer coefficients `c_e` such that

`D=sum_e c_e R_e`,

`|c_e| <= F_d(D):=(5log n+5)^d ||D||_infinity`
`                         +1/2+(Delta n)^d/2^(d+1)`.    (H1)

The dimension-dependent additive term is retained. The algebra below
modifies the generator collection, without multiplying its coefficient
bound by a power of `n`.

### 2.2 Unit body markers and their bounded allocation

For `d+1` different noncentral reflection orbits, choose positive labels
`a,b_1,...,b_d`. The generic selector

`Q_sigma = tensor_(i=1)^d (e_(sigma_i a)-e_(sigma_i b_i))` (H2)

has zero axis margins, native body trace one, and every other full-body
trace zero. This follows by direct substitution: the only common absolute
label among all its coordinate supports is `a`, and the only normalized
sign pattern reaching it is `sigma`. A proper signed contraction need not
vanish and is not asserted to do so.

Put

`J_d=2^d s_d`, `A_d=s_d Delta^d`,
`P_d=s_d(Delta^d+1)`, `Lambda_d=16(d+1)P_d`.

A raw product has total absolute trace
`sum_sigma |beta_sigma(R_e)|<=J_d`. Across all raw products that total is
at most `A_d n`: sum the bounded incidence `Delta^d` over the `n` cells
of each of the `s_d` bodies, counting the center separately for each sign.
Cancellation can only reduce the absolute trace. Thus there are at most
`A_d n` unit trace contributions in the entire graph-product family.

For each nonzero unit contribution, allocate a separate marker (H2) with
that trace sign. Its coefficient `epsilon_Q` is `+1` or `-1` according to
the contribution. Markers attached to one raw product use pairwise disjoint
noncentral orbit alphabets and avoid every orbit in that raw product.
Also allocate `n` dummy markers of each sign, with initial demand zero.
The total marker population is at most `P_d n`, and every sign population
`p_sigma` is at least `n`.

Here is a deterministic greedy existence argument with a dimension-only
load bound. Cap the use of any positive orbit label across all markers at
`Lambda_d`. Total planned label uses are at most `(d+1)P_d n`, so fewer
than `n/16` labels can be saturated. A marker's raw product and the earlier
markers attached to it forbid at most

`2d+(d+1)J_d`

additional orbits. Labels already chosen for this marker add only `d` more.
For all sufficiently large odd `n`, there are enough labels among
`(n-1)/2` positive orbits to choose its `d+1` labels. Dummy markers use the
same rule without raw-product restrictions.

Every target cell belongs to at most `Lambda_d` markers: if the cell is
in a marker, any of its nonzero coordinate orbits was used by that marker.
Markers contain no central coordinate. This counts canceled cells as well
as nonzero trace positions and does not assume that marker locations are
uniformly distributed.

### 2.3 Local projection and scalar marker demands

For each raw product set

`C_e = R_e - sum_(Q attached to e) epsilon_Q Q`.          (H3)

Every margin and every full-body trace of `C_e` is zero. Its at most
`J_d+1` checkerboard pieces have disjoint supports, so its nonzero entries
are exactly `+1` or `-1`. A contraction of magnitude two was split into
two separate unit markers; no entry of size two is silently treated as a
single paired prime switch.

Substitute (H3) into (H1). The remaining marker coefficient at an attached
marker is `mu_Q=epsilon_Q c_e`, and it is zero at a dummy marker. For each
sign,

`sum_(Q of that sign) mu_Q=beta_sigma(D)=0`.              (H4)

This is an exact scalar zero-sum equation. No tensor-valued flow on an
unknown signed-kernel module is being assumed.

### 2.4 Repairing marker-graph intersections

On each of the `p_sigma` markers take the same degree-64,
expansion-eight graph, whose existence holds for every sufficiently large
integer order, including even marker populations. A marker meets at most

`D_d^*=2^d Lambda_d`

other markers in a cell, by summing the marker cell-load bound over its
`2^d` cells. If an original graph edge has intersecting endpoint supports,
replace that labeled edge by a path of length two through a marker whose
support is disjoint from both endpoints. At most `2D_d^*+2` possible
middle vertices are excluded by support or identity.

Cap use of a middle vertex at 128. There are at most `32p_sigma`
replacements, so at most `p_sigma/4` vertices can be saturated. Since
`p_sigma>=n`, a permitted unsaturated middle vertex exists for every
replacement once `n>8D_d^*+8`. The resulting labeled multigraph has maximum
degree at most `64+2*128=320`. It still has expansion at least eight:
each original crossing edge has a crossing edge on its replacement path,
and the paths retain separate edge labels. Repeated geometric edges are
counted with their multiplicity.

Integral cut flow now routes (H4) with each edge coefficient at most
`ceil(F/8)`, where `F=max_e |c_e|`. Each edge yields a template

`Q_u-Q_v`.                                             (H5)

Its two supports are disjoint; it has zero margins and every body trace
zero. Adding these flow templates to the projected templates (H3)
reconstructs `D` exactly.

### 2.5 The resulting bounded physical template lemma

**Lemma BH(d).** For all sufficiently large odd orders, the fixed
collection (H3),(H5) consists of `O_d(n^d)` templates in `Bdy_d`. Each is
a sum of at most `J_d+1` pairwise cell-disjoint signed `d`-checkerboards,
has coefficients `+1,-1`, and each target cell belongs to at most

`B_d=Delta^d+321 Lambda_d`                              (H6)

templates. Every `D` in `Bdy_d` has an integer decomposition using them,
with projected coefficients bounded by (H1) and marker-flow coefficients
bounded by `ceil(F/8)`.

The cell-load bound follows from at most `Delta^d` raw products, at most
`Lambda_d` attached markers, and at most `320 Lambda_d` incident marker
edges through a target cell. Dummy markers are counted in the latter
bound. The total edge count is `O_d(n)`; the original raw family has at
most `(32n)^d` members. This proves all claims of BH(d).

For a physical error divisible by `g`, applying BH(d) to `D/g` gives
scalar coefficients bounded, for example, by

`(5log n+5)^d ||D||_infinity + 3g/2`
`                                  +g(Delta n)^d/2^(d+1)`. (H7)

The extra `g` pays the ceiling in the marker flow. All constants and
templates are fixed independently of the particular target `D`.

## 3. The corresponding residue solver

Keep the marker allocation. Replace the numeric graph-product coefficient
solver by the tensor product of a spanning-tree incidence basis of `G`.
For every modulus `h>=1`, this basis spans the zero-margin tensors over
`Z/hZ`, because a rooted tree incidence minor is unimodular. Equivalently,
use signed subtree sums successively in every tensor coordinate. These
are integral identities, not division by the number of labels. The tree
edges are a subset of the same graph-product and marker collection.

Apply the projection (H3), using coefficient representatives
`0,...,h-1`. If `D` has all body traces zero modulo `h`, the resulting
marker demand in each sign group has total zero modulo `h` by (H4).
Order that marker group arbitrarily and use its path prefix sums. Replace
an intersecting path edge by a two-edge route through a marker disjoint
from both endpoints. A middle-use cap four leaves fewer than `p_sigma/4`
saturated choices; the same forbidden-support bound proves existence for
the large-order threshold above. The routed path has maximum degree ten
and at most `2(p_sigma-1)` labeled edges.

Every resulting edge template is again (H5), with disjoint supports.
Its coefficients, as well as those of (H3), can be represented in
`0,...,h-1`. The residue collection has point load at most
`Delta^d+11 Lambda_d`, no more than (H6). Its templates can be kept
separate from the numeric collection without altering any constant-order
bound. This proves **Lemma BR(d)** over every composite residue ring.

For the actual prime controller use `h=g/2` and separate stages whose
actual common gap is `2 mod g`. Odd line targets and odd reference sums
have even discrepancy. Dividing that discrepancy by two, solving in
`Z/hZ`, and using nonnegative representatives therefore repairs the
residues. The physical drift of these stages must still be paid by the
packing caps below; matching a congruence is not itself a numerical bound.

## 4. Shared complementary traces before the half-family kernels

Now take `k=2d>=4`. The strict-majority source has already supplied the
axis stages and stages for every block of size greater than `d`. A new
stage must preserve all of them.

For an unordered complementary partition `A|F` into two `d`-blocks,
and signs `sigma,tau`, the two traces

`beta_tau(D_(A,sigma))` and `beta_sigma(D_(F,tau))`

are equal, by the corresponding two-block target identity and the same
identity for the actual array. This is true over the integers and over
the residue ring. There are exactly

`J_shared = binom(2d,d) 2^(2d-2)/2`

such identities; this is a fixed integer depending only on dimension.

Use a stage `Q_(A,sigma) tensor Q_(F,tau)`, with the two generic unit
selectors (H2) on disjoint noncentral orbit alphabets. The full signature
formula (SIG) in the frozen controller source gives exactly two nonzero
images among families of size at least `d`: `Q_(F,tau)` in native family
`(A,sigma)`, and `Q_(A,sigma)` in `(F,tau)`. It changes the selected
common trace by one on both sides and every other common trace by zero.
It preserves every axis and every larger varying family. Mixed directions
have no supporting vertex because the two orbit alphabets are disjoint.
Proper subsets of either block have size less than `d`; their sums are
outside the present theorem and their actual movement will still be bounded.

Give every common-trace identity `n` numeric scalar reservoirs. If the
current maximum half-family entry error is `E`, the trace error is at most
`nE`. Divide its integer grid coefficient into `n` summands, each of
physical magnitude at most `E+g`, by quotient and remainder. This does not
invert `n` modulo any modulus. Each reservoir's larger scalar capacity
corrects its part of the common trace. A residue repair needs only one
separate reservoir per common trace, with `g/2-1` stages, because one
residue representative suffices.

After this shared-trace pass, every native half-family residual tensor has
zero axis margins, all full-body traces zero, and every entry divisible by
`g`. Its numerical entries can have grown to the actual shared-pass load
bound `O_k(K_trace X)`; that larger error is retained for the next level.

## 5. Genuine compound prime swaps for the final half families

Fix a half-family `(A,sigma)` with complement `F`, and a template `M` from
BH(d) or BR(d) on `F`. Let the generic native selector `Q_(A,sigma)` use
orbits disjoint from every coordinate orbit in `supp M`. Then

`Q_(A,sigma) tensor M`                                 (H8)

has zero images on all axes, every family of size greater than `d`, and
every other family of size exactly `d`. Its native image is exactly `M`.
Indeed a mixed line misses its support; a full complementary `F` line has
zero contraction by the body-trace condition on `M`; a full `A` contraction
is the selected unit trace; and proper contractions have size less than `d`.
This is the complete preservation contract needed for the proven family.

The template `M` has at most `(J_d+1)2^d` nonzero entries, all `+1,-1`.
For each such inner cell, pair the outer selector vertices along one of
its coordinates. This uses `2^(d-1)` disjoint prime pairs per inner cell,
with their lower/upper orientations determined by the product sign.
All pairs within this stage have one actual common positive difference.
Swapping them realizes that difference times (H8) at every cell. The
number of pairs is at most

`M_half(k)=(J_d+1)2^(2d-1)=(J_d+1)2^(k-1)`.             (H9)

This is finite for each fixed dimension. No cell sees two overlapping
checkerboard pieces, no prime endpoint is reused, and no pair of gap twice
the common gap is requested. Stage gaps may vary between stages; the common
gap requirement applies to pairs within one stage.

Each native line sees a coefficient in `0,+1,-1` times the entire scalar
reservoir. Its two central values differ by at most `g`. Every nonnative
line that can meet the reservoir fixes at least one fresh selector
coordinate, and hence meets at most one stage. Such a line meets at most
`2(J_d+1)` cells of that compound stage. The whole-reservoir range is
therefore `O_k(X)` on every full signed line, including omitted families.
It is not assumed to be the two-cell bound for a single hypercuboid.

## 6. Disjoint support placement and numerical loads

The global placement order is: shared-trace stages, final half-family
templates, strict-majority stages, then axis stages. Prefix, macro, sign,
native-family and residue passes have separate caps. There are only
finitely many such passes at fixed `k`.

### 6.1 Shared traces

There are `J_shared n=O_k(n)` numeric reservoirs, each with at most
`L=o(n)` stages in a pass. A stage has `2^k` cells and all its coordinate
labels are free. Require all its `2(d+1)` selector orbits to be distinct,
and fresh across its complete reservoir. The total planned line incidences
in this pass are at most

`2^k ((3^k-1)/2) J_shared nL`.

With a cap `H L`, only `O_k(n/H)` lines can be saturated. Every potential
line key contains a free variable unless its varying set is all `[k]`;
the latter full bodies are avoided by separation of the two selector
alphabets. Test a key when its last free variable is assigned. Its label
depends injectively on that variable. There are only `O_k(1)` potential
support-vertex/direction tests, so a sufficiently large fixed `H` removes
fewer than `n/8` candidates at any free-label step.

For an occupied vertex, varying its last free variable follows a full signed
line. Previous pass caps give `o(n)` occupied cells on that line. Freshness
within a reservoir also costs `o(n)` labels, and the finitely many generic
conditions cost `O_k(1)`. Thus every free-label choice exists eventually.
No support is committed before all deferred tests are complete. The final
allowance `2^k` per potential key pays coincident vertex tests.

Every full signed line meets a given whole shared-trace reservoir in at
most one stage, because all its fixed coordinates use fresh labels, and
all full-body lines are avoided. Its reference contribution range is at
most `2X`. The actual total drift on any line is `O_k(LX)` by the cap.

### 6.2 Final half-family templates

Apply the selector-times-footprint packing lemma in the frozen
[controller source](hyperk_controller.md), Section 8.2, with

`r=d`, `B=B_d`, `s=(J_d+1)2^d`.

Its proof uses only a bounded native point load, the finite support size,
and orbit separation; it does not require `r>d`. Lines varying inside the
selector block have direct load at most `2^d B_d L` above each native
cell. For a potential line in the complementary block, the union over
selector placements projects to its `n` native points and has planned
load at most `2^d B_d nL`. That local bound yields `O_k(n/H)` saturated
keys in each deferred free-label test. Mixed lines are absent. The occupied
cell and freshness exclusions are `o(n)` as in the preceding subsection.
Consequently all half-family supports are disjoint and have per-pass full
signed-line occupancy `O_k(L)`.

The same proof places the old strict-majority stages around these new
reserves. Their existing signatures and capacities are unchanged. Their
total axis occupancy remains `o(n)`, which is exactly the hypothesis of
AP(k) for placing all axis stages last. There is no dependence on an
unproved uniform distribution of occupied cells, or on a global-volume
estimate standing in for a slice estimate.

## 7. One complete resource and correction order

For even `k>=4`, the new construction has the old `2k-3` axis levels,
`k/2` strict-majority levels, one shared-trace level, and one final
half-family level. Thus the largest level index is

`D_half=(5k/2)-2`.

Use the common ladder

`K_j=ceil(n^(3/5+3j/[20(D_half+1)]))`, `delta=n^(-1/5)`.

For odd `k`, use the already proved majority depth; `k=2` also uses its
previous construction. Every consecutive gap is positive, and the final
exponent stays below `3/4`. These are formulas for every fixed dimension,
not finitely many exponents reused past their range.

For each native half-family, BH(d) has `O_k(n^d)` templates. There are
`binom(2d,d)2^(d-1)` such families, a fixed dimension constant. The two
new levels therefore reserve

`O_k(n(P+K_trace)+n^d(P+g+K_final))` entries.             (H10)

The constant includes (H9), every marker edge and every sign. The existing
axis invoice is `O_k(n^(k-1)K_final)`, which dominates (H10), since
`d<=k-2`. The shared-trace residue invoice is `O_k(g)` and the final
residue invoice `O_k(n^d g)`. All seed endpoints are selected before other
prime allocations, and every selected endpoint, including dormant choices,
is charged to the common worst-case deletion allowance.

The general resource lemmas in
[hyperk_resources.md](hyperk_resources.md) apply with the actual finite
tuple bound (H9), the enlarged packing constants, and depth `D_half`.
They supply complete signed scalar intervals, growing-gap seeds, fresh
macro and residue tuples after concentrated deletion, and whole-reservoir
centering. Their inequalities have unchanged power margins:

* the full reserve is `o(n^k)` and is
  `o(delta X/(g log X))` even under concentrated deletion;
* every full signed line has `o(n)` occupancy, `O_k(P+g)` uncontrolled
  entries and `O_k(K_final)` macro entries;
* macro midpoint bias `delta K_final X` and whole-reservoir fluctuation
  `O_k(X sqrt(K_final log n))` are `o(K_0X)`;
* the unused pool's changed mean and its without-replacement completion
  error are paid, giving a genuine exact-pool baseline with all signed
  line sums `mu+o(K_0X)`.

The complete switching order is:

1. Repair axis residues, then strict-majority residues, then shared
   complementary traces modulo `g`, then every half-family residue using
   BR(d). Each pass preserves the previously repaired required data; the
   actual total line drift is `O_k(gX)`. Main reservoirs remain central.
2. Run the main axis levels, preserving all repaired residues. Run the
   strict-majority levels in decreasing varying-set size. Their earlier
   preservation and per-line drift contracts apply verbatim.
3. Let `E=O_k(K_previous X)` bound half-family errors. Every common trace
   has size at most `nE`. Split it into the `n` reserved scalar intervals,
   each part at most `E+g=o(K_trace X)`, and correct all shared traces.
   The resulting native entry error is `O_k(K_trace X)` by the actual cap.
4. Apply BH(d) to each remaining native tensor divided by `g`. Bound (H7)
   is `O_k(K_trace X log^d n)+O_k(g n^d)=o(K_final X)`.
   Every coefficient therefore fits its complete scalar interval. Use the
   compound genuine paired-prime stages (H8). Each changes only its own
   native half-family among the required lines, and preserves all axes.

At the end every required sum equals its target and every pool prime occurs
once. All thresholds depend only on fixed `k`, finite graph and marker
constants, the prime-distribution input, and finitely many strict resource
inequalities. Each condition holds for all larger odd orders. Taking their
maximum proves UH(k), and KPT gives PH(k). No evaluated cutoff or growing
dimension regime is asserted.

## 8. Why this stops at the stated family

At equality `k=2d`, a native `d`-block's only complementary required block
is its entire `d`-coordinate complement. The shared obstructions are scalar
body traces, and the marker residuals (H4) are scalar zero-sum demands.
That is why ordinary bounded-degree flow closes the proof.

For a smaller native block, the complement contains required proper signed
subblocks. Their contractions are tensors with free coordinates, and a
marker difference can cause additional mixed or complementary effects.
BH(d) does not kill those contractions. The all-body trace kernel `Bdy_d`
must not be silently replaced by the full signed-contraction kernel `K_d`.
The latter bounded coefficient, bounded physical support and marker-routing
problem remains the missing step of the full endpoint.

The independent signature controls include a zero-margin, zero-body-trace
rank-three footprint with a nonzero pair contraction. Tensoring it with an
outer selector shows exactly why the last pure-half stage cannot be reused
to claim all lower signed families. This is an obstruction to that shortcut,
not a disproof of the user's eventual-existence conjecture.

## 9. Reproducible controls and provenance

The separate [hyperk_half.py](../../originals/code/hyperk_half.py) implements dimension-
parameterized markers, projection, routed disjoint-marker paths, exact body
traces, compound physical prime switches and complete signed-line signatures.
Its deterministic fixtures use path graphs to check integer identities and
residue routing; they do not certify the asymptotic expander coefficient
bound from a path. The latter is the conventional graph argument above.

Run from the repository root:

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyperk_half.py
```

Finite controls, source hashes, independent review and remote CI are recorded
separately by the workspace owner. The frozen majority checkpoint is not
edited by this addition. Actual partial prime trades remain distinguished
from full arrangements. No complete new higher-dimensional prime arrangement
certificate is claimed by the template tests.
