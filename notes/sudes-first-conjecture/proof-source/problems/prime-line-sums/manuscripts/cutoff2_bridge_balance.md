# Balance preselected bridge stages through shared double blocks

Author: `/root/controller_redesign`. This additive finite component preserves
all frozen predecessors. It requires independent nonauthor review at its exact
scientific revision. It establishes no numerical square cutoff and imports no
new analytic prime-distribution theorem.

Dependencies are the bridge windows and shared-radius argument in
[BR](cutoff2_controller_bridge.md), the replicated positions and exact
unused-pool mean identity in [PB](cutoff2_prefix_balance_experiment.md),
the block concentration argument in [SQ](cutoff2_seed_quality_experiment.md),
and its application to variable-gap stages in
[WB](cutoff2_wide_balance_experiment.md). The actual pool is exactly the first
n^2 odd primes; all positions and values remain disjoint.

## BB1. Select a single population for every bridge stage

Let n be odd, d positive and even, Q=d(n+8), and let J>=1 bridge stages
have radii 0<r_j<=1/2. Fix 0<epsilon<=1/4. Their half-open windows are

    A_j=((1/2-r_j/2)X,(1/2-r_j/2+epsilon r_j)X],
    C_j=((1/2+r_j/2-epsilon r_j)X,(1/2+r_j/2)X].       (BB1)

Use any one permitted reduced class modulo the selected even gap g in
both windows. This may be the class supplied by CS to avoid the seed
class. Retain every previous analytic count, interval endpoint, overlap,
residue intersection and rounding condition.

Assume the existing local budget guarantees, after every allowed earlier
deletion, enough remaining lower and upper values that their product is
greater than the number of possible positive g-multiple differences below X.
Then some positive difference occurs twice. The two pairs have four distinct
endpoints: the lower and upper windows are disjoint, and a fixed difference
and either endpoint determine the other endpoint.

At EACH stage choose Q/2 such double blocks sequentially. Each time delete
the four selected entries before selecting the next block. This is covered
by exactly the original final budget: Q pairs, Q lower entries and Q upper
entries per stage. Ordinary pairs are now selected in blocks too, rather
than discarding one pair from a witnessed block. Every actual retained
entry is still counted. No supply is assumed independent of another window
or residue class. In particular the same overlap graph and every local
side-deletion budget must be used.

For either pair (p,q) in any block,

    (1-2epsilon)r_j X <= q-p <= r_j X,
    |(p+q)/2-X/2| <= epsilon r_j X/2.                (BB2)

The two pairs in one block have the same positive difference, divisible
by g. Different blocks may have different differences.

## BB2. Assignment, both diagonals, and grid coverage

Retain PB's cell positions, with its 2d rectangles on EACH main diagonal
per stage. Pair the dn ordinary pair slots arbitrarily into dn/2 fixed
slot blocks. Every diagonal rectangle is already one two-slot block.
There are Q/2 slot blocks in total. Assign selected blocks bijectively to
them, and permit the two whole pairs within a block to exchange slots.

Each diagonal rectangle remains an equal-gap trade, fixing every row and
column and the other main diagonal. All positions and entry values remain
disjoint. The two ordinary pair slots within a block need not represent
the same controller edge; each receives its own valid g-multiple difference.

Suppose the ordinary complete g-grids have coverage at least r_j X before
stage j, and both diagonal grids have coverage at least 2d r_j X. Every
new ordinary difference is at most r_j X and at least
(1-2epsilon)r_j X. Its appending therefore preserves a complete g-grid
and raises coverage by at least that lower bound. Each diagonal appends
2d rectangle differences, each at most r_j X, so it remains complete and
its coverage grows by at least 2d times the same guaranteed lower bound.

Thus any original radius schedule satisfying its shared lower-radius
induction remains valid. For example r_{j+1}=(2-2epsilon)r_j before the
terminal stages works exactly as before. Enough terminal r=1/2 stages
raise ordinary coverage to at least X and diagonal coverage to at least
2dX. This proof compares guaranteed lower bounds; it does not compare a
diagonal's independently chosen gap with another block's actual gap.
No selected bridge is released. The reservation is still exactly

                         B_b=2QJ.                       (BB3)

## BB3. Simultaneous midpoint allocation

Select all blocks first. Independently at each stage, uniformly permute
its blocks among the fixed slot blocks and uniformly choose each internal
pair swap. Every pair slot is consequently uniform among all Q selected
pairs at that stage. Write mu_j for their actual mean midpoint.
Both ordinary and diagonal slots use this SAME population and mean.

All stage midpoints lie in an interval of width
C_j=epsilon r_j X<=epsilon X/2. The SQ/WB block argument gives squared
conditional ranges at most

    C_j^2 sum_blocks [(w_1+w_2)^2+(w_1-w_2)^2]
                   =2 C_j^2 sum_slots w_s^2.

PB's positions give sum w_s^2<=3dJ+4 over all stages for an ordinary
line, and the smaller2dJ for a diagonal. The same conditional-range
Hoeffding inequality and union bound over2n+2 required lines therefore
give an assignment with every bridge midpoint contribution within

    u_b X,    u_b=(epsilon/2)sqrt((3dJ+4)log(8n+8))        (BB4)

of its own exact stage-mean reference. The success probability is at
least one half. This is a finite assignment existence argument; it is
not an assumption of random prime distribution. The other selected
families have disjoint entries and slots, so their successful allocations
can be fixed separately. No additional simultaneous probability budget
is needed.

## BB4. Cancellation against the actual unused-pool mean

Let r_0=2d(P_actual+J+J_w), let B_r be the actual residue-entry count,
and let r_L=r_0+q_L be a required line's reserved-cell count. Put

    N_0=n^2-r_0(n+8)-B_r,
    A_b=sum_j(mu_j-m),
    beta_b=|m/X-1/2|+epsilon/4.                          (BB5)

Then |A_b|<=J beta_b X. Its whole bridge family's deviation from
B_b m is2Q A_b, while the main stage contribution to each required
line is2d A_b. Every row and column meets at most one extra rectangle
over the complete joint family; its additional bridge midpoint charge
is at most2 beta_b X. A diagonal has no such extra charge.

For the completion reference about the actual unused-pool mean,

    2d A_b-(n-r_L)2Q A_b/N_0
      =2d A_b [(n+8)q_L-B_r-8n]/N_0.                    (BB6)

Let H satisfy |(n+8)q_L-B_r-8n|<=H for EVERY required line, and let
B>=r_0(n+8)+B_r with B<n^2. The entire bridge contribution is bounded by

    [u_b+2 beta_b+2d beta_b J H/(n^2-B)]X.               (BB7)

For the original BN/PB residues use H=B_r+8n with their original domain.
For a separately verified cyclic-residue layout one may use its own
proved H. This component does not silently change any residue count.
All separate residue, seed, growth, wide, completion, half-gap orientation,
target and flow errors remain charged. In particular the central-stock
mean enclosure still pays the full bridge deviation beta_b B_b X;
BB7 is a completed-line cancellation, not a smaller total reserved sum.

The difference between two bridge gaps does not enter BB6: that identity
concerns actual pair midpoints. The fixed pair orientations and the later
nearest attainable reservoir midpoint are treated as in PB/WB. No equality
of gaps between distinct blocks is assumed.

## BB5. Verification boundary

The certificate checks exact local side budgets with deliberately repeated
bridge windows and adverse preliminary deletions, sequential fresh actual-
prime double blocks, finite complete grids, and the original PB/RP slot
geometry. An actual first-n^2-odd-prime permutation verifies every pair
midpoint/half-gap identity, all required line references and both families
of diagonal trades. Independent finite block-permutation controls retain
the covariance and internal swaps. The exact mean identity is checked
with both signs and both old and cyclic coefficient hypotheses.

The complete required public source map is pinned. Missing, empty,
malformed, mismatched and extra maps, nonregular files and symlinked
ancestors are rejected, with physical source attacks on temporary copies.
The finite controls do not prove the imported concentration theorem or
any infinite numerical tail. The handwritten finite argument and its
independent conventional review remain separate from those controls.
