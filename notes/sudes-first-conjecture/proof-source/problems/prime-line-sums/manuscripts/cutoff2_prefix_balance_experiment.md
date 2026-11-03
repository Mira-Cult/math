# Shared prefix stages and balanced placement

*Presentation copy: mathematical delimiters and equation labels are adapted for GitHub rendering. The unchanged, hash-bound source is in the [complete replay packet](../../../../packet/README.md).*


Author: `/root/prefix_balance_research`, with the balanced permutation-layer
placement identified independently and jointly checked with `/root`.
The derangement conditioning gate in section 2 was suggested by
`/root/controller_redesign`. This is an additive research manuscript.

**Status.** The finite implications below have conventional proofs under
their displayed supply and numerical hypotheses. They have not received
independent nonauthor review and do not by themselves give a square cutoff.
In particular, simultaneous same-gap copies require the stronger batch
inequality below. Ordinary double-pair supply cannot be silently reused.
No permanent claim IDs, public note, or previously frozen file is changed.

The source architecture is the target-first controller at scientific
revision `125543e2b6fe9f2b25225e121ba9897bc097151d`,
[C1--C18](cutoff2_controller_redesign.md), together with
[FC](explicit_controller.md) and
[RBC](cutoff_reflected_bins_controller.md). The definitions of the exact
input pool and line family remain in [PROBLEM.md](../PROBLEM.md).
All logarithms below are natural.

## 1. What sharing means

Use two degree-`d` networks, where `d=2r`. Each is the multigraph of `r`
derangements on the `n` vertices. Every vertex has degree exactly `d`;
parallel edges are retained. There are exactly `dn` ordinary reservoirs
across the two networks.

All ordinary reservoirs will have the **same list of prefix differences**.
Each prefix stage nevertheless uses a different pair of primes in every
reservoir. At every stage, each diagonal uses `2d` equal-gap rectangles,
each requiring two further disjoint prime pairs. Thus the number of prime
pair slots per prefix stage is


```math
Q=d(n+8).                       \qquad\text{(PB1)}
```


There is no reuse of a prime or cell. The only shared data are a difference
value and its place in the common complete sequence.

Let `P_0<=P` be the actual common prefix length. Optionally append `J_b`
preselected bridge stages to each ordinary reservoir, and append exactly
`7K` wide stages. For each of these later stages, each diagonal again uses
`2d` rectangles. Their differences need not agree across reservoirs or
copies. Bridge stages are required to preserve and extend the complete
grid as in their separate construction; wide stages have differences in
`[(1/2-2w)X,(1/2+2w)X]`, with `7(1/2-2w)>=2`.
Before the wide stages, ordinary coverage must be at least `X` and
diagonal coverage at least `2dX`. For the geometric bridge construction,
each stage has a common radius envelope `R_i`, its gaps lie in
`[R_i/2,R_i]`, and the next radius is `3R_i/2`. If ordinary coverage
before a stage is at least `R_i`, it is at least `3R_i/2` afterwards;
if diagonal coverage is at least `2dR_i`, its `2d` copies increase it
by at least `dR_i`. Thus the amplified bridge induction is valid even
though the selected gaps differ. The two terminal `R_i=X/2` stages
likewise take ordinary coverage from at least `X/2` to at least `X`,
and diagonal coverage from at least `dX` to at least `2dX`.

The amplification of **all** main stages on each diagonal is material.
Ordinary controls avoid both diagonals. Merely balancing the ordinary
prefixes leaves an `O(dP)` unused-pool mean shift on those diagonals.
The replication makes every required line have the same main-cell count,
apart from at most two extra rectangle cells on a row or column.

## 2. Derangements with the required cuts

Require explicitly `0<kappa<d/2`, as in the inherited graph theorem.
In particular `a=kappa/d<1/2`; the entropy endpoint argument below
uses this hypothesis. The numerical conditions (PB2) alone do not
replace it.

The graph proof in the frozen target-first controller gives, for
`a=kappa/d`, `b_*=r-kappa/2-1>0`, a small-set failure bound


```math
\{\exp(1+rH(a))(s/n)^{b_*}\}^{s},
```


and the large-set entropy function `F(t)` with its endpoint-maximum
property. These calculations apply to independent uniform permutations,
before any conditioning. Put `t_0=1/256` and require


```math
\begin{split}
 1+rH(a)+b_*\log t_0+r\log3&\lt \log(1/8),\\
 F(t_0),F(1/2)&\lt -1/1000.                         \qquad\text{(PB2)}
\end{split}
```


The probability that any small set has a bad cut is then less than
`3^{-r}/7`. The probability for all larger sets is at most
`(2n)^d exp(-n/1000)`. Since `3^r<2^d`, it is less than
`3^{-r}/8` whenever


```math
(4n)^d\exp(-n/1000)\lt 1/8.           \qquad\text{(PB3)}
```


For `d<=512` and `n>=2^24`, (PB3) holds: at the endpoint,
`2^24/1000>26*512+3`, `log2<1`, and `exp(1)>2`; thereafter its
logarithmic derivative `d/n-1/1000` is negative.

For every `n>=2`, the fraction of permutations that are derangements is
at least `1/3`. This follows from the alternating inclusion-exclusion sum
`sum_(j=0)^n (-1)^j/j!`: its odd partial sums from the third term onward
are at least `1-1+1/2-1/6=1/3`, and its even partial sums are larger.
Thus the event that all `r` permutations are derangements has probability
at least `3^{-r}`. The total bad-cut probability is strictly smaller.
Their difference is positive, proving existence of derangements whose
multigraph has


```math
|\partial S|\ge\kappa\min(|S|,n-|S|).
                                                               \qquad\text{(PB4)}
```


This is an existence proof on the full integer tail. It does not assume
that conditioning preserves the original cut probabilities.

## 3. Enough distinct copies of one difference

Here is a general batch form of the prefix counting lemma. Suppose the
currently unused set contains at least `M` primes in one class modulo `g`
and in an interval of length `cX`. Suppose


```math
\frac{\sigma X}{M}\le R\le\frac XL,\qquad
 c,\sigma,L\gt 0,
```


and choose


```math
0\lt \eta\lt \frac1{2(c+1/L)}-\frac1{2\sigma},\qquad
 \epsilon=\frac1{2(c+1/L)}-\frac1{2\sigma}-\eta\gt 0.
                                                               \qquad\text{(PB5)}
```


Divide that interval into `ceil(cX/R)` half-open bins of length at most
`R`. The number of bins is at most `(c+1/L)X/R`. Cauchy--Schwarz
therefore gives at least


```math
\left\{\frac1{2(c+1/L)}-\frac1{2\sigma}\right\}
             \frac{M^2R}{X}
```


within-bin unordered pairs. Fewer than `eta M^2R/X` pairs have positive
difference below `eta gMR/X`: for a fixed lower endpoint, the number of
positive permitted steps is strictly less than `eta MR/X`.
There are at most `R/g` remaining differences. Consequently one positive
`g`-multiple `h` with


```math
\eta gMR/X\le h\le R             \qquad\text{(PB6)}
```


occurs on more than `epsilon M^2g/X` edges. A fixed-positive-difference
graph is a disjoint union of paths, and a matching contains at least half
its edges. In particular the sufficient condition


```math
\epsilon M^2g\ge2QX             \qquad\text{(PB7)}
```


provides `Q` vertex-disjoint copies of this same difference. This is the
extra cost of sharing one complete sequence across all reservoirs.

Starting with `s=ceil(sigma X/(gM))` seed stages, each using `Q`
disjoint gap-`g` pairs, gives initial complete coverage `sg`. Appending
each batch preserves the complete grid in every ordinary reservoir. A
diagonal has `2d` repetitions of each stage, hence complete grid coverage
through `2d` times the ordinary prefix radius. For subsequent bridges it
suffices that their stated gap bounds extend the ordinary complete grid;
the amplified diagonal grid can accommodate the same `2d` stage copies.

All seed pairs must survive earlier reservations. If the preselected
residue and bridge entries use at most `B_pre` primes, a vertex-disjoint
candidate seed matching of size at least `Qs+B_pre` suffices: at most
`B_pre` matching edges are hit. During the whole prefix phase, raw supply
must leave at least `M` unused class primes after deletion of
`B_pre+2QP` entries. These are explicit shared, adversarial deletion
budgets. No statistical independence among prime supplies is assumed.

Wide stages may be selected individually using RBC's unchanged
double-pair criterion and the new global reservation count below. They
do not need `Q` copies of a common wide difference.

## 4. Balanced placement by perfect matchings

Put `h=g/2`. The exact upper reservation count and the rectangle count are


```math
\begin{split}
 B_r&=4(n+1)(h-1),\\
 B_p&=2QP,\quad B_b=2QJ_b,\quad B_w=14QK,\\
 B&=B_r+B_p+B_b+B_w,\\
 J_{\rm rect}&=4d(P+J_b+7K)+2(h-1),\\
 L_{\rm cell}&=2d(P+J_b+7K)+6(h-1)+2.             \qquad\text{(PB8)}
\end{split}

Assume

\[
                 n\gt 4J_{\rm rect},\qquad n\gt 4L_{\rm cell}+8.
                                                               \qquad\text{(PB9)}
```


First place all main and residue rectangles jointly by FC's greedy
argument, with distinct rows and columns across all rectangles on both
diagonals. Every row and column meets at most one rectangle and hence
at most two rectangle cells. Ordinary controls will avoid both diagonals.
Place ordinary residue-path pairs by FC's two separate greedy passes.
They contribute at most `6(h-1)` cells on a row or column.

Now consider one permutation layer of one main stage of the row network.
Its edges are indexed by `i`, with endpoints `i,pi(i)`. Choose a bijection
`f` from these `n` edge indices to the `n` columns, and put the two cells
of edge `i` in column `f(i)`. For an edge, at most `2L_cell+4` columns
are forbidden by occupied endpoint cells or the two diagonals. Conversely,
for a fixed column, at most `2L_cell+4` edge indices are forbidden:
each occupied row is incident with at most two directed permutation edges,
and the two diagonal rows exclude at most four further edges.

Thus the allowed bipartite graph has minimum degree greater than `n/2`.
It has a perfect matching. For completeness, Hall's condition follows as
follows: a left subset of size at most `n/2` has more than `n/2`
neighbors; a subset of size greater than `n/2` has every right vertex
as a neighbor, because a right vertex cannot miss that many left vertices.

Every row receives exactly two cells in this layer, and every column
receives exactly two. They are distinct because `pi` is a derangement
and `f` is injective. Repeat for every layer and stage, transposing for
the column network. Previous occupied cells are explicitly forbidden, so
there is no overlap between passes. The final load is bounded by (PB8),
which justifies the forbidden-incidence bound during every partial pass.

Let `S=P_0+J_b+7K`. Every row and column has exactly `2dS` ordinary
main cells, plus zero or two rectangle cells. Each diagonal has exactly
`2dS` main designated cells, plus its `h-1` residue designated cells.
This is the count balance required below; an arbitrary greedy placement
with a maximum-load bound alone would not suffice.

## 5. Random allocation of the shared prefix copies

For prefix stage `t`, write `z_(t,j)` for the midpoint of its `j`th
prime pair, `1<=j<=Q`, and let `mu_t` be their mean. All prime pairs
have already been selected, disjointly. Allocate the `Q` pairs uniformly
at random to the `Q` prefix pair slots of stage `t`, independently for
different stages. This does not change the set of used primes, any
selected difference, or any reserved cell. Each diagonal rectangle still
contains two pairs of the same difference.

Put every complete main reservoir at its midpoint subset. A row's own
network then differs from the sum of its pair midpoints by at most `dg/2`;
a diagonal differs by at most `g/2`. These are the original complete-grid
identities. They hold for the entire prefix-plus-bridge-plus-wide list,
regardless of the allocation of pair midpoints. The perpendicular network
and rectangle row/column sums are exactly sums of pair midpoints.

For one row or column, each prefix stage has `d` ordinary pair slots of
weight one and `d/2` ordinary pair slots of weight two. At most one stage
has extra prefix-rectangle slots; their total weight is two and their
squared weights sum to at most four. A diagonal has `2d` slots of weight
one at every stage. Hence, for every required line, the sum of squared
weights over the prefix stages is at most


```math
3dP+4.                   \qquad\text{(PB10)}
```


All prefix midpoints lie in an interval of length at most `cX`, the
length of the prefix pool. For a weighted random permutation, expose the
positive-weight slots in decreasing order of weight. Its Doob difference
at a slot of weight `w_i` is


```math
\left(w_i-\frac{\text{remaining weight}}{\text{remaining slots}}\right)
 (Z_i-\text{previous remaining mean}).
```


The coefficient lies in `[0,w_i]`. Thus its conditional range length is
at most `w_i cX`. The conditional moment estimate proved in the frozen
controller gives the two-sided concentration bound


```math
\Pr(|Z-\mathbb EZ|\gt uX)
 \le2\exp\left(-\frac{2u^2}{c^2(3dP+4)}\right).
```


The union bound over all `2n+2` lines is at most one half for


```math
u_p=c\sqrt{(3dP+4)\log(8n+8)/2}.                \qquad\text{(PB11)}
```


Consequently some allocation satisfies this prefix-midpoint error on
every required line. This proof uses independent allocation permutations
after selection of the full disjoint prime set. It does not assume that
the earlier adaptive prime selections were independent.

## 6. Cancellation of the prefix mean shift

Suppose every prefix prime has distance at most `beta X` from `m`.
Write


```math
A=\sum_{t=1}^{P_0}(\mu_t-m),\qquad |A|\le\beta P X.
```


The total prefix deviation is exactly `2Q A`. A required line's expected
prefix midpoint deviation is `2d A`, with an additional contribution of
absolute value at most `2beta X` if it meets a prefix rectangle.

Use the actual number of reserved entries, denoted `B_actual<=B`, and let
`N_0=n^2-B_actual>0`. Put `r_0=2d(P_0+J_b+7K)`.
The actual global main count is `r_0(n+8)`. The reserved count on a line
is `r_0+q`, where `0<=q<=6(h-1)+2`; on a diagonal `q=h-1`.
Uniform completion by the unused primes adds the prefix mean correction
`-(n-r_0-q)2Q A/N_0`. Its sum with `2d A` is exactly


```math
\frac{2dA}{N_0}\{(n+8)q-B_r-8n\}.             \qquad\text{(PB12)}
```


For `n>=20` and `0<=q<=6(h-1)+2`,


```math
|(n+8)q-B_r-8n|\le B_r+8n.
```


Indeed the lower endpoint is `-(B_r+8n)`; at the upper endpoint the
needed comparison reduces to
`2h(n-20)+12n+24>=0`. It follows that the prefix contribution to the
expected completed line error is at most


```math
\left(2\beta+\frac{2d\beta P(B_r+8n)}{n^2-B}\right)X,
                                                               \qquad\text{(PB13)}
```


in addition to the random-allocation error (PB11). The `O(dP)` term
has disappeared from every required line, including both diagonals.

## 7. A complete centering invoice for composition

Assume every wide pair has midpoint within `delta X` of `m`, every
bridge pair has midpoint within `beta_b X` of `m`, and every residue
entry is within `gamma X` of `m`. The residue pair midpoints must still
be within `delta X` of `m`, as in FC/RBC. In the latter two assumptions,
pair midpoints refer separately to both pairs of a rectangle.

The same elementary concentration estimate for uniform completion gives


```math
u_c=\sqrt{n\log(8n+8)/2}.
```


After choosing the successful prefix allocation, some completion has all
line fluctuations at most `u_c X`. No independence between those two
existence choices is required. Finally impose the already chosen target
residues; their cost is at most `(g-2)X` on any required line.

The following one bound therefore suffices for all rows, columns, and
both diagonals:


```math
\begin{split}
 C_{\rm bal}={}&u_p+u_c+2\beta
    +\frac{2d\beta P(B_r+8n)}{n^2-B}+\frac{dg}{2X}+g-2\\
 &+\delta\left(14dK+2+\frac{n(B_w+B_r)}{n^2-B}\right)\\
 &+\beta_b\left(2dJ_b+2+\frac{nB_b}{n^2-B}\right)
   +\gamma\{6(h-1)+2\}.                         \qquad\text{(PB14)}
\end{split}
```


Here the two harmless `+2` bounds may both be paid even though a line
meets at most one rectangle. The formula separately accounts for prefix
mean, prefix fluctuation, completion fluctuation, bridge and wide means,
residue means, midpoint rounding, and the final residue repairs.

If `C_bal<c_0K`, the usual row and column target box condition
`c_0+D/(KX)<(999/1000)kappa`, and `KX>=1000g` hold, the integral
flow proof applies unchanged. Each diagonal's total difference is at least
`4dKX`; its symmetric range contains the same target box since
`kappa<d/2`. All swaps remain on disjoint reserved cells and use exactly
the original prime pool once each.

## 8. Net benefit and obligations still requiring a numerical certificate

The bound replaces a deterministic prefix term of order `dP` by one of
order `sqrt(dP log n)`, while also reducing the fixed wide midpoint load
from `21dK` to `14dK`. It increases the two diagonal families from a
constant number of reservoir copies to `2d` copies. This costs only
`O(d(P+K))` additional entries but changes the joint rectangle gate to
`C>112d` approximately when `K=floor(n/C)`.

This does **not** remove the global class invoice for `2dnP` prefix
entries. Once centering is reduced, that depletion and the supply of
initial matching seeds can become active. The batch condition (PB7) can
also bind when a growth rate is chosen extremely close to its counting
limit: the residual coefficient `epsilon` then becomes very small.
All three must be optimized together. The logarithmic gain in `X/n^2`
is essential in the batch condition; replacing `X` by `n^2` there can
discard the expected benefit.

For analytic bridges, only the growth stages need a common difference.
The bridge copies can be selected independently, with the same interval
and predecessor budgets as their separate proof and with `Q=d(n+8)`
substituted in the actual counts. Their constant count `J_b` makes the
last bridge term in (PB14) small even when the wider prefix pool is used.

No numerical square cutoff is asserted in this manuscript. The strongest
next bounded calculation is to compose (PB2), (PB7)--(PB9), (PB14), the
seed matching invoice and the separately charged prefix/bridge/wide
supplies with the optimized shorter-prefix profiles. A successful
floating-point search is discovery only. The final constants and the
complete odd-order tail require exact rational certification and fresh
nonauthor review.

## 9. Finite mechanism controls

The companion program `code/cutoff2_prefix_balance_controls.py` checks
the balanced support construction with actual disjoint cells, the exact
prefix-mean cancellation identity, and weighted-permutation conditional
increments by exhaustive finite cases. These controls support the changed
mechanisms; they neither prove the universal lemmas above nor supply the
prime counts, source domains, final cutoff, or kernel verification.
