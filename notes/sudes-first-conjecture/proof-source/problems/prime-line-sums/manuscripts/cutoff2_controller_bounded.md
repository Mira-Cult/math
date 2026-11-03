# A bounded-source controller from the order square root of 2^33

Author: `/root/controller_redesign`. This additive conditional controller
changes no frozen predecessor. It uses the published computed-range
prime-count theorem through the separately pinned S18/BG interfaces,
and the imported short-progression upper bound in BT. Those imports
are not proved by this arithmetic checker. Independent nonauthor review
of this exact component and a separate complete-tail composition are
required before declaring a new complete numerical theorem.

The entries are exactly the first n² odd primes, used once each.
Write X=p_(n²+1), T for their total, m=T/n², y=T/n,
u=log X, v=log_2 n, E=ceil(log_2 X), and e=ceil(log_2 y).
Unmarked logarithms are natural; e here is an integer parameter.
All rows, columns and both main diagonals are required. This component
covers every odd order satisfying

\[
                         n^2\ge2^{33},\qquad n<2^{18}.       \tag{BCM1}
\]

The first integer satisfying the lower condition is92682, and the first
relevant odd integer is92683. The upper handoff is to the frozen
[MC18 controller](cutoff2_controller_multiclass.md), then to the
accepted complete311744 tail through its root composition. MC18 is a
conditional component: this manuscript does not claim that its handoff
has already undergone a new complete composition review.

## BCM1. Actual source domains and a fixed parameter set

The [S18 interface](cutoff2_analytic_sub18_band.md) and
[BG geometry](cutoff2_bounded_pool_geometry.md) give, throughout BCM1,

\[
 \frac{487}{1000}X<m<\frac{123}{250}X,\qquad
 X/n^2>u-9/8,\qquad
 \#\{X/8<p\le X\}\ge\frac{112X}{125u}.                    \tag{BCM2}
\]

The printed BMOR Theorem1.9 is used only on its finite domain. The
index bound in S18.10 gives X<2^41<10^13; every requested entry
endpoint is between1 and X. The target prime arguments are treated
by S18's separate bounded-order target theorem, not by extrapolating
Theorem1.9 past its domain.

Put a_2=6931/10000 and b_2=693148/10^6. S18's before-ceiling
index bound gives

\[
 u<V(v)=b_2(293v/125-1).
\]

The exact comparison log(33a_2)>25/8 and the lower prime-index
bound give

\[
 u>U(v)=2a_2v+25/8,\qquad X/n^2>Q(v)=U(v)-9/8.            \tag{BCM3}
\]

In particular24<U(33/2)<V(18)<29. The full ceiling unit in V
comes from S18's before-ceiling statement; it is not subtracted from
an unrelated bound on E. We never assume g<=E in this controller.
Every permitted selected gap is one of2,4,...,40, and the source
supplies every reduced class for those actual moduli.

The exact common parameters are

\[
\begin{gathered}
 d=6,\quad\kappa=26/25,\quad G=40,\quad c=7/8,\quad
 \rho=112/125,\quad\alpha=81/100,\quad\eta=103/200,\\
 L=22,\quad C=700,\quad K=\lfloor n/C\rfloor,\quad
 z=8,\quad f=99999/100000,\\
 A=336,\quad\delta=1/A,\quad N=36,\quad w=N/A=3/28,\quad
 S_{\rm stock}=1600,\quad R_{\rm target}=2200 .             \tag{BCM4}
\end{gathered}
\]

Residue and bridge stocks retain one eighth of their stated analytic
lower counts. The equality7(1/2-2w)=2 preserves the seven-wide-stage
coverage. The global seed/growth pool is (X/8,X], of width cX.

The [PB graph proof](cutoff2_prefix_balance_experiment.md) is
re-specialized numerically, rather than invoked with an inherited
larger order premise. With d=6, kappa=26/25 and t_0=1/256,
its small-cut expression is below log(1/8). The two endpoint entropy
bounds are below -1/400. The same endpoint-maximum proof therefore
uses decay1/400. At n=2^16 the exact inequalities
(1/400)n>(16+2)d+3 and (1/400)n>d prove
(4n)^d exp(-n/400)<1/8 and its persistence. This proves the required
graph existence for every n>=2^16, including BCM1.

## BCM2. Weighted seeds and all requested residue classes

Use the weighted consecutive-prime path argument SQ2--SQ4 in
[SQ](cutoff2_seed_quality_experiment.md), with the actual larger
raw count rho X/u from BCM2. Give an edge of even length g<=40
weight1-g/42; longer edges have weight zero. The span of the full
path is at most7X/8. Its weighted edge total is therefore strictly
greater than (rho/u-1/48)X-1. An alternating weighted matching
retains at least half that total.

For each possible g put phi=phi(g), h=g/2 and b=ceil(log_2 h),
with b=0 for g=2. Let Q_s=d(n+8), and let s_g be the seed-stage
count in the exact input manifest. The demand for every reduced label
of gap g is

\[
                D_g=Q_s s_g+B_r/2+2Q_sJ_b,
       \qquad B_r=4(n+1)b,\quad J_b=5.                    \tag{BCM5}
\]

The certificate checks

\[
 (\rho/u-1/48)X-1>
          2\sum_{g=2,4,\ldots,40}\varphi(g)(1-g/42)D_g.    \tag{BCM6}
\]

Consequently one reduced label has its full demand before any entries
are reserved. Residue deletions destroy at most B_r/2 edges of that
fixed-class matching: BN's binary pairs have distinct endpoint classes.
All bridge entries are paid without any disjoint-supply assumption.

Choose the actual prime target lists first, using S18's R=2200
bounded target statement from v=33/2 and the parity-only exact-total
target lemma. Each of the row and column lists has length n and total T;
every target is within y/2200 of y. Choose both diagonal targets as
well. Repetitions among these targets are allowed. Their exact totals
give the row/column residue compatibility.

The [BN binary controls](cutoff2_controller_binary_narrow.md) prescribe
every target residue and both diagonal residues independently. For each
bit, CRT supplies lower and upper reduced classes a and a+2^(j+1).
The source is uniform in every reduced class, not only -1 and +1.
There are no residue gadgets when g=2. Keep the inherited repair bound
2bX; no improved signed-repair estimate is used in this component.

The five preselected bridge radii are regenerated from1/22, multiplying
by2-2epsilon_b with epsilon_b=22/416 until reaching1/2, then using
radius1/2 until the guaranteed lower coverage reaches1. The exact
windows lie in[X/4,3X/4], have length at least X/416, and have total
upper coverage below5X/2. The manifest includes both endpoints, every
overlap and every possible residue-band intersection. These are checked
by exact interval arithmetic, rather than inferred from a picture.

## BCM3. Full bounded-range counts, with every deletion paid

Let Gamma_g=518/125 for g=2 and Gamma_g=(259/125)phi(g)
otherwise. This is S18.3, including its explicit modulus-2 treatment.
For an entry bin centered at Y<=c_+X, where
c_+=123/250+1/4+w, S18.5 supplies at least

\[
 \frac{2\delta X}{\varphi(g)u}
       \left(1-\Gamma_g A\sqrt{c_+/X}\right)              \tag{BCM7}
\]

primes in every required class. For a bridge of radius rX and
width epsilon_b rX inside[X/4,3X/4], it supplies at least

\[
 \frac{\epsilon_b rX}{\varphi(g)u}
       \left(1-\frac{2\Gamma_g\sqrt{3/(4X)}}{\epsilon_b r}\right).
                                                               \tag{BCM8}
\]

The two parentheses are evaluated outward, using the lower X bound
in BCM3. They are positive. Relative to the earlier half-density
formulas, the multiplier is twice the appropriate parenthesis.
Thus deletion and floor invoices divide by that multiplier, and
the double-pair invoice divides by its square. No count is silently
doubled by calling the old half-density lemma.

The residue-side invoice pays B_r/2 entries per side. Every bridge
window pays all intersecting bridge slots, plus B_r/2 if it can meet
the relevant residue band. Those entries are selected before the seeds
and growth. The aggregate reflected-bin invoice pays the complete
eventual B and uses the retained index ratio
u/(X/n²)<1+(9/8)/Q(v). The stock-square check N S_stock²u²<X
and the integer floors are separately verified. All are re-evaluated
for every g through40, with its actual phi(g).

## BCM4. Fixed integer adaptive phases across all reduced classes

Use [MC](cutoff2_multiclass_prefix.md) with r=phi(g). Every pool
prime exceeds g, so it lies in a reduced class. Growth pairs need
equal endpoint residues; different pairs need not share the same
class. Their common stage difference remains a positive g-multiple.
Every subsequent swap therefore preserves residues, and each diagonal
rectangle retains two exactly equal differences.

For the whole band set

\[
\begin{gathered}
 n_0=92681,\quad U_0=U(33/2),\quad Q_0=Q(33/2),\quad V_1=V(18),\
 X_0=n_0^2Q_0,\quad q_0=d(n_0+8)/X_0,\quad
 m_f=f\alpha/V_1,\\
 m_0=\rho/V_1-4(n_0+1)b/X_0-2q_0(J_b+s_g),\quad
 R_*={\varphi(g)\over2\eta m_f},\quad S_0=s_gg-R_* .      \tag{BCM9}
\end{gathered}
\]

For the actual X, m_0X is a lower post-seed stock; m_fX is a real
terminal lower stock. Real lower bounds are permitted by MC/BT:
the actual cardinality remains an integer. Full B_r is subtracted
from pooled growth stock, because both residue endpoints may lie in
the union of reduced classes. The seed matching's B_r/2 saving is
not reused here.

The input manifest gives s_g and an explicit list of pairs
(lambda,J_lambda) for every g. The first lambda is0, denoting
ordinary MC growth with multiplier1. Later phases have positive
integer lambda and multiplier zeta=lambda phi(g)/(2g)>1,
as in [BT](cutoff2_bruntitchmarsh_prefix.md). Every stage cap is a
given integer; no floating root or optimized decimal is read.

For a positive-lambda phase, take the shifted starting threshold

\[
 S_{\lambda}=\left\lceil
  {\varphi(g)\exp(\lambda)\over\zeta\eta m_f}\right\rceil. \tag{BCM10}
\]

The exponential is enclosed upward by BT's exact rational Taylor
routine before taking this ceiling. Let a be the sum of preceding
phase caps and J the current cap. Define m_a=m_0-2q_0a and
t_max=zeta eta g rho/[phi(g)U_0]. The checker proves, for each phase,

\[
\begin{gathered}
 0<t_{\max}\le1,\qquad m_a-2q_0J\ge m_f>0,\\
 {\zeta\eta g\{Jm_a-q_0J(J-1)\}\over
       \varphi(g)(1+t_{\max})}
   \ge\log(S_{\rm next}/S_{\rm start}).                  \tag{BCM11}
\end{gathered}
\]

For the last phase replace the right side by V_1-log(L S_start),
which is at least the required log[X/(L S_start)]. All intermediate
thresholds are increasing, and S_0>0. The certificate also checks
s_ggL<X_0. If X/L is crossed before a later phase, selection stops.
Earlier phase completion only reduces deletions, so the full cap sum
still gives valid lower stocks and every later entry threshold remains
a valid sufficient target.

With epsilon=1/[2(c+1/L)]-eta, the simultaneous candidate condition is

\[
                  \epsilon m_f^2g\ge2zq_0\varphi(g).       \tag{BCM12}
\]

It supplies zQ_s disjoint pairs of one common difference, after every
previous deletion. BN retains Q_s in one of z midpoint bins of width
cX/z. Only those retained entries are reserved; unselected candidates
are still unused. The complete grid reaches X/L, with first-crossing
overshoot at most2X/L. The five bridges extend it beyond X, and the
seven-wide-stage family supplies the original K-dependent capacity.

Writing P_g=s_g+sum J_lambda, the independent global stock check is

\[
              B_r+2Q_s(P_g+J_b)\le(\rho-\alpha)X/u.        \tag{BCM13}
\]

All wide entries, including every diagonal copy, are charged in
B=B_r+2Q_s(P_g+J_b+7K). No overlapping supply is assumed independent.

## BCM5. Placement, exact completion and all-line centering

Use [RP](cutoff2_rectangle_packing.md) for the actual rectangle count
J_rect=4d(P_0+J_b+7K)+2b, P_0<=P_g. Here K>=1 and d=6,
so J_rect>=3. RP applies at n>=2J_rect+1. The retained ordinary
matching inequality

\[
 {8d(P_g+J_b)\over n}+{56d\over C}+{24b+16\over n}<1      \tag{BCM14}
\]

is stronger than RP's sufficient rectangle inequality, whose last
numerator is4b+1. No other PB placement hypothesis changes: every
rectangle uses unique rows and columns, avoids the center and the
unintended diagonal, and meets its designated diagonal once.

Sorted seeds and narrowed common growth stages give the BN/DP
allocation error

\[
 cX\sqrt{(3d+4)\log(8n+8)/2}
          +(10c/z)X\lceil\log_2 Q_s\rceil.                \tag{BCM15}
\]

The exact inequality d(262145+8)<2^21 bounds every allocation-depth
jump in BCM1. Use the [WB](cutoff2_wide_balance_experiment.md)
shared-population allocation and mean cancellation for the wide stages.
Seeds and wide stages use disjoint entries and slots; their separate
existence choices can be fixed successively.

The verifier computes Z>=B/n² for each gap and proves Z<=1/4.
Use BG's actual-Z completion expression with U_0, depth36 and n_0.
The unused-pool depth is at most36 because n<2^18. BG supplies an
exact bijection of every unused prime to every remaining position,
including both diagonals. Its allowance depends on Z; this component
does not replace it by the smaller27X estimate valid only near Z=.1.

Add the unchanged prefix mean correction, binary residue midpoint
error, the inherited2bX repairs, bridge midpoint error, WB error and
reservoir rounding. The certificate records each term individually.
It divides by the rigorous K lower bound n/C-1 and proves

\[
  \text{baseline error}<(4/5)KX,\qquad
 {4\over5}+{(123/250)C\over R_{\rm target}(1-C/n_0)}
                      <.999\kappa.                       \tag{BCM16}
\]

It also verifies KX>=1000g. The original integral graph routing then
repairs every row and column to its chosen prime target; amplified
independent diagonal reservoirs repair both diagonals. Each operation
only swaps existing entries and preserves already fixed lines/residues.

## BCM6. Whole-band persistence and verification boundary

All seed counts and phase caps are fixed throughout BCM1. Every
non-seed inequality uses the pointwise envelopes n>=n_0, u<=V_1,
u>=U_0 and X>=n_0²Q_0. Counts are bounded directly; smooth derivatives
are not transferred across E, e, K or depth jumps. The log term obeys
log(8n+8)<b_2(v+4)<=b_2*22. The expression sqrt(aK+b)/K decreases
for positive K, justifying the lower-K substitution in WB.

For the weighted seed condition expand its fixed demand sum as
A_0n+B_0, A_0,B_0>0. Its normalized upper bound is a positive sum
of terms proportional to

\[
 {e^{-jv\log2}V(v)\over Q(v)\{\rho-V(v)/48\}},
                           \qquad j=1,2.                 \tag{BCM17}
\]

If a=V'(v), the logarithmic derivative of each term is
-j log2+a/V-Q'/Q+(a/48)/(rho-V/48).
Dropping the negative -Q'/Q, the checker proves on the entire band

\[
 {a\over V(33/2)}+{a/48\over\rho-V(18)/48}<a_2<\log2.    \tag{BCM18}
\]

Thus both terms decrease. The lower-order endpoint check suffices;
the upper endpoint is also checked as a redundant consistency control.
Replacing2^v by its exact integer lower enclosure in an endpoint
only enlarges the upper invoice. The checker proves those enclosures
by integer eighth powers. This is a continuous-band proof, not a mesh
of sampled successes or an asymptotic claim.

Run the source-bound standard-library verifier:

    python3 -B problems/prime-line-sums/code/cutoff2_controller_bounded.py

Its manifest specifies every rational parameter, integer phase cap,
bridge overlap and source digest. It rejects missing, empty, altered,
nonregular, symlinked, extra and malformed source maps/files. Negative
controls underpay phase growth, entry stocks, seed demand, allocation
depth, completion depth and flow allowance. The complete required set
contains only recoverable research sources; no private artifact is needed.
Inherited discovery files may be pinned for provenance, but no floating
discovery value is read as an input to these mathematical checks.

The frozen finite profile passes1291 rational predicates,158 negative
controls and598 physical source attacks against119 required sources.
The largest prefix cap is467. The common-batch ratio is below.917249,
the weighted seed ratio below.898757, the pooled global invoice
below.815821, and the reflected-bin invoice below.890287. The largest
reserved fraction is below.181129. BG's corresponding completion
allowance is below38.630903X. Every bridge retains its full counted
stock; the worst floor and pair ratios are below.849984 and.812407.
The baseline center error is below.753067KX, inside the chosen.8KX
allowance. That allowance plus the complete target tolerance is below
.957737KX, against the capacity1.03896KX. These rounded decimals
are explanatory; the verifier uses the underlying rational bounds.

The output is a finite arithmetic and source-identity certificate.
The universal constructions, the two analytic imports and the final
all-odd-tail handoff remain ordinary mathematical obligations. This
component records no review that has not occurred and is not an
end-to-end kernel-checked proof.
