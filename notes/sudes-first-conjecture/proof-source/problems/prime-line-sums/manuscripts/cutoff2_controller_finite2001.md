# A finite controller for every odd order 2001 through 19483

*Presentation copy: mathematical delimiters and equation labels are adapted for GitHub rendering. The unchanged, hash-bound source is in the [complete replay packet](../../../../packet/README.md).*


Author: `/root/controller_redesign`. This additive manuscript composes
the explicit finite prefix family FPF, the exact target table FTT, and
central completion CC. It preserves every frozen predecessor. The
assertion below is conditional on its named conventional mathematical
components and imported BMOR theorem; the finite certificate is not a
kernel proof. Independent review and a published scientific revision
remain separate requirements. Local labels FC2K are not permanent IDs.

## 1. Statement, exact data, and dependency boundary

For every odd integer `2001<=n<=19483`, the construction below arranges
exactly the first `n^2` odd primes once each so that every row, column,
and both main diagonals have prime sums. Target primes may repeat.
The bounded statement has no omitted odd orders. Its first upper
handoff is the separately frozen FW construction at odd order19485;
the coordinator must review and publish the complete infinite-tail
composition before presenting a new all-tail record.

Retain


```math
X=p_{n^2+1},\quad T=\sum_{j=2}^{n^2+1}p_j,\quad
 m=T/n^2,\quad y=T/n,\quad
 E=\lceil\log_2X\rceil,\quad e=\lceil\log_2y\rceil.
```


All analytic logarithms are natural. The integer `e` is not Euler's
number. Here X,T and the targets come from the complete finite table
[FTT](cutoff2_finite_target_table.md), including its exact prefix sieve
and recursive Lucas primality certificates. At each order it supplies
three odd primes q,p,r with `(n-2)q+p+r=T` and every target within
`X/1000` of y. Use that n-term list for both row and column targets,
and q for both diagonal targets. Thus both total-compatibility
conditions hold exactly. FTT also gives `0.484<m/X<0.488` and
`X<10^10`. No asymptotic target lemma is invoked outside its domain.

The fixed controller modulus is g=2, so every odd target and every
odd completed line already has the required residue. There are **no
residue controls or other nonmain reservations**: the actual C0=0
premise in FP13 is satisfied. The new controller uses fixed integer
K=5 below2400 and K=6 from2400 onward; it does not use the old
`floor(n/E^3)` specialization. Every sufficient inequality is checked
at every actual odd order, including every change of X,T,Q and K.

The conventional finite mechanisms are [PB](cutoff2_prefix_balance_experiment.md),
[RP](cutoff2_rectangle_packing.md), [CY](cutoff2_cyclic_residue_centering.md),
[BB](cutoff2_bridge_balance.md), [WB](cutoff2_wide_balance_experiment.md),
and [CC](cutoff2_central_completion.md). Their original numerical
order premises are not silently transferred: the needed geometric,
graph, stock, completion and flow inequalities are rechecked here.

## 2. Degree-six correction graphs from order2001

Use d=6, `kappa=199/200`, and three derangements for each graph.
Reapply PB's graph argument with `t0=1/256`, `a=kappa/d`,
`b=3-kappa/2-1`, and the actual entropy function


```math
F(t)=3\{tH(a)+(1-t)H(at/(1-t))\}-2H(t).
```


The exact checker proves the conditioned small-cut inequality
`1+3H(a)+b log(t0)+3 log3<log(1/8)`, and both endpoint bounds
`F(t0),F(1/2)<-1/34`. The endpoint-maximum argument is the same
universal calculation in PB, whose domain `0<kappa<d/2` holds.
The large-cut tail is paid by


```math
n/34\gt 6\log(4n)+\log8.                         \qquad\text{(FC2K1)}
```


It holds at2001 with positive derivative `1/34-6/n`, and therefore
for every larger real n. This supplies two degree-exact-six graphs
with cut expansion kappa. A sampled graph is not substituted for this
conventional existence proof.

## 3. Protect the entire explicit prefix first

Use the following **alternative**, not jointly disjoint, FPF populations:

| Odd orders | FPF population | P | K |
|---|---|---:|---:|
|2001..2399|L|24|5|
|2401..2999|C27|24|6|
|3001..4999|M|26|6|
|5001..9999|H|28|6|
|10001..19483|T|30|6|

Put `Q=6(n+8)` and retain the first Q pairs **of each stage** of the
selected population. Its actual budget is `Bp=2QP`. FPF's full
finite sieve proves every endpoint belongs to the prescribed input
pool. All retained entries are protected before any bridge or wide
selection. Unretained maximal-population copies remain available.

With gaps `2,4,...,2^P`, every ordinary reservoir has the complete even
grid through `R0=2^(P+1)-2`. This uses the sharp finite induction
`h<=R+2`; no missing even value occurs at a joining endpoint. Each
diagonal has2d copies of every stage and the amplified complete grid.
The prefix stage means, ranges, total prime sum Sp and variance


```math
V_p=18\sum_j W_j^2+4\max_j W_j^2                 \qquad\text{(FC2K2)}
```


are computed from the actual truncated prime lists, not upper-order
copies or an assumed mean interval. Exact protected counts in every
later rational interval are computed from those same lists.

## 4. Bridge stock with the actual difference span

Set `eb=3/100`. Start R=R0. While R<X, put `r=min(R/X,1/2)` and take


```math
I=(X/2-rX/2,\ X/2-rX/2+e_b rX],\qquad I'=X-I.
```


The reflection uses the corresponding half-open convention; a change
of one endpoint to the other convention is conservatively harmless
in the explicit lower counts below. We may instead define I' directly
as `(X/2+rX/2-eb rX, X/2+rX/2]`, as the checker does.
Both intervals have width H=eb rX and lie inside `[X/4,3X/4]`.
Every cross-pair has a positive even difference in
`((1-2eb)rX,rX)`. After selecting the stage update


```math
R\leftarrow R+(1-2e_b)rX.                       \qquad\text{(FC2K3)}
```


Actual ordinary coverage remains at least R. Every appended gap is
at most the previous coverage, so all even grids persist. The2d
diagonal copies each advance by the same guaranteed lower bound;
their actual gaps need not agree across blocks. Stop when R>=X.
Let J be this exact finite number of stages and `Bb=2QJ`.

The only imported prime estimate needed in this new band is BMOR
Theorem1.9, equation(1.18), printed pp.434--435. The precise finite
domain and modulus-two reduction are recorded in [S18-1](cutoff2_analytic_sub18_band.md).
Sum its two modulus-four reduced classes. For every real
`2<=a<b<=X<10^10`, with `Gamma=518/125`,


```math
\#\{\hbox{odd primes in }(a,b]\}
 \ge {b-a-\Gamma(\sqrt a+\sqrt b)\over\log X}.     \qquad\text{(FC2K4)}
```


Both q4 source arguments are below their `4*10^13` threshold. The
finite computation supporting this published theorem is an imported
claim, not independently established by our arithmetic script.

For bridge j, a uniform initial lower count in either side is
`Wb=(H-2Gamma sqrt(3X/4))/log X`. Subtract the larger exact protected
prefix count of its two sides. Subtract Q for each earlier or current
same-side bridge window intersecting it, including the complete current
stage. All lower windows are disjoint from all upper windows. Let M
be the resulting bound with an additional unit of rounding loss.

Two side sets of size at least M provide at least M^2 cross-pairs.
Their even differences occupy at most `floor(H)+1<=H+1` values,
since the difference interval has length2H. Consequently


```math
M^2\gt H+1                       \qquad\text{(FC2K5)}
```


gives two pairs with the same difference. They are vertex-disjoint:
the side sets are disjoint, and a fixed difference determines the
upper endpoint from the lower and vice versa. Select Q/2 double
blocks sequentially. The entire Q-per-side current deletion was paid,
so FC2K5 holds after every earlier choice, without an independence
assumption. The full final bridge budget is retained elsewhere.

## 5. Wide stock and its paired self-depletion

Take `delta=1/1000`, `N=75`, `w=N delta=3/40`, `a=w+1/3`.
Partition the lower band
`(m-(a+w)X,m-(a-w)X]` into N consecutive bins of length2delta X,
and pair each with its reflected upper bin about m. The upper band
is `(m+(a-w)X,m+(a+w)X]`. All endpoints are checked inside `(2,X)`.
The bands are disjoint from every bridge window.

Every within-cell cross-pair has midpoint within delta X of m and
positive even gap in `[2X/3,(2/3+4w)X]`, whose upper endpoint is
`29X/30<X`. Thus exactly3K wide stages give ordinary coverage at
least2KX, and the amplified diagonal ranges are more than sufficient.

Let `cmax=m/X+a+w`. From FC2K4 and concavity of the square root,
each bin initially contains at least


```math
W={2\delta X-2\Gamma\sqrt{c_{\max}X}\over\log X}.
                                                               \qquad\text{(FC2K6)}
```


Pay W−1 per bin for integral rounding. Subtract the exact number of
protected prefix entries in the union of both whole wide bands; this
conservatively overpays simultaneous losses on opposing sides. No
bridge entry belongs to a wide band. For current side counts L_i,H_i,
put `S=sum_i min(L_i,H_i)`. **Each selected wide pair uses one endpoint
from each side of the same fixed cell**, so it decreases S by exactly1.
The fixed partition never changes. Therefore all3QK wide pairs cost
3QK, while the final entry budget remains `Bw=6QK`. Define


```math
S_* = N(W-1)-\text{protected wide entries}-3QK.
                                                               \qquad\text{(FC2K7)}
```


There are at least `sum_i L_i H_i>=S_*^2/N` eligible cross-pairs.
Their even gaps occupy at most `floor(2wX)+1` values. The checked gates


```math
S_*\gt 0,\qquad S_*^2\gt N(2wX+1)          \qquad\text{(FC2K8)}
```


thus provide an equal-gap double block after every preceding deletion.
Select all blocks sequentially, keeping the complete `Bw` budget.
This is a deterministic allocation-specific invoice, not independent
copies of overlapping prime supplies.

## 6. Cell geometry and exact unused-pool reference

Put `S=P+J+3K`, `B=Bp+Bb+Bw`, `N0=n^2-B`.
The actual uniform main degree is `rho=r0=12S`; the actual joint
rectangle count is `Jrect=24S`. Check


```math
B\le n^2/4,\qquad n\gt 48S+16,\qquad J_{rect}\ge3.
                                                               \qquad\text{(FC2K9)}
```


These reestablish RP packing, ordinary matching and the CY center-trim
factor conditions at every actual order. In particular all rectangles
are disjoint, their other cells avoid both diagonals, and the center
is initially empty. All main families have the same replicated slots.
The unused count agrees exactly with `n^2-rho*n-4Jrect`.

Every bridge midpoint is within `eb X/4` of X/2; every wide midpoint
is within delta X of m. Define the exact reference and uncertainty


```math
c={T-S_p-B_bX/2-B_wm\over N_0},\qquad
 \sigma={e_bB_b/4+\delta B_w\over N_0}.
                                                               \qquad\text{(FC2K10)}
```


For **every** permitted bridge and wide selection the actual unused
mean mu satisfies `|mu-c|<=sigma X`. This includes their signed total
mean changes; it does not replace the actual mean by m.

The input manifest supplies an exact rational epsilon for each odd
order via a complete consecutive run table. Set `kappa_c=sigma/epsilon`
and check `0<=kappa_c<=1/4`. The three central intervals from CC are
checked disjoint from every bridge and wide interval. FC2K4 minus the
exact protected prefix count and one rounding unit is a lower bound
for the **actually unused** stock in each central interval. Check


```math
\begin{split}
 \#I_-,\#I_+&\ge D=2n-1-J_{rect},\\
 \#I&\ge D+T_{ex}=5n-4J_{rect},\qquad
 T_{ex}=3n-3J_{rect}+1.                            \qquad\text{(FC2K11)}
 \end{split}
```


The two outer counts and whole count are distinct obligations. Apply
CC with its actual CY factor `k=n-rho-5`. Completion changes every
row and column from its original unused-mean expectation by less than


```math
X+[(5+T_{ex}/n)(1+\kappa_c)+3/n]\epsilon X.       \qquad\text{(FC2K12)}
```


Its two diagonal errors are at most2.01epsilon X, which is smaller
than the same common allowance. Every completion value is used once,
and no already assigned entry or line control is disturbed.

## 7. Full baseline and correction capacity

Let `L=log(8n+8)`, `Hc=8n`, and use the actual prefix stage means.
Define `beta_p=max_j |mu_j-m|/X`,
`Ap=sum_j(mu_j-m)/X`, `beta_b=|1/2-m/X|+eb/4`.
The simultaneous all-line baseline allowance, in units of X, is


```math
\begin{split}
 U_p&=\sqrt{V_pL/2}/X,
 &M_p&=2\beta_p+12|A_p|H_c/N_0,\\
 U_b&={e_b\over2}\sqrt{(18J+4)L}+2\beta_b
                      +12\beta_bJH_c/N_0,\\
 U_w&=2\delta\sqrt{(54K+4)L}+2\delta
                      +36\delta K H_c/N_0.
\end{split}                                                   \qquad\text{(FC2K13)}
```


These are FP's actual signed mean cancellation and BB/WB's balanced
block allocations, with Jw=3K. Each disjoint family can separately
be allocated to meet its simultaneous bound, keeping its original
stage populations fixed; no union of separate half-probability budgets
or independence of value supplies is assumed. The remaining ordinary
midpoint rounding costs `d g/(2X)=6/X`.

The exact finite test, using the actual largest FTT target deviation
`tau=max_z |nz-T|/(nX)`, is


```math
U_p+M_p+U_b+U_w+1+
 [(5+T_{ex}/n)(1+\kappa_c)+3/n]\epsilon+6/X+\tau
 \lt {999\over1000}{199\over200}K.                 \qquad\text{(FC2K14)}
```


Every row and column demand is even and has total zero. Give every
graph edge integer capacity `floor(KX/2)` after division by g=2.
The explicit `KX>=2000` gate pays the rounding so cut expansion
kappa supplies the whole demand box in FC2K14. Integral max-flow/min-cut
then repairs rows and columns without changing the other required
lines. The independent diagonal reservoirs have2d amplified copies;
their centered grids contain the same demand box. Only `2d>=kappa`
is needed here, so the old textual simplification `kappa>=1` is not
invoked for the present kappa below1. All changes permute assigned
prime entries, and every required line reaches its chosen prime.

## 8. Exact finite coverage and certificate scope

The public checker replays the FTT prefix and recursive prime proofs,
the complete FPF populations, and the CC mechanism controls. It then
evaluates every inequality for each of the8,742 consecutive odd orders.
Rational interval endpoints are counted exactly; logarithms use an
atanh series with an explicit positive remainder, and square roots
use integer outward rounding. No floating result enters acceptance.
Every order's exact data, number of bridges, bin counts, rectangle
counts, capacities and epsilon are checked. There is no smooth-tail
argument across an unexamined floor or ceiling jump in this finite band.

The strict input map includes the complete public helper closure and
all stated proof sources, and rejects missing, empty, altered,
malformed, extra or symlinked files and maps. Negative controls exercise
the interval pairing, self-depletion, grid join, central demands,
target/permutation interfaces, graph domain, and finite order coverage.
The script checks exact sufficient inequalities and finite mechanisms;
it does not prove the named analytic theorem, the conventional
concentration/graph/factor arguments, or a complete infinite tail by
itself. The separately recorded independent review must address this
exact frozen composition, not just its component predecessors.
