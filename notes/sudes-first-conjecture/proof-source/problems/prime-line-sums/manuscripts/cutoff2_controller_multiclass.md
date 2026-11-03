# Multiclass adaptive controller from order 2^18

Author: /root/controller_redesign. This additive conditional controller
preserves every frozen predecessor. Its exact revision and complete
composition require independent nonauthor review. The arithmetic checker
does not prove the imported analytic theorems or provide end-to-end
formal verification.

Use exactly the first n² odd primes, once each, and retain
X=p_(n²+1), T their total, m=T/n², y=T/n, u=log X,
v=log_2 n, E=ceil(log_2 X), e=ceil(log_2 y).
Unmarked logarithms are natural. Every row, every column and both main
diagonals are included. This component covers every odd order in

\[
                         n\ge2^{18},\qquad n^4<2^{73}.       \tag{CM1}
\]

At the upper boundary the frozen BQ controller applies, followed by AN
and the independently reviewed complete 2^19 tail. The root composition
is responsible for checking those handoffs. Their larger numerical
premises are not imported into this smaller band.

## CM1. Actual analytic and order domains

[OP](cutoff2_order18_pool.md) gives .47X<m<.53X,
rho=2187/2500=.8748, and the before-ceiling envelope

\[
 u<V(v)=b_2(233v/100-1),\qquad b_2=693148/10^6.
\]

The exact logarithm comparison log(36a_2)>321/100, with
a_2=6931/10000, gives the pointwise lower bounds

\[
 U_-(v)=2a_2v+321/100<u,\qquad
 Q(v)=U_-(v)-3/2<X/n^2 .                                  \tag{CM2}
\]

In particular u>28 throughout this band, and
u/(X/n²)<1+(3/2)/Q(v). These are coupled prime-index bounds,
not independent worst-case choices of n and X.

[LZ](cutoff2_analytic_low_zero_band.md) supplies, for the selected even
modulus g<=30, every reduced class in centered entry bins with
delta=1/924, extent w=99/924=3/28, every bridge interval of length
at least X/512 inside [X/4,3X/4], and .99 of the full reduced-class
density in (X/8,X]. The mean and extent bounds put the relevant
bin centers between (79/700)X and (621/700)X. The actual endpoints
and density denominators are those of LZ; no upper bound30 on E
is asserted.

For targets use the same bounded-order LZ interface R=5000 and OP's
finite size conditions. The parity-only target theorem constructs
row and column lists of exact total T, tolerance D=y/5000, and
independent diagonal targets. Target prime values may repeat.

The finite parameters are

\[
\begin{gathered}
 d=6,\quad\kappa=26/25,\quad c=7/8,\quad
 \alpha=41/50,\quad\eta=27/50,\quad L=37,\\
 C=1660,\quad K=\lfloor n/C\rfloor,\quad z=8,\quad
 f=99999/100000,\\
 A=924,\quad N=99,\quad S_{\rm stock}=4000,\quad
 G=30,\quad \chi=99/100.
\end{gathered}                                             \tag{CM3}
\]

The retained residue and bridge stocks are one eighth of their
analytic counts. The degree-six graph and cut expansion are checked
at n=2^18. Seven wide stages per K still suffice because
7(1/2-2w)=2. Neither the prescribed pool nor the two-diagonal
placement geometry changes.

## CM2. Fixed integers and weighted seed selection

The table specifies every candidate label before the label is selected.
These integers are uniform on the entire real v interval [18,73/4].
The final upper endpoint belongs to the successor controller.

| g | Seed stages s_g | Growth cap J_g |
|---:|---:|---:|
| 2 | 41 | 694 |
| 4 | 41 | 671 |
| 6 | 28 | 451 |
| 8 | 41 | 648 |
| 10 | 33 | 521 |
| 12 | 28 | 436 |
| 14 | 36 | 545 |
| 16 | 41 | 625 |
| 18 | 28 | 427 |
| 20 | 33 | 502 |
| 22 | 38 | 562 |
| 24 | 28 | 421 |
| 26 | 38 | 565 |
| 28 | 36 | 525 |
| 30 | 22 | 341 |

Write Q_s=d(n+8), b=ceil(log_2(g/2)), B_r=4(n+1)b.
The six exact rational bridge stages use initial radius1/L,
width factor epsilon_b=L/512 and multiplier2-2epsilon_b,
then radius1/2 until their coverage reaches1. The checker rebuilds
both reflected windows, all overlaps and residue intersections.

The seed demand for a possible label is

\[
 D_g=Q_ss_g+B_r/2+2Q_sJ_b,\qquad J_b=6.                    \tag{CM4}
\]

The weighted path matching of SQ, with OP's smaller-domain density,
is applicable because the certificate proves

\[
 (\rho/u-7/256)X-1>
 2\sum_{g=2,4,\ldots,30}\varphi(g)(1-g/32)D_g .             \tag{CM5}
\]

Thus at least one gap and reduced class supply its actual demanded
number of disjoint seed pairs. No favorable gap is assumed.
The B_r/2 saving belongs only to this single-class matching:
the residue gadgets' two endpoint classes are distinct for g>=4,
and B_r=0 for g=2. The bridges pay their full possible loss.

As in BN, first choose the targets, then select residue, bridge,
seed and growth entries. The initial seed grid uses the selected
single class. The subsequent growth entries may use all reduced
classes, by the separate [MC lemma](cutoff2_multiclass_prefix.md).
Each pair still has a positive g-multiple difference, and every
growth stage still has one common difference. This preserves both
the target-first residue repair and the equal-gap diagonal trades.

## CM3. Pooled post-seed stock and the integer growth cap

Set

\[
 n_0=2^{18},\quad V_1=V(73/4),\quad
 U_0=U_-(18),\quad Q_0=Q(18),\quad
 q_0=\frac{d(n_0+8)}{n_0^2Q_0},\quad r=\varphi(g).
\]

The full pool (X/8,X] has at least chi cX/u primes.
Every one exceeds g and therefore belongs to a reduced class.
Pay every selected residue entry, every bridge entry and every seed
entry against this total stock. The uniform real lower bounds are

\[
\begin{split}
 m_f&=f\alpha/V_1,\\
 m_0&=\chi c/V_1-\frac{4(n_0+1)b}{n_0^2Q_0}
                         -2q_0(J_b+s_g).
\end{split}                                               \tag{CM6}
\]

There is no B_r/2 saving in this pooled invoice. After j growth
stages the actual surviving cardinality is at least
X(m_0-2q_0j). MC's bin-and-class Cauchy bound needs only that total;
it does not require any uniform surviving count in an individual class.

Let epsilon=1/[2(c+1/L)]-eta. The exact checks are

\[
\begin{gathered}
 m_0-2q_0J_g\ge m_f>0,\qquad
 \epsilon m_f^2g\ge2zq_0r,\\
 S_0=s_gg-\frac{r}{2\eta m_f}>0,\qquad
 t_{\max}=\frac{\eta g\chi c}{rU_0}\le1,\\
 \frac{\eta g\{J_gm_0-q_0J_g(J_g-1)\}}
             {r(1+t_{\max})}\ge V_1-\log(LS_0),\qquad
 s_ggL<n_0^2Q_0 .                                         \tag{CM7}
\end{gathered}
\]

These are MC2 and MC8 evaluated from their numerical hypotheses.
Every J_g is an explicit integer; the proof does not trust a
floating quadratic root. Selecting zQ_s common-gap candidate pairs
and retaining Q_s within one of eight midpoint bins costs exactly
2Q_s entries per retained stage. Unselected candidates remain unused.
The narrowed midpoint width is cX/8.

The improvement over a single-class stock is visible in the first
two lines: the raw density is not divided by r, and the common-batch
condition pays one factor r rather than two. The factor r required
by subdivision into residue classes has not been dropped.

With P_g=s_g+J_g the complete reservation bound remains

\[
 B=B_r+2Q_s(P_g+J_b+7K).                                  \tag{CM8}
\]

The global growth invoice is now

\[
 B_r+2Q_s(P_g+J_b)\le(\chi c-\alpha)X/u.                    \tag{CM9}
\]

The residue stocks, each overlapping bridge quota, integer floors,
equal-gap double pairs, aggregate reflected-bin stock, and ordinary
and diagonal placement inequalities are unchanged finite formulas
from AN/BQ and are all re-evaluated. No supply or entry position is shared.

## CM4. Centering, completion and routing

BN's sorted-seed allocation and DP's simultaneous common-stage
rounding give prefix allocation error, in units of X, at most

\[
 c\sqrt{(3d+4)\log(8n+8)/2}
        +\frac{10c}{8}\lceil\log_2(d(n+8))\rceil.           \tag{CM10}
\]

The exact bound d(311744+8)<2^21 covers every allocation-depth jump
in this branch. Every seed stage and growth stage retains the PB
replicated diagonal positions and uniform stage population.

Use WB's shared wide-stage allocation and exact mean cancellation.
Writing Z for the certified upper bound B/n², its entire wide and
residue-mean contribution is

\[
 2\delta\sqrt{(21dK+4)\log(8n+8)}+2\delta+
 \frac{14d\delta K(B_r+8n)+\delta nB_r}{n^2-B}.              \tag{CM11}
\]

Seed and wide allocation can be fixed separately because their
entries and slots are disjoint and each family preserves its own
stage means. No prime-density assertion is probabilistic.

The certificate proves Z<=1/10. Also u>28 and the unused-pool
depth is at most37, because n²<2^(73/2)<2^37.
QF therefore gives an exact unused-prime bijection with every
line's completion error below50X. The center and both diagonals
are included. The checker records the stronger actual-Z QF
allowance but pays50X in the selected centering invoice.

Add all remaining PB/BN terms: prefix mean cancellation, binary
residue midpoint error and repairs, bridge midpoint error, and
reservoir rounding. Divide by the rigorous K lower bound n/C-1.
The stochastic wide expression sqrt(aK+b)/K decreases for positive K,
so its endpoint use is valid. All other normalized terms use direct
branch envelopes n>=n_0 and B/n²<=Z.

The checker proves baseline error below (3/4)KX, complete target
cost at most .53C/[5000(1-C/n_0)], and baseline plus target cost
below .999kappa KX. It also checks KX>=1000g. The bounded-degree
graph flow consequently repairs every row and column; the separately
reserved amplified diagonal reservoirs repair both diagonals.
Every operation swaps existing entries, preserving the exact input
permutation and all already repaired residues.

## CM5. Every order, every rounding jump

All table counts are fixed integers throughout the branch.
The actual n, X and u obey the pointwise envelopes used in CM6--CM7;
there is no derivative argument across a changing ceiling or floor.
K is bounded by n/C-1, the prefix depth by21, and the completion
depth by37. The verifier checks
311743^4<2^73<311744^4 and the corresponding exact eighth-power
enclosures used by its endpoint helper.

For seeds, expand the fixed weighted sum in CM5 as A_0n+B_0,
with A_0,B_0>0. Its normalized upper bound is a positive sum of

\[
 \frac{\exp(-jv\log2)V(v)}
 {Q(v)\{\rho-(7/256)V(v)\}},\qquad j=1,2.
\]

The same explicitly proved convexity calculation as AN11/BQ5
applies: the logarithmic second derivative is positive under
(7/256)V(18)>=2rho/3, and the supply denominator remains positive
at73/4. Both guards and both endpoint invoices are checked exactly.
Convexity, together with the other uniform envelopes, covers the
entire real-order interval. A sampled optimization mesh is not used.

## CM6. Reproduction and proof boundary

The exact run passes626 rational checks,139 negative controls and
508 physical source attacks against101 required source files.
The global pooled invoice is below .791744, the full common-batch
invoice below .591393, and the weighted seed invoice below .827184.
The reserved fraction is below .084526, meeting the .1 quantile
domain. Baseline error is below .693772KX, inside the .75KX
allowance; that allowance plus the full target tolerance is below
.927082KX, compared with capacity1.03896KX. The actual-Z
completion sensitivity is below43.427449X, though this profile
pays50X. The direct integer growth comparisons retain logarithmic
slack greater than .06959 for every possible selected gap.

Run the self-contained source-bound verifier:

    python3 -B problems/prime-line-sums/code/cutoff2_controller_multiclass.py

It enforces a complete canonical file set and rejects missing, empty,
changed, nonregular, symlinked or malformed source inputs. Negative
controls underpay the growth cap, the candidate multiplicity, the
weighted seed demand, the entry stocks, the depth envelopes and the
flow allowance. The manifest specifies every finite parameter and
integer table entry.

The imported analytic counts, the universal MC/PB/BN/WB/QF
constructions and the final handoff remain separately reviewable
mathematical claims. This component asserts no acceptance of its own
review and does not call its finite arithmetic a formal proof.
