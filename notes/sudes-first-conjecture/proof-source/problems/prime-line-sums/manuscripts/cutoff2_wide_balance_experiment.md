# Balance all wide stages through equal-gap blocks

*Presentation copy: mathematical delimiters and equation labels are adapted for GitHub rendering. The unchanged, hash-bound source is in the [complete replay packet](../../../../packet/README.md).*


Author: `/root/prefix_balance_research`, with `/root` supplying the
wide-stage question and checking the controller composition. This is an
additive finite component. It changes no frozen source and asserts no
new square cutoff. Independent nonauthor review must address the exact
scientific revision before this component is used in an accepted theorem.

The proof uses the finite reflected-stock lemma in
[RBC](cutoff_reflected_bins_controller.md), the geometry and midpoint
identity in [PB](cutoff2_prefix_balance_experiment.md), and the finite
block concentration proof in [SQ](cutoff2_seed_quality_experiment.md).
An optional deterministic variant uses
[DP](cutoff2_deterministic_prefix_experiment.md) and a separately proved
binary rounding lemma below. There is no new analytic prime-supply import.
Every analytic hypothesis of the reflected-stock lemma remains required.

Use the prescribed pool of exactly the first n² odd primes. Write X for
its largest prime, T for its total, m=T/n², and g for the selected even
seed gap. All logarithms below are natural unless indicated otherwise.

## WB1. Select every wide pair in a fresh double block

Let delta>0, let N>=1 be an integer, and put w=N delta. Retain RBC's two disjoint bands,
their disjoint half-open reflected bins A_j,C_j, and all their endpoint
requirements. Suppose each bin initially has at least W pool primes in
every reduced class modulo g. Let B be an upper bound for **all** reserved
entries in the complete controller, and suppose


```math
S_0=N\varphi(g)W-B\gt 0,\qquad S_0^2\gt NX.            \qquad\text{(WB1)}
```


After any set of at most B deleted pool entries, RBC gives


```math
S=\sum_{j,a}\min(L_{j,a},H_{j,a})\ge S_0,
\qquad
\sum_{j,a}L_{j,a}H_{j,a}\ge\frac{S^2}{N\varphi(g)}\gt X/g.
```


Each low--high pair has a positive g-multiple difference below X.
There are at most floor(X/g) such differences. Hence one difference
occurs for two distinct pairs. The pairs have disjoint endpoints:
a fixed difference and either endpoint determine the other endpoint,
and the lower and upper bands are disjoint. The partitions ensure that
the same pair is not counted under two bin/class labels.

Thus a fresh equal-gap **double block** exists after every allowed
deletion set. Its two pairs may have different lower residues and may
come from different matched bins. Each pair separately satisfies


```math
\left|(p+q)/2-m\right|\le\delta X,
 \quad(1/2-2w)X\le q-p\le(1/2+2w)X\lt X.             \qquad\text{(WB2)}
```


This uses the original aggregate stock criterion, not a new common-gap
batch criterion. In particular no Q-copy multiplicity condition has
been introduced.

Let d be PB's even degree, Q=d(n+8), and J_w=7K. At each wide stage,
select Q/2 fresh double blocks sequentially, deleting each block's four
primes before choosing another. Both Q and dn are even. Every selection
is protected by (WB1), since the deletion invoice includes the entire
eventual family. Its total consumption is still exactly


```math
B_w=2QJ_w=14d(n+8)K.             \qquad\text{(WB3)}
```


There is no temporary reservation of unused candidates and no independence
assumption about overlapping stocks. Compared with the former procedure,
ordinary pair slots now consume both pairs of selected blocks, instead
of selecting one pair from a witnessed block. Their number of entries
has not changed.

## WB2. Fixed slots, both diagonals, and complete grids

Keep every PB cell position. At each stage each diagonal rectangle is
one two-slot block; the 2d rectangles on each of the two diagonals use
4d slot blocks. Pair the remaining dn ordinary pair slots arbitrarily
into dn/2 fixed slot blocks. There are Q/2 slot blocks altogether.

Assign the selected blocks bijectively to the slot blocks. An internal
swap may exchange the two whole prime pairs inside any block. Its two
pairs always have equal difference, so every diagonal rectangle remains
a valid row- and column-preserving trade. The two diagonal families
retain their disjoint cells and avoidance of the opposite diagonal.

Before the wide stages, every ordinary reservoir already has a complete
g-grid with coverage at least X, and every diagonal has coverage at
least 2dX. By (WB2), every new difference is positive, is divisible by g,
and is less than X. Appending it preserves the complete grid in whichever
reservoir receives it. No common difference across different blocks is
needed. Each ordinary reservoir receives one pair per stage; each
diagonal receives 2d rectangles per stage.

The existing capacity condition


```math
7(1/2-2w)\ge2                \qquad\text{(WB4)}
```


still makes J_w=7K stages supply at least 2KX of added ordinary
coverage and 4dKX of added diagonal coverage. Thus the same K, wide-stage
count, rectangle count, cell-load bound, and flow capacities remain in
force. The later subset choice nearest each reservoir's actual midpoint
still has error at most g/2. Residues remain preserved because all wide
differences are g-multiples.

## WB3. A small simultaneous wide-allocation error

Select all primes before making this allocation. At each wide stage,
uniformly permute its Q/2 blocks among the fixed slot blocks and swap
the two pairs inside each assigned block independently with probability
1/2. Use independent allocations at different stages.

Each pair slot is uniform among all Q selected pairs of its stage.
Let mu_t be that stage's mean pair midpoint. The expected contribution
of a slot of line weight z is z mu_t. In particular ordinary and diagonal
slots now have **the same stage population and mean**.

For a required line, let w_1,w_2 be its weights in a slot block.
The SQ argument reveals block averages in nonincreasing order of
w_1+w_2, and then reveals the internal swaps. The squared conditional
ranges are at most


```math
(2\delta X)^2\sum\{(w_1+w_2)^2+(w_1-w_2)^2\}
                 =2(2\delta X)^2\sum_s w_s^2.
```


PB's unchanged positions give `sum_s w_s^2<=3dJ_w+4` for a row
or column. A diagonal has the smaller bound 2dJ_w. The same finite
conditional-range Hoeffding bound and union bound over all 2n+2 lines
give an allocation with every wide midpoint contribution within


```math
u_wX,
 \qquad
 \boxed{u_w=2\delta\sqrt{(3dJ_w+4)\log(8n+8)}.}             \qquad\text{(WB5)}
```


The success probability is at least one half. This is an existence
argument for a finite assignment, not an assumption about random prime
distribution. Other independently selected allocation families, such as
the sorted seed stages, can be fixed separately: their pairs and slots
are disjoint, and their exact stage means do not depend on these choices.
Thus no extra union-bound allowance is silently lost when combining
their deterministic error bounds.

## WB4. Exact cancellation against the unused-pool mean

Let P_0 be the actual prefix-stage count and J_b the bridge-stage count.
Write


```math
r_0=2d(P_0+J_b+J_w),\qquad
B_{\rm actual}=r_0(n+8)+B_r,\qquad
N_0=n^2-B_{\rm actual}\gt 0.                         \qquad\text{(WB6)}
```


Use a residue parameter r>=0 with
`B_r=4(n+1)r` and a required line's reserved-cell count
`r_L=r_0+q_L`, where `0<=q_L<=6r+2`.
For binary residues r=ceil(log_2(g/2)); for the older residue paths
r=g/2-1. A main diagonal has q_L=r. These are the exact PB/BN
invoices, not assumptions that all line counts are identical.

Put


```math
A_w=\sum_{t=1}^{J_w}(\mu_t-m),\qquad |A_w|\le J_w\delta X.
```


The complete wide family has total deviation 2Q A_w from B_w m.
Its expected main contribution on any required line is 2d A_w.
A row or column has at most two extra rectangle cells, contributing
at most 2 delta X beyond their own m baseline; a diagonal has no such
wide extra. These small extras are separate from the residue count q_L.

After completion about the actual unused-pool mean, the contribution
arising from A_w is exactly


```math
\begin{split}
2dA_w-(n-r_L)\frac{2QA_w}{N_0}
 &=\frac{2dA_w}{N_0}\{(n+8)q_L-B_r-8n\}.        \qquad\text{(WB7)}
\end{split}
```


For n>=20,


```math
|(n+8)q_L-B_r-8n|\le B_r+8n.              \qquad\text{(WB8)}
```


The lower bound follows from q_L>=0. At the upper endpoint
q_L=6r+2, the difference between the asserted upper bound and the
bracket is `2r(n-20)+14n-16>=0`. This includes both diagonals.

Let B>=B_actual be the certified full entry invoice, with B<n².
Combining (WB5)--(WB8), the wide midpoint and unused-pool mean
contribution is at most


```math
\left\{u_w+2\delta+
       \frac{2d\delta J_w(B_r+8n)}{n^2-B}\right\}X          \qquad\text{(WB9)}
```


to the completed baseline error. The usual separate total-residue
deviation is at most delta B_r X, so its unused-pool contribution
may be bounded by `delta n B_r X/(n²-B)` as before.
These are contributions to the uniform-unused-mean reference baseline;
the separately proved completion discrepancy and the unchanged reservoir
orientation error are still added in the complete centering invoice.

Accordingly, in the existing PB centering invoice replace the old
combined wide/residue-mean term


```math
\delta\left\{2dJ_w+2+\frac{n(B_w+B_r)}{n^2-B}\right\}
```


by


```math
\boxed{
 u_w+2\delta+
 \frac{2d\delta J_w(B_r+8n)+\delta nB_r}{n^2-B}.}            \qquad\text{(WB10)}
```


Every other centering term is retained. This is the exact reason that
the previous losses proportional to J_w disappear. The full reservation
B_w and the analytic reflected-stock gate (WB1) have not disappeared.

Balancing only the ordinary wide stages would not establish (WB7).
If ordinary midpoint populations had mean m+delta X and diagonal
populations had mean m-delta X, a diagonal's discrepancy from the grand
stage mean would still be linear in J_w. Selecting and assigning one
shared block population is essential.

## WB5. Optional deterministic block allocation

This alternative can replace u_w in (WB9)--(WB10) by


```math
\boxed{u_w^{\rm det}
       =40\delta\lceil\log_2(Q/2)\rceil+20\delta.}          \qquad\text{(WB11)}
```


First replace each selected block by its average pair midpoint. It lies
in the same interval of width 2 delta X. A slot block has line weight
w_1+w_2. The sum of these weights over all lines is at most 10, because
each original pair slot has total weight at most 5. Divide the block
weights by two and apply the already proved DP theorem simultaneously
to every wide stage. Multiplying its conclusion back by two gives an
error at most `40 delta X ceil(log_2(Q/2))` relative to the common
stage means. Every stage remains an exact block bijection.

It remains to choose the internal pair swaps. For an assigned block b,
let its two pair midpoints be a_b,b_b, and define the signed coefficient


```math
c_{L,b}=(w_{L,1}-w_{L,2})(a_b-b_b).
```


The difference between the actual line contribution and its block-average
contribution is `(x_b-1/2)c_(L,b)`, where x_b=0 or 1 chooses the swap.
Each column has absolute coefficient sum at most 20 delta X.

Here is the required binary rounding lemma, proved without a probabilistic
claim. For any finite real matrix with absolute column sums at most A,
start all variables at one half. Retain a row equation only while its
remaining absolute coefficient mass exceeds A. If F variables remain
fractional, fewer than F row equations remain, since the total mass is
at most AF. A nonzero homogeneous direction therefore reaches a new
integral coordinate. A dropped row's final drift is at most A, by direct
comparison with its value at dropping. Iteration produces a binary
vector with every row error at most A. If A=0 the assertion is immediate.
The algorithm is rational for rational inputs.

Apply this lemma once to **all assigned blocks in all wide stages**,
with A=20 delta X. It pays a single 20 delta X swap error per line.
There is no stage cardinality constraint on the internal swaps; each
choice merely exchanges two whole pairs inside its existing block.
This proves (WB11) while preserving every equal-gap rectangle, stage
population, prime, and occupied cell. Either WB5 or WB11 may be used;
their proofs are separate and no sampled allocation is a certificate.

## Experiments and verification boundary

On the existing floating 18.5-order profile, the gap-26 wide term divided
by K changes from about .134376 to .004022 using WB5, with the same
parameters and all other invoices unchanged. WB11 gives about .002320.
In the archived failed 18-order gap-26 profile, WB5 changes that term
from .194493 to .005971, moving its centering gate from 1.2020 to 1.0205
before any improvement to the separate completion lemma. These are
discovery comparisons, not a new theorem or an all-tail certificate.

The executable controls test adversarial reflected-stock deletion and
sequential fresh blocks using actual primes, exact block assignments,
signed simultaneous swap rounding, both-diagonal slot incidence, and the
completed-mean identity. An explicit negative midpoint fixture shows why
separate ordinary/diagonal means cannot be ignored. Required sources and
their hashes are complete, public, and checked before execution. Missing,
empty, altered, malformed, incomplete, extra, or symlinked source sets
fail closed. The optional deterministic mechanism calls only the pinned
public DP allocator and independently checks its resulting wide line sums.

Run `python3 -B problems/prime-line-sums/code/cutoff2_wide_balance_experiment.py`.
Successful controls are not formal verification or independent proof of
the analytic inputs. A complete controller must still certify every
unchanged gate, all order and parameter jumps, and its exact source closure.
