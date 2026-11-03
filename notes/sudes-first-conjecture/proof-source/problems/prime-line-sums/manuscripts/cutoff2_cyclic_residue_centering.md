# Balanced binary residue cycles and a smaller completion remainder

*Presentation copy: mathematical delimiters and equation labels are adapted for GitHub rendering. The unchanged, hash-bound source is in the [complete replay packet](../../../../packet/README.md).*


Author: `/root/prefix_balance_research`. The fixed-closing-pair and
balanced-diagonal proposal is due to `/root/controller_redesign`.
The permutation-layer placement, exact cell counts, and smaller regular
factor remainder below are the resulting refinements. This additive
component changes no frozen source and asserts no numerical square
cutoff. Its exact revision requires independent nonauthor review.

The finite dependencies are [BN](cutoff2_controller_binary_narrow.md),
[BR](cutoff2_binary_repair_bound.md),
[PB](cutoff2_prefix_balance_experiment.md),
[RP](cutoff2_rectangle_packing.md),
[CS](cutoff2_target_seed_separation.md), and
[RF](cutoff2_regular_factor_completion.md). No new analytic theorem is
imported. In particular all prime supplies and RF's central-stock
estimate retain their stated hypotheses and source domains.

## CY1. Prime pairs, bits, and unchanged supplies

Let n>=9 be odd, g>=2 even, h=g/2,
b=ceil(log_2 h), and r=floor(log_2 h). Both b and r are zero when h=1.
The j-th binary difference is delta_j=2^(j+1), for 0<=j<b.
Assume the same reduced-class supplies and disjoint-pair selection
hypotheses as BN, now paying the complete revised entry count below.
The lower and upper entry intervals are


```math
[m-X/4-\delta X,m-X/4+\delta X],\qquad
 [m+X/4-\delta X,m+X/4+\delta X],
 \quad 0\le\delta\lt 1/4.                                  \qquad\text{(CY1)}
```


Every pair has one lower and one upper entry, with positive difference
congruent to delta_j modulo g. The actual gaps lie in
[(1/2-2delta)X,(1/2+2delta)X]. The two pairs inside a diagonal
rectangle have the same actual gap and are disjoint.

For each bit, reserve n pairs for a directed row cycle
0->1->...->n-1->0 and n pairs for its column analogue. The closing
edge n-1->0 is fixed and is never switched. The other n-1 edges are
the original controllable path. Relative to BN there is exactly one
extra pair per bit in each orientation, hence 4b extra entries.
The two diagonal families still contain b rectangles each. Therefore


```math
B_r=4(n+2)b.                    \qquad\text{(CY2)}
```


For a fixed reduced class, every pair contains at most one member of
that class, and every double-pair rectangle at most two. The entire
family therefore uses at most B_r/2 primes of any fixed class. Each
side interval contains exactly B_r/2 entries. Every global pooled
stock must still pay all B_r entries.

All residue selections are sequential after previous deletions. If
H primes remain in each required class and H^2>ceil(X/g), the same
BN difference pigeonhole supplies two representations of one gap;
equal positive differences across the disjoint side intervals have
disjoint endpoints. The closing pairs need only single representations.
No count is reduced by assuming disjoint supplies.

CS's class avoidance is unchanged. For g>=8 every bit's two classes
can avoid the selected seed class, including the closing pairs.
For g=4,6 the seed-matching deletion charge becomes B_r/2=2(n+2)b.
For g=2 there are no residue entries. Bridge class avoidance and all
nonresidue deletion charges remain separate and unchanged.

## CY2. Place each residue cycle as a permutation layer

Place all main and residue diagonal rectangles jointly by RP first.
Let S=P_0+J_b+7K be the actual number of main stages and put
r_0=2dS. Their ordinary cells remain off both diagonals, with exactly
r_0 cells on every row and column. The actual rectangle count is


```math
J_{\rm rect}=4dS+2b.                 \qquad\text{(CY3)}
```


Use RP's explicit placement, whose rectangle rows and columns are
all distinct and avoid the central row and column. Its designated
diagonal cells are distinct and its other three cells avoid both
diagonals. Require J_rect>=3 and 2J_rect+1<=n.

For a row-cycle bit, use the derangement pi(i)=i+1 mod n.
Allocate each edge i->pi(i) to a column f(i), with f a bijection.
If the current row and column load is at most L, an edge forbids at
most 2L+4 columns: occupied cells at either endpoint and both diagonals.
A column forbids at most 2L+4 edges, because any occupied row is incident
with at most two cycle edges and its two diagonal positions exclude at
most four more. Thus n>4L+8 gives minimum allowed degree greater than
n/2 and a perfect matching by the Hall argument in PB section4.

This places one pair in each column and one incoming and one outgoing
entry in each row. The layer adds exactly two cells to every row and
column. Transpose the construction for each column-cycle bit. Previous
occupied cells are forbidden explicitly, so all pairs are mutually
disjoint and avoid every diagonal and rectangle.

After all 2b layers, every row and column has exactly 4b ordinary
residue cells. Continue with PB's usual ordinary main layers. A valid
upper load and its sufficient placement gate are


```math
L=2d(P+J_b+7K)+4b+2,\qquad n\gt 4L+8,\quad P_0\le P.       \qquad\text{(CY4)}
```


Every partial pass has load at most this final upper bound. CY4 also
implies RP's packing gate, since its right side exceeds
2[4d(P+J_b+7K)+2b]+1 by 12b+15. Both the improved local count and the
global count CY2 are required; adding fixed pairs to an arbitrary old
path placement would not establish the exact 4b count.

## CY3. Initial centering and arbitrary modular repairs

On every directed cycle edge put the upper entry at its source and
the lower entry at its target, including the fixed closing edge.
This retains BN and BR's sign convention. At each row vertex the
incoming and outgoing entries of one row-cycle bit are respectively
lower and upper. Its column-cycle contribution is an entire lower-upper
pair. Therefore each row and column has exactly 2b lower and 2b upper
ordinary residue entries. Their signed quarter-X offsets cancel.

A diagonal rectangle has template


```math
\begin{pmatrix}a&a+\lambda\\
                              c+\lambda&c\end{pmatrix}. \qquad\text{(CY5)}
```


Every row and column of it contains one lower and one upper entry,
before or after its double swap. As at most one joint rectangle meets
a row or column, its additional residue error is at most 2delta X.
The entire initial row/column residue deviation from its count times m
is consequently at most delta(4b+2)X.

For each main diagonal, initially flip exactly the lowest floor(b/2)
bit rectangles. The designated diagonal values then have floor(b/2)
upper entries and the other b-floor(b/2) lower entries. Its initial
deviation has absolute value at most
[(b mod 2)/4+b delta]X. A common initial residue allowance is therefore


```math
u_{\rm initial}=
 \begin{cases}
 0,&b=0,\\
 \max\{\delta(4b+2),(b\bmod2)/4+b\delta\},&b\gt 0 .
 \end{cases}                                            \qquad\text{(CY6)}
```


The ordinary target residues remain arbitrary subject to their exact
total compatibility. For desired half-corrections v_i modulo h, with
sum_i v_i=0 modulo h, choose
k_i=-sum_{t<=i}v_t modulo h in [0,h-1], for 0<=i<n-1.
Set the fixed closing coefficient k_(n-1)=0. Switch the binary digits
of k_i on the controllable edges. At vertex i the change is
A_(i-1)-A_i, where A_(n-1)=0. It is congruent to 2v_i modulo g,
including both endpoints, and its exact total is zero. Row controls
preserve every column; column controls preserve every row. Both avoid
the diagonals.

Every k<h has at most r nonzero digits, as proved in BR. Consequently
0<=A_i<=r(1/2+2delta)X, and the signed difference at a vertex has
absolute value at most the same bound.

For a diagonal let
u_0=2^floor(b/2)-1 be its initial bit state. This lies in [0,h-1]:
floor(b/2)<=r and 2^r-1<h. For a desired half-correction v, take
u=(u_0+v) modulo h in [0,h-1] and change the state from u_0 to u,
flipping exactly the differing bits. If S(u) is the sum of the
actual positive gaps selected by u, its change is S(u)-S(u_0).
Both numbers lie in [0,r(1/2+2delta)X]. Thus the same BR bound


```math
r(1/2+2\delta)X                      \qquad\text{(CY7)}
```


holds although some rectangles now reverse their initial switch.
Every row, column, and the opposite diagonal remains fixed.
The initial-state integer u_0 need not itself be a target residue.

Thus CY6 replaces the old gamma(6b+2) term, while CY7 retains BR's
repair bound. All controls are permutations of their own previously
reserved entries. The exact prime pool and every target total persist.

## CY4. The global and per-line mean invoices

The total residue sum differs from B_r m by at most delta B_r X:
the family is still a union of lower-upper pairs, each with midpoint
within delta X of m. Initial and final orientations do not change
that total. The global unused-pool mean correction for residues remains
delta n B_r X/(n^2-B), with the new full B_r.

PB's main stage mean cancellation remains exact. With actual reserved
count B_actual=r_0(n+8)+B_r and N_0=n^2-B_actual, a row or column has
r_0+q reserved cells with q=4b+e, e in {0,2}; a diagonal has q=b.
For a common-stage mean sum A, its ordinary reference plus completion
mean shift is


```math
\frac{2dA}{N_0}\{(n+8)q-B_r-8n\}.                      \qquad\text{(CY8)}
```


The coefficients inside braces are exactly


```math
24b+e(n+8)-8n \quad\hbox{or}\quad -(3b+8)n.              \qquad\text{(CY9)}
```


For n>=9 their absolute values are at most (3b+8)n.
For the row/column expressions the lower endpoint is at least -8n;
the upper comparison follows from
3b(n-8)+14n-16>=0. The diagonal attains the displayed envelope.
Thus a shared prefix or wide mean term previously paying B_r+8n
in PB/WB's corresponding identity may instead pay


```math
(3b+8)n.                    \qquad\text{(CY10)}
```


The numerator change does not remove the separate residue global-mean
charge, main rectangle midpoint errors, or allocation discrepancies.
Using B>=B_actual in the positive denominator is still conservative.
The improved RF count below is a completion parameter; it does not
replace r_0 by r_0+4b inside the main-stage cancellation identity.

## CY5. The exact post-diagonal support

Retain RF's hypotheses for the center and diagonal preassignment, including
B<=n^2/4, its exact-pool construction, and its mean-shift bounds. It adds
at most 3X error relative to the original completion expectation on a
row or column, and at most 3X/2 on either diagonal.

Set rho=r_0+4b, the exact ordinary reserved-cell count per row and
column. After both diagonals are completely assigned, every row's
occupied count is rho+q_i, and likewise every column's, where:

* the central row and column have q=1;
* a noncentral line meeting no rectangle has q=2;
* a rectangle line containing its designated diagonal cell has q=3;
* its other parallel line has q=4.

These statements use RP's distinct rows and columns and its explicit
avoidance of the central row and column. Every rectangle has one line
of each of the last two types in each orientation. There are exactly
J_rect rows with q=4 and exactly J_rect columns with q=4.

Require


```math
\rho+4\le n/4.                 \qquad\text{(CY11)}
```


CY4 already implies this with the actual P_0. The remaining degrees
lie in [n-rho-4,n-rho-1], and all remaining cells avoid both diagonals.

Remove for the moment one available edge incident with the central row
whose column has q<=3, and one incident with the central column whose
row has q<=3. Such edges exist: each center vertex has degree
n-rho-1>=3n/4+3, while at most J_rect< n/2 opposite vertices have q=4.
The removed edges are distinct and their other endpoints are noncentral.
Their removal raises each center q to2 and the other two endpoint
q values by one, never above4. The trimmed graph therefore has degrees
in [n-rho-4,n-rho-2].

Apply RF1 with minimum-degree parameter n-rho-4>=3n/4 and Delta=2.
It supplies a positive
regular factor of degree


```math
k=n-\rho-5.                   \qquad\text{(CY12)}
```


This factor is also a subgraph of the original residual support.
Each original vertex has at most4 edges outside it, including the two
temporarily removed edges. Those cells are filled in the completion;
they are not discarded or added to the reservation invoice.

## CY6. Exact exceptional stock and completion allowance

The ordinary reservations occupy rho n cells. The J_rect rectangles
occupy 4J_rect more, including exactly J_rect diagonal cells.
Completing the diagonal union adds 2n-1-J_rect cells. The number of
still-empty cells is therefore exactly


```math
N=n^2-\rho n-3J_{\rm rect}-2n+1.
```


For the factor CY12 its complement has


```math
T=N-kn=3n-3J_{\rm rect}+1\le3n+1.                     \qquad\text{(CY13)}
```


In RF2 choose exactly T central unused primes for these cells.
The maximum local exceptional degree is4. The proof of RF2 gives
error less than [1+(4+T/n)epsilon]X from the post-diagonal unused
mean: 4epsilon X for a local exceptional line, T epsilon X/n for
the factor mean shift, and less than X for the sorted matching blocks.
After paying the preceding 3X preassignment error, a uniform completion
allowance is


```math
[4+(7+1/n)\epsilon]X.                \qquad\text{(CY14)}
```


The sharper T/n can be retained if the actual rectangle count is known.
Both diagonals keep their smaller preceding allowance.

RF's mean-location bound sigma remains unchanged, using the new B_r
and total B. Retain its separation condition
sigma+epsilon<1/4-w and its analytic endpoint and source-domain
hypotheses. Then the central interval loses no wide or residue entry.
It pays at most B_p+B_b+2n previous deletions and needs at most3n+1
exceptional values. Hence RF's existing raw central count suffices if


```math
\frac{2\epsilon X-(1036/125)\sqrt X}{\log X}
                       \gt  B_p+B_b+5n+1.                \qquad\text{(CY15)}
```


CY15 uses exactly the analytic interface already stated in RF; this
project does not independently prove its imported source computation.
Every central and factor entry is taken from the remaining prescribed
pool and used once. The later modular and main flow repairs take
place in their disjoint reserved cells as before.

## CY7. Complete substitution list and proof boundary

A controller using this component must make all of these coupled
changes, with its pointwise integer b and actual executed main stages:

| Quantity | Revised sufficient invoice |
|---|---|
| Residue entries | B_r=4(n+2)b |
| Fixed-class or one-side residue deletion | B_r/2 |
| CS seed deletion for g=4,6 | 2(n+2)b |
| Joint rectangles | 4d(P+J_b+7K)+2b, unchanged |
| Maximum occupied load | 2d(P+J_b+7K)+4b+2 |
| Initial residue centering | CY6 |
| Later modular repair | r(1/2+2delta), unchanged from BR |
| Shared main mean coefficient | (3b+8)n in CY8 |
| RF density | actual r_0+4b+4<=n/4 |
| RF central exceptional stock | at most3n+1 entries |
| RF all-line completion | CY14 |

All other analytic, target, seed, common-batch, flow, and disjointness
hypotheses remain required. In particular the extra closing pairs
must be selected and paid before the subsequent supplies are invoked.
The new placement is essential; it is not an estimate for an unchanged
arbitrary path placement.

The adjacent exact checker exercises the binary states and signed
transfers, the matching placement after every occupied pass, both
diagonal templates, the exact cell/entry counts, the center trim and
regular factor, and the original-reference mean identities. A complete
first-n^2-odd-prime fixture verifies entries, classes, initial lower-upper
balance, all residue repair effects and both independent diagonals.
It does not assert prime line sums for that fixture.

The source manifest has a fixed required-file set and is checked before
the controls. Negative tests attack orientations, omitted closing edges,
bad binary initial states, cell collisions, the center trim, underpaid
stock, and incomplete or altered source manifests. The finite program
does not establish analytic prime counts, a numerical cutoff, or formal
verification. The universal finite arguments are CY1--CY6 and their
named conventional dependencies; exact-revision independent review
remains necessary.
