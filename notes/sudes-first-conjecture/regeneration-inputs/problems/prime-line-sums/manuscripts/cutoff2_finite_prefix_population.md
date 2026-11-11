# Finite common-gap prefix populations on orders 2400 through 3000

Author: `/root/prefix_balance_research`. This additive source proves a finite
prime-pair supply and a conditional balanced-allocation interface. It changes
no frozen controller, claim ID, analytic source, or public note. Independent
nonauthor review of its exact scientific revision is required. No square
cutoff, full-tail theorem, or formal-verification claim is made here.

The prescribed pool is the one in [PROBLEM.md](../PROBLEM.md). The balanced
pair-slot interface is stated explicitly below; its historical source is
[PB](cutoff2_prefix_balance_experiment.md), sections 1, 4--6. All logarithms
in this file are natural. A ``range'' means maximum minus minimum, not an
interval radius.

## FP1. Three alternative finite populations

Put

\[
 B=95\,000\,000,\qquad d=6,\qquad Q_*=d(3000+8)=18\,048,
 \qquad P=24.
\]

The prescribed gap sequence, indexed from zero, is

\[
 h_j=2^{j+1}\quad(0\le j\le23).
 \tag{FP1}
\]

There are three **alternative** populations. Profile U uses prime endpoints
in `(43,B]`. Profile C27 uses `[27,000,000,74,000,000]`, and profile C40
uses `[40,000,000,88,000,000]`.
For each profile the certificate deterministically produces, at every stage
j, an ordered list of exactly Q_* pairs

\[
 (a_{j,i},a_{j,i}+h_j),\qquad 0\le i<Q_*.
 \tag{FP2}
\]

Every endpoint is prime. All 866,304 endpoints are distinct **within a
profile**, including across different stages. Different profiles are not
jointly disjoint and must not be combined without a new check. Each list
is ordered by increasing lower endpoint. The companion input manifest
contains every stage's complete surviving candidate count, chosen window
index, endpoint extrema, exact range, endpoint sum and SHA-256 digest.
It also pins the concatenated retained lower-endpoint stream. Upper
endpoints are recovered by adding the prescribed gap.

For every integer `2400<=n<=3000`, put `Q(n)=6(n+8)`. Use exactly the first
Q(n) pairs of each stage. This gives distinct entries at every order in
the band, not a sample of orders. The retained entry count is

\[
 B_p(n)=2Q(n)P=288(n+8),
 \tag{FP3}
\]

from 693,504 at n=2400 to 866,304 at n=3000. Every omitted candidate and
every unused tail copy `i>=Q(n)` remains unreserved. The smaller-order
construction is allowed to leave entries unused by this component; they
are available for the subsequent completion of the prescribed pool.

The sieve certifies

\[
 \pi(95\,000\,000)=5\,489\,749.
 \tag{FP4}
\]

Consequently there are only 5,489,748 odd primes at most B, fewer than
`2400^2=5,760,000`. All the selected primes therefore belong to the first
n^2 odd primes at every n in the band. This implication uses the finite
prime count, not an imported prime-index estimate. The finite population
claim itself also applies to even n; only its future square application
will restrict to odd n.

These are protected populations: select their entries before any other
overlapping reservation, or prove that earlier selections avoid them.
Their existence after an arbitrary earlier deletion is **not** asserted.
Later supplies must pay the actual deletion count (FP3), unless a separate
interval or allocation argument proves that some of these entries cannot
deplete that supply.

## FP2. Sieve, matching, and minimum-range selection

The public checker uses a standard-library Eratosthenes sieve. Array entry
k represents `2k+1`. It marks 1 as nonprime and, for each surviving odd
`p<=floor(sqrt(B))`, marks the odd multiples from p^2 in steps 2p.
No prime is marked: every marked number has factor p and is at least p^2.
Every odd composite is marked, because it has a prime factor at most its
square root, and that factor survives until its marking pass. Prime 2 is
counted separately. This proves the complete finite count and primality
of every entry the selector can use. Small sieves and the base-prime
domain are also compared against direct trial division in the controls.

At each stage, enumerate every currently available pair `(a,a+h_j)`
whose two endpoints lie in that profile's interval. These pairs are
already a matching. Indeed `3` does not divide h_j. If two distinct
fixed-gap edges shared a vertex, the three vertices would be
`a,a+h_j,a+2h_j`; one is divisible by 3. All vertices exceed 43, so they
cannot all be prime. Thus a fixed-gap graph here has no component with
two edges. No greedy matching loss, maximum-matching assumption, or
probabilistic independence is involved.

Write the increasing candidate lower endpoints as
`c_0<...<c_(N-1)`. Provided `N>=Q_*`, choose the smallest index i attaining

\[
 \min_{0\le i\le N-Q_*}(c_{i+Q_*-1}-c_i).
 \tag{FP5}
\]

Retain exactly the Q_* candidates in that consecutive window, and mark
only their endpoints unavailable for later stages. The windows minimize
the range among all Q_*-element candidate subsets: any such subset with
smallest index i has largest index at least `i+Q_*-1`. Equal gaps make
the midpoint range exactly the lower-endpoint range. The leftmost-index
tie rule makes the full regeneration deterministic.

Deletion tests require each retained endpoint to be available immediately
before it is marked. Since all candidate edges at a stage are disjoint,
the available-prime count decreases by exactly `2Q_*` at every stage.
Unretained candidates are never marked merely because they were examined.
The final live-mask digest and the complete retained-stream digest are
checked in addition to each local count and pair-list digest.

## FP3. Exact measured supplies and ranges

The following counts are after all earlier retained stages in the same
profile have been removed. W_j is the full Q_*-pair midpoint range.

| j | gap | U candidates | U range | C27 candidates | C27 range |
|---:|---:|---:|---:|---:|---:|
|0|2|420754|2520960|197999|4031190|
|1|4|415204|3141780|193849|4134636|
|2|8|410116|3413748|189384|4157964|
|3|16|406789|3584670|186020|4189416|
|4|32|398733|3710664|179390|4291758|
|5|64|394337|3837180|174597|4323492|
|6|128|388944|3928638|169971|4300518|
|7|256|384196|3924690|165299|4365060|
|8|512|379157|3999810|159321|4396800|
|9|1024|374005|4103994|154911|4447200|
|10|2048|367869|4093968|149985|5065326|
|11|4096|364790|4173660|146619|4813332|
|12|8192|357033|4268328|138848|5401848|
|13|16384|352119|4304610|135829|5388996|
|14|32768|347530|4325892|131795|5543856|
|15|65536|342992|4406736|127217|5526474|
|16|131072|337496|4393980|122366|5740320|
|17|262144|331746|4434978|117845|6054876|
|18|524288|324538|4500948|111561|6476340|
|19|1048576|319290|4518924|106861|6882684|
|20|2097152|309171|4591650|99521|7068360|
|21|4194304|295352|4887984|91199|7639314|
|22|8388608|278999|4912776|77721|8636928|
|23|16777216|251656|4868016|59822|8577990|

For U,

\[
 \sum_jW_j^2=414\,426\,016\,843\,200,
 \qquad \max_jW_j=4\,912\,776.
 \tag{FP6}
\]

For C27,

\[
 \sum_jW_j^2=765\,704\,561\,939\,244,
 \qquad \max_jW_j=8\,636\,928.
 \tag{FP7}
\]

The higher central profile C40 has the following exact data.

| j | C40 candidates | C40 range |
|---:|---:|---:|
|0|196474|4232370|
|1|192634|4265376|
|2|188357|4306968|
|3|184703|4390740|
|4|177857|4412688|
|5|173557|4428126|
|6|168709|4429950|
|7|164363|4497000|
|8|158360|4460316|
|9|154267|4779768|
|10|149403|4967568|
|11|146296|5292210|
|12|138475|5465772|
|13|135287|5628810|
|14|131007|5700960|
|15|126505|5673390|
|16|121253|6068310|
|17|117282|6356292|
|18|112133|6474504|
|19|107068|7188720|
|20|99073|7347984|
|21|92489|7873260|
|22|80730|8127168|
|23|59304|8615460|

For C40, the squared ranges sum to 801,615,658,790,268 and their maximum
is 8,615,460. Every quantity is recomputed from the actual retained pairs,
not from a prime-density model. The alternatives trade fluctuation,
mean bias and possible deletion savings; no net controller improvement
follows from these population data alone.

The original exploration used 25 stages with gaps `2,2,4,...,2^24`, the
same endpoint intervals and the same Q_*. That reproducible rule retained
902,400 entries and covered through 33,554,432. Its allocation bounds at
n=3000 were 201,050,605 (U), 277,056,837 (C27), and 280,899,450 (C40).
The sharper complete-grid condition in FP4 removes the repeated gap,
saves 36,096 entries at Q_*, and gives the adopted 24-stage profiles.

During that 25-stage exploration, `[26,000,000,74,000,000]` also had enough
pairs, but raising its lower endpoint to 27,000,000 permits a simpler
conservative separation from later low wide windows. The trial
`[42,000,000,88,000,000]` had more fluctuation than the C40 alternative.
Neither abandoned profile nor any raw discovery binary is a certificate
dependency. All the adopted 24-stage populations regenerate from the
public standard-library checker and its exact input table.

## FP4. Complete grids and independent diagonal pairs

Each ordinary reservoir receives one pair from every stage. The subset
sums of its positive differences form the complete even grid

\[
 \{0,2,4,\ldots,2^{25}-2\}.
 \tag{FP8}
\]

Proof: before any stage the grid is `{0}`. At every stage the new gap
equals the previous total coverage plus 2. The shifted old grid begins
at the next even value, so its union with the old grid has no missing
even value. Summing (FP1) gives exactly `sum_(j=1)^24 2^j=2^25-2`.
This uses the sharp lattice condition `h<=coverage+2`; requiring
`h<=coverage` would unnecessarily force a repeated initial gap 2.

In the PB slot interface there are dn ordinary pair slots and 8d extra
pair slots per stage, altogether Q(n). Each diagonal has 2d rectangles
per stage, each receiving two different pairs of that stage's common
gap. Its designated-line differences therefore contain 2d copies of
the same complete sequence, yielding the complete even grid through
`2d*(2^25-2)`. All rectangles use distinct entries. Independent bijections
of the stage population to its labelled slots preserve these statements.

This source supplies entries and gap sequences, not a low-order graph
expansion theorem or a complete placement proof. A caller must supply
distinct cells with the PB incidence properties and preserve avoidance
of both diagonals by ordinary controls. It must also prove that the
subsequent bridge or wide differences extend (FP8), and that the final
flow and diagonal capacity reach the target box. Coverage `2^25-2` is
not being identified with X.

## FP5. Variance using every actual stage range

Assume a PB slot family at the selected n: on each ordinary row/column,
stage j has d ordinary weights 1 and d/2 ordinary weights 2. Across the
entire main family, that line meets at most one extra rectangle; its
extra pair weights total 2 and their squared weights total at most 4.
Each diagonal has 2d weights 1 at every stage. These are explicit
incidence premises, including the diagonal amplification; a mere
maximum-degree bound does not replace them.

Let `W_j(n)=a_(j,Q(n)-1)-a_(j,0)`, and let mu_j(n) be the actual mean
of the Q(n) retained pair midpoints. Uniformly permute each already
selected stage population among its labelled pair slots, independently
across stages. Selection itself was deterministic and need not have
independent supplies. The endpoint set and all gaps stay unchanged.

For a required line, expose positive-weight slots in decreasing order of
weight within each stage. If the exposed weight is w, its Doob increment
has coefficient `w-(remaining weight)/(remaining slots)` multiplying
the difference between the revealed midpoint and the preceding
remaining mean. This coefficient lies between 0 and w. Thus the
conditional range length is at most `w W_j(n)`. The elementary bounded
range exponential-moment inequality gives the two-sided bound

\[
 \Pr(|Z-\mathbb EZ|>t)\le2\exp(-2t^2/V(n)),\qquad
 V(n)=3d\sum_jW_j(n)^2+4\max_jW_j(n)^2.
 \tag{FP9}
\]

The diagonal squared-weight contribution is smaller. The single extra
rectangle is paid once across the entire family, not once per stage.
Union over all `2n+2` required lines shows that some simultaneous
allocation has error at most

\[
 u_p(n)=\sqrt{V(n)\log(8n+8)/2}.
 \tag{FP10}
\]

Indeed the failure probability is at most 1/2. This is an existence
argument for the allocations, not an assertion that a random trial
always succeeds. The weighted-permutation conditional-increment
identities and small exact expectations are checked separately.

Since Q(n) is increasing and the lists are ordered, every W_j(n) and
V(n) is nondecreasing on the entire integer band, including every change
of Q. At Q_*, the exact values are

| Profile | V(3000) | Uniform integer upper bound for u_p(n) |
|---|---:|---:|
|U|7556209775282304|195208873|
|C27|14081068216015128|266480449|
|C40|14725986462271224|272514584|

The certificate proves these integer upper bounds using rational log
enclosures and squared comparisons. It also checks every one of the 601
integer orders and records its exact V(n), actual prefix prime sum, and
entry count. At n=2500, the sharper allocation upper bounds are
161,131,405 for U and 219,249,215 for C27. No floating-point result is
used to certify these bounds. The order tables also expose each profile's
exact smallest and largest stage means and midpoints, so a caller can
compare mean and fluctuation costs together.

## FP6. Actual means and the completion invoice

The mean of the chosen narrow window, or its first Q(n) entries, need
not equal the mean of the candidate matching. Only the retained means
mu_j(n) may enter the controller. If S(n) is the sum of all retained
lower endpoints over the 24 stages, then

\[
 \sum_j\mu_j(n)=\frac{S(n)}{Q(n)}+2^{24}-1,
 \qquad \text{prefix prime sum}=2S(n)+Q(n)(2^{25}-2).
 \tag{FP11}
\]

These identities and the exact sums are checked for every order.
Write `m=T/n^2` and `A=sum_j(mu_j(n)-m)`. The total prefix deviation
from m is exactly 2Q(n)A. Its expected main contribution to every
required line is 2dA. A row or column meeting a prefix rectangle has
the additional expectation `2(mu_j(n)-m)` for that rectangle's stage.
The two diagonals have no such extra term.

For clarity, the full PB cancellation can be used in the following
explicit conditional form. Suppose all balanced main stages have
common count r on a required line and total entry count `r(n+8)`.
Let C_0 be the total number of other reserved entries, and let q be
the number of a line's reserved entries beyond r. Put
`N_0=n^2-r(n+8)-C_0>0`. Uniform completion by the actual unused pool
has prefix contribution `-2Q(n)A/N_0` to its per-entry mean displacement
from m. Its normalized absolute cost is exactly `|2Q(n)A|/(XN_0)`;
there is no need to replace it by a bound using the worst individual
stage mean. Uniform completion on the required line
adds the prefix mean contribution
`-(n-r-q)2Q(n)A/N_0`. Its sum with 2dA is exactly

\[
 \frac{2dA}{N_0}\big((n+8)q-C_0-8n\big).
 \tag{FP12}
\]

This is an algebraic identity, before any fluctuation estimate. It does
not replace the required completion discrepancy theorem. In the gap-two
case with no residue family, C_0=0 and q is 0 or 2 on rows/columns and
0 on the diagonals. If `beta X>=max_j|mu_j(n)-m|`, then the prefix's
expected completed-line contribution is bounded by

\[
 2\beta X+\frac{16dn|A|}{N_0}
 \le 2\beta X+\frac{16dnP\beta X}{N_0}.
 \tag{FP13}
\]

The first version retains the exact aggregate mean. The allocation
error (FP10), completion fluctuation, midpoint-orientation error, other
stage-family means, target tolerance, and flow capacities still have to
be paid separately. No numerical bound on m or X is assumed for FP13.

## FP7. Conditional separation benefits for the central profiles

The C27 endpoints lie in `[27,000,000,74,000,000]`.
Any later stock wholly below 27,000,000 or wholly above 74,000,000
is disjoint from this prefix. Its prefix deletion invoice is then zero.
Stocks intersecting the interval do not receive that saving.

More generally let J be any real interval, with its endpoint inclusion
conventions specified. The exact number of protected prefix entries in
J is

\[
 \sum_j\left(\#\{i<Q(n):a_{j,i}\in J\}
       +\#\{i<Q(n):a_{j,i}\in J-h_j\}\right).       \tag{FP15}
\]

The disjointness already proved prevents double counting. Each term can
be evaluated by two binary searches in the ordered lower-endpoint list.
The public function `protected_interval_count` accepts exact rational
endpoints and all four open/closed conventions. This gives an exact
prefix deletion invoice for interval prime stock, and a valid upper
invoice if a further residue restriction is imposed. All other earlier
deletions must still be paid separately. No independent-supply assumption
is made when the later interval is chosen adaptively.

For example, suppose a caller independently proves

\[
 \frac{121}{250}X\le m\le\frac{123}{250}X,
 \qquad97\,000\,000\le X\le165\,000\,000,
 \tag{FP14}
\]

and its lower wide window is entirely below `m-X/3`, while its upper
wide window is entirely above `m+X/3`. Exact arithmetic then gives

\[
 m-X/3\le(119/750)\,165\,000\,000=26\,180\,000
 <27\,000\,000,
\]

\[
 m+X/3\ge(613/750)\,97\,000\,000>74\,000\,000.
\]

Thus C27 cannot deplete those wide supplies. For C40 use instead the
stronger conditional lower bound `X>=108,000,000`: then
`(613/750)X>=88,272,000>88,000,000`, and the same upper estimate is below
40,000,000. This source checks that conditional arithmetic; it does
**not** establish these premises or (FP14) on the proposed
order band or import a larger-order mean theorem outside its domain.
The selector's exact pool inclusion (FP4) does not imply (FP14).

## FP8. Reproduction, controls, and remaining obligations

Run from a recovered source tree with Python 3.12 and its standard library:

```
python3 -B problems/prime-line-sums/code/cutoff2_finite_prefix_population.py
```

The required scientific closure consists of this manuscript, the checker,
its exact input manifest, PROBLEM.md and the pinned PB source. The checker
requires the complete nonempty file set and rejects malformed maps,
unknown keys, missing files, mismatched bytes, empty files, nonregular
files and symlink substitutions. It reconstructs the sieve and all
three profiles from scratch; no private binary, downloaded prime table,
compiled program, NumPy, or discovery output is needed. SHA-256 uses
four-byte little-endian lower endpoints in increasing stage order.

Controls include independent trial-division sieve comparisons, exact
minimum-window selection against exhaustive small subsets, repeated-gap
and different-gap prime fixtures, full ordinary and amplified diagonal
subset grids, disjoint pair/cell assignments on a small PB support,
weighted-permutation conditional increments, actual-mean cancellation,
all-order truncation, and deliberate failures of prime, gap, count,
disjointness, window, mean and source conditions. Their roles are to
check finite mechanisms and arithmetic. The universal sieve, allocation,
and cancellation arguments above remain conventional mathematics.

The numerical controller must still prove an applicable graph, all cell
packing, subsequent supplies after the correctly ordered reservations,
completion and target bounds, capacities and a contiguous upper handoff.
The low-order pair population by itself supplies none of those missing
premises. It is neither a constructed square nor a claim that the
remaining finite range of orders has been solved.
