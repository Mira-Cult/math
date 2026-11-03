# Complete classical cutoff at 311744

*Presentation copy: mathematical delimiters and equation labels are adapted for GitHub rendering. The unchanged, hash-bound source is in the [complete replay packet](../../../../packet/README.md).*


Coordinator and composition author: `/root`. This is an additive composition
of separately frozen components. The exact scientific revision, its source
closure and the complete composition require independent nonauthor review
before this proposed cutoff is accepted. No public note is changed.

## LC1. Statement and verification boundary

For every odd integer n>=311744, there exists an n-by-n square containing
exactly the first n² odd primes, each once, such that every row sum, every
column sum and both main diagonal sums are prime. Prime line sums may
repeat; equal line sums are not required. The first relevant odd order is
311745.

This is an unconditional classical construction. Rosser--Schoenfeld and
Bennett--Martin--O'Bryant--Rechnitzer remain imported analytic theorems,
including the published finite zero verification used by BMOR. The
project does not recompute that verification, assume RH above its finite
height, or prove the imports in a formal kernel. Its scripts certify
finite rational inequalities, outward enclosures and exact source identity.
The infinite construction and persistence arguments are conventional
mathematical proofs, assessed by independent nonauthor agent review.

Put v=log_2 n. The proof covers the following contiguous branches:

| Exact order conditions | Finite controller |
|---|---|
| n^4>=2^73 and n^8<2^147 | First BQ table, 73/4<=v<147/8 |
| n^8>=2^147 and n^2<2^37 | Second BQ table, 147/8<=v<37/2 |
| n^2>=2^37 and n^4<2^75 | First AN table, 37/2<=v<75/4 |
| n^4>=2^75 and n<2^19 | Second AN table, 75/4<=v<19 |
| n>=2^19 | Reviewed complete quality theorem at scientific 1dafa359f1ddeec43253058a0a5ab2e2151bd565 |

The integer comparisons

    311743^4 < 2^73 < 311744^4,
    339958^8 < 2^147 < 339959^8,
    370727^2 < 2^37 < 370728^2,
    440871^4 < 2^75 < 440872^4

prove the displayed boundary translations exactly. They also show there
is no uncovered odd integer between branches. All later orders use the
preserved complete theorem, with its full historical source closure.

## LC2. Coupled scales and original source domains

Use the prescribed notation


```math
X=p_{n^2+1},\quad T=\sum_{j=2}^{n^2+1}p_j,\quad
 m=T/n^2,\quad y=T/n,\quad
 E=\lceil\log_2X\rceil,\quad e=\lceil\log_2y\rceil.
```


Write u=log X. Unmarked logarithms are natural; the integer e is not
Euler's number. The baseline choices K=floor(n/E³) and D=y/e⁴ are
explicitly replaced in the new bands by K=floor(n/C) and D=y/5000.
BQ uses C=1365 and AN uses C=1280. This affects correction capacities
and prime target tolerances, not the pool or required lines.

The freshly specialized [OP](cutoff2_order18_pool.md) proves, from
n>=2^18 and the original prime-index and prime-count domains,


```math
n^2\lt X\lt n^3,\qquad .47X\lt m\lt .53X,\qquad
 u\gt 2v\log2+\log(2v\log2)\gt 28.
```


Its weighted seed pool contains more than .8748X/u primes in (X/8,X].
This is OP's polynomial comparison at u>=28; the older .8749 density
is not used below its u>=29 premise.

OP's before-ceiling envelopes are


```math
\log_2X\lt (58/25)v-1\quad(v\ge73/4),\qquad
 \log_2X\lt (463/200)v-1\quad(v\ge37/2).
```


Their derivation includes the full one-unit ceiling allowance before
taking E. Subtracting one from an arbitrary bound on E would not suffice.
Both controllers retain the index gain


```math
X/n^2\gt u-3/2
```


from the original upper prime-count theorem, instead of discarding the
logarithm. Each controller has its own certified lower affine bound on
u and upper affine bound on u over each complete branch.

## LC3. Entry progression supplies and the actual selected gap

Use [LZ](cutoff2_analytic_low_zero_band.md) with actual even moduli
g<=30, so phi(g)<=12. This is a cap on the chosen gap, not on E.
The two required profiles are:

| Orders | delta | Bin count N | Common extent N delta |
|---|---:|---:|---:|
| n^4>=2^73 | 1/1120 | 120 | 3/28 |
| n^2>=2^37 | 1/1344 | 144 | 3/28 |

The separate mean estimate puts every residue or reflected-bin center
between 79X/700 and 621X/700. LZ checks actual displaced endpoints,
including its full allowed displacement X/100, above log scale26 in
both profiles. Every requested interval lies strictly between2 and X;
all selected entry primes are therefore in the exact prescribed pool.

Each reduced class has at least delta X/[phi(g)u] primes in a centered
entry bin. Every bridge interval of length H>=X/512 inside [X/4,3X/4]
has at least H/[2phi(g)u] class primes. The global prefix class in
(X/8,X] has at least693X/[800phi(g)u] primes. These three error budgets
are separate and all pass; no interval borrows another's supply.

The analytic improvement keeps the signed boundary in the low-zero
partial summation. BMOR counts both signs with multiplicity, and


```math
\sum_{1\lt |\gamma|\le H}|\gamma|^{-1}
 =N(H)/H-N(1)+\int_1^H N(t)t^{-2}\,dt.
```


Combining the boundary with the small-zero contribution before bounding
N leaves one copy of N(1). LZ applies the primitive-conductor upper
majorant only after every remaining count coefficient is nonnegative.
Its reciprocal-zero caps, finite heights, higher-zero estimates and
prime-power removal are explicitly certified in their source domains.
The corrected primitive/imprimitive identity and omitted prime powers
remain paid. Fixed modulus bounds and decreasing error envelopes establish
the analytic whole tails independently of jumps in E.

The [SQ](cutoff2_seed_quality_experiment.md) finite matching argument,
with OP's new density, selects the gap and reduced lower-endpoint class.
Use the weights max(0,1-g/32) on the consecutive-prime path. One
alternating matching carries at least half the total weight and is
globally vertex-disjoint before its label is chosen. For every gap label
preassign its entire demand


```math
D_g=Q_s s_g+B_r/2+2Q_sJ_b,\quad Q_s=6(n+8),
 \quad B_r=4(n+1)\lceil\log_2(g/2)\rceil.
```


The BQ and AN certificates each check


```math
(.8748/u-7/256)X-1\gt 
 2\sum_{g=2,4,\ldots,30}\varphi(g)(1-g/32)D_g
```


over every order in their branches. All possible labels are paid, so
neither the gap nor its totient is assumed favorable. All seed primes
exceed30. Each deleted prime destroys at most one edge of the already
disjoint matching. The demand includes the complete bridge and residue
deletions before the surviving seed stages are chosen.

## LC4. Exact-total targets at their own scale

Apply LZ4 only on its stated band 2^18<=n<=2^19. It provides the dense
parity seed and every reduced-class target interval for D=y/5000.
This band has X<2^44, y<2^63, e<=63 and
L=ceil((693148/10^6)(e+1))<=45. The target's selected even modulus
is at most44, with phi at most20; its separate analytic endpoint
floor is39. From the lower index and mean inequalities, even the more
conservative endpoint3y/4 satisfies log(3y/4)>39.604248.
These facts are proved at the actual y scale, separately from entry
endpoints. The q=2 parity seed uses its own verified zeta height and
error budget. The target radius5000 is not silently extended above
order2^19.

Reapply the finite [parity target proof](cutoff2_target_parity.md) and
[dense-seed refinement](cutoff2_target_dense_seed.md) with these actual
supplies. OP invokes the size inequalities SO11--SO12 at integer bins
j>=17 and R<=5000, with fresh mean and index inputs. The exact base
inequalities are


```math
2^{17}\ge19(4\cdot17+4)^2,\qquad
 2^{51}\ge100000(4\cdot17+4)^2.
```


Their integer-bin induction establishes the complete list-length,
fine-grid and radius conditions. SO13's old literal log y>40 claim
is not imported below order19; LZ4 supplies the required fresh scale.
The dense-seed construction has L>=26 on this band.

For odd n, T is odd. The finite lemma gives exactly n odd prime row
targets with total T and exactly n odd prime column targets with total
T, all within D of y. Choose both prime diagonal targets independently
in that tolerance interval. Target values may repeat. Targets are chosen
before residue repair, so the construction does not require a prime in
a class forced by an already fixed square.

## LC5. Prefixes, residues, allocations and completion

The binary residue proof [BN](cutoff2_controller_binary_narrow.md)
represents every even correction modulo g by bounded nonnegative
coefficients on steps2,4,...,2^b, where b=ceil(log_2(g/2)). Its explicit
CRT choice makes both endpoint classes reduced. Its paths repair all
row and column residues with the exact-total compatibility; disjoint
rectangles repair both diagonals independently. It reserves exactly
B_r=4(n+1)b entries. A fixed class loses at most B_r/2 entries, because
the two classes of each bit pair are distinct, including the treatment
of g=2 with b=0.

The [adaptive prefix lemma](cutoff2_adaptive_prefix_experiment.md)
starts from the actual lower stock after the seeds and preselected
bridges have been paid. At stage j it uses M_j=M_start-2Q_sj, with a
fixed terminal shift X/(2 eta M_final). The certified stage counts
give enough growth to reach X/L. The source proof permits real lower
bounds for stock; all selected primes and stage counts are integers.
Each common-gap stage supplies z Q_s disjoint candidate pairs, then
keeps Q_s pairs in a single narrow midpoint bin. Unselected candidates
remain unused. BQ uses z=2 and AN uses z=4, paying the corresponding
full matching multiplicity. The certificate also pays the full table
cap even when selection stops early.

BN sorts the seed-pair midpoints into stages and bounds the combined
seed discrepancy independently of the number of stages. DP's exact
simultaneous group rounding allocates the narrowed common-growth
stages. Every assigned pair stays in its stage; its common difference
preserves all diagonal rectangle gaps and reservoir grids. Exact slot
cardinalities and total line incidence include both diagonals.

On the BQ branches only, apply [WB](cutoff2_wide_balance_experiment.md):
select every wide pair in a fresh equal-gap double block, including
ordinary pairs. The existing reflected-stock inequality supplies such
a block after every deletion set of size at most the total budget B;
no extra reserved entries or common-copy multiplicity is introduced.
Allocate all ordinary and diagonal blocks from one shared stage
population. The common stage mean cancels the former term proportional
to the number of wide stages. The remaining stochastic error is


```math
2\delta X\sqrt{(21dK+4)\log(8n+8)}.
```


The seed and wide allocations concern disjoint pairs and slots, with
their stage means unchanged. Choose an allocation meeting each separate
existence bound, successively. This does not add two one-half failure
probabilities and incorrectly infer a simultaneous success.

BQ proves the actual reserved fraction B/n²<=1/10. Its unused-prime
completion uses [QF](cutoff2_quantile_completion.md). Fix an unused
center first when necessary, costing at most X per line; every
remaining cell has at most three required incidences. Simultaneous
rounding over decreasing prime quantile widths gives error at most
X+6 sum W_j. Original prime-count bounds and the same adversarial
deletion budget control every W_j. With u>=28 and actual integer
depth at most37, QF gives a per-line error below50X. It explicitly
pays the possible center deletion, endpoints and all ceiling units.
It fills every remaining cell with every remaining input prime once.

AN deliberately retains its previously frozen DC completion allowance
114X and original wide centering invoice. It does not depend on BQ's
improvements. Its exact depth22 prefix and depth38 completion bounds
cover all ceiling jumps on its own order range.

## LC6. Geometry, capacities and complete order persistence

Both new controllers use degree6 and cut expansion26/25. The original
random-derangement graph proof is re-specialized at n=2^18, with fresh
small-cut, large-cut and conditioning bounds. The graph and integral
flow are finite existence arguments. They are not an assumption about
the behavior of a sampled graph.

All residue, bridge, prefix and reflected supplies refer to the same
pool. Their exact budgets charge adversarial deletions and all window
overlaps. Only proved class/side-specific savings are used. The full
reserved-entry count and placement inequalities ensure disjoint cell
supports, ordinary controls avoiding both diagonals, and independent
diagonal rectangles avoiding the opposite diagonal and center.

The centering invoices use the exact unused-pool mean cancellation,
including every prefix, residue, bridge, wide and completion term. The
baseline discrepancy plus the full target tolerance fits the cut-flow
capacity .999*(26/25) KX. Integer routing slack, K>=n/C-1, all fifteen
totients and the complete finite gap tables are checked. Integral flow
repairs rows and columns. The independent diagonal reservoirs then
repair both diagonal targets while preserving already fixed lines.

Fixed integer seed and growth caps remove those jumps inside each
branch. Rational lower/upper envelopes for n,u,X/n² and stock are valid
throughout each closed branch. The prefix and completion depths are
actual integer upper bounds, not differentiated ceilings. The weighted
matching invoice is a positive sum of convex smooth functions of v,
proved by the explicit log-convexity guard and positive denominators;
both endpoints are certified. Changes of E,e,K or the selected gap
therefore leave no uncovered orders.

## LC7. Reproducibility and dependency ledger

Run `code/verify_cutoff2_lower_campaign.py` with
`inputs/cutoff2_lower_campaign_constants.json`. Its default run checks
the complete source closure, reproduces all newly used components and
the complete reviewed order19 fallback, rebuilds the source-located
inequality ledger, and runs malformed-manifest, missing-file, substitution
and dependency-route controls. No private artifact or floating discovery
output is a proof input. The complete required-file set is explicit;
missing, empty, malformed, mismatched and symlinked sources fail.

The dependency graph keeps every new-band route separate from the
preserved upper tail. In particular, old target-scale reachability cannot
stand in for LZ4, the old weighted density cannot stand in for OP2, and
the original completion bound cannot stand in for QF. Ordinary proof
review, imported analytics, finite arithmetic and formal verification
are recorded as distinct categories. Formal verification is absent.

The separate finite witness family for all odd orders1 through201 is
useful computation but is not part of this infinite-tail proof and does
not bridge the remaining interval202 through311743.
