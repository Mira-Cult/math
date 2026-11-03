# Complete classical prime-line tail from odd order 2001

*Presentation copy: mathematical delimiters and equation labels are adapted for GitHub rendering. The unchanged, hash-bound source is in the [complete replay packet](../../../../packet/README.md).*


Composition author and coordinator: `/root`. This additive theorem uses the
exact bounded sources frozen at scientific revision
`10cb5da79f1296c9d41a580e2d0841bc0102bb23` and the preserved complete
311744 theorem at `42e42804c6174ebaa4c2fb23ade104989aa86874`.
The present composition has its own scientific freeze and independent
nonauthor review; component reviews do not replace that obligation.
The public note is unchanged.

## T2001.1. Statement and exact partition

For every odd integer **n>=2001**, there exists an n-by-n square containing
exactly the first n² odd primes, each once, in which every row sum, every
column sum, and both main diagonal sums are prime. The prime line sums
may repeat. No equality of line sums is required.

The following table is a disjoint cover of the odd integers in the tail.
The upper endpoint in each finite row is its last odd integer.

| Odd orders | Exact defining condition | Canonical construction |
|---|---|---|
| 2001–19483 | 2001<=n<=19483 | [FC2K](cutoff2_controller_finite2001.md) |
| 19485–27553 | 2^57<=n^4<2^59 | [FW](cutoff2_controller_far_wide.md) |
| 27555–35733 | 2^59<=n^4 and n^8<2^121 | [EW](cutoff2_controller_early_wide.md) |
| 35735–38967 | 2^121<=n^8 and n^4<2^61 | [NC](cutoff2_controller_narrowest.md) |
| 38969–46339 | 2^61<=n^4 and n^2<2^31 | [SC](cutoff2_controller_stratified.md) |
| 46341–55107 | 2^31<=n^2 and n^4<2^63 | [GP](cutoff2_controller_gap_profiles.md) |
| 55109–65535 | 2^63<=n^4 and n<2^16 | [CF](cutoff2_controller_factor.md) |
| 65537–92681 | 2^16<=n and n^2<2^33 | [WC](cutoff2_controller_wheel.md) |
| 92683–262143 | 2^33<=n^2 and n<2^18 | [BCM](cutoff2_controller_bounded.md) |
| 262145–311743 | 2^18<=n and n^4<2^73 | [MC18](cutoff2_controller_multiclass.md) |
| n>=311745 | n odd and n>=311744 | [complete LC theorem](cutoff2_lower_campaign_theorem.md) |

The certificate compares the integer powers at both sides of every displayed
odd boundary. For example, `19483^4<2^57<19485^4` and
`311743^4<2^73<311745^4`. It also checks each internal rational-logarithmic
table boundary by integer powers. Positive integer powers are strictly
increasing, so these comparisons prove the entire partition, not just its
endpoints. There is no uncovered odd integer and no inference from isolated
successful orders. No square is transferred from one order to another.

## T2001.2. Common objects and the logical composition

In every row use the same definitions


```math
X=p_{n^2+1},\qquad T=\sum_{j=2}^{n^2+1}p_j,\qquad
 m=T/n^2,\qquad y=T/n,\qquad
 E=\lceil\log_2X\rceil,\quad e=\lceil\log_2y\rceil.
```


Analytic logarithms are natural. The symbol e denotes an integer ceiling,
not Euler's number. The original K=floor(n/E³), D=y/e⁴ are not premises of
the new bands: each controller states and verifies its replacement K and
target tolerance. In FC2K, K=5 or6 and the target tolerance is X/1000;
elsewhere K=floor(n/C) with an explicit, sometimes gap-dependent, integer C
and D=y/R. These changes do not change the prescribed input pool.

For each fixed odd n choose its unique row in the table. Its prime-index
and mean inputs, progression supplies, target construction, graph, disjoint
reservations, completion, and integer routing are supplied by the sources
listed below and by the explicit dependency manifest. Thus all premises of
that row's conventional construction are satisfied at that same n,X,T,m,y.
Its conclusion is exactly T2001.1. The LC row already includes its complete
unbounded continuation; it is not a conditional controller assumed to work
outside its domain. Taking these cases proves T2001.1.

The substantive bounded proofs remain in their canonical manuscripts.
The present proof supplies the missing case composition and rechecks its
actual source routes. The machine-readable ledger distinguishes conventional
lemmas, imported analytic theorems, exact finite data, and arithmetic gates.
It binds the complete canonical target sources even where a controller's
executable helper closure alone would not include them.

## T2001.3. Source domains and targets, by band

The analytic sources are classical and unconditional. Rosser--Schoenfeld's
original prime-index inequalities are applied to n²+1 in their stated
domain. Bennett--Martin--O'Bryant--Rechnitzer (BMOR), Theorem1.9 and
definition(1.18), printed pp.434–435, supplies the bounded-argument entry
estimates. Its finite verification is an **imported published result**, not
a computation repeated by this project. Montgomery--Vaughan's Theorem2,
equation(1.10), printed p.121, supplies the short-progression upper estimate
only in the prefix phases which explicitly invoke it.

The larger-scale target sources use the primitive-correct classical explicit
formula and its verified-height estimates, with signed exceptional-zero
contributions and omitted prime powers paid as in the preserved sources.
There is no RH or quasi-RH assumption. Inclusion of historical alternative
files in a preserved source closure does not select their alternative route.

Entry primes and target primes have different scales. The relevant target
routes are as follows; the target modulus is independent of the entry gap.

| Controller | Exact-total target provider | Tolerance |
|---|---|---|
| FC2K | [FTT](cutoff2_finite_target_table.md): `(n-2)q+p+r=T`, all three prime, for every listed order | X/1000 |
| FW | [T75](cutoff2_target_below1475.md), four adjacent bands | y/R, R=1240,1390,1550,1730 |
| EW | [TB](cutoff2_target_below15.md), three adjacent bands | R=1920,2100,2300 |
| NC | [TE](cutoff2_target_local_extension.md), both actual `(e,L)` cases | R=2550 |
| SC | [TL](cutoff2_target_local_band.md) through v=123/8; [DT](cutoff2_target_density_tradeoff.md) thereafter | R=2800,2800,1800 |
| GP | DT from v=31/2 | R=2200 |
| CF | Its own CF1 specialization of [S18](cutoff2_analytic_sub18_band.md) | R=1050 |
| WC | S18 bounded target profile beginning at v=16 | R=1300 |
| BCM | S18 bounded target profile beginning at v=33/2 | R=2200 |
| MC18 | [LZ4](cutoff2_analytic_low_zero_band.md), with [OP](cutoff2_order18_pool.md) finite size conditions | R=5000 |

All non-FTT rows use the canonical [parity target proof](cutoff2_target_parity.md)
and [dense-seed refinement](cutoff2_target_dense_seed.md), with the explicitly
stated changes to density, selected modulus, finite grid and list length.
Each supplies exactly n odd prime targets of total T for rows and columns,
and permitted prime targets for the two diagonals. Lists and diagonal target
values may coincide. They are chosen before the line residues are fixed.

CF does not use DT's larger R. Its separate exact checks establish target
endpoint logarithm at least1741/50, parity endpoint at least701/20, moduli
through42 with totient at most18, and the actual finite target list and grid
inequalities. WC and BCM stay within their respective S18 target profiles;
MC18 stays within LZ4's order interval [2^18,2^19]. No uniform target statement
is extended beyond its source domain.

For WC through GP, the actual mean and index interfaces are
`.487X<m<.492X` and `X/n²>log X-9/8` on their separately proved logarithmic
scale domains. NC uses TE's sharper actual scale interval, rather than a
looser controller envelope, to justify its raw density. EW and FW use the
lower mean bound .486 from TB and T75. Their real entry endpoints and
moduli satisfy the original BMOR bounded domains. FC2K uses exact X,T from
its finite table, with X<10^10; its modulus-two counts are the sum of the
two reduced modulus-four classes, both within the printed q=4 domain.
The q=2 reduction is an interval prime count, not an invalid identity of
primitive and imprimitive character explicit formulas.

The 311744 predecessor, including every older scale translation and
all-odd infinite-tail argument, is preserved byte for byte. Its entire
source manifest is required, not a pointer to a missing private artifact.

## T2001.4. Allocation, depletion and finite mechanisms

All controllers retain disjoint entry positions and select actual unused
primes. Their midpoint, interval and residue supplies are charged against
the correct deletion sets, including earlier adaptive choices. The degree
six graphs are re-specialized from their actual entropy inequalities at
each smaller order, not invoked under an obsolete larger-order premise.
Integer capacities and cut expansion repair all row and column demands;
independent diagonal rectangles preserve the other lines. Targets have
the same total T, so the required zero-total flow compatibility is exact.

The intermediate bands progressively use multiclass growth, exact wheel
windows, actual gap-dependent totients and demands, regular-factor
completion, stratified seed groups, cyclic residue layouts, diagonal
preallocation and early wide reservations. Their stock equations keep
all retained entries. In particular, early wide reservations are charged
in the subsequent growth stock even when they are absent from the earlier
wide-selection depletion. No common prime supply is treated as independent
copies. Finite twin seeds in FW are a single explicitly counted matching
below2^30 which is inside the prescribed pool for the whole FW band;
no all-scale twin-prime statement is used.

For FC2K, [FPF](cutoff2_finite_prefix_family.md) gives five alternative
explicit stage populations, with gaps `2,4,...,2^P`. For the actual n retain
exactly Q=6(n+8) pairs from each stage of its selected population. Only one
population is used at a time. Its full prefix is protected first, its
actual midpoint statistics are computed, and its exact intersections
with later intervals are counted. The initial even grid is complete
through `2^(P+1)-2`. There are no residue gadgets because g=2 already
matches every odd target and line sum.

The FC2K bridge lemma counts its actual even-difference span. The wide
lemma keeps one fixed reflected partition: selecting a pair in one cell
decreases the sum of opposing minimum side counts by exactly one. This
justifies the smaller stock depletion while still charging both input
entries in the full reservation budget. Equal-gap blocks remain disjoint.

[CC](cutoff2_central_completion.md) works with the actual unused mean,
an explicitly bounded reference interval, and separately verified outer
and whole central stocks. Its completion error is


```math
X+\big[(5+T_{ex}/n)(1+\kappa_c)+3/n\big]\varepsilon X,
 \qquad T_{ex}=3n-3J_{rect}+1.
```


The graph degree is6, its expansion is199/200, and the large-cut estimate
uses decay1/34 from n=2001. FC2K explicitly checks that the diagonal
capacity requires only `2d>=199/200`; it does not import an unnecessary
older simplification that the expansion exceed1. FTT's exact target
deviation, every midpoint and completion contribution, and every integer
capacity are included in the final demand-box inequality.

These details are conventional finite proofs with source-bound arithmetic
certificates. A passing arithmetic script alone is not a substitute for
the proofs of matching, concentration, completion, or integral flow.

## T2001.5. Floors, ceilings and the infinite tail

FC2K checks each of the **8742 consecutive odd orders** from2001 through19483.
Its finite table contains exact X,T and prime certificates for the targets.
The prefix sieve and the complete target prefix sieve are replayed from
public C++17 source. No floating-point acceptance or extrapolation is used.
Every epsilon-table transition, K change and bridge count is evaluated at
the actual integer n. Rational endpoint inclusion is treated exactly.

The other finite bands use exact integer roots of rational powers of2,
fixed integer stage and recipe counts on closed parameter cells, and
pointwise bounds such as `floor(n/C)>=n(1-C/n0)/C`. Their before-ceiling
prime-index bounds pay the full ceiling unit before taking E. Analytic
scale monotonicity is proved for smooth envelopes that bound every actual
rounded value; no derivative is passed through an unexamined rounding
jump. Graph-tail and seed-budget persistence have their own hypotheses.

Above311744 the preserved complete theorem supplies the entire remaining
infinite tail. Thus the conclusion is about every odd n>=2001, with no
missing finite interval or subsequence restriction.

## T2001.6. Reproduction and limits of the certificate

Run the following from a source export containing the complete manifest:

```sh
python3 -B problems/prime-line-sums/code/verify_cutoff2_tail2001.py
```

Python's standard library and a C++17 compiler are required. The default
command validates the complete strict source set, regenerates the located
inequality ledger, checks every branch and target route, runs all ten
bounded controller certificates and the full preserved311744 certificate,
and exercises malformed-input and physical-file negative controls.
`--composition-only` omits component execution and reports a different,
strictly weaker status. It is not the full reproduction command.

The input manifest, component inputs, exact finite prime data and every
needed proof and checker source are public and hash-bound. Missing, empty,
malformed, extra or mismatched source maps are rejected. Sources outside
the export are not silently supplied. The proof still imports the named
classical analytic theorems. Independent agent review is conventional
review, not external referee acceptance or end-to-end kernel verification.
Finite squares below2001 are a separate obligation; T2001.1 does not
assert them merely because the remaining range is small.
