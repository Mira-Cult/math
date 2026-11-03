# Full signed-line prime hypercubes in dimension four

Composition author: `/root`. The component authors and shared contributions
are identified in their canonical sources below. This is a conventional
mathematical proof, pending independent review at the opening scientific
checkpoint. No kernel verification, numerical threshold, or priority claim
is asserted. All labels are manuscript-local; no accepted cube or square
statement is modified.

## 1. Exact theorem and dependency order

**Theorem SC4.** There is an integer `N_4` such that for every odd integer
`n>=N_4`, the first `n^4` odd primes admit a bijective placement in `[n]^4`
for which every full signed-coordinate line has prime sum. For `n>=3` this
is exactly

\[
                     4n^3+12n^2+16n+8
\]

distinct lines: four axis families, twelve two-coordinate families, sixteen
three-coordinate families, and eight full diagonals. The separate singleton
case is `[3]`. Repeated line sums are allowed. Section sums are not required
to be prime. The pool is exactly `{p_2,...,p_(n^4+1)}`, with no omissions,
repetitions, extra prime, or change of indexing.

The proof factors through a physical universal theorem:

**Theorem USC4.** Write `X=p_(n^4+1)`, `T=sum_(j=2)^(n^4+1) p_j`,
`mu=T/n^3`, and `K_0=ceil(n^(3/5))`. For every sufficiently large odd `n`,
every odd integer full signed-line target vector satisfying the exact
compatibility equations of SI4, with each directional axis total `T` and
each coordinate within `K_0X` of `mu`, is realized by a permutation of that
exact pool.

The canonical proof sources, in logical order, are:

| Obligation | Canonical source and result | What it supplies |
|---|---|---|
| Exact geometry and integer compatibility | [hyper4_incidence.md](hyper4_incidence.md), SI4 | All eventual equations, saturated image, odd lifts, explicit integer generators |
| Prime targets | [hyper4_targets.md](hyper4_targets.md), SPT4 | A structured compatible prime vector, exact total `T`, displacement at most `mu^(3/5)` |
| Actual axis permutation | [hyper4_axis.md](hyper4_axis.md), U4/AP4 | Five physical correction levels, grouped fresh-pair supply, axis packing and preserved-line bounds |
| Extra permutation stages | [hyper4_trades.md](hyper4_trades.md), PT/EP4 | Eight-pair and compound stages, global disjoint placement, residue routing, descending correction |
| Joint baseline and final margins | Sections 2--5 here | Simultaneous centering, common depletion budget, full composition and entire odd tail |

SI4's integer lift is used to identify compatibility; it is never substituted
for U4's physical arrangement. SPT4 is a target construction, not an array.
EP4 is needed even after the bounded integer solver is known: its prime pairs
and cells must be physically disjoint. The graph and analytic imports are pinned
in U4 and SPT4 to the reviewed PR79/PR77 sources, not to later cutoff work.

## 2. Common scales and complete resource table

Choose once and for all the fixed graph degree, expansion constants, marker
caps and placement cap in the component sources. Put

\[
 K_j=\lceil n^{(15+j)/25}\rceil\quad(0\le j\le4),
 \qquad(K_5,K_6,K_7)
   =(\lceil n^{.77}\rceil,\lceil n^{.78}\rceil,\lceil n^{.79}\rceil),
 \qquad\delta=n^{-1/5}.                              \tag{HC1}
\]

Let `F=ceil(100 log X)`,
`P=ceil(4096F^2)+32F ceil(log_2 X)`, and `Q_*=2^40 n^3K_4`.
The common even gap satisfies `g<=16ceil(log_2X)`. Uniformly over its possible
values, `P=O(log^2 n)` and `g=O(log n)`. Prime number theory gives

\[
 X\sim4n^4\log n,\quad T/n^4\sim X/2,
 \quad\mu\sim2n^5\log n.                            \tag{HC2}
\]

The following table charges a line's actual accumulated numerical drift, not
merely the size of a formal coefficient. Constants are fixed before `n` grows.
Every reserve includes both legal reference orientations on the same entries.

| Stage or resource | Global entries or tuples | Worst local load / drift | Demand and strict margin |
|---|---|---|---|
| Common seed matching | Available `>>X/log^3X` disjoint `g`-pairs; demand `O(n^3P)` pairs | Prefix `O(P)` cells per required line | `n^3P=o(X/log^3X)` |
| Worst deletion | All selected endpoints at most `Q_*` | May all lie in one requested interval/class | `Q_*=o(delta X/(g log X))`, exponents `3.76<3.80` |
| Fresh repeated differences | At least 40 matched equal-gap pairs per growth/macro/residue request | Prefix uncontrolled; macro midpoint error at most `delta X` per cell | Growth threshold `4096gF^2`; macro/residue multiplicity `>>delta^2X/(g log^2X)` tends to infinity |
| Axis level 0 | `O(n^3(P+K_0))` | `O(K_0X)` per axis; extras avoided | Hyperplane error `O(n^2K_0X)`; `n^2` complete intervals per edge |
| Axis level 1 | `O(n^3(P+K_1))` | `O(K_1X)` | Plane error `O(nK_0X)`; `n` intervals per edge; `K_0=o(K_1)` |
| Axis level 2 | `O(n^3(P+K_2))` | `O(K_2X)` | Horizontal error `O(K_1X)=o(K_2X)` |
| Axis level 3 | `O(n^3(P+K_3))` | `O(K_3X)` on remaining axes/extras | Coefficients `O(K_2X log^2n)+O(gn^2)=o(K_3X)` |
| Axis level 4 | `O(n^3(P+K_4))` | `O(K_4X)` on extras; bodies avoided | Coefficients `O(K_3X log^3n)+O(gn^3)=o(K_4X)` |
| Old and extra residues | `O(n^3g)` total, extra part `O(n^2g)` | `O(gX)` on each line | Representatives `0,...,g/2-1`; no division by a nonunit |
| Eight body reservoirs | `O(P+K_5)` | At most `8X` lower-family spill over whole pass | Errors `O(K_0X)=o(K_5X)` |
| Triple graph reservoirs | `O(n(P+K_5))` | Pair drift `O(X)` by incident-edge and fresh-orbit bounds | Coefficients `O(K_4X)+O(g)=o(K_5X)` |
| Twelve common pair traces | `O(n(P+K_6))` | Pair drift `O(K_6X)` by separate cap | Trace `O(nK_4X)` divided among `n` reservoirs; each `o(K_6X)` |
| Pure pair templates and marker flows | `O(n^2(P+K_7))`, at most40pairs per stage | `O(K_7)` cells; exact preservation of every other family | `O(K_6X log^2n)+O(gn^2)=o(K_7X)` |
| All macro centering | Axis plus extra reserves `<Q_*=o(n^4)` | Midpoint error `O(delta K_7X)` | `delta K_7=O(n^.59)=o(K_0)` |
| Whole-bundle orientation | One independent bit per main reservoir | Range `O(X)`; `O(K_7+P)` relevant bundles per line | Fluctuation `O(X sqrt((K_7+P)log n))=o(K_0X)` |
| Unused-pool completion | Every remaining prime, exactly once | `O(X sqrt(n log n))` per line, plus changed mean | `sqrt(n log n)=o(K_0)` |
| Compatible prime windows | `4n^3+12n^2+16n+8` targets | `|q-mu|<=mu^(3/5)` | `mu^(3/5)=o(X)` and hence `o(K_0X)` |

The axis total invoice is `<2^24n^3K_4`; all extra entries total
`O(n^2(P+g+K_7))=o(n^3K_4)`. Thus their sum is `<Q_*` eventually, with a
fixed margin. Pair matching uses this full allowance at every request,
even when prior deletions concentrate in the worst class and window.

## 3. Joint reservation and exact-pool centering

Fix a compatible odd target vector as in USC4. Plan every extra support by
EP4, then every axis support by AP4 around it. Extra axis load is `o(n)`,
which is exactly AP4's external geometry hypothesis. Prefix, macro-level,
family and residue caps are separate. Consequently the union has

* `O(P+g)` uncontrolled prefix/residue cells per required line;
* `O(K_7)` macro cells per required line;
* `o(n)` total axis load, and fewer than `Q_*` reserved cells in total.

Allocate all common seed endpoints, then every other stage from its fresh
matching. Different stages use different prime entries and different cells.
Each stage is assigned one of its two legal switch configurations. This is
a partial bijection from the actual pool, not an array of invented numbers.

Independently choose one of the two complementary central configurations
of each entire main reservoir, with equal probability. Residue stages remain
fixed. U4 and PT prove the whole-bundle range `O(X)` on every signed line;
the newly reserved controls do not invalidate the old range, because their
supports are disjoint. Each line meets at most `O(K_7+P)` random reservoirs,
as every such reservoir uses a cell on that line. Each macro cell has its
actual pair midpoint as expectation, even when several pairs are switched
together. Individual cells are not treated as independent.

For a line `L`, let `r_L` be its reserved-cell count and `C_L` their sum.
The expectation error is

\[
 |\mathbb E C_L-r_Lm_0^*|
   =O(\delta K_7X+PX+gX),\qquad m_0^*=T/n^4.           \tag{HC3}
\]

Hoeffding's bounded-independent-variable inequality, applied to whole
reservoir contributions, and a union bound over `O(n^3)` required lines
give a simultaneous choice with

\[
 |C_L-r_Lm_0^*|\le E,
 \quad E=O(\delta K_7X+PX+gX+
                      X\sqrt{(K_7+P)\log n}).        \tag{HC4}
\]

This use has a fixed range constant, even for exceptional lines meeting many
stages of a native reservoir: their two central scalar states differ by at
most `g`. Both reference choices retain all later signed grid capacities.

Let `M` and `m_unused` be the number and mean of unused pool entries.
Eventually `M>=n^4/2`. Sum (HC4) over one axis partition, which has `n^3`
lines and counts every reserved cell once. The exact pool total yields

\[
 |m_{\rm unused}-m_0^*|\le n^3E/M\le2E/n.             \tag{HC5}
\]

Uniformly biject the unused primes to the unused cells. The expected full sum
on any required line is within `3E` of `mu`; this explicitly pays the changed
unused-pool mean. Sampling without replacement from `[0,X]` has the same
bounded-range tail used in U4:

\[
 \Pr(|S_L-\mathbb ES_L|>u)
      \le2\exp(-u^2/(2nX^2)).                         \tag{HC6}
\]

Take `u=5X sqrt(n log n)`; multiplying this bound by the exact line count
tends to zero. Thus some completed bijection has all required sums
`mu+O(E+X sqrt(n log n))=mu+o(K_0X)`. No prime is discarded. The small
primes dividing `g` are simply among the unused entries if not reserved.

## 4. Correcting every target by legal swaps

Perform the separate five-level old residue repair, then PT's descending
extra residue repair. They change each line by `O(gX)=o(K_0X)` and leave
every required sum congruent to its target modulo `g`. Main reservoirs
remain in their central states. The extra residue repair is axis-neutral;
later old main stages preserve every extra residue because their gaps are
multiples of `g`.

Now perform U4's five numerical levels without merging distinct passes:

1. Set every `w` hyperplane total, using `n^2` scalar reservoirs per edge.
2. Set every `(z,w)` plane total, using `n` reservoirs per edge.
3. Set both horizontal axis lists in every such plane.
4. Correct each `z`-axis residual matrix while preserving the horizontal lists.
5. Correct the `w`-axis residual three-tensor while preserving all three others.

Exact compatibility supplies the successive zero-total or zero-marginal
conditions. The tensor right-inverse bounds, including `512gn^2` and
`16384gn^3` integer-rounding terms, fall strictly within their distinct
capacities. The initial bound required by U4 is precisely the joint centering
bound just proved. Extra reserved supports are never switched by an axis
stage. All axes now have their exact targets.

The old supports avoid the eight full diagonals, so their errors remain
`O(K_0X)`. Every other extra line has error `O(K_4X)` by the separate old
pass caps. Apply PT's four numerical stages in order: bodies, triple vectors,
twelve common pair traces, and pure pair kernels. Each demand, residue and
capacity has been proved in PT and the table above. Every stage preserves
the axes and all already fixed higher families. The last pure pair stage
preserves all other pair families as well. At the end every required sum
equals the prescribed odd target.

All changes were swaps of disjoint preassigned prime pairs, with a simultaneous
orientation for each checkerboard or compound stage. Their union preserves
the exact bijection throughout. This proves USC4.

## 5. Prime targets, uniformity, and limits of the conclusion

SPT4 supplies a vector of primes satisfying every SI4 identity and all four
directional totals `T`, with displacement at most `mu^(3/5)=o(X)` by (HC2).
Every such prime is odd for large `n`, and the vector lies inside USC4's
neighborhood. Apply USC4. This proves SC4.

Every threshold in this argument depends only on fixed dimension four,
the fixed degree/expansion constants, fixed marker/packing caps, and the
one-dimensional analytic interfaces. Choose their maximum, together with
SI4's order requirement `n>=17`, the finite-list length/window requirements,
the fresh-supply inequalities, the `o(n)` packing and concentration bounds,
and the finitely many strict capacity inequalities in the table. Each is
valid for every larger order; restricting to odd orders removes parity and
is the only subsequence restriction. No prime-power condition appears.

The Thorner--Zaman short-interval input in the cited interface has ineffective
constants. Consequently this proof supplies an eventual integer `N_4`, not
a numerical cutoff. The square cutoff and any separate cube cutoff are not
transferred. Fixed dimension is essential to the stated invoices; no theorem
for dimension growing with `n` is claimed.

The finite incidence torsion at orders 3 and 5 remains a diagnostic guard.
SI4's eventual saturation has its own explicit proof, and USC4 acts on its
large-order lattice. Finite prime target vectors at small orders are not
certificates of integer lifts or actual prime arrangements. The independent
array checker accepts only an exact pool permutation with every required
line present and its actual sum prime.

## 6. Architecture ledger and verification boundary

| Route | Resolution |
|---|---|
| Independent three-dimensional slices | Insufficient: slice pools and fourth-direction axes are coupled; replaced by five global marginal levels |
| Independently chosen prime pair matrices | Insufficient: violates twelve complementary-pair trace identities; replaced by the set-of-absolute-labels SPT4 construction |
| An isolated one-line pair correction | Forbidden by fixed margins; replaced by compatible matrix generators |
| Shared fixed marker rectangles | Integer lift exists but local loads can be macroscopic; replaced by bounded marker allocation and graph flow |
| A single generic hypercuboid for every pure-pair effect | Insufficient to remove both traces with bounded load; compound stages use at most forty equal-gap pairs |
| Global greedy occupancy alone for all `O(n^2)` extra bundles | Loses a factor `n`; fixed-coordinate slice and diagonal-support counts repair it |
| Large final capacity with exponent at least `.80` | Breaks `delta K=o(K_0)`; the proved `.77,.78,.79` hierarchy has strict margins |
| Direct general joint integer flow | Retained alternative; unnecessary after the triangular solver and local packing are proved |

The supporting code tests exact arithmetic identities, tuple orientations,
whole-bundle incidences, small incidence lattices, target compatibility and
corrupted certificates. Such tests are finite and do not prove the estimates
above. Reviews must identify the exact source revision and the reviewer's
authorship exclusions. Repository integrity, remote CI, conventional review
and kernel verification are separate statuses. Current evidence and the next
bounded action are recorded in [HYPER4_HANDOFF.md](../HYPER4_HANDOFF.md).
