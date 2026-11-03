# Independent end-to-end composition review: signed prime hypercubes in dimension four

Reviewer: `/root/hyper4_composition_review`.

Review date: 2 November 2026.

Scientific source reviewed: `b837e307fc41975d0fb332c8215d6835ba47a271`.
Additional physical-control checkpoint:
`61755c8ca37f8ab796ca4eefac6af890825b1b68`.
Component review notes consulted as published at
`721f818e113d4e730cfe1c190e79d8abcaca3f1c`.

## Verdict and authorship boundary

**Accept the conventional composition proof of USC4 and its application with
SPT4 to SC4. I found no blocking mathematical defect.** This judgment concerns
the five scientific sources bound below and their stated pinned imports. It
does not constitute kernel verification, a formal GitHub approval, a remote CI
result, a numerical cutoff, or a priority assessment.

I was assigned after the scientific source was frozen. I did not author any
of SI4, MP4, MR4, U4, AP4, PT, EP4, HP, HW, SPT4, USC4 or SC4; I did not
write their original controls or contribute a source repair during this
review. Inherited author discussion was not substituted for reading the
sources. I made no changes to author manuscripts, code, Git objects or refs.
This review note is my only repository contribution.

My scope is the end-to-end implication: the independently checked component
interfaces must coexist on the same exact pool and support plan, their
preservation and size contracts must hold in the stated order, and their
quantifiers must yield every sufficiently large odd order. I also examined
the mathematical arguments behind the delicate composition boundaries rather
than accepting the component reviewers' verdicts as the final conclusion.

## 1. Source binding and dependencies

I read the repository working agreement and research protocol, the problem
index and reference records, and the complete composition, axis and extra-trade
sources. I checked the SI4, MP4 and MR4 interfaces and their bounded template,
ring and physical boundaries, and checked HP/SPT4, the exact-total weights,
and the stated analytic and finite-list domains used at the controller
interface. I consulted the separate incidence, geometry and analytic review
notes with their authorship and import disclosures.

For execution, I extracted an immutable `git archive` of checkpoint `61755`.
I byte-compared every scientific manuscript there with `git show` at `b837`,
and later also with the shared checkout at `721f818`. All five were identical:

| Manuscript | SHA-256 |
|---|---|
| [hyper4_cube.md](../manuscripts/hyper4_cube.md) | `1a3173d3cb7635bd021aafa42673343ad6ea54ab0928a7aae08cb6c3a9689501` |
| [hyper4_axis.md](../manuscripts/hyper4_axis.md) | `ca9cefea5142343144dfa27904279066743d67e7f79a4c763ff0fc3ab45e4496` |
| [hyper4_trades.md](../manuscripts/hyper4_trades.md) | `76c41b51b437fbe693a86bd7ec04593a9cc9bb11afe11a6d21661bd75812d418` |
| [hyper4_incidence.md](../manuscripts/hyper4_incidence.md) | `b91309ac57931ac4fcd7d382cb1973806dfc3aa02f96148e324da7dd589c1f67` |
| [hyper4_targets.md](../manuscripts/hyper4_targets.md) | `d289b119e80b4fd93c9b277e26da96d32870675916c96aa6f03e54f881b64b1f` |

The dependency direction is sound. SI4 identifies the homogeneous integer
compatibilities, while MP4/MR4 provide bounded and residue coefficient
decompositions. None of those signed integer lifts is used as a positive
prime array. U4 supplies its own physical five-pass construction. PT and EP4
supply actual extra-family swaps and their disjoint placement. SPT4 supplies
one compatible prime vector, while USC4 realizes every nearby compatible odd
vector. No one of these results assumes the final array whose existence it
is meant to prove.

The retained PR79/PR77 interfaces are explicit. The composition does not
import a later numerical-cutoff estimate or restore the superseded fixed-gap
or ternary interfaces. The independent analytic review separately refetched
the pinned FL source and checked the printed Thorner--Zaman hypotheses; the
incidence review checked that the graph input applies also to the possibly
even marker population. Those component reviews address external-input
issues; my verdict below checks how the resulting contracts are used together.

## 2. Joint reservation, fresh values and complete capacities

The reservation order does not contain an occupancy circularity. EP4 plans
all extra supports first and proves maximum axis load
`O(P+K_7+g)=o(n)`. That is precisely AP4's geometric external-support
hypothesis. AP4 then packs the five old stages around those supports. Its
extra-line caps and full-body avoidance survive this order. The stronger
centering properties required in U4 Section 7.3 are subsequently established
by PT; they are not silently inferred from small axis load alone.

Selecting the common gap from the pool is compatible with planning geometry
before assigning values to cells. The gap is fixed throughout the construction.
Every prefix has at most the stated `P` stages, so support slots can be planned
to that upper bound; unused slots need not be assigned a reservoir value.
The common seed matching is reserved before other prime requests, as required
by the fresh-set argument. Its old-plus-new demand is `O(n^3P)`, including
the constant cost of up to forty pairs per compound stage. Since
`X` has order `n^4 log n`, the demand-to-supply ratio is
`O(log^4 n/n)`, tending to zero.

All later requests charge every previously selected endpoint against the
same allowance `Q_*=2^40 n^3K_4`, including dormant switch choices. The
axis invoice is below `2^24 n^3K_4`; the extra invoice is
`O(n^2(P+g+K_7))=o(n^3K_4)`. Thus the promised allowance is actually
available. The fresh count is uniform under deletion concentrated in one
window and residue class, not just average depletion. Its least power is
`3.80`, whereas the reserve power is `3.76`.

I checked the common-difference grouping at the boundary used by the physical
construction. At `R>=4096gF^2`, the grouped growth argument gives at least
256 edges of one difference; maximum degree two supplies a matching of at
least 86, exceeding forty. Macro stages use disjoint lower and upper
intervals, so the representations of one difference already form a matching.
The compound physical stage requires no difference `2d`: its matrix template
has at most twenty entries, each `+1` or `-1`, and pairing along the outer
selector uses at most forty actual pairs of difference `d`.

Complete subset-sum coverage, rather than a gcd claim, pays the capacities.
The prefix covers every grid point to at least `X`; every added gap is within
the current covered length. The macro total is at least `8K_jX`. If its
total scalar is `R_b`, a central subset with
`q_b=g floor(R_b/(2g))` and its complement each leave distance at least
`4K_jX-g` to both endpoints. This eventually contains the claimed signed
radius `3K_jX`, from either chosen reference configuration. Rounding therefore
does not remove one side of the available interval. Opposite correction signs
are alternative configurations of the same entries, with no endpoint reuse.

## 3. Centering dependent cells and the remaining pool

The independent random variables are whole complementary reservoirs. Each
cell is toggled to its partner under complementation, so its mean is its
actual pair midpoint. This remains true when several pairs must switch as
one stage and when many stages must be selected together. No cellwise or
stagewise independence is assumed.

The whole-reservoir range is the necessary nontrivial input. Native lines
can meet many stages, but their scalar coefficients are fixed and the two
central scalar totals differ by at most `g`. Nonnative lines meet at most one
stage, with at most two relevant old-controller cells; the extra controllers'
fresh-orbit rules and exact zero images supply their corresponding bounds.
Consequently the range is `O(X)`, with a fixed constant, on every required
line. Each line meets only `O(K_7+P)` random reservoirs. Prefix and fixed
residue cells have their separate `O(P+g)` load allowance.

The simultaneous reserved-sum error is therefore legitimately

`E=O(delta K_7X+PX+gX+X sqrt((K_7+P)log n))`.

I checked the unused-mean step algebraically. Summing the reserved-line bound
over one axis partition counts every reserved cell exactly once, so the
reserved total differs from its nominal mean by at most `n^3E`. The remaining
pool size is at least `n^4/2`; hence its mean differs from `T/n^4` by at most
`2E/n`. A line contains at most `n` unused cells, so its completed conditional
mean differs from `mu` by at most `E+2E=3E`. This argument uses the actual
unused multiset and exact pool total, not an unchanged-mean approximation.

After fixing the orientations, a uniform bijection of all unused primes has
the stated without-replacement tail. With
`u=5X sqrt(n log n)`, the displayed bound is `2n^(-25/2)` for one line;
multiplication by `4n^3+12n^2+16n+8` tends to zero. Dependence between
different line sums is harmless for this union bound. The resulting full
array uses every prescribed entry once and has all sums
`mu+o(K_0X)`. It is a genuine baseline permutation before any numeric flow
is applied.

## 4. Residue routing and the ordered physical corrections

Every baseline sum and every USC4 target is odd, so their difference is even.
The separate residue stages have actual gaps `2 mod g`, supplied using the
reduced classes `-1,+1 mod g`. For `h=g/2`, solving divided errors over
`Z/hZ` is therefore legitimate even when `g` has small odd prime factors.
No target residue is assumed to be a unit by the physical theorem.

The old residue repair fixes all axis residues first. The remaining divided
extra errors inherit pair margins, triple totals and common-trace identities
over that ring from the actual array and chosen target. PT then fixes body,
triple, common-trace and pure-pair residues in its stated order. Tree-product
bases and routed path prefix sums are integral identities and do not invert
`n` or another possible nonunit. A coefficient in `0,...,h-1` is realized
by that many distinct separate stages. These repairs have actual drift
`O(gX)` by their local caps; they leave the main reservoirs in their chosen
central configurations. Every later main gap is a multiple of `g`, preserving
all repaired residues.

The five numerical axis passes retain the required intermediate information:

1. Hyperplane totals have error at most `(1+o(1))n^2K_0X` and `n^2`
   scalar reservoirs per graph edge. The summed capacities have a strict
   margin, including grid floors, and the directional grand total gives zero
   demand sum.
2. Plane totals have error `O(nK_0X)` and correct hyperplane sums, with `n`
   intervals per edge at the larger `K_1` scale.
3. Both horizontal line lists then have the exact plane total. Their separate
   physical systems preserve one another, using the `K_2` scale for errors
   `O(K_1X)`.
4. Each remaining `z` residual matrix has exactly zero integer margins by
   axis compatibility and the already fixed families. The retained bound
   `O(K_2X log^2 n)+O(gn^2)` fits `K_3X`.
5. The final `w` residual three-tensor has all three integer marginals zero.
   Its bound `O(K_3X log^3 n)+O(gn^3)` fits `K_4X`, with the actual
   `16384gn^3` rounding cost retained.

The old support restrictions preserve all bodies numerically. Separate pass
caps, rather than an inference from global volume, bound pair and triple
errors by `O(K_4X)`. All errors remain multiples of `g`.

The descending extra correction also closes without an uncharged spill.
Bodies use `K_5` capacity and cause at most `8X` drift on a fixed lower line.
Afterward each triple vector has zero total as an integer by the exact axes
and the target compatibility equations. Its graph coefficients are
`O(K_4X)+O(g)=o(K_5X)`. Freshness within a bundle and the incident-edge
count across bundles bound the entire triple pass's pair drift by `8Delta X`.

The pair residuals consequently have exact zero margins and size
`E_1=O(K_4X)`. A common trace has size at most `nE_1`; splitting it into
`n` grid integers of size at most `E_1+g` is ordinary quotient/remainder
division, not division modulo `g`. Each coupled move changes both sides of
the one intended compatibility equation and none of the other eleven traces.
The actual local cap pays accumulated pair drift `O(K_6X)`, which can be
larger than the chosen scalar errors because a subset realization can switch
many stages. The proof correctly retains that larger drift.

Finally the pair matrices have zero margins and both traces zero. MP4 applied
to the residual divided by `g` supplies scalar coefficients bounded by
`O(K_6X log^2 n)+g/2+512gn^2=o(K_7X)`. The marker coefficients have the
same upper bound. PT implements these compound matrices with changes only
in their native family. Thus all axes, triples, bodies and previously finished
pair families remain exact. No formal signed integer lift replaces this
physical last step.

## 5. Joint margins, targets and the entire odd tail

I recomputed the powers using exact rational arithmetic, with positive
power slack required wherever a logarithm or fixed constant must be absorbed.
Representative margins are:

| Inequality | Positive power slack |
|---|---:|
| Fresh worst-class supply versus total reserve | `1/25` |
| Axis reserve scale versus extra reserve scale | `97/100` |
| `K_0` versus `delta K_7` | `1/100` |
| `K_0` versus square root of `K_7` | `41/200` |
| `K_0` versus square root of `n` | `1/10` |
| Each of the last two axis flow scale gaps | `1/25` |
| Triple capacity versus old-stage error | `1/100` |
| Common-trace per-reservoir capacity versus old-stage error | `1/50` |
| Pure-pair capacity versus its input error | `1/100` |
| `X` versus `mu^(3/5)` | `1` |
| Analytic `71/120` versus `7/12+1/240` | `1/240` |

The rounding terms have still larger margins: `gn^3/(K_4X)` and
`gn^2/(K_7X)` tend to zero with power slacks `44/25` and `279/100`.
The same calculation rejects the tempting `.80` final exponent: then
`delta K_*=n^.60`, leaving no centering slack. It also rejects merging the
last axis scales, which would leave no positive power to absorb `log^3 n`.
These are method failures correctly avoided by the source schedule.

SPT4 fits the actual universal interface. The ordinary set of absolute fixed
coordinates checks every block-partition identity term by term, including
the complementary-pair equations. Its weighted total uses the exact weights
`1,8,18,48,24,48`, summing to `n^3`; the finishing parity and mod-8 repair
preserve the exact total `T`. Its two FL lists have length `(n-1)/2` and
original modulus 2, rather than an unjustified collection of independent
overlapping prime matrices. The target distance `mu^(3/5)=o(X)` lies well
inside `K_0X`. Every target is odd eventually. USC4 does not need a stronger
arbitrary-prime-pattern or residue-prescription theorem.

All choices of degree, caps, orbit thresholds and analytic slack are fixed
before `n` increases. The estimates are uniform in the allowed growing gap,
the compatible target tuple, and the previous deletion pattern. There are
only finitely many separate threshold conditions, each valid for every larger
order. Taking their maximum gives every sufficiently large odd `n`; there is
no prime-power, congruence-class, or infinite-subsequence restriction beyond
oddness. SI4's explicit `n>=17` is not confused with the eventual packing,
analytic or final existence threshold. The latter remains ineffective through
the cited short-interval input.

## 6. Replayed evidence and its limits

Environment: Python 3.12.14. The following commands were run from the root
of the immutable `61755` archive after the scientific byte comparison:

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyper4_trade_controls.py
python3 -B problems/prime-arrays-beyond-square/code/hyper4_axis_controls.py
python3 -B problems/prime-arrays-beyond-square/code/verify_hyper4_incidence.py
python3 -B problems/prime-arrays-beyond-square/code/hyper4_targets_controls.py self-test
python3 -B problems/prime-arrays-beyond-square/code/check_hyper4_certificate.py --self-test problems/prime-arrays-beyond-square/inputs/hyper4_singleton.json
```

All passed. The principal outputs were:

| Control | Result and scope |
|---|---|
| Extra physical controls | 256 exact images; actual eight-pair and forty-pair shapes; four whole-bundle classes; seven corruptions rejected |
| Axis controls | 52 physical patterns; 19 changes from nonzero reference states; 16 exceptional endpoint cases; 24 composite-ring checks; eight five-pass numeric controls; separate occupancy, orientation and capacity negative controls |
| Incidence checker | Independent line inventories, all gadget orientations, integer/odd lifts, marker and residue controls; full exact order-three and order-five certificates passed |
| Target controls | Finite arithmetic checks and independently regenerated order-three and order-five target vectors; seven corruptions rejected at each order |
| Arrangement checker | 272 and 888 lines at orders 3 and 5; eight geometric and eight arrangement corruptions rejected; exact singleton `[3]` verified |

The axis physical certificate has canonical digest
`c5cff56b6bd6408f056cbbb9fae618b82d320519cf44548bc51492837737557d` and uses
the exact 14,641-entry first-prime pool at order 11. It is a controller
certificate, not a prime-line arrangement. The eighty-vertex forty-pair
fixture is a partial trade, not a full array. The order-three and order-five
prime targets are not claimed to be integer lifts or arrangements. Their
incidence matrices retain the recorded finite torsion, consistently with
SI4's different large-order domain.

I also ran, from the shared successor checkout:

```sh
python3 -B check.py --base cdb7879e358f93afa54b685027a27692d22635a9
```

Repository integrity and all 45 tooling regression tests passed. This is local
metadata/tooling evidence only. The asymptotic verdict rests on the conventional
arguments and interface audit above, not on these finite runs.

## 7. Findings and delivery boundary

No proof repair is requested by this review. One nonblocking delivery finding
was sent to the coordinator: the frozen `OPEN_PROBLEMS.md` still grouped
dimension four with the unresolved `D>=4` physical implication. The final
index should distinguish the reviewed dimension-four result from dimensions
at least five. That administrative correction does not alter a hypothesis or
mathematical source and does not require reopening the proof verdict.

The separate [incidence review](hyper4_incidence_review.md),
[physical/geometric review](hyper4_geometry_review.md), and
[analytic/target review](hyper4_analytic_review.md) were consulted with their
declared authorship boundaries. My acceptance of the final composition is
independent of their acceptance language; it depends on the checked joint
reservation, centering, residue, capacity and preservation reasoning recorded
here. The resulting conclusion is precisely the full signed-line theorem for
the first `n^4` odd primes, for every sufficiently large odd order. It makes
no section-sum, numerical-cutoff, growing-dimension, novelty or formal-
verification claim. No public note, accepted cube proof, separate cutoff lane
or unrelated research was modified by this review.
