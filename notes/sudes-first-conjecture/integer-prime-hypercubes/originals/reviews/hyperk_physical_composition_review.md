# Independent physical and composition review: every fixed dimension

Reviewer: `/root/physical_composition_review`. Date: 2 November 2026.

**Verdict: no blocking defect found in the physical controllers U(k), UM(k)
and UH(k), or their stated prime-target compositions PM(k) and PH(k).**
The strongest accepted conclusion in this scope is the exact first-prime-pool
theorem for all axes and all full signed-coordinate lines varying in at least
`ceil(k/2)` coordinates, for every fixed `k>=2` and all sufficiently large
odd orders. The remaining families of sizes `2,...,ceil(k/2)-1` are not
accepted through this review. The requested all-full-line theorem remains
open in dimensions at least five.

## Authorship, revisions and scope

I was assigned this review after the first source was frozen. I did not author
the physical controllers, their component proofs, prime-target construction,
resource ledger, composition, producer scripts, retained inputs, or proposed
kernel architecture. My only additions are this review and the separately
authored [hyperk_physical_controls.py](hyperk_physical_controls.py). I changed
no author source, retained input, claim or Git reference.

The reviewed scientific sources are:

1. `5692d37633ef4b509e8429cddf4ed762e7235d08`: the complete
   [axis/majority controller](../manuscripts/hyperk_controller.md), its code
   and two retained partial-prime stages, and the physical composition in
   [hyperk_cube.md](../manuscripts/hyperk_cube.md).
2. `f9697734c0c1d87eb8ab8af4051d0e8495ac9b56`: the additive
   [half-coordinate controller](../manuscripts/hyperk_half.md) and its code.
   The first checkpoint's controller, composition, target and resource bytes
   were independently checked to be unchanged at this second revision.

I used separate `git archive` directories for both revisions, and compared
the reviewed files byte for byte with `git show`. The reviewer program
enforces nine bindings for the first source and two additional bindings for
the half-coordinate source before running its controls. Principal SHA256s:

| File | SHA256 |
|---|---|
| `manuscripts/hyperk_controller.md` | `bcccf122f966daf70101bfff1f4cf00cfc9559c68c5097d80c981ae405cf1f23` |
| `manuscripts/hyperk_cube.md` | `98911845eb32e57ef381ad4c6c6e93914b45846f1597747ecef61f7538731eec` |
| `code/hyperk_controller.py` | `150d0d1b3d49bb4c8c134e8cd93622b3cabdc9dd14bd3d11d7f5f3eeb3112965` |
| `manuscripts/hyperk_half.md` | `0a15b37c530754a70f4b42ac410445c88532b0c6f28856bedf5ac280ee09afbe` |
| `code/hyperk_half.py` | `2ba335cb46208f3597a8aeff619ceb62f6661eaac57738cab92cb08eb727201c` |

I read the repository working agreement and research protocol, required problem
records and code instructions, the full reviewed physical/composition sources,
the inherited tensor-expander proof, and the supplied resource interface.
There is no deeper working agreement in the problem directory. I also checked
the graph-existence argument F1 in the exact public reproduction explicitly
cited by the frozen cube source: Mira-Cult/math
`4aaac8b416546d7e2fbc975faa960fe84d8e6f32`,
`notes/sudes-first-conjecture/controller.md`, Git blob
`02bec4fe02c246a900104ebbc125965ccb66617d`. The earlier scientific commit
`4ac266e7c4994a8502eb2a0c57d6b1d3fbd801c5` is not a locally available
tree here; I did not pretend to replay that object. The cited reproduction
contains the complete elementary argument used for this graph interface.

The complete integer-image theorem and the analytic derivation of KPT/FL/TZ
have their own independent reviews. My composition review checks their exact
interfaces and the resource substitutions; it does not claim a second full
analytic or integer-lattice review. The supplementary full-kernel research
manuscript is outside my acceptance scope. This is conventional internal
mathematical review, not journal refereeing, a novelty determination, a formal
GitHub approval, remote CI or proof-kernel verification.

## 1. Exact stages and all-axis control

The signed signature formula (SIG) is direct substitution in the line sum.
It includes repeated and opposite native endpoints and the central coordinate.
A product of two-point coordinate supports meets any full signed line in at
most two cells. Pairing along one difference coordinate gives exactly the
alternating signs when all pairs in the stage have the same actual gap.
The proof consequently uses actual disjoint swaps, rather than interpreting
an arbitrary integer entry increment as an available prime change.

The central and repeated-pair counterexamples are necessary qualifications:
a central vertex may lie on every signed body, and identical two-point factors
give body coefficient `1+(-1)^k`. Neither is a generic unit selector.

I checked the variable-dimensional stage recurrence, including both the
native data and preserved data:

| Stage | Corrected data | Preservation and coefficient interface |
|---|---|---|
| Descending aggregates, `d=k,...,3` | Totals of the `(d-1)`-dimensional sections inside each already fixed enclosing section | Transfers along coordinate `d` preserve the enclosing total and the coordinate-`d` axes; `n^(d-2)` scalar reservoirs per graph edge supply the necessary section-scale capacity. |
| Two horizontal families | The first two directional axis lists in every fixed outer tuple | Correct plane totals make both list demands zero-sum. Each family preserves the other exactly. |
| Ascending tensors, `d=3,...,k` | The coordinate-`d` axis tensor | Earlier axes and the integer compatibility equations make every residual marginal zero; graph products preserve all earlier axes. |

There are exactly `(k-2)+1+(k-2)=2k-3` capacity levels. The `k=2` case
contains only the horizontal level. The argument controls the globally
assigned subpool totals and does not invoke a lower-dimensional prime theorem
on unrelated slice pools.

The graph proof supplies degree at most 64 and cut expansion at least eight
for every integer graph order, including odd and even orders. Its permutation
union bound is below one; discarding loops leaves the asserted degree and
cut counts. The inherited lazy-walk calculation gives spectral gap at least
`1/256` and operator norm at most `5 log n+5`. Nearest-integer coefficient
rounding followed by tree-product repair pays the actual rank-`r` term
`(Delta n)^r/2^(r+1)`. There is no dimension-two rounding constant reused
in higher tensor ranks.

### Packing and complete-bundle ranges

For a one-free-coordinate pass, deleting that coordinate leaves footprints
of point degree at most `Delta^(k-1)`. Their total planned load over any
native signed line is bounded by that degree times `nL`. Therefore a
saturated-line cap excludes only `O_k(n/H_k)` possible free labels.
Occupied-cell exclusions use the actual native axis load, and whole-reservoir
freshness excludes `o(n)` more choices. This is a local projection argument,
not an average-volume assertion.

For an aggregate pass with `r=d-1`, I checked both required section counts:
`Delta n^(r-1)L` at a fixed native endpoint and outer tuple, and
`Delta n^rL` with the native coordinate varying. Inner axes, native axes,
outer axes and the surviving signed directions each use the appropriate
one of these counts. A possible nonaxis line fixes every generic inner
coordinate. Hence its saturated-key exclusions cost only `O_k(n^r/H_k)`
free tuples. Previously occupied cells are bounded section by section by
`2n^(r-1)M=o(n^r)`. This addresses concentrated occupation in a section.

The separate prefix, macro and residue passes are essential and present.
They prevent uncontrolled prefixes from acquiring the macro occupancy bound.
Freshness across the entire reservoir makes a nonnative line meet at most
one stage. Native axis contributions have a fixed scalar coefficient, so
the two complementary central reservoir states differ by at most `g` there.
All other ranges are at most `2X`. Generic free orbits avoid every full body.
These conclusions include the lines omitted from the eventual target family.

### Residues and numerical closure

Odd sections and odd targets give even discrepancies. Dividing these even
integers by two and solving over `Z/(g/2)Z` is legitimate; it does not invert
two in that ring. Prefix sums on paths and their tensor products are integral
identities, valid over composite rings. There is no division by `n`.
Each representative needs at most `g/2-1` actual stages with gap `2 mod g`.
The proved caps bound their numerical drift by `O_k(gX)`.

The first aggregate error has size `(1+o(1))n^(k-2)K_0X`, and the
expansion-eight cut-flow condition fits inside the combined first-level
capacity. Subsequent errors include preceding incidental displacement and
are dominated by the next strictly larger scale. The tensor inverse is
applied only after its zero-margin and divisibility conditions hold. Its
rank-dependent rounding term is negligible relative to the next capacity.
Every later main gap is divisible by `g`, so these switches preserve all
previously matched residues.

There is one nonblocking wording issue in Section 5.2: the first aggregate
demands sum across the `n` labels of coordinate `k`; the prose says "the `k`
labels." The surrounding definitions, sums and capacity exponents use `n`
correctly. This is a label-count wording issue, not a repair to the argument.

## 2. Strict-majority families and the general placement interface

For a native varying block `A` of size `r>k/2`, its complementary tensor has
rank `d=k-r<r`. Once the axes are exact, the prescribed axis/block partition
identities make that residual tensor zero-margin. The generic native selector
uses a common positive orbit and separate positive alternative orbits, all
disjoint from the complementary footprint. It has exactly one unit native
body trace. Mixed contractions miss the support. A contraction wholly in
the complement has size at most `d<r`; a proper contraction inside the
selector has size less than `r`. Thus only the native family can move among
families of size at least `r`. Processing block sizes in descending order
is genuinely triangular, including all relative signs.

The selector-times-footprint packing lemma is valid with the claimed
generality. Above one native point the total support load is at most
`2^rBL`. Over a complementary line it is at most `2^rBnL`. Each deferred
key test is injective in the last selector variable occurring in that key.
Over-testing a potential key before all its varying coordinates are fixed
is harmless: the direction and fixed coordinates already define that line.
For an occupied vertex, varying its last selector variable follows one full
signed line, including the case where the common selector variable occurs
in several coordinates. Existing signed-line caps therefore bound its
forbidden choices. This validates the deferred greedy argument rather than
assuming independent random placement.

Extra supports are placed first. The axis construction then uses only their
proved `o(n)` maximum axis load. This order prevents circular packing
assumptions. Complete-bundle ranges and the residue correction use the
same freshness/signature facts. The total largest index
`D_M=3k-floor(k/2)-4` is correct. This establishes the physical UM(k)
interface used by PM(k), with no premise about the missing small blocks.

## 3. The complementary equality case

The half-coordinate extension correctly uses the inner space `Bdy_d` of
zero-axis-margin tensors with every full-body trace zero. It does not call
that space the kernel of every proper signed contraction.

### BH(d) and BR(d)

Only `O_d(n)` raw graph products have nonzero body traces, counted with
absolute trace multiplicity: each body has `n` cells, and each cell belongs
to at most `Delta^d` raw products. Central cells are counted for every
relevant body pattern. Each unit trace receives a separate generic marker.
Markers attached to the same raw product use disjoint noncentral alphabets
and avoid its endpoint orbits. The projected template therefore has
disjoint checkerboard pieces and entries only `+1,-1`, including when a raw
trace has magnitude two.

The greedy orbit-use cap `Lambda_d=16(d+1)P_d` is sufficient. The total
planned uses imply fewer than `n/16` saturated positive orbit labels;
raw-product and within-template exclusions are dimension-dependent constants.
Adding `n` zero-demand markers of every sign guarantees marker populations
at least `n`, without needing a lower bound on the number of nonzero traces.
Any target cell lies in at most `Lambda_d` markers.

The remaining coefficient at each marker is one signed raw coefficient,
and its sum in each sign population is the corresponding trace of the
target. This is a scalar zero-sum flow problem. It avoids the unresolved
kernel-valued routing issue of the full-family architecture.

Replacing a graph edge whose endpoint marker supports intersect by a two-edge
route through a disjoint marker preserves every cut lower bound: every
original crossing edge still has a separately labeled crossing edge on its
replacement path. Parallel geometric edges retain their multiplicities.
The cap of 128 middle uses gives maximum degree 320. The forbidden-support
count and `p_sigma>=n` ensure a permissible middle vertex eventually.
Every resulting marker-difference template has disjoint endpoint supports.
Its body traces cancel and it remains pairable.

Consequently the point-load bound `Delta^d+321 Lambda_d` counts raw,
attached-marker and routed-edge support incidences, even for eventual zero
coefficients. Integral cut flow gives the stated coefficient bound. Its
physical rescaling includes the ceiling cost in (H7).

For residues, the tensor product of a spanning-tree incidence basis is an
integral basis of the zero-margin module, so it remains valid over every
composite residue ring. The marker demands then have zero totals in that
ring. Routed path-prefix flows use representatives `0,...,h-1`; a middle
cap four gives degree at most ten and the stated point-load bound. No
unproved tensor-kernel solver is consumed by BR(d).

### Shared traces, compound stages and geometry

For `k=2d`, each complementary block/sign pair has one common scalar trace.
The prescribed two-block identities make the two residual traces equal.
Two generic selectors on disjoint alphabets change exactly that common trace
and its two native families among the blocks of size at least `d`. All axes,
larger blocks and other common traces are preserved. The count
`binom(2d,d)2^(2d-2)/2` correctly identifies unordered complementary pairs.

A trace of size at most `nE` is split into `n` signed grid coefficients
using ordinary quotient and remainder. Each has magnitude at most `E+g`.
This is an integer interval decomposition, not an attempted inverse of `n`
modulo the gap. The separate residue trace requires only one reservoir.
Afterward each native half-family residual satisfies precisely BH(d)'s
zero-margin, zero-body-trace interface.

For a final stage, the outer generic selector is orbit-disjoint from the
entire bounded inner template. Mixed lines have no supporting cell; the
complementary full body vanishes; every other required nonaxis image is
the native template itself. Pairing along an outer coordinate realizes
the complete compound template with at most
`(J_d+1)2^(k-1)` fresh equal-gap pairs. All nonzero template entries are
unit signs, so no hidden doubled gap or overlapping stage is required.

The shared-trace packing argument can use its total incidence count because
this particular pass has only `O_k(n)` reservoirs and each key has a free
fixed-coordinate variable. Its saturation exclusions are `O_k(n/H)`;
full-body keys are absent by orbit separation. This is not an illicit use
of the much larger whole-array volume bound. For final half templates, the
previous selector packing lemma applies with the proved fixed `B_d,s`;
that lemma's placement proof never needed the strict inequality `r>d`.

Freshness gives whole-reservoir range at most `2X` for shared traces and
`O_k(X)` for compound final stages. The latter correctly pays up to
`2(J_d+1)` cells of a nonnative line in one compound stage; it does not
reuse the single-cuboid two-cell bound. New extra stages, old majority
stages, and finally the axis stages can therefore be packed in the stated
order with separate prefix/macro/residue caps.

## 4. Complete composition and resource closure

The physical correction order is compatible with the support-planning order:
all supports and fresh entries are reserved before baseline completion;
then all required residues are repaired; numerical axes and strict-majority
families are fixed; common half traces are fixed; and the body-kernel
half-family corrections finish. Each step preserves the preceding required
data, and each remaining numerical error includes the preceding pass's
actual displacement.

For even `k>=4` the level count is
`(2k-3)+k/2+2`, giving largest index `D_half=5k/2-2`.
In particular dimension six has index 13, not the old strict-majority index
11. Odd dimensions retain their majority construction. The new reserve
`O_k(n(P+K_trace)+n^d(P+g+K_final))` is dominated by the axis invoice
because `d<=k-2`. The finite tuple bound includes the entire compound stage.

The geometry verifies all three explicit hypotheses of JC on **every** full
signed line, including omitted families: separate prefix/residue and macro
occupancy, a whole-reservoir range `O_k(X)`, and complementation of every
macro cell to its prime partner. Thus the independent random objects are
whole reservoirs. Summing the reserved-sum error over an axis partition
pays the changed unused-pool mean; filling by the entire complementary pool
preserves exact bijectivity. There is no unaccounted mean shift.

For any fixed finite depth, the ladder has positive adjacent gaps and top
exponent strictly below `3/4`. The complete reservation is smaller than the
worst reduced-class midpoint supply by a positive power, the midpoint bias
and complete-bundle fluctuation are below the baseline tolerance, and the
without-replacement error has the required `n^(1/2)` scale. Later capacities
absorb preceding errors times every fixed logarithmic power and all
`g n^r` rounding terms. All tuple sizes and geometric constants depend only
on fixed dimension. Taking a finite maximum of thresholds consequently
works for every sufficiently large odd order, with ineffectivity inherited
from the analytic input.

KPT provides odd prime targets satisfying all two-block identities and the
same exact axis total `T`. Its radius `mu^(3/5)=o(X)` lies inside the
universal-controller radius. Restriction therefore supplies exactly the
displayed UM/UH hypotheses. No arbitrary integer lift, small-order Smith
test, or independently chosen line prime is substituted for this target
interface. This validates PM and the stronger PH composition using the
named analytic inputs.

For a smaller native block, a proper complementary contraction can remain
nonzero even when all body traces vanish. The retained rank-three example,
and its six-dimensional outer-selector product, demonstrate that failure.
The proof correctly stops there. The full bounded-load signed-kernel
controller remains a substantive additional obligation.

## 5. Exact replay and independent controls

All author scientific replays ran in the separate bound archives under Python
3.12.14. Both commands passed:

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyperk_controller.py
python3 -B problems/prime-arrays-beyond-square/code/hyperk_half.py
```

The first reported 56 complete signature checks, 30 genuine partial prime
trades, 25 whole-reservoir intersection checks, 25 numeric/composite-residue
recurrences, 380 majority signatures, 11 majority partial prime trades,
11 majority bundle checks, nine rejected corruptions and the retained
complementary-spill counterexample. The half source passed integer and
composite-ring reconstructions at inner dimensions two, three and four,
six complete compound signatures, three shared-trace signatures, five
actual partial prime compounds and seven corruptions. Its finite marker
graphs are routed paths and are expressly not expander capacity certificates.

The reviewer program imports no author producer. Reproduce it by archiving
each scientific revision to a fresh directory and passing those directories:

```sh
python3 -B problems/prime-arrays-beyond-square/reviews/hyperk_physical_controls.py /tmp/hyperk-physical-review-5692d376 --half-source /tmp/hyperk-physical-review-f9697734
```

The additional independent controls passed:

| Check | Scope and result |
|---|---|
| Endpoint-step geometry | Exact inventories at seven feasible `(k,n)` cases, including dimensions five and six. |
| Retained prime stages | Independent trial division, initial-pool membership, disjoint swaps, exact orientation and full signature for the 16-pair and 32-pair fixtures. Fourteen corruptions rejected. These remain partial stages. |
| Local occupancy identities | Twenty-five native-point/line-shadow and aggregate-section checks at path degree two, dimensions two through six. No expansion is claimed for that path. |
| Majority signatures | 380 independently summed complete signatures across all relevant blocks/signs through dimension six. |
| Body-kernel reconstruction | Exact rational elimination independently generates coefficient nullspaces at inner ranks two, three and four; three integer reconstructions and twelve composite-modulus reconstructions pass. Three nonzero-trace inputs are rejected. |
| Interleaved complementary coordinates | Eight full compound signatures and 24 shared-trace signatures at dimensions four, six and eight. Native blocks need not be contiguous. |
| Marker-edge rerouting | All 1,024 cuts of a ten-vertex example retain or increase their boundary; degree and middle-use accounting match, and every routed edge has disjoint endpoint supports. This is not an expander existence test. |
| Scalar shared-trace split | 1,827 signed exact quotient/remainder decompositions, including negative totals and composite gaps. |
| Depth and scope controls | Exact finite-depth formulas through dimension twenty; central/repeated-pair failures; equality spill; and a surviving omitted pair-family contraction in a six-dimensional compound. |

The reviewer reconstruction uses raw path products on three labels embedded
in a larger alphabet. Its computed kernel dimensions are coefficient-space
diagnostics for those products, not full incidence ranks at the ambient order.
The finite checks examine algebra, signatures, actual local swaps and the
stated local counting identities. They do not prove the eventual packing or
prime-distribution statements; those are the conventional arguments reviewed
above. No complete new higher-dimensional arrangement is inferred from them.

After adding the reviewer artifacts, `python3 -B check.py` in the delivery
working tree passed repository integrity and all 45 tooling tests. This
records local structural evidence only. I did not run remote CI or alter
any workflow, runner gate or permission.

## Disposition

No scientific repair is required within this review's scope. The optional
coordinate-label wording note above can be retained separately without
changing either frozen proof. Publication of these reviewer-owned files,
final delivery integrity, remote CI and maintainer integration are coordinator
tasks. The full all-dimension, all-full-line objective must retain its open
status; PH is a proved intermediate family with a complete conventional
physical composition, not completion of the user's primary theorem.
