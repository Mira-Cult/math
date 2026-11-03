**Public reading copy.** Presentation and links have been normalized. Historical status statements below belong to their source revisions; see the [current publication status](../README.md#review-and-verification-status). The matching original bytes are in the [source archive](../originals/HYPERK_HANDOFF.md).

# Every fixed dimension: ownership and recovery

Owner/coordinator: `/root`; research authorized by Mira on 2 November
2026. Isolated branch `research/signed-prime-hypercubes-all-k-20261102`.
This workspace investigates full signed-coordinate prime lines for every fixed
integer dimension k >= 2, using exactly the first n^k odd primes and every
sufficiently large odd order n. **State: research complete on 3 November
2026. The full fixed-dimension theorem FP has a complete conventional proof
and a completed independent composition review consuming the separately
reviewed components. No named mathematical lemma remains open in this
qualitative proof chain.** Publication and maintainer disposition remain
separate from mathematical review; no merge or formal approval is performed.
The delivery head and its remote CI result are recorded in PR83.

The earlier reviewed baseline at
`1e7883d705cafbaf717bfacefcf6695baebf6dbe` remains byte-identical. Its
half-coordinate theorem and then-open full endpoint are historical stages;
the additive November 3 sources below resolve the missing families.

## November 3 completion: full composition and exact review pins

Canonical new sources, all additive to the reviewed baseline:

- [Uniform real frame UF](manuscripts/hyperk_full_controller.md), author
  `/root/controller`: independent local KG sampling, expected incoming
  support, a uniform matrix estimate, real correction, and integer rounding.
- [Exact integral frame AF](manuscripts/hyperk_reconstruction_alt.md), author
  `/root/full_reconstruction` with root and controller contributions:
  signed equality and center strata, integer generic-box contraction,
  fixed palettes, exact path subdivision, and bounded point load.
- [Distributed kernel BK](manuscripts/hyperk_distributed_kernel.md), author
  `/root/kernel_architecture`: composition of UF and AF, logarithmic
  covering radius, and every composite residue ring.
- [Full physical composition FC/FP](manuscripts/hyperk_full.md), author
  `/root`: compatible shared-trace splitting, disjoint random greedy
  placement, all-line load bounds, and the common resource ledger.

All four current authors are excluded from independent review of this new
composition. Their cross-checks are author checks. The first new scientific
revision was published before review began:
`c7f22dd8a01d28ab02c832f6c2b8b4145d88b6bb`, tree
`65756bab209c4fd74e32327344942bfc56a1bb25`.
The final composition revision is
`c5cf3d829f83dcc388af6f065d7f9bda66789458`, tree
`faf629e6c7357585720385a36e9a0b3aaf28fb49`. It makes the capacity indices
and computable packing constants explicit. Its six UF/AF/BK manuscript and
program files are byte-identical to the first new freeze. The two FC/FP
scientific files are bound to the second freeze. No reviewed scientific
file is changed by this delivery.

| New independent review | Scientific source | Completed verdict and scope |
|---|---|---|
| [Uniform frame](reviews/hyperk_uniform_frame_review.md), `/root/incidence_review` | `c7f22dd8a01d28ab02c832f6c2b8b4145d88b6bb` | No blocking defect in UF, its input-independent quantifiers, both matrix variances, physicalization, or integer rounding. |
| [Integer absorber and synthesis](reviews/hyperk_absorber_review.md), `/root/half_kernel_review` | Same first freeze | Positive review of AF and its arbitrary-modulus interface, and BK's exact deduction from UF and AF. |
| [Full physical composition](reviews/hyperk_full_composition_review.md), `/root/physical_composition_review` | `c5cf3d829f83dcc388af6f065d7f9bda66789458` | No blocking defect in FC or FP after reading both completed component reports and matching their unchanged source bytes. |

Each reviewer discloses earlier reviewer-only involvement and all scientific
authorship exclusions. The full review checks shared-trace splitting,
simultaneous legal switches, every full-line packing case, complete-bundle
ranges, fresh prime supply, residues, the changed unused-pool mean, and the
variable-depth resource inequalities. Its conclusion covers all varying
sizes `1<=r<=k`; the former omission `2<=r<ceil(k/2)` is resolved.

Review qualifications are preserved rather than edited into old claims.
The second freeze fixes baseline `K_0`, axis capacities `K_1,...,K_(2k-3)`,
and the following partition capacities; its combined packing constant pays
the macro-stage factor 33. The reports also make explicit the primitive
one-row incidence case at complement dimension one and the choice of the
seed gap from the known pool before gap-dependent residue slots are planned.
These are not unresolved assumptions. Frozen author introductions retain
their freeze-time candidate wording; this handoff and the attributed reports
record the completed review status. Historical reviews below keep their
original source and scope.

The new author controls are `hyperk_full_controller.py`,
`hyperk_reconstruction_alt.py`, `hyperk_distributed_kernel.py`, and
`hyperk_full.py`, all under `code/`. They check exact kernel identities,
unit physical signatures, residue generation, partition contracts,
compatible splitting, and symbolic resource inequalities; they are not
full high-dimensional arrangement certificates. Recover from the PR's
current published head, read these four sources and this section, and
preserve the unchanged foundational scientific revisions listed below.

The owner replayed all three independent programs against the exact source
archives and read all three final reports. The controls import no author
code. Among their checks are both matrix variance sums, an independent full
absorber replay from an eliminated incidence matrix, composite-modulus lifts,
6,674 complete signature equations, 20 compatible trace splits, 249 residue
calculations, all 20,160 injections in a packing-law fixture, and multi-pass
disjoint packing through dimension six with full-line loads re-enumerated.
Their negative controls detect omitted families, body-only kernels,
incoherent palettes, cellwise rounding, unpaid amplification, concentrated
occupancy, broken bundle freshness, invalid residues, duplicate or composite
prime endpoints, and target-vector/arrangement confusion. These are finite
checks; the general conclusions rest on the dimension-parametric proofs.

The independent exact-pool checker also passed its retained genuine arrays
and all 53 negative controls, including twelve singleton cases. No new full
higher-dimensional arrangement is claimed as a finite certificate. All 84
inherited scientific, code and input files are byte-identical to the earlier
reviewed baseline; the code README is an intentionally updated index. The
six new component files match the first new freeze, and the two full
composition files match the second. Local history-aware integrity passed
all 45 tooling tests. The scientific remote runs
41606542706 (archival source; see provenance)
and 41607443461 (archival source; see provenance)
concluded **skipped, not passed**. No CI configuration or gate was changed.

PR81 was rechecked at delivery preparation at
`2d4eb572742790d3f4b810126ef744732210628c`. Its five qualitative
manuscripts were fetched and compared byte-for-byte with the pinned
`b837e307fc41975d0fb332c8215d6835ba47a271` source: all are unchanged.
Its reviewed cutoff is then `2^1463`, with a separate `2^1460` corollary
under review. No new numeric source is imported here and no file in that
lane was changed.

### Current endpoint and remaining scope

| Obligation | Current status |
|---|---|
| Exact full-line integer image and congruence interface | Proved and independently reviewed in the stable range. |
| Joint prime targets with the exact total `T` | Proved and independently reviewed for every fixed dimension. |
| UF, AF and exact integral/residue synthesis BK | Proved conventionally; new independent component reviews complete. |
| Full disjoint physical controller FC and all resource inequalities | Proved conventionally; full composition review complete. |
| Requested exact-pool theorem FP for every fixed `k>=2` | Proved conventionally, with no remaining named conditional lemma; complete composition independently reviewed. |
| Finite geometry, matrix, residue, switch and corruption controls | Passed; distinct from proof of an asymptotic theorem. |
| Repository integrity | 45 local tooling tests passed; remote runs observed skipped. |
| Formal kernel verification | Not performed or claimed. |
| Explicit general `N(k)`, growing dimension, all small odd orders | Subsequent questions; outside FP's conclusion. |

The next repository action is maintainer disposition of the completed
reviewed checkpoint under the existing CI and integration requirements.
No additional mathematical premise is proposed for this endpoint. Recovery
and exact-archive commands for the new reviews are in
code/README.md (historical reference; not supplied in this package); the older provenance remains below.
The final delivery comparison also confirms all 22 inherited review files
are unchanged and all 126 local links scanned in the new proof/review bundle
and its indexes resolve. The eight new scientific files retain their exact
reviewed bytes.

## Frozen foundation and lane boundary

- Public square/cube source: Mira-Cult/math
  `c212563021093355c6cb33bf6e6731b43b32edac`,
  `notes/sudes-first-conjecture`.
- Reviewed cube science: `a2445962ec6e06b2a893980fb7a183057eb9bcee`;
  delivery `cdb7879e358f93afa54b685027a27692d22635a9`.
- Four-dimensional scientific source:
  `b837e307fc41975d0fb332c8215d6835ba47a271`; controls
  `61755c8ca37f8ab796ca4eefac6af890825b1b68`; reviewed delivery and this
  branch's parent `112c2bca0d38f82391a34994b63153e7ec08aa74`.
- PR81 was rechecked at opening. Its head
  `50f60405faeee5c1188dfea5934b382ab7e3de85` starts an independent numerical
  cutoff continuation. The qualitative five manuscripts are unchanged from
  the scientific source and have four recorded independent internal reviews.

This branch owns only new `hyperk` sources and a corresponding index entry.
Square, cube, four-dimensional cutoff, Carmichael and public-note work remain
with their existing owners. Manuscript-local labels will be used; no permanent
claim IDs are allocated or changed. No merge, approval or history rewrite is
part of this task. A new mathematical statement is not an accepted premise
merely because finite controls or a previous author claim support it.

## Component authorship and interfaces

1. `/root/incidence`: full integer incidence image, signed intersection types,
   eventual torsion/saturation, bounded generators and exact finite controls.
2. `/root/targets`: absolute-label-set prime targets, exact weights, gcd and
   residue completion, uniform one-dimensional analytic interface.
3. `/root/controller`: recursive marginal and direct-generator architectures,
   complete signed-line signatures, physical fresh-pair and cell allocation.
4. `/root`: global resource ladder, concentration of complete switch bundles,
   exact-pool completion, composition, publication and independent review.
5. `/root/kernel_architecture`: recursive pure selectors, local full-kernel
   projections, bounded marker palettes and precise reconstruction failures.

The dimension-parametric incidence and target milestones are complete.
At the earlier reviewed baseline the physical theorem reached the
half-coordinate family described below. The full reconstruction and physical
composition are now separately reviewed above; the partial theorem's reviews
were not used as acceptance of that new argument.

## First scientific checkpoint

Published workspace: PR83 (archival source; see provenance).
The first frozen scientific revision is
`5692d37633ef4b509e8429cddf4ed762e7235d08`, tree
`53bedaa1ff807edb012596b326e313f88257f558`. The opening ownership checkpoint
is `a403b367a981f686a094c61cfbfac04a4f848e77`. All independent reviews below
name their exact scientific source; later delivery files do not retroactively
change it.

The conventional author results and exact unresolved endpoint are composed in
[hyperk_cube.md](manuscripts/hyperk_cube.md). The full integer image is proved
for odd n >= 3^k by a monic polynomial argument; joint prime targets and exact
weighted completion are proved for every fixed k. The physical controller
proves all axes and every signed line varying in more than k/2 coordinates.
The all-full-line permutation theorem remains open at the distributed
signed-kernel controller. These statements were author claims at the first
freeze; the exact-revision reviews and their limited scopes are recorded
below, separately from the unchanged scientific source.

Canonical new components:

- [Integer image, sparse kernels, pure selectors and compatible flows](manuscripts/hyperk_incidence.md).
- [Joint prime targets, weights and gcd completion](manuscripts/hyperk_targets.md).
- [Physical axes and majority-coordinate lines](manuscripts/hyperk_controller.md).
- [Common finite-depth resource ledger and joint centering](manuscripts/hyperk_resources.md).

Reproduction from the repository root:

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyperk_incidence.py self-test
python3 -B problems/prime-arrays-beyond-square/code/hyperk_targets.py self-test
python3 -B problems/prime-arrays-beyond-square/code/hyperk_controller.py
python3 -B problems/prime-arrays-beyond-square/code/hyperk_resources.py
python3 -B check.py --base 112c2bca0d38f82391a34994b63153e7ec08aa74
```

The inherited local integrity check initially failed because an ordinary local
clone omitted unreferenced historical review objects. Recovering 395 loose
content-addressed objects from the frozen-source checkout, verifying every
object against its SHA-1 and preserving existing objects, repaired provenance.
The repeat passed integrity and all 45 tooling tests. No source, review,
workflow or permission was changed to bypass the initial failure.

Public square/cube sources were fetched at the exact requested public revision
and verified against their returned Git blob IDs. The frozen parent contains
the reviewed cube and four-dimensional manuscripts. All five new scientific
sources are separate files; inherited science remains byte-identical.

## Recovery and evidence boundary

Recover the published branch and the frozen parent above. Read AGENTS.md,
RESEARCH_PROTOCOL.md, the problem index and HYPER4_HANDOFF.md. The PR description
records the full current published head; the additive scientific commit is
frozen before reviewers examine it.
Inherited reviews pertain only to their recorded source and dimension. The
new reviews below explicitly identify their own all-k scopes. Conventional proof, independent internal
review, finite tests, remote CI and kernel verification are separate statuses.

The new exact-revision distributed-kernel and full-composition reviews are
complete, as recorded above. No merge or public-note incorporation is performed.

## Review and verification of the first checkpoint

The [independent incidence review](reviews/hyperk_incidence_review.md), by a
nonauthor of every reviewed source, found no blocking defect at
`5692d37633ef4b509e8429cddf4ed762e7235d08`. It covers IK, the stable rank,
integer section, KG, PS and MF. Its additional controls use a separate archive
and enforce nine source hashes. Nonsymmetric integer lifts, entry moduli
sharing factors with `n`, independent full-matrix geometry for small Smith
computations, relabeled selectors and lattice-valued rounding all passed.
The review does not accept physical packing or the full permutation theorem.
The [independent target/resource review](reviews/hyperk_targets_resources_review.md)
also found no blocking defect at the same exact source. It covers the weight
and gcd formulas, prime completion KPT, and RL/FS/JC while retaining every
geometric hypothesis of the centering lemma. Its new controls check the
dimension-five and dimension-six target fixtures by independently generated
geometry, 1,600 additional weighted completions, gcd recurrence through degree
128, and the exact unused-pool expectation. The separate physical/composition
review is now complete and linked below.

The coordinator's independent arrangement checker and retained exact-pool
square are added after the first scientific freeze. Its replay checks genuine
arrays, not only target lists: all nine entries/eight lines in the square,
the inherited 27-entry/49-line and 125-entry/109-line signed cubes, singleton
degeneracies, and 41 negative controls. See the code instructions (historical reference; not supplied in this package).
These are finite certificates, not a cutoff or a higher-dimensional example.

The first scientific revision's remote integrity run
41528112489 (archival source; see provenance)
completed with conclusion **skipped, not passed**. The commit-run wrapper
initially returned no results because it filters to `pull_request`; direct
Actions inspection found the `pull_request_target` run above. No workflow,
runner gate, permission or branch protection was changed. Local integrity
passed all 45 tooling tests; neither status is mathematical verification.

## Supplementary local kernel investigation

This supplement and the first two review records are frozen at
`99cd33eb8f91682342a671b46599f43b1365ed7c`, tree
`8c989f3d035b10ffce0497da3ff441e5edbb8123`. Its remote run
41530608087 (archival source; see provenance)
also concluded **skipped**, not passed. The five original scientific
manuscripts remain byte-identical to the first scientific revision.

The separate [kernel investigation](manuscripts/hyperk_kernel_research.md)
and [controls](../originals/code/hyperk_kernel_research.py) are additive author work. The
[independent kernel review](reviews/hyperk_kernel_review.md) found no blocking
mathematical defect at its exact frozen revision. They prove recursive pure signed
selectors, finite pairable local projectors, bounded point degree for a whole
family of independently projected graph products, and the coherent-marker
slice identity. Explicit recurrences give their dimension costs.

The distinction is exact: independent marker palettes permit bounded load but
can fail reconstruction; coherent markers recover the exact slice identity
but can meet complementary endpoints and create forbidden mixed contractions.
The code retains both counterexamples, a successful disjoint-endpoint control,
and a color-restriction counterexample. Rational averaging alone controls
coefficients rather than the number of stages sharing a physical cell. These
findings strengthen the local toolkit without closing BK(d).

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyperk_kernel_research.py --self-test
```

The coordinator replay passed all 11 local-kernel full signatures, 8 pure
selector signatures, 48 coordinate-pairing checks, dimension-dependent
invoices and palette constants, the three substantive obstruction controls,
and three corrupted-selector rejections. These are exact finite checks, not
a full prime arrangement or an asymptotic packing proof.

The additional reviewer controls implement the actual cyclic palettes for
all 64 and 512 products in degree-two graph fixtures, exercise all 72 witnesses
in a dimension-four stress case, and verify the coherent identity for both
one- and two-block partitions, including a central example. The review makes
the unsigned fixed-partition convention in (G2), its outer sign in the full
sum, and the unweighted nature of its zero coefficient marginals explicit.
An embedded selector sum need not vanish. These qualifications preserve the
exact reconstruction obstruction.

## Additive half-coordinate controller

Frozen scientific revision: `f9697734c0c1d87eb8ab8af4051d0e8495ac9b56`, tree
`9a66390b89b52d2e416d1c4ed705a9cb39c4044c`. The source and code were frozen
before the two nonauthor physical review scopes began. Its remote run
41530925341 (archival source; see provenance)
completed **skipped**, not passed.

The stronger author theorem UH/PH(k) is canonical in
[hyperk_half.md](manuscripts/hyperk_half.md), with separate
[dimension-parameterized controls](../originals/code/hyperk_half.py). For every fixed
`k>=2`, every sufficiently large odd order admits the exact initial-prime-pool
arrangement for every axis and every full signed line of size
`r>=ceil(k/2)`. The omitted sizes are exactly `2<=r<ceil(k/2)`; the full
all-dimension endpoint remains open. The
[physical/composition review](reviews/hyperk_physical_composition_review.md)
and a second focused
[half-kernel review](reviews/hyperk_half_kernel_review.md) found no blocking
defect at this exact frozen source. The supplement does not alter the earlier
science.

For even `k=2d`, shared complementary traces are scalar and can be repaired
before each native tensor is corrected in the zero-margin, zero-body-trace
kernel. The bounded marker flow is proved for that kernel, not for all proper
signed contractions. Its complete resource depth is `D_half=5k/2-2`, and
its worst simultaneous tuple uses `(2^(2d-1)+1)2^(k-1)` equal-gap pairs.
Both are finite functions of fixed dimension. The old ladder accommodates
them with strict slack. Odd dimensions use the earlier majority theorem.

| Diagnostic k | Lines included in PH(k) | Exact omitted families |
|---:|---|---|
| 4 | `4n^3+12n^2+16n+8` | None |
| 5 | `5n^4+40n^2+40n+16` | `20n^3` pair lines |
| 6 | `6n^5+80n^3+120n^2+96n+32` | `30n^4` pair lines |

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyperk_half.py
```

The author replay checks 15 exact integer/composite-residue reconstructions,
complete compound and shared-trace signatures, disjoint partial prime
stages, seven malformed controls and an explicit proper-contraction scope
counterexample. The path fixtures check identities and disjoint routing;
the expander capacity estimate is proved conventionally in the manuscript,
not inferred from those fixtures. No new full higher-dimensional array is
presented as an arrangement certificate.

The coordinator replayed the exact frozen half-source bytes successfully.
The common resource program gives final exponent `147/200` and adjacent
gap `3/200` for `(k,D)=(5,9)`, and final exponent `207/280` and gap
`3/280` for `(6,13)`. The concentrated-deletion and midpoint margins are
respectively `13/200` and `17/280`, both strictly positive. These diagnostics
test the stated variable-depth formula; they do not replace its proof.

## Separate arrangement-harness correction

The verifier at the kernel scientific freeze correctly accepts the singleton
array, but its optional negative-control harness assumed at least two entries
and an ordered pool with a composite line. The coordinator found this during
delivery, and the independent kernel reviewer reproduced the `IndexError`.
The delivery harness now handles the singleton without those assumptions;
the actual certificate-acceptance logic and frozen arrangement are unchanged.
Its current self-test passes the original 41 rejected corruptions plus twelve
singleton controls, 53 in total. This finite harness correction is separate
from the reviewed mathematical results, and the earlier frozen source and
finding remain available.

## Historical November 2 delivery: review scopes and status

Four distinct nonauthor reviewers produced five records. Each record names
its authorship exclusions, exact archive, source hashes, conventional argument
and independently implemented controls. None is a formal GitHub approval,
journal report, novelty judgment or proof-kernel check.

| Review | Exact scientific source | Accepted scope; excluded endpoint |
|---|---|---|
| [Incidence](reviews/hyperk_incidence_review.md) | `5692d37633ef4b509e8429cddf4ed762e7235d08` | IK, rank, integer section, KG, PS, MF; no physical packing. |
| [Targets/resources](reviews/hyperk_targets_resources_review.md) | `5692d37633ef4b509e8429cddf4ed762e7235d08` | KP/KW/KPT and RL/FS/JC with their geometric hypotheses. |
| [Local kernel supplement](reviews/hyperk_kernel_review.md) | `99cd33eb8f91682342a671b46599f43b1365ed7c` | Recursive selectors, LP, palette bound, coherent slices and exact obstruction limits; no BK. |
| [Physical/composition](reviews/hyperk_physical_composition_review.md) | First science and `f9697734c0c1d87eb8ab8af4051d0e8495ac9b56` | U/UM/PM and BH/BR/UH/PH, including the complete target/resource composition. |
| [Focused half-kernel](reviews/hyperk_half_kernel_review.md) | `f9697734c0c1d87eb8ab8af4051d0e8495ac9b56` | Independent second check of BH/BR, shared traces, complete signatures and local packing. |

Both physical reviewers checked the marker rerouting with parallel edge
labels retained, composite residue identities, compound stage signatures and
the distinction between full-body and full signed kernels. Their new controls
include exact cut enumeration, independently generated kernel demands, bounded
integer flows, scalar trace splitting, interleaved coordinate blocks, and
explicit failures when orbit separation or a body condition is omitted.

Nonblocking precision notes are preserved in the corresponding reviews:
MF uses a linear scalar-flow operator; the positive common gap satisfies
`2<=g`; the first aggregate sums over the `n` labels of coordinate `k`;
and the local projector uses the G2 sign/coefficient conventions described
above. The frozen scientific files were not silently rewritten to erase
these findings. No blocking mathematical correction was required.

| Obligation | Status at delivery |
|---|---|
| Exact geometry and eventual full integer image | Proved conventionally and independently reviewed; odd `n>=3^k`. |
| Joint prime targets with exact `T` and all partition identities | Proved conventionally and independently reviewed. |
| Arbitrary finite-depth resource ladder and fresh supply | Proved conventionally and independently reviewed; centering retains its explicit geometric hypotheses. |
| Physical hypotheses for the half-coordinate family | Proved and checked by two independent physical review scopes. |
| Exact-pool prime theorem for axes plus `r>=ceil(k/2)` | Proved conventionally; complete composition independently reviewed. |
| Local pure selectors and projected templates | Proved conventionally and independently reviewed; global reconstruction excluded. |
| Full signed-kernel distributed reconstruction BK(d), at the earlier delivery | Open there; exact failures of proposed shortcuts retained. The November 3 candidate is separate above. |
| Requested all-full-line theorem in every fixed dimension, at the earlier delivery | Open there; missing sizes `2<=r<ceil(k/2)`. The November 3 full candidate is separate above. |
| Retained arrays, targets, stages, ranks and corruption tests | Exact finite evidence with distinct certificate kinds. |
| Local repository integrity | 45 tooling tests passed; not mathematical verification. |
| Observed remote CI | Skipped, never reported as passed. |
| Kernel verification, numerical `N(k)`, growing dimension, all small odd orders | Not claimed. |

For recovery, use the delivery head recorded in PR83, then archive the three
scientific revisions above before replaying their reviewer scripts. Review
programs deliberately bind old exact sources instead of the latest mutable
checkout. All seven new scientific manuscripts and their producer inputs
retain their frozen bytes; the final delivery adds reviews, status and the
separately disclosed arrangement-harness correction. The square, cube and
four-dimensional scientific sources remain byte-identical to the parent.

Final coordinator checks: `python3 -B check.py --base
112c2bca0d38f82391a34994b63153e7ec08aa74` passed all 45 tooling tests.
Byte comparisons passed for 14 frozen new sources/input, all nine retained
first-science inputs, and all 17 inherited manuscripts. All 97 local Markdown
links in the new scientific/review bundle and its indexes resolved. These
checks concern delivery integrity and provenance; the mathematical judgments
are the separately attributed reviews above. The delivery's remote run is
recorded in the PR description after publication.
