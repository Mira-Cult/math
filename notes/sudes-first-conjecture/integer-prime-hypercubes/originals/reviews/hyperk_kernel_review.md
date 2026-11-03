# Independent review: local kernel templates and the distributed obstruction

Reviewer: `/root/incidence_review`. Review date: 2 November 2026.

Exact frozen scientific revision:
`99cd33eb8f91682342a671b46599f43b1365ed7c` (PR83).

**Verdict: no blocking mathematical defect found in the stated local
results or the preserved obstruction examples.** This review covers
PS(b), LP(d), the finite-palette point-incidence bound, the coherent-slice
identity and the failed-architecture limits in
[hyperk_kernel_research.md](../manuscripts/hyperk_kernel_research.md).
It does not accept BK(d), exact distributed reconstruction, physical global
packing, or the full prime-hypercube theorem. The newer half-family
physical source is outside this review.

## Authorship and source boundary

I did not author the reviewed investigation, its code, or the coordinator's
arrangement verifier and square input. The investigation author is
`/root/kernel_architecture`. My only additions for this assignment are
this review and [hyperk_kernel_controls.py](hyperk_kernel_controls.py).
I have preserved the earlier incidence review and its exact source pin.
No author source, input, claim, or Git reference was modified. This is
conventional internal mathematical review, not a formal GitHub approval,
remote CI, or proof-kernel verification.

I read the complete new manuscript and its code, together with the
arrangement verifier and retained square certificate for the evidence
boundary. The repository protocol and problem scope were read for the
preceding incidence review and remain applicable. Replays used a separate
`git archive` of this new revision, byte-compared to `git show`; the
reviewer controls enforce all four hashes before importing any source.

| Frozen file | SHA256 |
|---|---|
| `manuscripts/hyperk_kernel_research.md` | `c4dc2db4da2e502f0bc8d564e44c2f504b13e9e0fae7ae77b780cfdb70838f44` |
| `code/hyperk_kernel_research.py` | `4c96f78d90110752293dc798059f87c091b7d6578ea63c0734cc3541d3d2cc34` |
| `code/check_hyperk_certificate.py` | `ed71e345fdc92c30303657a11ef34909d42a5413ea9eb00a1c59ae645f94dd76` |
| `inputs/hyperk-square3-arrangement.json` | `b2367b8e8edc6d506054751566f0ba7ddbfc4e92f2213bd641316ea1f9d18d4f` |

## 1. Recursive pure selectors

The recursion has a valid base at `b=2`: the common positive label in
the two factors gives native body contraction one, the distinct private
labels give no other common parameter, and each axis contraction is zero.
For larger `b`, the same copy of `Q_C` is used wherever the subset `C`
appears. This consistency is necessary for the cancellation and is
explicitly enforced in both manuscript and code.

For a tested proper positive block `D`, terms with `D` in the unused
coordinates pair bijectively with terms containing the selector `Q_D`.
Both have native contraction one, identical remaining factors and
opposite outer signs. If `D` lies properly inside another selector,
inductive purity makes its contraction zero. If it crosses groups,
disjoint reflection-orbit alphabets preclude a common parameter. These
possibilities exhaust the unpaired terms. Axis contractions vanish
factorwise; other signed orientations miss the positive support. On the
full positive body every nonempty proper-block collection crosses at
least two alphabet groups, leaving only the raw tensor's unit contraction.

Different collections assign some coordinate to different alphabet
groups, even if they cover the same union. Their supports are consequently
disjoint. The inductive entries and two-point differences are all signed
units, so no coefficient of magnitude two is introduced by summation.
Zero axis sums then imply equally many positive and negative cells in
every coordinate fiber. Pairing those cells gives a disjoint exhaustive
pairing along any chosen coordinate. This is a numeric switch template;
it does not itself furnish the fresh equal-gap prime endpoints.

The alphabet and support recurrences in (PS2) count exactly the stated
construction. The alphabet count allocates each proper-subset copy once;
the support sum counts disjoint partition terms. The listed values through
dimension six check. Common injective relabeling into distinct reflection
orbits preserves equality and reflection incidence. Whole-coordinate
reflections then give any normalized body orientation. This does not
permit unrelated independent relabeling of the same abstract alphabet
in different coordinates.

## 2. Local projector and signed witnesses

For any signed block the first varying coordinate fixes its parameter,
so an edge product has at most two witnesses. Each contributes a signed
unit. The ordinary scalar can therefore be zero or have magnitude two;
the construction retains the individual signed witnesses and does not
replace them by an unjustified unit coefficient.

Each witness receives its own orbit alphabet, disjoint from all raw
endpoint orbits and from the other witnesses in that bundle. For any
tested signed block `D`, its native scalar on the raw factors agrees
exactly with the native scalar of the **shared** `Qtilde_D`. Thus the
inclusion-exclusion pair cancellation remains valid. Proper internal
contractions vanish by purity and mixed alphabet groups cannot meet.
There is one additional case worth making explicit when reading the
proof: a tested block with the same coordinate set as a selector but a
different normalized orientation vanishes by the selector's other-body
purity. It is not one of the paired native terms.

The center is harmless in this argument. A zero witness is a single
parameter, even though several different signed blocks can witness it.
Those are different line constraints with separately allocated selectors.
The selectors use only noncentral orbits, so no central cell creates an
intersection between selector and raw groups. Opposite endpoint labels
are likewise accounted for by the signed witness definition and orbit
avoidance.

After expanding the witness sums, distinct decorated collections assign
different alphabet groups to some coordinate. Consequently their supports
are disjoint and all surviving entries remain `+1` or `-1`, including
the zero-scalar and coefficient-two cases. Zero axes give the same
coordinate-fiber pairing as PS. All involved block, witness and partition
sets have sizes bounded solely in the fixed dimension. LP therefore gives
the stated finite local full-kernel templates. It makes no reconstruction
statement about independently projected expansions.

## 3. Finite-palette bounds, including zero

The palette statement is valid for the collection of graph-edge products,
with one fixed orientation for each edge and degree counting edge
incidences. It is not a statement about an arbitrarily repeated multiset
of the same product. An additional repetition load would need to be
counted separately in a physical application.

There are at most `w_d=2(h_d-d)` witnesses in a bundle. The monotone
alphabet recurrence gives `a_d` as an upper bound for every selector
alphabet. At a greedy step there are at most

`2d+(w_d-1)a_d`

forbidden positive orbits. Taking `H_d` palette blocks indexed, for
example, by `0,...,H_d-1`, the hypothesis `m>H_d a_d` makes all their
candidate positions distinct for the current witness, even across the
cyclic wrap. A forbidden orbit therefore eliminates at most one palette.
The stated `H_d=2d+w_d a_d+1` leaves an admissible choice. The center is
not assigned a fictitious second representative: its witness is separately
tagged, uses base zero, and its noncentral selector must avoid the already
chosen alphabets just like every other witness.

For the point-incidence bound, fix an output coordinate in a selected
block. Each palette/index pair determines at most one residue
`rho(t) mod m`. Since `rho(t)` ranges over `0,...,m-1`, that residue
gives at most the two nonzero witnesses `t=+(rho+1),-(rho+1)`, plus
the exceptional possible witness `t=0` when `rho=0`. Thus the precise
upper bound `2H_d a_d+1` is covered by the manuscript's `3H_d a_d`.
This also handles arbitrary signs of the observed output coordinate.

For each resulting witness tuple, an original edge in a covered
coordinate is incident to its specified signed witness value. An edge
in an uncovered coordinate is incident to the observed output value.
There are at most `Delta^d` choices of the complete edge product. Once
that product is fixed its chosen palettes are fixed; there is no extra
factor for alphabet words, coefficients or placements. The displayed
recurrence counts the collections of disjoint signed blocks, and each
contains at most `floor(d/2)` blocks. This proves exactly the stated
`B_(d,Delta)` bound. Dimension one is the immediate separate edge-difference
case; the palette formulas use the explicitly defined `a_d` for `d>=2`.

Summing this point-incidence estimate over a specified signed equality
or central stratum gives the stated support bound by its number of cells.
The argument pays for support with zero net contraction as well. It does
not infer occupancy from trace cancellation. The constants are large
but finite for every fixed dimension, under the stated ambient-order
hypothesis.

## 4. Coherent slices and the reconstruction boundary

The exact algebra behind (G2) is sound. To make the sign convention
unambiguous, let `C_pi(R)` denote the unsigned product for a fixed
partition, before its outer factor `(-1)^|pi|` in (LP1). For selectors
depending only on `(H,t)`, expansion of the edge factors gives

`sum_e x_e C_pi(R_e) = sum_(t_H) (tensor_H Q_(H,t_H)) tensor F_pi(t,.)`,

where `F_pi(t,z)` is the literal slice of `M` at the prescribed signed
coordinate values. This is the displayed G2 identity. The contribution
to the complete projector has the additional outer sign
`(-1)^|pi|` on both sides. No Möbius sign disappears in the full sum.

If `M` is in the full signed-line kernel, then for each fixed parameter
tuple its free-coordinate slice is in the full kernel on those free
coordinates. This follows because a free-coordinate line is one of the
original required lines with the other coordinates fixed. Furthermore,
summing `F_pi` over any one marker parameter is the corresponding
contraction of `M`, so its **unweighted coefficient marginal** is zero.
These are genuine full-kernel slices, not merely zero-axis slices.

The qualifier "unweighted" matters. In general
`sum_t F_pi(t,.)=0` does not imply that the sum after insertion of the
varying selector `Q_(H,t)` is zero. The tests below explicitly retain
nonzero embedded sums with zero coefficient marginals. Thus neither the
coherent identity nor the point-incidence estimate is an exact
reconstruction theorem.

Adaptive palettes establish endpoint avoidance and the point bound, but
the selector associated with `(H,t)` can then depend on other raw
endpoints. It cannot be pulled outside the edge-product sum, and (G2)
no longer follows. Conversely, a globally coherent selector need not
avoid every complementary endpoint. The manuscript states this mismatch
as an open obligation and does not combine the two incompatible
properties as if they were already simultaneous. The equation expressing
failure of independently projected reconstruction is supported by an
exact nonzero full-kernel residual.

The unsigned-component convention for (G2), and the equal-coordinate-set
different-orientation LP case noted above, are useful precision points.
They do not require changes to the stated local mathematical results;
this review records explicitly how the formulas are read and checked.

## 5. Failed architectures and exact counterexamples

The shared-label counterexample has the claimed images. The two pair
selectors have equal native trace one, so their difference is in `K_2`.
The one-coordinate difference is in `K_1`. Nevertheless their tensor
product has full positive body contraction one and nonzero mixed pair
image `e_a-e_c`. This directly refutes unrestricted
`K_b tensor K_t subset K_(b+t)` on common label supports. Disjoint
reflection-orbit supports restore the implication, because a block is
either internal or crosses disjoint absolute-value supports. Here
disjointness includes the central singleton orbit if it is present.

The color-restriction example also has the claimed force: globally
cancelling pair traces become `+1` and `-1` on separate monochromatic
boxes. Color-resolved contractions therefore constitute extra conditions,
not consequences of membership in the ordinary kernel. If imposed, they
give the corresponding internal box kernels by the definitions; their
correction stage and load still need proof.

The averaging discussion is correctly limited. Averaging genuine fixed
linear projections that are the identity on `K_d` is an exact rational
identity there, but says nothing about integral physical support counts.
The anchored zero-axis basis has exactly `(n-1)^d` supports containing
the center. This demonstrates failure of the naive separate-reservoir
implementation; it is not a lower bound for other decompositions and
is not asserted to be a full-signed-kernel basis. The source preserves
both qualifications. None of these local or negative results closes BK.

## 6. Replayed evidence and independent additions

All following scientific commands ran under Python 3.12.14 against the
archive of the exact revision:

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyperk_kernel_research.py --self-test
python3 -B problems/prime-arrays-beyond-square/code/check_hyperk_certificate.py --self-test problems/prime-arrays-beyond-square/inputs/hyperk-square3-arrangement.json --negative-controls
```

The kernel self-test passed eight pure-selector full-signature checks,
14 coordinate-pairing checks, 11 local-projector full-signature checks
and 34 projector pairing checks; symbolic invoices through dimension
seven; palette-constant diagnostics through dimension six; and the
marker-reconstruction, endpoint-overlap, disjoint-endpoint repair and
color-restriction controls. Three corrupted selectors were rejected.

The independent reviewer controls may be run from a checkout containing
this review by passing a fresh archive directory:

```sh
mkdir /tmp/hyperk-kernel-review-source
git archive 99cd33eb8f91682342a671b46599f43b1365ed7c problems/prime-arrays-beyond-square | tar -x -C /tmp/hyperk-kernel-review-source
python3 -B problems/prime-arrays-beyond-square/reviews/hyperk_kernel_controls.py /tmp/hyperk-kernel-review-source
```

They passed the following additional checks. The palette assembly,
partition enumeration, sparse step-word signatures and slice identity
are independently written; the finite pure-selector inputs are imported
from the byte-bound author source.

| Control | Result |
|---|---|
| Complete products of an eight-edge degree-two graph, `d=2` | All 64 projected templates have zero full signed image; eight center witnesses; maximum point incidence 10, against bound 1836. Ambient order 105. |
| Same construction, `d=3` | All 512 projected templates have zero full signed image; 224 center witnesses; maximum point incidence 22, against bound 916344. Ambient order 6945. |
| Saturated signed-witness example, `d=4` | All 72 possible witnesses are allocated simultaneously; resulting 9872 signed cells have zero full image and disjoint component supports. Ambient order 811353. |
| Palette inversion | The actual witness is recovered among at most `3H_d a_d` candidates, including center aliases, negative witnesses and cyclic wraparound. |
| Four-dimensional coherent partitions | One- and two-block G2 identities agree exactly. Both yield embedded support 64 with zero coefficient marginals; wrong-orientation and crossing-original-group controls give zero. |
| Three-dimensional central slices | A full-kernel tensor reconstructed from 157 anchored edge products satisfies G2 with central witnesses, kernel-valued slices, zero marker marginals and nonzero embedded support 64. |
| Finite arrangement boundary | An independent sieve, independent signed-line sums and an exact pool comparison verify the supplied order-three square. |

The arrangement verifier was also read in full. It generates actual
full-line cell sets by endpoint/step enumeration, verifies each constraint
against that inventory, recomputes every sum from entries, checks exact
primality by trial division, and compares the sorted entries with the exact
initial odd-prime pool. It rejects duplicate or omitted constraints,
misreported sums, invalid coordinates, wrong entry types, shifted pools,
duplicate or wrong entries, composites and target-vector masquerades.
Its self-test passed 41 negative cases and the separate supplied square
test passed another 13. The inherited cube certificates at orders three
and five passed; five singleton cases passed. Accepted family metadata
is reported explicitly, so an intermediate-family certificate is not
reported as a full-family certificate.

There is a separate frozen test-harness limitation. The coordinator
identified that `negative_controls` assumes at least two entries and
also assumes the ordered pool has a composite required sum. I confirmed
that ordinary verification of `build(2,1,[3])` passes, whereas applying
the frozen negative-control harness to it raises `IndexError`. The five
singleton successes above are positive verification cases, not singleton
negative-control replays. This does not make the verifier accept a bad
certificate and does not affect the kernel results. A generic harness
correction announced by the coordinator belongs to a later delivery and
is not covered by this frozen source pin.

The square certificate is a real finite arrangement, and the local
projected tensors are signed numeric templates. These are different
evidence types. Neither acceptance establishes a uniform asymptotic
theorem, and the verifier and source both preserve that boundary.

Local `python3 -B check.py` in the delivery working tree passed all 45
integrity/tool tests after the reviewer files were added. This verifies
repository structure and tool behavior, not mathematical correctness.

## Disposition

The reviewed results supply improved local pure selectors, exact
full-kernel projection of each individual edge product, a quantitative
finite-palette support bound, and the coherent-slice identity. Their
counterexamples identify why those ingredients do not yet assemble into
BK(d). No mathematical correction was required for these kernel claims;
the separate singleton negative-control harness follow-up is recorded
above.

The remaining obligation is exactly the one named by the author: an
integer, globally bounded-load reconstruction that simultaneously keeps
local physical purity, endpoint avoidance and exact compatible slice
routing. This review confers no completed status on that obligation or
on the full signed-line prime-permutation theorem. Remote CI, publication
and integration are separate delivery matters.
