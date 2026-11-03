**Public reading copy.** Presentation and links have been normalized. Historical status statements below belong to their source revisions; see the [current publication status](../../README.md#review-and-verification-status). The matching original bytes are in the [source archive](../../originals/reviews/hyper4_incidence_review.md).

# Independent incidence review: four-dimensional signed lines

Reviewer: `/root/hyper4_incidence_review`.

Frozen author revision: `b837e307fc41975d0fb332c8215d6835ba47a271`
(private PR81). Review date: 2 November 2026.

**Verdict: accepted for the stated integer-incidence and bounded numeric
interfaces, with no blocking defect found.** This verdict covers SI4, MP4 and
MR4 in [hyper4_incidence.md](../manuscripts/hyper4_incidence.md), their stated
numeric contracts with the physical controller, and the retained exact
small-order incidence certificates. It does not by itself accept the fresh
prime supply, physical support packing, analytic prime targets, or the final
prime-permutation composition. Those require the distinct reviews requested
by the research order.

## Authorship and source boundary

This reviewer was spawned after the author source was frozen. I did not write
the incidence manuscript, its original producer/checker, the marker projection,
the prime-target construction, U4, or the extra-controller packing proof. I
supplied only this review and the accompanying additional adversarial control
[hyper4_incidence_adversarial.py](../../originals/reviews/hyper4_incidence_adversarial.py). No author
source or Git reference was modified. This is a conventional mathematical
review, not a formal GitHub approval or kernel verification.

I read the repository working agreement and research protocol, the problem's
index/model/reference/interface records, the full frozen incidence manuscript,
the axis-image and tensor-expander imports in
[incidence.md](../manuscripts/incidence.md), and the integral cut-flow proof in
[signed_incidence.md](../manuscripts/signed_incidence.md). I inspected the
numeric-template boundary used by [hyper4_trades.md](../manuscripts/hyper4_trades.md).
The five principal incidence files, the two imported incidence sources, and
the inherited Smith checker were byte-compared with their frozen Git versions
before reporting the replay. The intervening delivery additions did not change
these reviewed bytes.

For the graph-order issue I also fetched the actual
F1/F2 source at scientific revision 4ac266e7c4994a8502eb2a0c57d6b1d3fbd801c5 (archival source; see provenance).
F1 holds for every integer order at least two, so its use on a possibly even
marker population does not introduce an odd-order or subsequence hypothesis.
I checked its 32-permutation cut argument and F2's integral capacity argument.

Selected SHA256 bindings at the frozen revision:

| Source | SHA256 |
|---|---|
| `manuscripts/hyper4_incidence.md` | `b91309ac57931ac4fcd7d382cb1973806dfc3aa02f96148e324da7dd589c1f67` |
| `code/hyper4_incidence.py` | `39be5acaea82d2f5261122be29c1e37f5e6ae4a0818b7d36ba092bdac7b56a1c` |
| `code/verify_hyper4_incidence.py` | `a2a44ee682336f358dde3f552d11ff54cafb4ad354e968a623e00e1455bcf416` |
| `inputs/hyper4_incidence_n3.json` | `3e86b23f3910c32c27b3c5700e1fb10a1b26d1ef650095b2a2592763cb283abc` |
| `inputs/hyper4_incidence_n5.json` | `969799b33e0d633450fd2129182a9c073adf97c15bb5f19dc9c81be167373899` |

## Mathematical audit

### SI4: complete image, rank, integer kernel and congruences

I independently rederived the necessity of (A), (P), (T) and (C) by the
displayed partitions of coordinate and diagonal sections. In particular,
the twelve complementary-pair trace identities are independent restrictions
after the axis, pair-margin and triple-total constraints; they cannot be
removed merely because all directional grand totals match.

For sufficiency, the integral axis splitting and the sequential slice lift
are valid over the integers. Subtracting a lift leaves twelve zero-margin
matrices, sixteen zero-total vectors and eight body scalars. The subsequent
four steps are genuinely triangular:

1. Five distinct noncentral orbits give a unit on one body, with lower-family
   spill only. Reflections provide all eight orientations without introducing
   another body image.
2. Four fresh orbits avoiding the two endpoint orbits give a native triple
   transfer. Its pair spills have disjoint row/column orbit supports and
   therefore both signed traces zero. Central or reflected transfer endpoints
   do not invalidate this conclusion.
3. Two generic unit-trace rectangles on disjoint orbit sets correct exactly
   one shared complementary trace, on both sides of its identity at once.
4. The anchored projection `K_uv` removes both traces integrally. Its support
   uses at most five noncentral orbits. At the claimed minimal order `n=17`,
   eight available orbits leave the three required by the outer selector.
   That selector isolates the native pair kernel; mixed contractions vanish
   by orbit separation and complementary contractions vanish by the two
   zero traces. No denominator is introduced.

These steps suffice for **every odd `n>=17`**, not just tested orders. The
resulting image is exactly an integer kernel of homogeneous equations, hence
saturated. I checked the rank calculation

`[n^4-(n-1)^4] + 12(n-1)^2 + 16(n-1) + 8 - 12`

equals `4n^3+6n^2-4n-9`. Each matrix's two trace coordinates are independently
surjective onto `Z^2` using the two unit markers, and the twelve equations
equate disjoint pairs of those trace coordinates. Thus there is no uncounted
rank loss in that subtraction. The dependency and array-kernel ranks follow.

Fixing all orbit choices makes the lift section integer-linear. Therefore
`B_u-J(L_4 B_u)` is a genuine integral generating set for the full kernel;
the source correctly calls it redundant rather than a basis. Subtracting the
constant array `r` and dividing target coordinates by `q` proves the stated
entry-congruence criterion. The fixed total then has the required congruence
automatically by summing any complete axis family. No coprimality of `n` and
`q` is needed for this integer-lift statement.

### MP4: bounded projection and marker-flow repair

I checked the tensor-expander import including its integer correction, not
only its real inverse. Rounding the graph-product coefficient matrix creates
entry error at most `Delta^2/2`; the tree-product repair contributes at most
`Delta^2 n^2/8=512n^2`. Thus the retained `1/2+512n^2` term is justified.
The spectral-gap estimate at degree 64 and expansion eight gives the stated
`5 log n+5` right-inverse bound.

Only `O_Delta(n)` graph rectangles can meet a signed diagonal. A rectangle
has total absolute trace at most four, so distributing its unit trace terms
among separate markers gives at most five disjoint signed rectangles. The
orbit-use cap `256 Delta^2` leaves enough eligible labels uniformly in large
`n`, and bounds every marker-cell load. This avoids the otherwise serious
concentration at fixed marker cells.

The lower bound on both marker populations is sound. For the plus trace,
every `R_ee` contributes. For the minus trace, reflection preserves the
zero-sum subspace and sends a nonzero edge column to a nonzero vector; the
edge columns span that subspace, so it has nonzero pairing with some edge
column. Distinct first edge labels give distinct contributions. Thus each
population is at least `|E(G)|>=4n`.

Replacing a conflicting marker-graph edge by a two-edge path through a
disjoint marker preserves expansion: each originally crossing labeled edge
has a crossing edge on its path, and edge copies remain distinct. The use
cap 128 gives maximum degree 320. The fixed forbidden-support count and
`p>16L+8` guarantee an eligible middle marker. Integral cut flow then gives
coefficients at most `ceil(||X||_infinity/8)`. I checked the resulting native
cell-load bound `Delta^2+321L` and the `O_Delta(n)` count of templates that
touch either signed diagonal, including trace-cancelling rectangles.

The compound template entries are all `+1` or `-1`, because the component
rectangles are cell-disjoint. The stated numeric interface therefore permits
the physical implementation with at most forty same-difference pairs; it
does not quietly demand increments of `2d` on a shared cell. This observation
does not itself supply those prime pairs or their global placement.

MP4 is correctly stated for all sufficiently large odd `n`, rather than
claiming its marker population and extra orbit inequalities already hold at
17. SI4's explicit order 17 and MP4's further eventual threshold are distinct.

### MR4: composite-modulus residue routing

The spanning-tree columns are an integral basis of the zero-sum lattice.
Their tensor product thus expands every zero-margin residue matrix over
`Z/hZ`, including nonfields. Projecting the rectangle coefficients leaves
marker demands with zero total modulo `h`. Prefix sums along the marker
ordering give edge coefficients in `0,...,h-1`. The repaired path has degree
at most ten: two original incidences plus two per at most four uses as a
middle vertex. Identical coefficients on the two replacement edges cancel
at that middle vertex, over every modulus.

The residue solver never divides by `n`, a trace multiplicity, or a nonunit.
It uses the whole fixed marker collection even when most tree-product
coefficients are zero. The resulting template and diagonal-touching counts
remain bounded as stated. The manuscript correctly leaves the actual
integer drift and the distinct-stage capacities to the physical proof.

## Replayed evidence and adversarial additions

Commands ran under Python 3.12.14 from the successor repository root:

```sh
python3 -B problems/prime-arrays-beyond-square/code/verify_hyper4_incidence.py
python3 -B problems/prime-arrays-beyond-square/reviews/hyper4_incidence_adversarial.py
python3 -B check.py
```

The original checker passed independent full-line inventories at orders
3, 5 and 17; all orientation/gadget checks; integer and odd lifts; marker
projection; residue routing for `h=1,5,6,13,65`; and the supplied corruption
controls. The two exact small-order certificates passed:

| Order | Full lines | Full rational rank | Array-kernel rank | Nonunit factors |
|---|---:|---:|---:|---|
| 3 | 272 | 81 | 0 | `3` four times, `6` once |
| 5 | 888 | 572 | 53 | `5` eighteen times, `10` seven times, `30` eight times, `60` twice |

I inspected the independent geometric reduced matrix and the verification
of the elementary operations, integer transforms and their integer inverses.
The checker verifies the entire transformed matrix, complete pulled-back
kernel/dependency bases, and every recorded divisibility row. Its conclusion
does not depend on trusting the producer's HNF/Smith library output. The
indices `486` and `2^19 3^10 5^35` are finite saturation defects, not exceptions
to the theorem whose incidence assertion starts at 17.

The additional reviewer control is deliberately different from choosing a
random array and lifting its already-attainable line vector. It independently
chooses zero-margin pair matrices, imposes only the twelve cross-trace
equations, chooses arbitrary zero-total triple vectors and arbitrary body
values, and asks the author lift to realize those equation-selected targets.
Actual line sums are then recomputed directly from their defining cells.
The checks passed at orders 17, 19 and 21, with respectively 23,400, 32,080
and 42,680 lines. A further nonconstant example at `n=17` passed the requested
entry congruence `3 mod 17`, so the modulus shares the whole order and cannot
be inverted. These are signed integer lifts, not positive arrays or prime
arrangements.

The repository integrity command passed, including all 45 tooling regression
tests. That pass establishes only repository/tool consistency. The uniform
mathematical verdict rests on the audited constructions above; finite tests
do not prove the entire odd tail. I found no unresolved incidence or bounded
numeric-solver obligation within this review's stated scope.
