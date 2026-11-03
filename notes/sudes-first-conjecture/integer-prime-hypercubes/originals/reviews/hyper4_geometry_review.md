# Independent physical and geometric review of the four-dimensional controller

Reviewer: `/root/hyper4_geometry_review`.

Proof revision reviewed: `b837e307fc41975d0fb332c8215d6835ba47a271`.
Additional finite-control revision reviewed:
`61755c8ca37f8ab796ca4eefac6af890825b1b68`.

## Verdict and authorship boundary

**Accept within the stated physical/geometric scope.** I found no blocking
defect in the five-level physical axis controller U4/AP4 or the extra-family
physical correction and placement arguments PT/EP4. Their stated imported
integer and analytic interfaces are used consistently, with the actual
prime-pair multiplicities, depletion and local loads paid. This is a
conventional nonauthor mathematical review, not kernel verification or a
formal GitHub approval.

I was newly assigned to this review after the author source was frozen. I did
not author U4, AP4, PT, EP4, the marker construction, the prime targets, or their
original controls, and I made no changes to author sources or Git refs. The
earlier constant correction and deferred-cap clarification visible in the
reviewed source were already present when I began; I do not claim authorship
of those repairs. My own additional central-compound regression is recorded
below.

The main sources examined were [hyper4_axis.md](../manuscripts/hyper4_axis.md)
and [hyper4_trades.md](../manuscripts/hyper4_trades.md), with the bounded
template and residue interfaces of
[hyper4_incidence.md](../manuscripts/hyper4_incidence.md). I also checked the
joint-centering handoff against [hyper4_cube.md](../manuscripts/hyper4_cube.md).
The independent analytic review owns the printed short-interval and
prime-target hypotheses; the independent incidence review owns the full
eventual integer-image theorem. This note does not replace either review or
the final composition review.

I extracted immutable `git archive` snapshots of the two named revisions and
read and ran the relevant code there. A direct Git comparison confirmed that
all five scientific four-dimensional manuscripts were byte-identical between
these revisions. Relevant SHA-256 values at the proof revision are:

| File | SHA-256 |
|---|---|
| `manuscripts/hyper4_axis.md` | `ca9cefea5142343144dfa27904279066743d67e7f79a4c763ff0fc3ab45e4496` |
| `manuscripts/hyper4_trades.md` | `76c41b51b437fbe693a86bd7ec04593a9cc9bb11afe11a6d21661bd75812d418` |
| `code/hyper4_axis_controls.py` | `45e31300287c6976e455e89b185d4eb8f33d470ceacbdb73fed98c83473206b2` |

## 1. Actual permutations and finite capacities

I checked the cellwise orientation rule for ordinary pairs, two-pair
rectangles, four-pair cuboids and eight-pair hypercuboids. In each case the
actual change is the signed tensor coefficient times the common actual prime
difference. It is essential that all pairs in a stage share that difference;
the proof supplies it before using the numeric tensor. Disjointness is required
both within the stage and across stages, and is maintained separately for
cells and prime endpoints.

For a pure pair template `M`, its at most five cell-disjoint signed rectangles
give at most twenty entries, each exactly `+1` or `-1`. Pairing the outer
selector along one coordinate uses at most `2*20=40` distinct pairs. This
implements `d A_sigma tensor M` directly; it does not ask for primes a distance
`2d` apart or stack overlapping cuboids on the same cells. Both inner margins
and both inner signed traces are zero, while the outer selector has one unit
trace. The native pair image is consequently `dM`; all other images vanish.
Orbit separation excludes mixed-pair, triple and body support, not just their
net changes.

The seed/growth argument supplies a complete interval on the `g`-grid. Its
induction uses `d<=R`, not merely a gcd assertion. At the enlarged threshold
`R>=4096gF^2`, binning yields at least 256 equal-difference edges, and the
maximum-degree-two matching argument supplies at least forty disjoint pairs.
The macro appendages remain inside the already complete interval's extension
range. Their total scalar sum is at least `8K_jX`; the central subset and its
complement differ by at most `g` and each retains a complete signed interval
of radius `3K_jX` eventually. Thus both signs are genuine legal configurations
of the same reserved primes, without fractional switching or a second use of
an endpoint.

The fresh-set calculations charge every previously selected endpoint, even
unused switch options. The full axis invoice is below `2^24 n^3K_4`; the new
invoice is `O(n^2(P+g+K_7))=o(n^3K_4)`. Their sum fits the common
`2^40 n^3K_4` deletion allowance. The smallest class supply has power
`3.80`, exceeding the deletion power `3.76`. The proof does not presume that
deletions are equidistributed. The residue classes `-1,+1 mod g` are units
for every even `g` and give differences `2 mod g`; target totals themselves
need not be units.

## 2. The five axis passes and AP4

The five passes retain the correct physical preservation contracts:

1. Transfers between `w` hyperplanes preserve every `w` axis.
2. Transfers between `z` planes at fixed `w` preserve every `z` axis and the
   already fixed `w` hyperplane totals.
3. The two horizontal edge systems preserve one another's axis sums and the
   fixed plane totals.
4. The rank-two checkerboards fix the `z`-axis matrices while preserving the
   `x,y` families.
5. The rank-three checkerboards fix the `w`-axis tensor while preserving all
   three previously fixed families.

Exact axis compatibility, rather than only the total `T`, supplies the zero
integer margins needed in the last two passes. The integer rounding terms
`512gn^2` and `16384gn^3` are retained at their respective dimensions.
Separate correction scales preserve the claimed smaller intermediate drift.

I re-derived AP4's local planned-load counts. At levels 0 and 1 the relevant
hyperplane and plane totals are bounded by the number of incident graph edges
times the actual reservoir multiplicity. At levels 2--4 a fixed projected
coordinate point occurs in at most `Delta`, `Delta^2`, or `Delta^3` labeled
edge tuples. Summing over a signed parameter gives the asserted
`O(Delta^k nL)` union loads. Parallel edge labels are included. The tables'
saturation constants are loose upper bounds; the fixed cap `10^15` leaves
ample positive fraction of candidates. Occupied-cell exclusions use actual
axis load `o(n)` and remain valid with the pre-reserved extra controls.

The orbit restrictions never demand avoidance of the whole extra-line union.
They exclude the free coordinate from all relevant native endpoint orbits,
so each surviving extra line fixes that coordinate. Fresh transverse labels
across the entire reservoir therefore permit at most one stage on such a
line. A Cartesian checkerboard meets a full line in at most two vertices.
This also covers central, reflected and coincident endpoints in the native
coordinate pairs. Every old support avoids all full four-coordinate bodies.

## 3. EP4: whole groups and the exceptional matrix supports

For bodies, triples and common traces there are only `O(n)` reservoirs. Their
entire pass therefore has `O(nL)` incidences with required lines. At most
`O(n/H)` lines can be saturated. I checked the source's potential-line-key
convention: a nonnative surviving key contains a free label in a fixed
coordinate, and depends injectively on that label when its last variable is
assigned. Native body/triple lines have direct load bounds. Potential keys
may be tested before actual incidence is known, because this merely excludes
more choices. Testing existing load plus eighty before committing any support
pays every later within-stage coincidence. Thus deferred labels do not
invalidate earlier cap tests.

Occupied vertices also have a controlled last-variable trajectory: varying
that label traces a subset of one full signed line. Existing maximum line
load `o(n)` excludes only `o(n)` candidate values. The fresh-orbit rule costs
another `o(n)` choices across a complete prefix-plus-macro reservoir. These
are pointwise exclusion bounds, not average placement claims.

For the `O(n^2)` pure pair reservoirs, the global saturation argument would
be insufficient. EP4 uses the correct stronger inputs. If each matrix cell
belongs to at most `B` templates, then a slice at one fixed inner coordinate
has at most `4BnL` planned cells. The native pair lines and outer-coordinate
axes have direct `BL` and `2BL` bounds. The slice estimate bounds saturated
inner-coordinate axes by `O(Bn/H)`. Only `E_*n` templates meet an inner
signed diagonal, so complementary pair lines also have only `O(n/H)`
saturated candidates. The ordered selector choices `a,c,b` make each new
candidate axis or complementary-line key injective in the newly chosen
label. This establishes the local packing step without losing a factor `n`.

The reviewed source correctly counts `(0,0)` on both inner signed diagonals,
using the conservative bound `160E_*nL`. Numeric zero trace does not license
ignoring these support incidences. My central-compound test below confirms
the distinction. Summing the fixed number of separate family/pass caps keeps
all loads `o(n)`, permitting AP4 to be packed afterward. No stage or prime
entry needs to be shared across controllers.

## 4. Whole-reservoir drift, residues and final capacities

For a body reservoir, a lower line meets at most one stage and one vertex;
all eight body corrections therefore spill at most `8X` to such a line. A
pair line can meet at most `8Delta` triple reservoirs: two choices of the
third varying coordinate, at most four compatible sign patterns, and at
most `Delta` graph edges incident to its remaining fixed coordinate. Fresh
free orbits give at most one stage per reservoir. Hence the entire triple
pass has `O(X)` pair drift, not `O(nK_5X)`.

The coupled trace pass has `n` reservoirs per common trace. Splitting a trace
of size `nE` into `n` grid integers bounded by `E+g` is ordinary integer
quotient/remainder splitting; it never divides by `n` in a residue ring.
The separate `K_6` occupancy cap pays its actual pair drift. The final pure
pair solver then receives maximum error `O(K_6X)`, and its coefficients
`O(K_6X log^2 n)+O(gn^2)` fit the `K_7` capacities. Each such reservoir
changes only its native family.

The residue stages are separate from main reservoirs and use nonnegative
representatives `0,...,g/2-1` on distinct stages. The path/tree identities
hold over composite rings. The sequence respects already fixed higher
families modulo `g`, preserves axes exactly, and has actual drift `O(gX)`
by the separate cap. Subsequent main differences are multiples of `g`, so
all residues remain fixed.

The two central configurations of each whole main reservoir give each
macro cell its actual pair midpoint as expectation. A native aggregate can
see many stages but the central scalar difference is at most `g`; a lower
line's contribution range is at most `X` or `2X` by the whole-reservoir
intersection bounds. Thus whole reservoirs are the independent variables.
The joint midpoint scale is `delta K_7=n^.59=o(n^.60)`. The proof separately
pays the unused pool's changed mean and the without-replacement completion
noise. I found no hidden cellwise-independence assumption.

## 5. Replayed finite evidence

Environment: Python 3.12.14; standard library for all commands below.
Commands were run from the root of the corresponding immutable archive.

At `b837e307fc41975d0fb332c8215d6835ba47a271`:

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyper4_axis_controls.py
python3 -B problems/prime-arrays-beyond-square/code/hyper4_axis_controls.py --verify problems/prime-arrays-beyond-square/inputs/hyper4_axis_physical.json
```

Both passed. The first checks 52 switch patterns, 19 changes from nonzero
reference states, 16 exceptional endpoint cases, 24 composite-ring prefix
tests, eight numeric five-pass compositions, planned projection-union loads
with parallel edges, and the listed pool/support/orientation/capacity negative
controls. The retained certificate is a permutation of all 14,641 initial odd
primes at order 11, with eighteen disjoint stages. Its canonical certificate
digest is `c5cff56b6bd6408f056cbbb9fae618b82d320519cf44548bc51492837737557d`.
It is a physical-controller certificate, not a prime-line arrangement.

At `61755c8ca37f8ab796ca4eefac6af890825b1b68`:

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyper4_trade_controls.py
python3 -B problems/prime-arrays-beyond-square/code/hyper4_trade_controls.py --verify problems/prime-arrays-beyond-square/inputs/hyper4_forty_pair_trade.json
```

Both passed: 256 exact image cases; actual eight-pair and forty-pair stages;
four whole-bundle families; seven corrupted partial certificates rejected;
exact rational budget margins. The forty-pair input has eighty distinct
prescribed-pool entries, gap six, and twenty nonzero native pair-line images.
It is explicitly a partial trade, not a full array certificate.

For an additional reviewer regression, run the following at the latter pin:

```sh
python3 -B - <<'PY'
import sys
from collections import Counter
sys.path.insert(0, 'problems/prime-arrays-beyond-square/code')
import hyper4_trade_controls as h
r = h.tensor(h.edge(0, 1), h.edge(0, 1))
assert (h.trace(r, 1), h.trace(r, -1)) == (2, 1)
m = h.add((1, r), (-1, h.rectangle(2, 3, 4)),
          (-1, h.rectangle(5, 6, 7)),
          (-1, h.rectangle(8, 9, 10, -1)))
a = h.rectangle(14, 15, 16)
t = h.tensor(a, m)
im = h.image(t)
assert len(m) == 16 and h.trace(m, 1) == h.trace(m, -1) == 0
assert len(im) == 16
assert all(k[0] == (0, 1) and k[1] == (1, 1) for k in im)
inc = Counter(k for p in t for k in h.line_incidence(p)
              if k[0] == (2, 3))
assert len(inc) == 8
assert all(inc[(2, 3), (1, s), (x, y)] >= 1
           for x, y in a for s in (1, -1))
assert h.verify_physical(h.make_physical(t))['pairs'] == 32
print('Central compound: 32 physical pairs; eight complementary support '
      'lines; zero complementary line changes. Passed.')
PY
```

This passed. It tests a central matrix cell that belongs to both complementary
signed diagonals, a case distinct from the maximum-forty-pair fixture.

I also ran `python3 -B check.py` in the owned repository after writing this
review note. Repository integrity and all 45 tool regression tests passed.
This local tooling result is separate from the mathematical verdict and is
not a remote CI result.

## Remaining boundaries

No new repair is requested by this review. The exact analytic hypotheses,
SPT4 prime targets and full SI4 integer image still require their separately
assigned reviews, and the coordinator must perform the final composition
review at an available frozen revision. None of the finite tests proves
an eventual estimate, a numerical cutoff or a successful remote CI run.
No public source, accepted cube manuscript, unrelated lane or formal approval
was changed during this review.
