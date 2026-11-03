# Independent review of the half-coordinate kernel and physical templates

Reviewer: `/root/half_kernel_review`. Date: 2 November 2026.

Exact scientific revision:
`f9697734c0c1d87eb8ab8af4051d0e8495ac9b56`.

**Verdict: no blocking defect found in BH(d), BR(d), the shared-trace
correction, or the compound signature and packing arguments in Sections
2--6 of [hyperk_half.md](../manuscripts/hyperk_half.md).** The arguments
have fixed dimension as a parameter; the finite controls below are supporting
implementation checks, not the reason for the universal conclusion.

This is a deliberately focused second physical review. The full U/UM/UH/PH
composition, analytic prime supplies, target construction and resource ledger
have separate review owners. This note does not accept the open controller
for every full signed family in dimensions at least five.

## Independence and exact source

I was assigned this review after the source was committed. I authored none
of its mathematics, code, inputs, or dependencies. I changed only this note
and [hyperk_half_kernel_controls.py](hyperk_half_kernel_controls.py). I did
not edit author files, Git objects, branch references, repository permissions,
or workflows, and made no remote write or formal GitHub approval.

I read the repository agreement, protocol, required problem context and code
instructions; there is no deeper `AGENTS.md`. All scientific reads and the
author replay used a separate `git archive` of the exact source above. The
following bytes were compared directly with `git show` at that revision.
The independent control program enforces the same five hashes before running.

| Frozen file | SHA256 |
|---|---|
| `manuscripts/hyperk_half.md` | `0a15b37c530754a70f4b42ac410445c88532b0c6f28856bedf5ac280ee09afbe` |
| `code/hyperk_half.py` | `2ba335cb46208f3597a8aeff619ceb62f6661eaac57738cab92cb08eb727201c` |
| `manuscripts/hyperk_controller.md` | `bcccf122f966daf70101bfff1f4cf00cfc9559c68c5097d80c981ae405cf1f23` |
| `manuscripts/incidence.md` | `2c9e334928fbadffa703ad2baebbcabd3049a3c356037805526565d8256b53e5` |
| `manuscripts/hyper4_axis.md` | `ca9cefea5142343144dfa27904279066743d67e7f79a4c763ff0fc3ab45e4496` |

I also inspected the inherited graph-existence statement and its elementary
32-permutation proof, which has no parity restriction on graph order. This
matters because a marker population can be even despite odd array order.
The tensor-expander proof in `incidence.md`, Section 3, is explicitly for
arbitrary fixed tensor rank. Its additive rounding term is the one retained
in (H1), not the matrix-only bound.

## Conventional mathematical findings

### Bounded unit-marker population and allocation

Every target point belongs to at most `Delta^d` labeled raw edge products.
Summing this incidence bound over the `n` points of each full body, and
over its `2^(d-1)` signs, bounds the sum of the absolute body traces by
`2^(d-1) Delta^d n`. Taking the absolute value after summation cannot
increase that bound. The center is correctly counted once for each sign;
the proof never assumes those bodies are disjoint there. Thus only `O_d(n)`
unit markers are needed although the raw product family has `O_d(n^d)`
members.

A generic marker on distinct positive orbits has exactly one common label
among all coordinate factors. Its designated full-body trace is one and
every other full-body trace is zero. Proper signed contractions can be
nonzero, as the source explicitly allows. Reflections preserve the unit
trace statement for each normalized body sign.

The orbit-use cap `Lambda_d=16(d+1)P_d` is sufficient. Before a new label
is assigned, at most `n/16` positive orbits can have reached that cap,
because the entire planned marker population uses at most `(d+1)P_d n`
labels. The endpoint and within-bundle exclusions are a dimension-only
number. For sufficiently large odd `n`, these exclusions leave a choice
among `(n-1)/2` positive orbits. Appending `n` dummy markers in each sign
population has already been charged to `P_d n`; it supplies the necessary
lower population bound without assuming many genuine trace contributions.

For any fixed target cell, one of its noncentral coordinate orbits bounds
the number of markers containing it by `Lambda_d`. If a coordinate is zero,
no marker contains that cell. This is a literal support-incidence bound,
not a bound on net trace values.

### Projected templates remain physical

For one raw product, its endpoint orbits and the attached markers' alphabets
are mutually separated. Its checkerboard pieces are therefore cell-disjoint.
Splitting an absolute trace of two into two unit markers is essential:
it makes every nonzero projected entry `+1` or `-1`. The subtraction has
zero axes and zero body traces by construction.

Substituting these projected products into the integer edge-product
expansion leaves the scalar coefficient `epsilon_Q c_e` at each attached
marker. Summing those coefficients in one sign population is exactly that
body trace of the input tensor. Hence it is zero. No assertion about
unknown complementary kernel modules is used in this step.

The coefficient bound (H1) is supported by the imported theorem: the real
graph right inverse has norm at most `5 log n+5`, coordinate rounding has
at most `Delta^d/2` residual per cell, and the smaller sides of the `d`
tree cuts give `(Delta n)^d/2^(d+1)`. All coefficients are integers; there
is no division by a possibly nonunit residue.

### Disjoint-marker rerouting preserves the required cuts

A marker meets at most `2^d Lambda_d` other markers in a cell, even if
several markers or several cells coincide. For a bad graph edge, the two
endpoint supports and endpoints themselves exclude at most `2D_d^*+2`
middle vertices. At most `p_sigma/4` candidates can already have middle-use
count 128, since there are at most `32p_sigma` original edges. The stated
large-order inequality consequently leaves a legal middle vertex.

Replacing an edge by two separately labeled edges through that middle
vertex contributes exactly the same endpoint divergence. Every old edge
crossing a cut has at least one crossing edge on its replacement path.
The old edges have distinct labels, so these counted replacement crossings
are distinct even when their geometric endpoints agree. Therefore every
cut boundary has at least its former multiplicity. The maximum degree rises
by at most twice the middle-use cap, giving 320.

The scalar cut-flow argument is then valid: for demands bounded by `F`, a
cut demand is at most `F` times its smaller side. Edge capacities
`ceil(F/8)` meet every cut inequality. Integral max flow gives labeled
edge coefficients within those capacities. The resulting difference
`Q_u-Q_v` has disjoint supports and zero full-body traces. Thus (H3) and
(H5) reconstruct the original tensor exactly, not merely approximately.

Each target cell sees at most `Delta^d` raw products, `Lambda_d` attached
markers, and `320 Lambda_d` marker-edge incidences. This proves the stated
`B_d` bound for the whole fixed template collection, including dormant
zero-coefficient templates. It is independent of the input target tensor.

### Arbitrary residue rings, including modulus one

The frozen source uses a spanning tree of the **same** graph for the residue
edge-product coefficients. Its reduced incidence minor is unimodular, or
equivalently its signed subtree sums form an integer right inverse on the
zero-sum module. Tensoring those identities works over `Z/hZ` for every
`h>=1`. The tree edges are already among the raw products and therefore
use the same allocated projection markers.

Marker demands sum to zero in each sign population modulo `h`. Path prefix
sums and the same endpoint-divergence identity remain exact modulo `h`.
At most `p_sigma-1` path edges are replaced; a middle-use cap four excludes
fewer than `p_sigma/4` saturated choices and gives maximum degree ten.
Parallel replacement labels must again be retained. Representatives in
`0,...,h-1` require no inverses; for `h=1` every coefficient is zero and
no actual residue stage is needed.

For the prime application, dividing the even discrepancy by two before
passing to `Z/(g/2)Z` is valid. The source does not divide by two within
`Z/gZ`, and it pays the resulting numerical drift separately.

### Shared traces, complete signatures and physical pairing

In dimension `2d`, two disjoint `d`-blocks are complementary. The relevant
two-block identity therefore equates scalar full-body traces, with no
remaining free coordinate. A product of two generic selectors on disjoint
orbit alphabets changes only its two native `d`-families among all families
of size at least `d`. Mixed directions miss the support, and proper
subsets of either block have size below `d`. The selected shared trace
changes by one on both sides; all other shared traces stay fixed.

An integer multiple of `g` with magnitude at most `nE` splits into `n`
multiples of `g` of magnitude at most `E+g`, using ordinary quotient and
remainder. The source does not assert division by `n` in a residue ring.

For a final compound `Q_A tensor M_F`, orbit separation removes every
mixed direction. The complementary full-body contractions vanish by
membership in `Bdy_d`; the native `A` contraction is exactly `M_F`.
These observations cover every full signed line of size at least `d`,
not only the two all-positive bodies. The axes vanish as well.

Since `M_F` has only unit signed entries and disjoint checkerboard pieces,
pairing the outer selector along one coordinate gives precisely the
simultaneous tuple size in (H9). Each pair occupies two distinct cells;
different inner cells or outer pairs cannot overlap. Assigning fresh
equal-gap prime pairs with the product sign gives the stated actual
permutation increment. Prime supply for that finite tuple size is an
explicit dependency, not inferred from the algebraic pairing.

### Packing and whole-reservoir ranges

The shared-trace stage count is `O_k(nL)`. Hence the count of saturated
full signed lines is `O_k(n/H)` under a cap `HL`. A potential line that
can meet a stage has a free label in its fixed-coordinate key: full bodies
are absent because the two selector alphabets are disjoint. Testing a key
when its last relevant label is assigned is injective in that label.
Over-testing keys before all varying coordinates are assigned is harmless.
The bounded number of potential keys and a sufficiently large fixed cap
leave a positive fraction of available labels.

For a proposed occupied vertex, changing its last free label follows a full
signed-coordinate line. Earlier caps therefore remove only `o(n)` choices.
Within-reservoir freshness and the finite orbit exclusions cost respectively
`o(n)` and `O_k(1)` additional choices. A stage is committed only after all
deferred tests. This explains why the global count is enough for the shared
trace stage, whose reservoir count is only `O_k(n)`.

For the much larger final family, the source instead uses the necessary
local bounds: at most `2^d B_d L` cells above one fixed native point, and
at most `2^d B_d nL` over a projected native line. These are deterministic
bounds from template point degree. They justify the selector-packing lemma
at `r=d`; its packing proof never needs the strict-majority inequality.
The algebraic preservation argument is supplied separately by `Bdy_d`.

Freshness makes every nonnative full signed line meet at most one stage
of a reservoir. In a compound stage it can meet up to `2(J_d+1)` cells,
which the source explicitly pays. Native lines see a fixed unit coefficient
times the scalar reservoir, whose two central states differ by at most `g`.
The resulting whole-bundle range is `O_k(X)`, including omitted families.
Shared-trace reservoirs have the smaller two-cell bound. These are the
geometric hypotheses needed by the separate centering lemma.

## Exact checks and adversarial controls

Python: 3.12.14. The frozen author command passed from the archive:

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyperk_half.py
```

It checked 15 integer/composite-ring reconstructions, compound and shared
signatures, the stated partial prime swaps, seven malformed inputs and the
proper-contraction scope guard. The marker paths in that test are correctly
labeled identity fixtures, not asymptotic expander certificates.

The reviewer-owned program imports no author module. Its geometry generates
every full signed line through each support point by equal-absolute-value
membership, branching over every sign at the center. Replay it against an
archive of the reviewed source:

```sh
mkdir /tmp/hyperk-half-kernel-source
git archive f9697734c0c1d87eb8ab8af4051d0e8495ac9b56 problems/prime-arrays-beyond-square | tar -x -C /tmp/hyperk-half-kernel-source
python3 -B problems/prime-arrays-beyond-square/reviews/hyperk_half_kernel_controls.py /tmp/hyperk-half-kernel-source
```

All independent controls passed:

| Control | Exact result |
|---|---|
| Local projections at inner dimensions 2, 3, 4 | Nine complete signatures, including zero, opposite and repeated endpoints; unit entries and pairing in every coordinate |
| Omitting a unit marker from a magnitude-two trace | Four cases give a nonzero body trace and are rejected |
| Intersecting unit markers | Their unrepaired difference has coefficient `-2` at `(1,3)`, demonstrating the real physical issue |
| Labeled graph replacement | All 254 nontrivial cuts of the doubled complete graph on eight markers retain or increase boundary multiplicity; 56 edges become 58, maximum degree 16 |
| Erasing parallel labels | The expansion-eight claim fails in the negative control |
| Integer cut flows | 62 independent augmenting-path reconstructions within `ceil(F/8)` per labeled edge |
| Residue path repair | 80 exact controls, including moduli 1, 4, 6, 8, 9, 15 and 30 |
| Compound signatures and whole-bundle support | Nine complete signatures across dimensions 4, 6, 8; every nonnative line meets at most one stage and respects the compound cell-count bound |
| Dropping a body-trace condition | Creates a second protected native family |
| Dropping endpoint-orbit separation | Creates a forbidden full body even with a valid complementary kernel factor |
| Confusing body kernel with full signed kernel | A rank-three body-kernel tensor has a nonzero proper pair contraction, which survives in the omitted lower family of a six-dimensional compound |

The doubled complete graph is a finite all-cuts diagnostic, not the general
graph-existence proof. No finite control establishes the large-order marker
allocation or physical packing by itself. The retained partial prime stages
are not full exact-pool arrays with all required sums prime.

After adding the reviewer files, local `python3 -B check.py` passed all 45
integrity/tooling tests. That result checks repository structure and tooling,
not the mathematical arguments.

## Disposition

No author correction was required within this review's scope. The distinction
between `Bdy_d` and the full signed-contraction kernel is essential. For a
native block smaller than half the coordinates, required complementary
contractions have free indices and the scalar marker-demand proof no longer
applies. This review supplies no missing tensor-valued marker-routing theorem.

The verdict is conventional internal mathematical review. It is not remote
CI, proof-kernel verification, journal refereeing, a formal GitHub approval,
or approval to announce the all-full-line theorem. The coordinator retains
the integration and final delivery responsibility.
