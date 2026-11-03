# Independent incidence review: every fixed dimension

Reviewer: `/root/incidence_review`. Review date: 2 November 2026.

Exact frozen scientific revision:
`5692d37633ef4b509e8429cddf4ed762e7235d08` (PR83).

**Verdict: no blocking defect found in the stated integer-incidence results.**
This covers Theorem IK, the stable rank recurrence, the explicit integer
section and its coarse bound, Lemma KG, Lemma PS, and Lemma MF in
[hyperk_incidence.md](../manuscripts/hyperk_incidence.md). The conclusions
include saturation and the complete integral compatibility interface for
every fixed `k>=2` and odd `n>=3^k`. They do not include a bounded-load
distributed kernel decomposition, physical prime-pair realization, joint
prime-target construction, or the full prime-permutation theorem.

## Authorship, scope and exact source

I was assigned this review after the scientific revision was frozen. I did
not author any reviewed manuscript, proof, producer, certificate, target
lemma, controller, or resource inequality. My additions are only this review
and [hyperk_incidence_controls.py](hyperk_incidence_controls.py). I did not
edit an author source, claim, input, or Git reference. This is conventional
internal mathematical review, not a formal GitHub approval, remote CI run,
or proof-kernel verification.

I read `AGENTS.md`, `RESEARCH_PROTOCOL.md`, the problem's required index,
model, references, open-problem and code records, the entire frozen
incidence manuscript and its parameterized code. I inspected the inherited
Smith reducer/replayer in `signed_incidence.py` and the unit-pivot
preconditioner in `signed_kernel_certificate.py`. The analytic target and
physical-controller manuscripts are outside this review's scope.

All scientific replays used a `git archive` of the exact revision, separate
from the active author checkout. The manuscript, code, two imported code
files and five retained Smith inputs were compared byte for byte with
`git show` at the frozen revision. The reviewer controls independently
enforce their nine SHA256 bindings before importing code. Principal hashes:

| File | SHA256 |
|---|---|
| `manuscripts/hyperk_incidence.md` | `fd2ab35b539415ac65a132b7fddfb6acaa87b5af65f579f9eb64f27cc7e403d8` |
| `code/hyperk_incidence.py` | `8b2bbd2e88fdbfeb5461f6b85e1bd39626df8d4b6caa0818816aff99bd47283e` |
| `code/signed_incidence.py` | `aeabf8bc33a9e3816f58f0467e101e5af4fa070c95c8feda77fa1ada4fa69bd3` |
| `code/signed_kernel_certificate.py` | `b6de0cdcac1d7a99b1cbbb259f4e451875e996dea426bb78a2381f35018850f4` |

## Mathematical findings

### IK: global monomial order and exact integral syzygies

The marker construction gives one distinct positive reflection orbit per
signed block. There are `(3^k-1)/2` blocks, so odd `n>=3^k` supplies all the
required labels. Adding `k+1` to every provisional variable weight and
clearing denominators gives positive integer weights. Weighted degree,
with a monomial-order tie breaker, is a global multiplicative well-order;
the shift does not change comparisons between terms of the same
multidegree. This addresses the possible failure of a merely local or
rational weight ordering.

For a term at another block's marker orbit, avoidance of a negative weight
forces containment of its coordinate set and agreement of its signs up to
simultaneous reversal. A proper containment has weight strictly below one.
Equality would be the same normalized signed block; its reversed
parameter is not a second leading term. Any negative-weight variable
forces the term below one as well. Zero receives negative weight in every
coordinate. Thus each prescribed leading monomial is unique and monic,
and the distinct absolute marker labels make different leading monomials
pairwise coprime as monomials in the actual variables. Coordinate-set
overlap does not undermine that coprimality.

I checked the integral cancellation argument rather than appealing to a
field Gröbner-basis result. If several summands of a representation have
the same maximal leading product, their coefficients can be consolidated
against one pivot by integer multiples of the Koszul relations. The
pairwise-coprime leading monomials ensure the required product divides
that maximal monomial. All introduced products are lower. In a syzygy,
the last coefficient at the maximal monomial is zero, so the maximal
monomial strictly decreases. This terminates and generates every
syzygy integrally. The same cancellation, applied to a representation of
a nonzero ideal element, leaves its leading monomial divisible by a
leading generator. Consequently no nonzero standard-monomial combination
lies in the ideal, and monic division gives the claimed free integral
quotient. No division by a coefficient or by `n` is hidden here.

All reductions preserve multidegree. In degree `(1,...,1)`, a Koszul
generator for two overlapping coordinate blocks would have degree two
in the overlap and cannot occur. For disjoint blocks its complement
multiplier is a linear combination of fixed-coordinate monomials. These
are exactly the signed two-parameter partition identities (PC). Thus
the proof obtains every **integer** row relation, including shared trace
relations; it does not merely count the rational rank.

The free standard-monomial quotient splits the cell lattice over the
row lattice. A target satisfying PC therefore defines a well-defined
homomorphism on the row lattice and extends integrally over all cells.
This proves the complete image description. Equality with the integer
solutions of homogeneous integer equations proves saturation. Summing
the axis-axis PC identities gives the common directional total.

For the entry-congruence claim, subtraction of the constant target `nr`
and division by `q` preserve all PC identities. This is an integral
operation precisely when each target is `nr mod q`. Lifting, multiplying
by `q` and adding `r` proves sufficiency even when `q` and `n` are not
coprime. Necessity follows from line length. At odd `n`, odd targets
therefore admit odd integer lifts. The manuscript expressly makes no
positivity, distinctness, or pool-permutation inference from that fact.

### Rank recurrence and partition hierarchy

In multilinear degree, a collection of leading monomials has a common
multiple exactly when its coordinate blocks are disjoint. For `r` blocks
covering `t` coordinates there are
`binom(k,t) S(t,r) 2^(t-r)` choices, each dividing `n^(k-t)` cell
monomials. This gives the stated inclusion-exclusion kernel polynomial.
Its exponential generating function and the derivative recurrence (I11)
follow, including the displayed dimension-five and dimension-six
polynomials. They apply in the proved stable range, not at every odd
order. The retained small-order torsion therefore does not contradict
IK.

The local triangular statement after (I13) also checks. Orbit separation
eliminates a contraction mixing two selected blocks or a selected block
and the complement. A block contained wholly in the complement
annihilates its full-kernel tensor. Every other surviving contraction
refines or deletes selected blocks and strictly reduces
`|U|-number_of_blocks`, except for the identical partition. Singletons
already vanish. Noncentral selectors prevent the center from creating
an overlooked mixed intersection. This supplies an algebraic triangular
ordering; it is not a global packing theorem, and the source does not
claim otherwise.

### Integer section and sparse kernel basis

For compatible targets, setting every standard cell to zero defines a
unique extension. The recursive section (I14) is this extension, so a
different leading-divisor rule cannot change its result. The provisional
cell-weight interval is `[-k^2,k]`, and every rewrite drops the weight by
at least `1/k`; hence `D_k=k^2(k+1)` is a valid branch bound. A recursion
tree of branching at most `n-1` gives (I16), with no unrecorded rounding
term. The source correctly calls this norm bound physically unaffordable.

Normal-form coefficient functionals annihilate every line polynomial.
Their values on standard cells form the identity matrix, and the split
quotient proves they are a full **integral basis**, not just independent
rational vectors. This verifies the coefficient formula in (I18).

For the support bound, a coordinate can be rewritten only when its old
value is a designated marker. Any initial nonmarker therefore survives
along every branch and must equal the final standard coordinate. This
includes zero and unused positive or negative labels. On a branch
contributing to a fixed standard monomial there are at most `2h_k`
marker parameter choices and at most one possible nonmarker choice.
Together with the depth bound this proves support at most `s_k^k` and
coefficient magnitude at most `s_k^D_k`, where `s_k=3^k`.

The shared markers may accumulate contributions from many basis vectors.
The explicit nonclaim following KG is essential and correct: individual
bounded support does not imply bounded cell load, slice load or line
occupancy after summation. Redistributing markers changes the basis
expansion and needs a separate exact argument. I have not accepted any
such distribution theorem through this review.

### PS: arbitrary common alphabet relabeling and pairability

For `alpha=(1,...,1,-(b-1))`, every nonempty proper subset sum is nonzero
and has magnitude at most `b-1`. Each divides `lcm(1,...,b-1)` and hence
is a unit modulo both selected moduli. The moduli need not be prime.
Every proper positive signed block therefore intersects the two modular
hyperplanes in one point each. A mixed-sign line cannot intersect the
strictly positive support. Fixed outside coordinates cause no exception:
if any misses the alphabet the entire line misses that copy.

The arbitrary relabeling is a **common bijection for the alphabet in all
coordinates**, as specified by the alphabet's Cartesian power. Equal
physical positive coordinates then still have equal modular indices;
the argument uses no numerical affine structure of the actual labels.
Coordinatewise independent, unrelated relabelings would not have this
property and are not asserted. Whole-coordinate reflection preserves the
claim for any desired body sign pattern.

The two congruence hyperplanes are disjoint and have one opposite-sign
point in each coordinate fiber, giving disjoint opposite-sign pairings
along any prescribed coordinate. Disjoint alphabets for the three copies
avoid overlapping cells, and `2p-q=1` gives the unit full-body image.
The support and pair counts are consequently exact. The statement
properly leaves distinct prime endpoints, equal-gap supply and global
packing to the physical controller.

### MF: actual-image rounding and integer tree repair

The estimate (I23) uses a real lift and rounds **cell coordinates**. Each
incidence row contains at most `n` ones, so its rounding error is at most
`n/2`; the rounded image lies in the actual image lattice even when that
lattice is nonsaturated. No bound on the real preimage is needed.

I read the scalar flow operator in MF in its linear sense, as required
by its proof and its stated Green-operator example. Applying that same
linear operator to every coordinate makes each edge value a real linear
combination of compatible demands. Image rounding leaves a zero-total
vertex residual in the image lattice of norm at most `Delta*n/2`. A tree
edge can be repaired by the residual sum on the smaller cut side, of
size at most `p/2`; this gives `Delta*p*n/4`. Adding the real-flow and
edge-rounding bounds proves (I24). Existence of a flow operator for all
zero-sum demands entails the required graph connectivity. The final
`O_k(E log n+n^2)` specialization is explicitly conditional on the stated
bounded-degree fixed-gap scalar operator and graph order `O_k(n)`.

Making the word "linear" explicit in the lemma statement would improve
precision, but is not a mathematical repair: it is already the operator
used and identified in the proof. MF gives compatible vector coefficients,
not a decomposition into physical switches.

## Exact finite evidence and negative controls

Under Python 3.12.14, I ran the frozen author's self-test from the archive:

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyperk_incidence.py self-test
```

It passed all stated geometry, marker, lift, congruence, cuboid, selector
and retained Smith checks, including the supplied corruption controls.
The retained order-three ranks were `7,27,81,243,729` in dimensions
`2,3,4,5,6`; nonunit factors were `3` once in dimension two, and `3`
with multiplicity `k` plus `6` once in dimensions three through six.

To replay the reviewer controls, archive the scientific source to a fresh
directory, then pass that directory to the reviewer-owned program. For
example, from a checkout containing the frozen commit and this review:

```sh
mkdir /tmp/hyperk-incidence-review-source
git archive 5692d37633ef4b509e8429cddf4ed762e7235d08 problems/prime-arrays-beyond-square | tar -x -C /tmp/hyperk-incidence-review-source
python3 -B problems/prime-arrays-beyond-square/reviews/hyperk_incidence_controls.py /tmp/hyperk-incidence-review-source
```

The independent additions passed:

| Check | Result and scope |
|---|---|
| Nonsymmetric compatible targets | At `(k,n)=(2,9),(3,27)`, random axis data, independent proper-diagonal lists with their required totals, and independent body targets lift exactly. Seed `20261102`; 20 and 2353 full lines. |
| Section independence | Choosing the last leading divisor gives the same complete lift as the author's first-divisor rule in both cases. |
| Noninvertible modulus | Entry residue `-4 mod n` lifts exactly. Changing an unconstrained body target by one preserves PC but fails the required entry residue and is rejected. |
| Full incidence Smith comparison | Independently constructed full matrices at `(2,3),(3,3),(4,3)` give ranks `7,27,81` and exactly the retained reduced nonunit factors. |
| Kernel basis | All 98 standard pivots at `(2,11)` give zero full-line image, the standard-cell Kronecker values, and the asserted coordinate support containment, including center and unused orbits. |
| Relabeled/reflected selector | A shuffled positive alphabet in dimension three, reflected to body signs `(1,-1,-1)`, has exactly that unit body image among all full lines at `n=41`; the 86 signed cells remain correctly paired. |
| Compatible rounding | An exact-fraction example on an index-two image lattice and a four-vertex cycle verifies image rounding, integer residuals and the tree-repair bound. Independent target-coordinate rounding leaves that lattice in the negative control. |

The full-matrix Smith comparison uses independent geometry but the inherited
Smith producer and inspected replay routine; it is not a second independently
implemented Smith algorithm. The replay permits only unimodular swaps,
distinct-source integer additions and sign changes, then checks every
off-diagonal and zero entry and the positive divisibility chain. Additional
negative controls reject self-addition of a row or column, an out-of-range
index, an unknown operation, and a changed invariant factor. Changing a
Smith record's `not_an_arrangement` field to false is rejected. A selector
sign corruption changes its independently summed full-line image.

The reduction used in the retained certificates is legitimate over the
integers. Splitting one coordinate as
`Z e_0 direct-sum span_Z{e_u-e_0: u!=0}` makes the all-axis kernel the
tensor product of the zero-sum factors. The other direct summands are
detected integrally by the axis map, contributing
`n^k-(n-1)^k` unit factors. A block contraction of the remaining tensor
lies in the zero-margin lattice on the fixed complement. Its noncentral
entries are integral coordinates for that lattice, so retaining those
entries loses neither rank nor torsion. The displayed extra-row coefficient
`(-1)^|B| + indicator(all nonzero labels match the signed parameter)`
is exactly the contraction of an anchored tensor. This explains why the
full-matrix checks agree with the reduced certificates.

I also ran `python3 -B check.py` in the delivery working tree after adding
the reviewer files: all 45 integrity/tool tests passed. This check concerns
repository structure and tool behavior, not the truth of the mathematics.

## Disposition and limits

The reviewed conventional arguments establish the eventual exact integer
image, parity/congruence interface, rank, finite local selector and the
stated numeric bounds. The tests support their finite implementations and
reject the listed corruptions; they do not prove the universal statements.
No proof assistant or remote CI was run as part of this review. Repository
source publication, final delivery integrity and integration remain
coordinator tasks, separate from this mathematical verdict.

No scientific correction was required within this scope. The main exposed
interface remains open exactly where the source says: affordable
distributed decomposition and physical packing of compatible coefficients
for all full signed-line families. The full prime-hypercube theorem must
not inherit a completed status from this incidence review.
