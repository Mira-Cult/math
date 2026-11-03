# Independent review of the uniform real full-kernel frame

Reviewer: `/root/incidence_review`. Review date: 3 November 2026.

Exact scientific source: `c7f22dd8a01d28ab02c832f6c2b8b4145d88b6bb`.
Exact source tree: `65756bab209c4fd74e32327344942bfc56a1bb25` (PR83).

**Verdict: no blocking mathematical defect found in UF(d,eta) or its
integer rounding interface.** The conventional proof establishes the
stated fixed frame, chosen before every demand, for every fixed `d>=1`
and `eta>0`, at all sufficiently large odd orders. The proof uses the
previously reviewed monic kernel basis and pure selectors, together with
the specified rectangular matrix Bernstein inequality. This verdict
does not establish the separate integer absorber, correction hierarchy,
prime-pair supply, global physical packing, or final prime-permutation
composition.

## Authorship and exact source boundary

I did not author the new scientific argument or its code, including the
contributions attributed by the coordinator to `/root`, `/root/controller`,
`/root/full_reconstruction` and `/root/kernel_architecture`. I previously
reviewed the general incidence source at `5692d37633ef4b509e8429cddf4ed762e7235d08`
and the kernel supplement at `99cd33eb8f91682342a671b46599f43b1365ed7c`.
My authorship in those tasks was confined to their reviewer-owned notes
and controls. I did not author the imported KG or PS proofs. Those
scientific manuscript and code bytes remain unchanged at the present
source revision.

For this assignment I added only this review and
[hyperk_uniform_frame_controls.py](hyperk_uniform_frame_controls.py).
No author source, input, claim, or Git reference was modified. I reread
the repository working agreement and research protocol, inspected the
problem's current scope/interface records, and read the complete new
[frame manuscript](../manuscripts/hyperk_full_controller.md) and
[companion code](../code/hyperk_full_controller.py). The relevant imported
prime-pair fixture functions were also inspected. The scientific source
was recovered into a separate `git archive`, with its tree and bytes
checked against the exact commit.

| Source | SHA256 |
|---|---|
| `manuscripts/hyperk_full_controller.md` | `38de54de8b5e5d751e9d700f689b9417b610019d56e170d47f209c86e2adbec6` |
| `code/hyperk_full_controller.py` | `ac6503a6d9db1282fc2dcf471e57a9e53f73959c7354f5d6c70edc9368a9cf65` |
| `manuscripts/hyperk_incidence.md` | `fd2ab35b539415ac65a132b7fddfb6acaa87b5af65f579f9eb64f27cc7e403d8` |
| `manuscripts/hyperk_kernel_research.md` | `c4dc2db4da2e502f0bc8d564e44c2f504b13e9e0fae7ae77b780cfdb70838f44` |

The reviewer controls enforce these and the three other directly imported
code hashes before execution. This is conventional internal review, not
formal GitHub approval, remote CI, or proof-kernel verification.

The coordinator subsequently published composition clarification commit
`c5cf3d829f83dcc388af6f065d7f9bda66789458`. I byte-compared the two UF
source files at that commit with the scientific revision above: both are
identical. This continuity check does not review the changed composition
text or rebind the scientific source pin.

## 1. Expected incoming support: ER

The active-block invariant is valid. Distinct active leading monomials
cannot share a coordinate, since that coordinate would have to carry two
different designated absolute labels. When a selected active block is
rewritten, all other previously active blocks are coordinate-disjoint
from it and remain unchanged. Any newly active block must intersect the
rewritten coordinates. Its marker orbit must then be the absolute value
of the common new parameter. Since the marker assignment is injective,
at most one new block can be activated. Thus the active count does not
increase; choosing a nonmarker parameter removes the selected block and
creates none. In particular zero causes a strict decrease and is never
treated as a two-element orbit.

Starting with `r` active blocks, a branch can therefore make at most `r`
nonmarker choices. Its total length is at most the imported weight bound
`D0`. For length `l` and `u` nonmarker choices, there are at most
`binom(l,u)(2h)^(l-u)n^u` possible parameter histories. Summing over
`l<=D0` and `u<=r` is bounded by the manuscript's
`(2h+2)^(D0+1)n^r`. This counts more than the surviving normal-form
monomials, so cancellation cannot invalidate the upper bound.

For `j` prescribed active blocks, the required nonzero absolute labels
must be distinct and have the correct signs; otherwise the event is
impossible. In the possible case a uniform marker injection has exactly
the required assignments with probability `1/(m)_j`. There are at most
`h^j` ordered candidate collections. Consequently the displayed upper
bound for `E n^r` follows by a union bound and
`n^j/(m)_j<=6^j` for `m>=2d`. Summing normal-form coefficients by their
standard-monomial indices gives precisely the expected incoming support
in (UF4), including zero columns for nonstandard indices.

This reasoning genuinely adds information to the earlier KG support
inclusion. That inclusion alone would not control incoming support.
For `d=1`, the construction reduces directly to `K_v=e_v-e_a` for
`v!=a` and a zero column for `v=a`, so the one-dimensional case does not
need an extrapolated prime-array theorem or an unproved incidence import.

## 2. Exact unit physicalization of a compact column: PU

The axis identity (UF5) is exact over the integers. Expanding its right
side, every term with a nonempty set of anchor coordinates contains a
zero marginal of `Z`. The remaining term is `Z` itself.

Distinct anchor orbits outside the entire column support rule out every
nonaxis witness involving an anchor. A mixed anchor/original witness
would require an anchor orbit to appear in the original support, and
two anchors cannot supply the same absolute parameter. The only possible
witness therefore uses the original endpoint in every coordinate of the
block and has coefficient `+1`. Hence `beta_H` is exactly zero or one,
also when the original endpoints include zero, repeated labels or
reflected labels.

Pure-selector cancellation then makes each projected star a full-kernel
tensor. In addition to native, proper-subblock and crossing-group cases,
a block on the same coordinate set with a different orientation vanishes
by the selector's other-body purity. Disjoint selector alphabets make
distinct partition terms cell-disjoint, including terms with different
signs on the same coordinate set. Thus no entry has magnitude greater
than one. Zero axes supply disjoint opposite-sign pairings along every
coordinate.

The exact reconstruction argument uses one common linear operator for
**all roots of one compact column**. Repeated contractions on disjoint
blocks give the displayed operator `P`; its action on each star is (UF6).
Every nonempty contraction of `Z` is zero, so `P(Z)=Z`. Applying that
operator to the integer identity (UF5) proves (UF7). Auxiliary choices
may differ between different KG columns, but may not vary independently
between roots within one column. The source enforces this distinction.

The finite constants `A_d` and `q_d` count the allocated alphabets and all
partition supports, with zero-scalar terms safely overcounted. At most
`S` templates are used per column and their integer coefficients are
bounded by `C`. In particular physicalization does not replicate a
template once per unit of a potentially growing coefficient.

## 3. Expected actual unit-template incidence: EP

The conditioning in EP is legitimate. First fix a sampled KG column,
including its entire support. Its auxiliary labels are then a uniformly
ordered injection from the remaining positive orbits. At most `dS`
orbits have been excluded, independently of the ambient order.

Fix a partition, one abstract support word in each selector, and the
uncovered coordinates using anchors. Write `s=|pi|+|J|`. A root that can
contribute must have one common signed parameter on each selected block,
and its nonanchor uncovered coordinates are already prescribed by the
output cell. There are at most `n^s` roots. For each, hitting that output
requires at least `s` different auxiliary positions to take prescribed
different orbit labels: one position from each selector alphabet and
each of the distinct anchors. Conflicting prescriptions have probability
zero. Otherwise the conditional probability is bounded by
`1/(m-excluded)_s`, and hence by `(6/n)^s` for sufficiently large `n`,
uniformly in the column being conditioned on.

For clarity, an explicit sufficient ambient condition for this step is

`m >= max(h, 2d, 2(dS+A_d+d+1))`.

It leaves all auxiliary positions available and gives every denominator
factor at least `m/2`; since `2/m<=6/(2m+1)`, the stated probability
bound follows. This is merely one coarse sufficient threshold, not a
claimed optimal order.

Summing the conditional estimate over the roots and then all columns
uses ER at each root and cancels `n^s` against `n^-s`. The sum over
anchor choices is `7` per uncovered coordinate; selector words contribute
their support sizes. The resulting bound is exactly `GF_d`. It counts
actual support incidences, including dormant templates, rather than
coefficient magnitudes or net traces. No independence between the
templates within a column is needed or asserted here.

## 4. Uniform operator and both matrix variances

I opened the author's
[primary Tropp PDF](https://tropp.caltech.edu/papers/Tro11-User-Friendly-preprint.pdf)
and checked Theorem 1.6 on printed page 5. I also checked
[arXiv:1004.4389v7](https://arxiv.org/abs/1004.4389v7), whose revision date
is 15 June 2011 and whose bibliographic record matches the cited 2012
publication. The theorem applies to independent mean-zero rectangular
matrices with an almost-sure operator-norm bound. Its variance parameter
is the larger norm of the two sums of second moments, and its prefactor
is the sum of the matrix dimensions. These are the hypotheses and form
used below; no specialized fixed-dimension probability result is being
extrapolated to a growing matrix.

For each input index the expectation of its sampled column is the same
as its column in a common-marker projection. Linearity of expectation
therefore gives `Abar` as the average of the common projections, which
fix every element of the real full kernel. Every realized column is
itself in that kernel. Both facts are exact before concentration.

For the centered rank-one summand, the bound
`2C sqrt(S)/T` follows from the triangle inequality and the same bound
on the mean column. For the right variance, each contribution is supported
on its input coordinate. The sum is diagonal and its largest diagonal
entry is at most `SC^2/T`; there is no extra factor `N`.

For the left variance, the precise positive-semidefinite step is

`sum E XX* <= (1/T) sum_v E(K_v K_v*) =: B`.

The subtracted matrix is the sum of the outer products of the mean
columns and is positive semidefinite. One then bounds the **upper
matrix B**, not the individual entries of the centered covariance, by
absolute row sums. At output `y`, its absolute row sum is at most

`(1/T) sum_v E[ |K_v(y)| ||K_v||_1 ] <= SC^2 G/T`.

Since `B` is symmetric positive semidefinite, this is a valid spectral
upper bound; positive-semidefinite domination gives the same upper bound
for the covariance. This distinction avoids an invalid entrywise use of
the positive-semidefinite order. The manuscript's argument has the valid
reading above. The two variance estimates give `V/T`, and substitution
of the summand bound into Tropp's formula yields (UF11), including its
`2N` prefactor and `4/3` term.

For the raw row count, the summands are independent indicators indexed
by `(v,j)`. For the physical count, each summand is the **whole column's**
number of incident templates, lies in `[0,S]`, and is independent of the
other sampled columns. Its variance is at most `S` times its mean.
The source does not treat the templates from a shared column as
independent Bernoulli variables. This grouping is necessary.

In either scalar estimate, after scaling by the bound on a summand, the
relevant Bernstein exponent has factor

`(b+2)^2 / (2b+(2/3)(b+2)) >= 1` for `b>=0`.

This verifies the asserted `exp(-T)` tails at the displayed thresholds.
Union bounds over output cells are valid without independence between
different rows or between the three success events. The proposed
constant in (UF14) is more than sufficient to make the spectral failure
and both row-load failures have total probability less than one.

The successful sample depends only on `d,eta,n`. Its spectral estimate
is an operator estimate on the entire finite-dimensional space, not a
pointwise estimate for one independent demand. Its restriction therefore
works simultaneously for every real kernel demand, even one selected
after the frame is known. This is the required quantifier order.

## 5. Neumann bound and integral remainder

The restriction `R0=I-A` preserves the real kernel. On that space the
identity `Abar=I` gives spectral norm at most `epsilon`; the row bound
gives supremum norm at most `L`. Hence every term in the Neumann series
has the two stated bounds. The first increases geometrically and the
second decreases geometrically. Splitting at the displayed crossover,
with a floor or ceiling absorbed into a constant, gives the exponent

`theta = d log L / (2 log(L/epsilon))`.

The chosen epsilon satisfies

`theta <= d eta / (2(d+3eta)) < eta`.

This is a genuine all-dimension inequality for every fixed positive
`eta`, not a finite list of successful exponents. The constants may be
large but depend only on `d,eta`. The Neumann series converges in the
kernel and telescopes to `Az=D`. No integer inversion or small-infinity-
norm one-step contraction is claimed.

Physicalizing each sampled column gives the stated real coefficients
with the exact identity `sum c_alpha J_alpha=D`. The support bound `q_d`
depends only on dimension; the sample count is `O_(d,eta)(log n)`, so
the number of templates and their point incidence have exactly the
claimed orders. Multiplicities are counted even when coefficients vanish.

For integer `D`, nearest-integer rounding of these unit-template
coefficients leaves an integer full-kernel remainder. Each incident
template contributes at most one half at a cell, giving the bound
`rho_d T/2`. The alternative of rounding a KG-column scalar first is
also valid because its physicalization coefficients are integers; its
different bound follows from raw-column incidence. The two methods
must not be replaced by entrywise rounding of an arbitrary real array,
which can destroy kernel compatibility.

Section 7 is a conditional interface to a separate integer absorber.
Assuming its stated bound, applying it only to the logarithmic remainder
gives (UF17). With discrepancies measured in actual sum units, rescaling
the gap units gives (UF18). For fixed ambient `k` and `1<=d<=k-2`, its
gap-dependent residual term is indeed `o(X)` under the stated growth
assumptions. Complement dimension zero and the actual physical hierarchy
are separate scalar/composition obligations, not additional assertions
of UF(d,eta). I have not reviewed the absorber or prime-permutation
composition through this conditional discussion.

## 6. Exact replays and independent controls

The frozen author command ran under Python 3.12.14:

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyperk_full_controller.py
```

It passed, reproducing the manuscript's two finite uniform-operator
fixtures, rational inversions and integer remainder bounds; all twelve
compact-column physicalizations; coordinate pairings and partial
prime-switch fixtures; 42,720 higher-dimensional active-block checks;
symbolic invoices through dimension six; and six malformed-input or
false-shortcut controls. The prime fixtures preserve their selected
partial pools and verify endpoint primality; they are not full arrays
using every prescribed initial prime.

The reviewer controls were run against the exact archive. To reproduce:

```sh
mkdir /tmp/hyperk-uniform-frame-review-source
git archive c7f22dd8a01d28ab02c832f6c2b8b4145d88b6bb problems/prime-arrays-beyond-square | tar -x -C /tmp/hyperk-uniform-frame-review-source
python3 -B problems/prime-arrays-beyond-square/reviews/hyperk_uniform_frame_controls.py /tmp/hyperk-uniform-frame-review-source
```

They passed the following controls. The normal-form elimination, active
divisor audit, step-word line signatures, covariance construction,
operator sampling, compact-column assembly and rounding are independently
written. The finite recursive selector inputs are imported from the
byte-bound source and checked through their resulting full-line images.

| Independent control | Exact outcome |
|---|---|
| All 24 marker injections, `(d,n)=(2,9)` | Last-divisor elimination agrees with the author's columns; all 3840 possible active-divisor transitions checked, including 480 strict nonmarker decreases. |
| Unused noncentral orbit, `(2,11)` | 240 further transitions checked, including 72 strict nonmarker decreases. |
| Expected incoming support | Exact maximum `38/3` in the order-nine two-dimensional ensemble. |
| Both covariance sums | Right diagonal norm `91/12`; left centered absolute-row bound `661/8`; uncentered PSD upper-matrix absolute-row bound `262/3`. These are exact finite quantities, not universal constants. |
| Uniformity of the mean | The mean operator fixes every one of the 62 integral basis vectors, not only one chosen demand. |
| Independently sampled fixed operator | With 4096 samples per input and seed `2026110301`, exact induced-norm multiplication bounds the squared spectral error by `5369665/37748736 < 1`. |
| Exact auxiliary-allocation expectation, `d=1,n=9` | All 72 permitted marker/auxiliary outcomes enumerated. Expected actual template incidence is `27/4` at each positive cell and one at each nonpositive cell. |
| Shared-column correlation | The shared-anchor count has variance `8/9`; treating its two templates as independent would give the incorrect `4/9`. |
| Three-dimensional coefficient-three column | An independently reduced 96-cell KG column is exactly rebuilt by 96 common-projector unit templates in each of two auxiliary alphabets. |
| Independent unit-coefficient rounding | Averaging those two exact expansions and rounding each unit coefficient gives a full-kernel integer remainder of norm 48, exactly its actual point-incidence bound 48. |

Additional negative controls construct a rank-one map that fixes one
kernel demand while failing another, and an eight-column centered matrix
ensemble whose left variance is eight while its right variance is one.
They exhibit why one-demand validation and one-sided variance control
are insufficient. A zero-total real vector whose entrywise rounding has
nonzero total rejects the rounding-outside-the-kernel shortcut.

These tests probe finite implementations and false alternatives. The
dimension-parametric conclusions rest on the proofs audited above.
There was no proof assistant, no remote CI run, and no complete
prime-arrangement construction in this review.

Local `python3 -B check.py` passed all 45 integrity/tool tests after the
reviewer files were added. This checks repository structure and tool
behavior, not the mathematical conclusions.

## Disposition

| Obligation | Review status |
|---|---|
| ER and exact compact-column physicalization | Conventional proof checked; no blocking defect found |
| EP for actual unit-template incidence | Conditional sampling and support count checked; no blocking defect found |
| Universal spectral sample and Neumann estimate | Both variances and all quantifiers checked against the primary probability theorem |
| Integer logarithmic remainder | Conventional proof checked; exact finite rounding control passed |
| Integral absorber and full physical composition | Outside this review; not implied by UF |
| Computation, remote CI and kernel verification | Finite local replays passed; remote CI and kernel verification not performed here |

No correction to the frozen UF science was required. The publication
and integration decisions remain with the coordinator, and this
component verdict must not be relabeled as an independent review of
the entire prime-hypercube theorem.
