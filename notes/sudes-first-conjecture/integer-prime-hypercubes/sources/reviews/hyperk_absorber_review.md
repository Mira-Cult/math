**Public reading copy.** Presentation and links have been normalized. Historical status statements below belong to their source revisions; see the [current publication status](../../README.md#review-and-verification-status). The matching original bytes are in the [source archive](../../originals/reviews/hyperk_absorber_review.md).

# Independent review of AF and the AF + UF synthesis BK

## Verdict and exact scope

**Positive mathematical review within the stated component scope.** I found no
blocking defect in AF(d), its all-modulus generation statement, or the deduction
of BK(d,eta) from the stated UF(d,eta) interface and AF(d). The integral absorber
has a fixed family, bounded point degree, and the claimed maximum-coefficient
bound. The synthesis applies its polynomial loss only to an integer rounding
remainder of logarithmic supremum norm.

This is not an acceptance of the complete prime-hypercube theorem. Availability
of fresh prime endpoints, all simultaneous placements, the correction hierarchy,
concentration, completion of the exact initial-prime pool, and the final resource
ledger are outside this review. UF's probabilistic construction is separately
reviewed; here its exact consumed statement and the rounding deduction were
checked. No formal kernel verification, remote CI result, or finite prime-array
certificate is asserted.

- Reviewer: `/root/half_kernel_review`, acting independently of the new authors.
- Date: 2026-11-03.
- Exact scientific commit: `c7f22dd8a01d28ab02c832f6c2b8b4145d88b6bb`.
- Exact tree: `65756bab209c4fd74e32327344942bfc56a1bb25`.
- Prior involvement: independent review of the earlier half-coordinate kernel
  and physical-template component only. I did not author the new AF, UF, BK,
  or full-composition arguments.
- Authorship exclusions: `/root`, `/root/controller`,
  `/root/full_reconstruction`, and `/root/kernel_architecture` contributed to
  the new science and are not counted as its independent reviewers here.
- Only this review and its companion reviewer controls were written. No author
  manuscript, author program, claim record, branch, commit, or remote state was
  modified by this reviewer.

The reviewed sources were extracted with `git archive` into an isolated directory
and checked against the named commit's blobs. All nine bound files below are also
byte-identical at `c5cf3d829f83dcc388af6f065d7f9bda66789458`; this equality was
checked directly. The present review remains pinned to the earlier scientific
commit, and does not extend to that later commit's composition changes.

## Canonical sources and bindings

Primary scope is [AF](../manuscripts/hyperk_reconstruction_alt.md), Sections 1--8,
and [BK](../manuscripts/hyperk_distributed_kernel.md), Sections 1--5. I inspected
the consumed statement of [UF](../manuscripts/hyperk_full_controller.md), the
PS/LP constructions in [the kernel supplement](../manuscripts/hyperk_kernel_research.md),
and the saturation/KG interfaces in [the incidence source](../manuscripts/hyperk_incidence.md).
All claim labels in this report are manuscript-local; no permanent claim ID is
created or promoted.

Paths in the table are relative to `problems/prime-arrays-beyond-square`.

| Source | SHA-256 |
|---|---|
| `manuscripts/hyperk_reconstruction_alt.md` | `623cae1101615723a9ddc367145675c41d93067ee64502663b56d072059eeeb5` |
| `code/hyperk_reconstruction_alt.py` | `ab974d038fcc852645d3af0020ff2be47f93adfb847b8c2f95327a0f53b76060` |
| `manuscripts/hyperk_distributed_kernel.md` | `a0ea6e14b51b2cdd92b4c9da442f1fef3eeeafa26cf3ef3f84dd4290f9c6ac27` |
| `code/hyperk_distributed_kernel.py` | `b05dc1078ba84f7969898abd6d6444249b12d953df0a8fd7316abae0e2535e8a` |
| `manuscripts/hyperk_full_controller.md` | `38de54de8b5e5d751e9d700f689b9417b610019d56e170d47f209c86e2adbec6` |
| `manuscripts/hyperk_kernel_research.md` | `c4dc2db4da2e502f0bc8d564e44c2f504b13e9e0fae7ae77b780cfdb70838f44` |
| `code/hyperk_kernel_research.py` | `4c96f78d90110752293dc798059f87c091b7d6578ea63c0734cc3541d3d2cc34` |
| `manuscripts/hyperk_incidence.md` | `fd2ab35b539415ac65a132b7fddfb6acaa87b5af65f579f9eb64f27cc7e403d8` |
| `code/hyperk_incidence.py` | `8b2bbd2e88fdbfeb5461f6b85e1bd39626df8d4b6caa0818816aff99bd47283e` |

The independent program [hyperk_absorber_controls.py](../../originals/reviews/hyperk_absorber_controls.py)
imports no author module. Its SHA-256 at this review is
`2e029660aa6dac06bdc64598ae78fcf5dd2c41b2203289e43d9f089e8cf91b3c`.
It verifies all nine source bindings before running.

## 1. Integral contraction and strict strata

### Generic zero-margin tensors

The star identity in GA is an integer identity. For a fixed anchor tuple,
expanding a term that uses an anchor in a nonempty coordinate set invokes a
vanishing marginal; no average of tensors is taken as the answer. The good-cell
boxes have disjoint reflection orbits between factors. Subtracting them preserves
both generic support and zero margins, so the bad-cell estimate applies again
at the next step. The union bound is `p^2/m`, and the factor `2^p` is the full
box support cost. Consequently the stated threshold really gives an integer
remainder with at most half the preceding `l1` norm. Integer termination and
the geometric coefficient-cost sum are valid for inputs of arbitrary amplitude.

For an independent implementation I selected the `p` least-loaded positive
orbits instead of searching all anchor tuples. Give an orbit the sum of
`|F(x)|` over cells containing it. Total orbit load is `p ||F||_1`; the `p`
least-loaded orbits have total load at most `p^2 ||F||_1/m`. This yields the
same bad-mass estimate and an exact deterministic control of GA. A dense generic
cycle required two actual contractions, with norms `128, 8, 0`.

### Rooted selectors and opposite endpoints

The auxiliary selector indexed by a proper coordinate subset is reused in
every partition term. Its alphabet remains fixed while the root parameter
changes. This coherence is essential to both the PS cancellation and the later
path identity.

For nonzero `t` outside the auxiliary orbits, the only full-block diagonal
support cell of the rooted selector is its root cell. A negative `t` changes
neither the collision classification nor the native signed-line class. In the
difference of two rooted selectors, every all-auxiliary cell is identical and
cancels. Each surviving cell therefore exposes an endpoint. The two surviving
parts are disjoint even for `u=-v`: at a root coordinate the other endpoint
selector can use neither that root value nor an auxiliary with its absolute
value. Thus the difference remains unit-valued, and its claimed point-load
argument does not conceal auxiliary-only support.

### The central block and full signed contractions

For the raw central box, distinct positive auxiliary labels ensure that every
nonaxis signed block has exactly the witness `t=0`, with coefficient one.
The private signed-block alphabets in LP make its decorated partition terms
disjoint. No correction term reaches the all-zero cell. This proves the unit
central template, its coefficient one there, and the stated alphabet/support
invoices. It also treats the singleton center orbit explicitly.

The tensor product used for a compact stratum lift is in the full kernel.
A contraction contained in one factor vanishes by that factor's full-kernel
property. A contraction crossing factors cannot have a nonzero parameter,
because their nonzero orbit alphabets are disjoint, and it cannot have zero
parameter because only the central factor can use zero. This verifies all
signed sections, not just the full-body traces.

### Increasing orbit count

The stratum margin lemma uses an actual signed-block line equation. When its
parameter is zero or coincides up to sign with another block parameter, the
cell has fewer nonzero orbits. Those terms vanish by the induction hypothesis.
All remaining terms belong to the specified signed type. Extension by zero
on nongeneric parameter tuples therefore has zero margins.

Every nonzero factor of a lift always retains an endpoint orbit. Leaving its
native diagonal introduces an additional private orbit; leaving the central
cell of the center factor does the same. Private alphabets prevent these
additional orbits from merging with another factor. All spill consequently has
strictly larger orbit count. It is safe to process types in arbitrary order at
one fixed count, after every smaller count has been cleared.

The `l1` ledger is also correctly ordered. It tracks the compact lifts, with
support at most `S_d`, and grows by at most `1+2S_d` per type. The total compact
coefficient cost is at most the stated `C_d ||M||_1`. It does not accumulate
an extra power of `n` at each stratum. The number of types and all palette,
support, and threshold constants are finite functions of fixed `d`; their
large size is acceptable for this component's quantifiers.

## 2. Fixed family, routing, and point degree

The `2d+1` disjoint palettes suffice: a compact parameter box touches at most
`2d` endpoint orbits, so one palette avoids them all. Its chosen auxiliary data
remain fixed for that compact lift's complete subdivision. The stated palette
invoice pays the central factor and every noncentral factor separately.

The robust graph argument is elementary and valid. After at most `F_d` whole
orbits are deleted, consecutive surviving positive labels have cyclic gaps at
most `F_d+1`. The corresponding positive graph is connected, as is its negative
copy, and the sign-switch edges join them. The threshold leaves surviving
orbits and enough labels for the palettes. No spectral expansion property is
asserted or needed.

At each subdivision step, the deleted orbits are the chosen palette and the
endpoints of all other current factors, including the previously selected
graph edges. There are at most `P_d+2(p-1)` of them. The current endpoints
survive. Exact telescoping with unchanged auxiliary data produces generic
edge tuples in one fixed indexed family.

The maximum-coefficient proof withstands the relevant adversarial distinction.
Fix one final ordered edge tuple. The first edge occurs at most once on the
first simple path; it fixes the next path, whose specified edge also occurs at
most once; induction gives at most one complete branch producing that tuple.
Its coefficient in one compact lift is therefore `0,+1,-1`. Summing compact
lifts bounds each final indexed coefficient by their original total absolute
coefficient cost. There is no bound here on the total absolute coefficient
after routing, and the manuscript correctly does not use one. Path length is
absent from the earlier stratum ledger because subdivision is an exact identity
for the already chosen compact tensor.

The point-degree count includes the entire support of each template. In a
nonzero block, some coordinate displays an endpoint outside the palette;
undoing its block sign determines that graph vertex. There are at most `|B|`
coordinate choices and at most `Delta_d` incident graph edges. The product
bound, summed over signed types and palettes, therefore pays even cells with
zero net contraction. With no nonzero blocks there is just one template per
palette, which is also covered. Indexed duplicates remain counted.

Finally, unit coefficients and zero axis margins imply equal positive and
negative counts in every axis fiber. Pairing them proves the asserted local
equal-gap-switch form along any selected coordinate. It does not choose fresh
prime endpoints or disjoint placements for different frame members; those
remain explicit downstream obligations.

## 3. Residues, rounding, and the numerical interface

Saturation is used in the correct direction. If `A M0=q y`, the integer vector
`y` lies in the rational span of the integer image. Stable saturation gives
`y=A Z`, and `M0-q Z` is an exact integer kernel lift. AF then applies, and
reducing its integer coefficients gives representatives from `0` through
`q-1` in the same fixed family. No bound on the intermediate lift is required.
This works for composite moduli, moduli sharing factors with `n`, and `q=1`.

The explicit KG version in BK is consistent with this argument: standard-cell
values specify a kernel element; coefficient-one elimination determines all
other cells over every residue ring. IK is formally stated for dimension at
least two. The remaining `d=1` case consumed here is immediate: its incidence
map is the single sum row and has image `Z`. The separately stated `d=0`
scalar convention creates no residue or pairing problem; pairing is then in
an outer coordinate.

UF is consumed only through its fixed, input-independent family of unit
templates, its logarithmic point degree, and its real coefficient bound.
Rounding template coefficients preserves integral full-kernel membership for
an integer input. At each cell the error is at most half its template degree,
so the exact remainder has supremum norm at most `(U/2) log n` and `l1` norm
at most `(U/2)n^d log n`. Applying AF to that remainder gives BK's additive
`n^d log n` term. Rounding is never applied entrywise.

For a real input, the rounded combination is still an integer kernel element
within the same logarithmic cell distance. Its remainder need not be integral,
and AF is correctly not applied to it. This establishes precisely the stated
lattice covering-radius interface. The indexed union of the two fixed families
has the declared support, size, and point degree. The displayed constant `V`
pays the coefficient ceilings as well as these counts for `n>=3`.

The parity paragraph also has the right ring: divide the even integer line
discrepancy by two before reducing modulo `h=g/2`; do not invert two modulo
`g`. A switch gap congruent to two modulo `g` implements twice the coefficient
modulo `g`, and `h=1` needs no repair. Numerical drift remains a separate
capacity charge. In the nonaxis use `d<=k-2`, BK's additive term divided by
`X` is `O_k(n^-2 log n)` under the stated gap and pool-scale inputs. Its
`n^eta` loss and logarithmic family incidence must still be paid by the final
capacity ladder. This review does not certify those physical payments.

## 4. Independent exact controls and negative controls

The reviewer program uses Python's standard library and exact integers or
fractions. Signed-line images are derived directly from support cells. At a
zero parameter it explicitly enumerates every normalized sign vector. Thus
missing central sign classes cannot be hidden by a nonzero-only convention.

The strongest end-to-end finite control starts with a separately constructed
full square incidence matrix at `n=9`. Independent integral row and column
operations give 19 unit pivots and zero remaining rows, with both transformation
identities verified. Seed `2026110307` supplies free integer kernel coordinates.
Their resulting tensor, supported in `[-4,4]^2`, is embedded by zeros in the
larger alphabet with `m=90`. It is not generated from AF templates as its input.
The program then implements every absorber stage, exact graph subdivision,
and reconstruction independently of author code.

| Independent control | Observed result |
|---|---|
| Complete two-dimensional absorber | Input `l1=350`; all six types cleared; final remainder zero |
| Stratum norms | `350, 376, 416, 458, 434, 434, 0` |
| Compact lift cost | 113 lifts; total absolute coefficient 603 |
| Graph subdivision | 211 expansion terms; 147 used indexed members; maximum coefficient 39 |
| Rooted selectors and differences | 16 cases in dimensions 1--4, including negative and opposite endpoints and mixed signs |
| Central templates | Complete signed signatures and pairing in dimensions 1--3 |
| Generic contraction | Norms `128, 8, 0`; exact reconstruction and coefficient-cost checks |
| Simple-path telescoping | 20 final tuples, each occurring at most once in the compact expansion |
| Complete fixed-frame fixture | All 294 generic edge-pair members enumerated; actual maximum point degree 9 |
| Residue lifts | Moduli `1,2,3,4,6,8,9,12,15,30`, with exact incidence and congruence checks |
| Coefficient rounding followed by AF | Nonzero integral remainder of `l1=6`; absorbed exactly; maximum final coefficient 1 |
| Real covering radius | A nonintegral full-kernel input has an explicitly checked nearby integer full-kernel element |

The maximum point degree 44 among the 147 members used in the full replay is
also recorded by the program. This is a used-subfamily observation; it is not
substituted for the proof about the entire asymptotic fixed family. The separate
294-member fixture enumerates its whole chosen finite frame.

The negative controls deliberately reject six plausible false shortcuts:

1. A walk traversing a cycle twice telescopes but gives an edge coefficient
   of magnitude two; the simple-path hypothesis cannot simply be dropped from
   the unit-prefix argument.
2. Different auxiliary palettes on consecutive rooted differences leave an
   extra term, even though the sum still lies in the full kernel.
3. Restricting to the generic stratum before clearing lower-orbit strata gives
   nonzero parameter margins.
4. The tensor `(e_1-e_2) tensor (e_1-e_3) tensor (e_4-e_5)` has zero axes and
   zero full-body traces but nonzero pair-section traces. A body-only kernel
   test would falsely accept it.
5. Rounding the cells of a real full-kernel tensor independently breaks its
   margins, whereas rounding coefficients of a full-kernel template does not.
6. At `n=3`, exact elimination leaves a factor-three row after six unit pivots.
   The program constructs a kernel vector modulo three that violates the
   associated primitive row modulo three, proving that it has no integer
   kernel lift. This prevents transferring stable saturation to small orders.

The graph controls check exact identities and finite support incidence. They
are not expansion certificates, asymptotic probability arguments, or proofs
from a list of dimensions. The universal claims above were assessed from the
dimension-parametric arguments.

## 5. Reproduction and evidence boundaries

The executed Python version was `3.12.14`. The frozen author commands both
passed in the isolated archive:

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyperk_reconstruction_alt.py --self-test
python3 -B problems/prime-arrays-beyond-square/code/hyperk_distributed_kernel.py --self-test
```

These include the author's symbolic invoices at dimensions five and six,
full signed signatures, strict spill, and finite residue/rounding controls.
They are supporting finite evidence, not the proof of arbitrary dimension.

From the repository root, the reviewer replay can be reproduced as follows:

```sh
review_dir="$(mktemp -d)"
git archive c7f22dd8a01d28ab02c832f6c2b8b4145d88b6bb problems/prime-arrays-beyond-square | tar -x -C "$review_dir"
python3 -B problems/prime-arrays-beyond-square/reviews/hyperk_absorber_controls.py "$review_dir"
```

The independent replay passed, including all negative controls. A local
`python3 -B check.py` run also passed all 45 repository integrity/tool tests.
This last result concerns metadata and tool behavior, not mathematical validity.
Raw logs and the temporary archive were not added to the repository.

| Obligation | Review outcome |
|---|---|
| GA, rooted differences, central LP, strict signed-stratum clearing | Positive conventional proof review |
| Fixed palette/graph family, maximum coefficient, full point load | Positive conventional proof review |
| AF over integers and arbitrary residue rings in the stable range | Positive conventional proof review using the named incidence interface |
| UF probability proof | Outside this review; separately assigned |
| UF + AF rounding, exact BK reconstruction, covering radius | Positive review of the deduction from the precise named components |
| Complete physical all-line prime-hypercube composition | Outside this review |
| Finite controls | Passed at the bound scientific bytes |
| Formal kernel verification or finite prime arrangement | Not claimed |

No blocking correction to AF or BK is requested. The coordinator may attach
this review to those components while preserving the separate UF and full
physical-composition review obligations.
