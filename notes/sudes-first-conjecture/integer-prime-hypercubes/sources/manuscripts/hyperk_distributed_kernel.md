**Public reading copy.** Presentation and links have been normalized. Historical status statements below belong to their source revisions; see the [current publication status](../../README.md#review-and-verification-status). The matching original bytes are in the [source archive](../../originals/manuscripts/hyperk_distributed_kernel.md).

# A fixed distributed integer kernel frame and its residue interface

Author: `/root/kernel_architecture`. This is an additive component of the
continuation of PR83 after delivery
`1e7883d705cafbaf717bfacefcf6695baebf6dbe`. It leaves the frozen scientific
sources and their review records unchanged. All labels here are
manuscript-local. The author contributed to the selector and absorber
architecture and is therefore excluded from independent review of those
arguments and this synthesis.

The canonical constructions are **UF(d,eta)** in
[the uniform real-frame manuscript](hyperk_full_controller.md) and **AF(d)**
in [the integral absorber manuscript](hyperk_reconstruction_alt.md).
This source proves their exact composition and records the interface that
the physical controller may consume. It does not repeat their constructions.
Availability of prime pairs, disjoint placement, the correction hierarchy,
and completion of the exact pool remain obligations of the final
composition manuscript. No tensor in this source is presented as a
prime-array arrangement.

## 1. Definitions and quantifiers

Use the centered alphabet `I={-m,...,m}`, of odd size `n=2m+1`, and the full
signed-coordinate line geometry of [PROBLEM.md](../PROBLEM.md). Let `A_d,n`
be its integer incidence map and write

`K_d(Z)=ker A_d,n`,

`K_d(R)=ker(A_d,n: R^(I^d) -> R^(lines))`,

`K_d(q)=ker(A_d,n: (Z/qZ)^(I^d) -> (Z/qZ)^(lines))`.

Axes are included in these definitions. All nonaxis signed blocks, all
fixed complementary coordinates, and the central reflection orbit are
also included. The integer and real kernels have the same defining
equations; the residue kernel is specified separately because its lifting
requires the stable integer-incidence result.

A **unit kernel template** is a tensor in `K_d(Z)` with entries in
`{-1,0,1}`. A fixed indexed family may include several identical tensors;
every occurrence counts separately in its size and support incidence.
For a family `F`, define its point degree by

`load(F)=max_(x in I^d) #{alpha: F_alpha(x)!=0}`.

The complete family, including templates whose eventual coefficients
vanish, must be reserved in the physical construction. Its geometry
cannot be selected after observing the target error.

For `d=0`, use the single scalar template `1`; the line-incidence system
is empty. Its product with an outer selector is paired in an outer
coordinate. All substantive statements below are for fixed `d>=1`.

## 2. The two canonical component interfaces

Fix `d>=1` and a real `eta>0`. For all sufficiently large odd `n`, the
two component theorems supply the following families, both chosen before
the input tensor.

| Component | Fixed family and support | Coefficient statement |
|---|---|---|
| UF(d,eta), Sections 1--6 | `J`, at most `U n^d log n` unit templates, each of support at most `q_d`, with `load(J)<=U log n` | Every `D in K_d(R)` has a real expansion with maximum coefficient at most `U n^eta ||D||_infinity` |
| AF(d), Sections 1--7 | `Gamma`, at most `A_d n^d` unit templates, each of support at most `S_d`, with `load(Gamma)<=B_d` | Every `R in K_d(Z)` has an integer expansion with maximum coefficient at most `C_d ||R||_1` |

Here `U=U(d,eta)` and `q_d,A_d,B_d,S_d,C_d` are finite constants. Enlarge
`U` if necessary so one value covers both UF bounds. The absorber source
gives finite recurrences for every AF constant and a sufficient positive
orbit threshold `M_d`. The uniform-frame source gives its marker, support,
sampling and concentration constants, followed by an explicit choice of
the spectral error in terms of `d,eta`. Taking the maximum of these
thresholds and the incidence threshold suffices. None is uniform as
`d` or `eta^-1` grows.

AF additionally proves that its same fixed family generates `K_d(q)`
for every positive integer `q`, once `n>=3^d`. This is an integer-lattice
statement, not a consequence of rational rank or numerical Smith data.

Both components produce genuine unit templates. Their proofs pay the
support of auxiliary terms whose contracted sum is zero. Every template
has zero axis sums, so along any chosen coordinate its positive and
negative cells can be paired within individual axis fibers. The pairing
uses exactly half of its support cells as pairs. This local physical
property does not assert that prime endpoints for different templates
have already been chosen.

## 3. Exact integer reconstruction

**Theorem BK(d,eta).** For every integer `d>=1` and every real `eta>0`
there are finite constants `N(d,eta), V(d,eta), Q(d)` such that, for every
odd `n>=N(d,eta)`, there is a fixed indexed family `F_d,n` with:

1. Every member is a unit kernel template, has support at most `Q(d)`,
   and is pairable along any chosen coordinate.
2. The family has at most `V(d,eta) n^d log n` members and point degree
   at most `V(d,eta) log n`.
3. Every integer `D in K_d(Z)` has an exact integer expansion

   `D=sum_alpha z_alpha F_alpha`,

   with

   `max_alpha |z_alpha| <= V(d,eta) [n^eta ||D||_infinity + n^d log n]`. (BK1)

4. The subfamily `Gamma` generates `K_d(q)` for every positive integer
   `q`; its coefficients can all be chosen in `{0,...,q-1}`. This
   residue subfamily has point degree at most `B_d`, independent of `q`.
5. Every `D in K_d(R)` is within `V(d,eta) log n`, in cell supremum
   norm, of an integer element of `K_d(Z)`.

The order of quantifiers is

`for every d,eta; there exist N,V,Q; for every odd n>=N;`
`there exists F_d,n; for every input D; there exist coefficients.`

In particular the family is independent of `D`. The statement allows
an arbitrarily small fixed power loss in the large-error term. It does
not claim the stronger `E polylog n` bound proposed in the earlier
unresolved BK interface. The later capacity ladder must explicitly pay
`n^eta` and the logarithmic support multiplicities.

### Proof of the integer statement

Take the indexed union `F=J disjoint_union Gamma`; common tensors retain
their separate indices. For `D in K_d(Z)`, choose a real UF expansion

`D=sum_(alpha in J) c_alpha J_alpha`.

Round each `c_alpha` to a nearest integer `a_alpha`, using any fixed tie
rule. Define

`R=D-sum_(alpha in J) a_alpha J_alpha`.

This is an integer tensor in the full signed-line kernel: both terms are
integer kernel tensors. At any cell, only the templates counted in its
point degree can contribute a rounding error. Since their nonzero entries
have magnitude one,

`||R||_infinity <= (1/2) load(J) <= (U/2) log n`,

`||R||_1 <= (U/2) n^d log n`.                           (BK2)

Apply the integer absorber to `R`. It supplies integer coefficients
`b_gamma` with

`R=sum_(gamma in Gamma) b_gamma Gamma_gamma`,

`max_gamma |b_gamma| <= (C_d U/2) n^d log n`.             (BK3)

The rounded real-frame coefficients satisfy

`max_alpha |a_alpha| <= U n^eta ||D||_infinity + 1/2`.   (BK4)

Combining these two expansions proves exact reconstruction. No limiting
approximation remains in (BK1). The finite constants can be taken, for
example, as

`Q(d)=max(q_d,S_d)`,

`V(d,eta)=U+A_d+B_d+C_d U+2`.

For `n>=3`, `log n>1`, so this one value pays family size, point degree,
the coefficient ceiling, and both terms of (BK1). These are intentionally
loose bounds. The coefficients need not minimize support or norm.

For a real input, the same rounded UF combination is still an integer
element of `K_d(Z)`, and the pointwise estimate (BK2) still bounds its
distance from the input. The remainder need not be integral in this
case, and AF is not applied to it. This proves item 5, the lattice
covering-radius interface used for compatible splitting of shared traces.

Notice why the two steps are ordered this way. AF's `n^d` loss is applied
only to the logarithmic rounding remainder, never to the original
large error. Conversely rounding is performed only on coefficients of
unit full-kernel templates. Rounding cells separately would not preserve
compatibility.

### Counts on intersection strata

The point-degree bound directly implies a support invoice on every set
of cells `S`:

`sum_alpha |supp(F_alpha) intersect S| <= V(d,eta) log n |S|`. (BK5)

Thus a signed equality or central-coordinate stratum with `p` free
parameters has at most `V(d,eta) n^p log n` support incidences. This counts
intersections with every template, including templates with zero trace
on that stratum. It does not infer an occupancy estimate merely from a
vanishing signed contraction or a global template count.

## 4. Composite moduli, lifting, and parity

Part 4 of BK is the residue conclusion of AF, restricted to its fixed
integral subfamily. The stable incidence lemma IK is essential: arbitrary
small-order incidence matrices can have torsion, and those orders are
not silently included in this interface.

There is also an explicit way to see the lift used in that argument.
Fix one marker assignment for the monic basis KG of
[the incidence manuscript, Section 5.2](hyperk_incidence.md). Let `S` be
its standard cells, and let `K_v` be the integer basis vectors. If
`Dbar in K_d(q)`, choose integer representatives `r_v` of its values at
standard cells and form

`H=sum_(v in S) r_v K_v`.

Then `H in K_d(Z)` and `H modulo q = Dbar`. Indeed the difference has
zero standard coordinates and zero line contractions modulo `q`.
For a nonstandard coordinate, its chosen line relation expresses its
value as the negative sum of lower-weight values with coefficient one.
Induction in the same monic reduction order makes the difference zero
everywhere. This works over every `Z/qZ`, including composite moduli and
moduli sharing factors with `n`.

Apply AF to `H` and reduce its coefficients modulo `q`. Their least
nonnegative representatives lie between `0` and `q-1`, while the family,
its supports, and its point degree remain unchanged. A large intermediate
norm of `H` is harmless here: it is the reduced coefficients that are
physically realized. There is no division by `q`, by `n`, or by a
nonunit residue in this construction.

For the prime controller, let the common even main gap be `g` and put
`h=g/2`. The current sum on an odd-length line and its odd target have
the same parity, so their discrepancy is an even integer. Once a native
stage's compatibility equations place the half-discrepancy in `K_d(h)`,
BK supplies residue coefficients `0<=c_gamma<h`. A fresh equal-gap switch
whose actual gap `b` satisfies `b=2 modulo g` contributes

`c_gamma b Gamma_gamma = 2 c_gamma Gamma_gamma modulo g`.

It therefore repairs the original even discrepancy. The stage must
reserve up to `h-1` such unit switches per indexed residue template.
If `h=1`, there is nothing to repair. All subsequent main switches use
gaps divisible by `g`, preserving the repaired residues. This explains
the division by two in the integer discrepancy before entering the
residue ring; it is not division by two inside `Z/gZ`.

This paragraph is an interface for a native correction stage. The full
composition must prove that its current residual lies in the stated
kernel and must pay the actual numerical drift caused by residue
switches. Matching residues alone does not finish numerical correction.

## 5. Numerical units and the capacity obligation

Suppose the discrepancy to be represented is an integer tensor `Delta`
whose entries are divisible by the common gap `g`, with
`||Delta||_infinity<=E`. Apply BK to `D=Delta/g`. The scalar values that
must be supplied by equal-gap reservoirs obey

`g max |z_alpha| <= V(d,eta) [n^eta E + g n^d log n]`.  (BK6)

For a nonaxis native block of size `r>=2` in ambient dimension `k`, its
complement dimension is `d=k-r<=k-2`. In the regime used by the inherited
prime-supply lemmas, `g=O_k(log X)`, and the exact initial-prime pool has
`X asymptotic to k n^k log n`. Consequently

`g n^d log n / X = O_k(n^(d-k) log n) = O_k(n^-2 log n) -> 0`. (BK7)

The second term is therefore smaller than one `X`-scale reservoir for
all sufficiently large odd `n`, uniformly over the finitely many
complement dimensions of a fixed `k`. This calculation consumes no
dimension-independent threshold.

The first term requires real slack. If consecutive large-error and
capacity scales are `n^a X` and `n^b X`, the composition must choose
`eta<b-a`. A finite number of stages permits such a choice after the
whole dimension-dependent depth has been specified. Constants depending
on that choice remain fixed as `n` tends to infinity. The additional
`log n` in family size and point degree must also be included in total
reservations, line occupancy, midpoint bias and concentration; it may
be absorbed by a strict positive power margin, not dropped from the
ledger.

The combination AF+UF avoids an unproved uniformly bounded inverse on
the original incidence matrix. It instead supplies a fixed physical
frame with an exact integral finish and a quantified small power loss.
The final composition remains responsible for every prime-pool and
packing inequality that consumes this frame.

## 6. Dependency graph, checks, and scientific status

The dependency chain is:

| Input | Used for |
|---|---|
| IK and KG in `hyperk_incidence.md` | Stable integral/residue kernel structure and the common-marker bases used by UF |
| PS and LP in `hyperk_kernel_research.md` | Unit physical templates, central blocks, and rooted differences used by AF and UF |
| AF(d) in `hyperk_reconstruction_alt.md` | Fixed exact integer absorber and all-composite-modulus generation |
| UF(d,eta) in `hyperk_full_controller.md` | One universal real frame with bounded support incidence and arbitrarily small fixed power loss |
| BK(d,eta), this source | Exact integer reconstruction, residue interpretation and the combined numerical invoice |
| Final full controller | Correction hierarchy, fresh endpoint supply, disjoint placement, centering and exact-pool completion |

The companion
[hyperk_distributed_kernel.py](../../originals/code/hyperk_distributed_kernel.py)
performs exact author checks with Python 3.11 or newer and the standard
library:

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyperk_distributed_kernel.py --self-test
```

It independently enumerates every signed contraction of its sparse
fixtures. It checks rooted differences with positive, negative and
opposite endpoints; central LP templates; full signed partition lifts
through dimensions five and six; exact native restrictions and refinement
of orbit types; support incidence of a finite fixed graph frame; integer
coefficient rounding; and monic lifts modulo `2,3,4,6,8,9,12`. The graph
fixture checks actual incidence, not an expander or asymptotic sampling
claim. Exact symbolic invoices include dimensions five and six, retaining
the enormous coefficient constant in factored form rather than expanding
its digits.

Four negative controls reject restriction before coarser strata are
cleared, entrywise rounding outside the kernel, doubled coefficients
misidentified as a unit physical template, and a lift whose different
parameter factors share an endpoint orbit. The independent prime-array
certificate checker remains separate and is not replaced by these tests.

At author completion, BK is a conventional deduction from the two named
component proofs. Its components and this deduction require independent
review at an exact frozen source revision. Finite checks, repository
integrity, remote CI, independent mathematical review, and formal kernel
verification are separate statuses. No formal kernel verification or
complete finite prime arrangement is asserted by this source.
