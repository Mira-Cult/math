# Independent review of the general normalization, controller, and composition

Reviewer: /root/analytic. Review completed 2026-11-03.

## Finding and exact source

**No blocking mathematical or finite-certificate defect was found in the
reviewed scope.** I accept the new exact normalization and local arguments,
the fixed-rank physical transfer under its stated inputs, and the final
composition with its explicitly named analytic dependencies as conventional
proofs in that scope. This is an internal mathematical/code review, not
kernel verification, external refereeing, a formal GitHub approval, or a
remote CI result.

The exact scientific revision reviewed is

    d9bd9ac92851a9996c14dd2fdf49f1879bcae97b

with tree 85c7e494de3ea0bd3db7d508530541b2f15cbade and definition parent
a7f841cf1dba596477ffc360e20fef273a14d729. The commit is available locally.
Before executing the programs I compared all seventeen files listed below
byte for byte with git show at that revision. All matched. The four
previously frozen quartic manuscripts have an empty diff against scientific
revision 6f8524253c32db096e38715fd69e880e0fa85fdd.

No frozen scientific source was edited during this review.

## Authorship, scope, and exclusions

I authored general_analytic.md, and therefore **exclude that entire
manuscript from independent acceptance**, including GW/GP/GE/GL/GT/GS/GI/GM/GU.
Its hash is recorded only to bind the dependency used in composition.

Before the freeze I discussed the logarithmic-face decision issue, the
energy-domain repair, phase-independent log cells, and reflected endpoint
geometry with the normalization author and coordinator. The energy-cell
interpolation and endpoint observations were shared. I read GN2 and the
corresponding parts of the composition for consistency, but do not count
those shared observations as an independent review of my own contributions.
Likewise, the analytic matching/endpoint content overlapping GC(r)'s G5
remains an explicit dependency, rather than a second independent acceptance
of my analytic lemmas.

The independent acceptance covers:

- **GN1, GN3, GN4**, authored by /root/normalization: exact finite
  associate comparison and complete prefixes; certified subgroup bounds and
  full-unit coverage; norm-two classification, unit index, and exceptional
  associates; rational obstruction; and the K23 nonprincipal-prime control.
- **GC(r)**, authored by /root/controller, as a physical theorem under
  H1--H4: DG specialization, seed index and contained ideal, reserved-prefix
  attainability, rank-r zonotopes, whole-element operations, parameter and
  depletion invoices, concentration, integer flows, and complete line stages.
- **CYC composition**, authored by /root: correct use of the named
  normalization/analytic/controller inputs, exact-total and residue
  compatibility, canonical model selection, all line families, and quantifiers.
- **All four new programs and their frozen inputs**: producer/search code
  authored by /root, independent checker by /root/controller, and unit
  utility by /root/normalization. I authored none of these implementations
  or the seven retained arrays.

The earlier immutable spatial imports and IT tensor theorem are the same
ones examined in the
[quartic normalization/controller review](normalization-controller-review.md).
I checked their scope and hypotheses at the new call sites. This review does
not invent a new review of an unavailable upstream revision or claim the
analytic sources as independently proved here.

## Mathematical scrutiny

### Exact normalization and unit coverage

GN1's trace form is positive definite, and its inverse-Gram bound includes
every integral element with energy at most the starting candidate's energy.
Testing that the quotient is both integral and norm one tests the whole
associate class in the CM field. It does not merely test membership in a
chosen unit subgroup. The finite minimum, exact half-open torsion sector,
and final coefficient order consequently give existence, uniqueness, and
starting-generator independence.

The independent-unit search needs to recognize only a nonzero determinant.
Dovetailing candidates and certified precision prevents a dependent tuple
from blocking the search. Dirichlet's theorem guarantees eventual success.
The subgroup's centered log parallelotope is used only to prove a bound,
not to decide an element's canonical boundary. With
$`U=\prod A_i`$, its estimate is
$`E(\mathrm{can}\alpha)\le sU|N\alpha|^{2/r}`$.
Applying the same estimate to a unit proves that the subgroup generators
together with all units of energy at most $`sU`$ generate the full unit
group. This pays for every unit-index coset without an unverified index-one
assertion or a GRH assumption.

The complete bounded-norm coefficient box follows from that estimate and the
inverse trace Gram matrix. The quotient-field criterion is sufficient and
necessary: if $`N\alpha=p^f`$ and
$`\gcd(\Phi_c,\alpha\bmod p)`$ is irreducible of degree $`f`$, the containing
maximal ideal and $`(\alpha)`$ have the same index. Conversely a prime
principal ideal gives just that finite field. A principal proper power of
a nonprincipal prime ideal is therefore rejected. Neither rational-prime
norm nor irreducibility is substituted for primality.

The reduced-conductor convention is necessary for the omission rule:
ramification depends on the field conductor, so the displayed factor two
in a conductor such as six is not an excuse to omit an unramified class.
The frozen quartic pool definitions are preserved exactly.

### Local obstruction and class-number control

GN3a's characteristic-two argument is valid: the odd-order part of the
cyclotomic root retains its order because $`X^d-1`$ is separable modulo
two. A norm-two residue field therefore forces odd part one. At a power
of two the sole prime is $`(1-\zeta_c)`$, of norm two and total
ramification.

GN3b proves the full unit-index assertion. For a unit, its conjugation
quotient is torsion. An odd torsion exponent would make a torsion-adjusted
unit divided by $`1+\zeta_c`$ real; the former has prime valuation zero,
the denominator valuation one, whereas every element of the real
subfield has even valuation. This contradiction leaves only the real-unit
coset. All associates of the norm-two prime consequently have boundary
first phases. Conversely an integral element on such a boundary has
positive odd prime valuation, so a retained prime cannot lie there.
Ordinary positive-coefficient sums remain strictly inside the sector.
This excludes **all** exceptional associates, even those with arbitrarily
large unit multipliers. Divisibility then excludes units, and the strict
sector excludes zero. The even-order impossibility is complete.

The rational obstruction separately handles both parities and uses an
actual axis line. The omission of two is explicitly a different rational
pool. It is not imported as an extra omission in any nontrivial cyclotomic
field.

For K23 I checked the ideal argument, not just the numerical Gauss sum.
The quadratic prime $`\mathfrak p=(2,\omega)`$ has exact class order three:
the norm form has no value two, and $`2-\omega`$ has ideal
$`\mathfrak p^3`$. The two degree-eleven primes above two in K23 extend
the two split quadratic primes. A principal extended prime would have
principal relative norm $`\mathfrak p^{11}`$, contradicting that order.
Both primes are nonprincipal, while their product is $`(2)`$; this proves
that the element two is irreducible and not prime. The argument establishes
a three-torsion ideal class, not an asserted exact K23 class number.

For source fidelity I reopened Milne's Algebraic Number Theory v3.08,
Theorems 5.1/5.9 and the printed p.101 K23 norm-descent argument, at
https://www.jmilne.org/math/CourseNotes/ANT.pdf. I also checked the official
PARI bnfcertify documentation at
https://pari.math.u-bordeaux.fr/dochtml/html-stable/General_number_fields.html:
the full-unit versus flag-one distinction in GN1 is correct. No PARI
calculation or database class-number assertion is used as evidence.

### Rank-r controller and quantitative costs

The controller keeps the arithmetic rank $`r`$ separate from spatial
dimension two or three. A rectangle still consumes two disjoint pairs and
a cuboid four; every pair is a pair of actual fixed-pool elements.

At the seed scale, the adjugate estimate yields

```math
d_\Gamma=O(\ell^r),\qquad
 \|G^{-1}\|_\infty=O(\ell^{r-1}/d_\Gamma),\qquad
 d_\Gamma O\subset\Gamma.
```

Thus $`\mathfrak q=d_\Gamma\mathfrak d_2\subset\Gamma`$ is an actual
contained ideal, with $`N\mathfrak q\le\ell^{r^2+2}`$ eventually.
The seed lattice is not asserted to be an ideal. For nonprincipal
$`\mathfrak d_2`$, rational scaling of that fixed lattice is sufficient
for its counts and finite quotient routing.

The multiscale prefix remains in $`\Gamma`$. Its last residual has size
$`O(d_\Gamma\ell)`$, and the inverse determinant factor cancels this
$`d_\Gamma`$, leaving $`O(\ell^r)`$ seed coordinates per final correction.
The total $`O(\ell^{r+1})`$ prefix fits inside $`P=\lceil\ell^{r+10}\rceil`$.
The doubled reference prefix is counted explicitly.

The rank-r zonotope argument uses an actual feasible polytope. An extreme
point has at most $`r`$ fractional coefficients; after rounding, the
residual is an element of $`\Gamma`$ of size $`O_K(R)`$, and the separately
reserved prefix attains it. This is complete integer attainability, not
only real-span coverage. Complementation flips the entire physical stage,
so a recombined coordinate demand produces one permutation.

I recalculated the profile

```math
g=r+10,\quad b=r^2+2,\quad c_{\rm box}=5g,\quad
 a_2=rc_{\rm box}+b+100,\quad h_r=a_2+3g.
```

The decisive margins are respectively 100 logarithmic powers for worst-case
local deletion, $`g-r=10`$ for graph flows, $`g-r-2=8`$ for the tensor
flow, and $`c_{\rm box}+a_3-h_r=g`$ for midpoint bias. The total reservation
is $`O(M/\ell^{a_2})`$; each local class has supply
$`\gg M/\ell^{rc_{\rm box}+b}`$, and each equal-gap matching has one
additional logarithm in its denominator. Global depletion is charged to
each local request. The proof takes only the needed submatchings.

Seed copies, modular switches and prefixes cost
$`O(n^{D-1}\mathrm{polylog}n)`$, and their per-line costs are $`o(n)`$.
The body/diagonal term with the larger capacity is lower order because its
type count is smaller by a factor of $`n`$. These statements are checked
for both dimensions, not inferred from a rank-four example.

Whole-reservoir randomization gives midpoint expectations while keeping
all coordinates and pair stages together. The bound on the unused-pool
mean follows by summing over an axis partition and using the exact total.
The filler concentration is sampling without replacement. No independence
among coordinates or line events is assumed.

The crucial tensor remainder is the pinned $`O(n)`$ integer correction,
which becomes $`O_K(n\ell)`$ after returning from seed coordinates:

```math
\frac{n\ell}{K_2R}
   =O_K(\ell^{a_2+1}/R)\longrightarrow0,\qquad
 R\asymp_K n^{D/r}(\log n)^{1/r}.
```

This pays for every fixed $`r`$, and explicitly does not prove a
growing-rank result. The former quadratic remainder would not suffice.
The square and cube stages include both square diagonals, all four bodies,
and all six slice-diagonal families with the cited preservation contracts.

### Composition and quantifiers

CYC invokes the exact energy pool at new conductors and CPA4 only for the
three retained quartic pools. It uses the principal-prime density constant
and complete norm ties rather than treating all prime ideals as elements.
Its application of my analytic lemmas was checked at the interface level;
that check is not independent acceptance of those lemmas.

The product of ramified prime ideals is a fixed valid target modulus. GN3
ensures it includes every norm-two prime. Requiring unit target residues
there makes the claimed unramified targets legitimate. For a power of two,
odd $`n`$ makes the exact pool total, the square list length, the cube tensor
length, and every face-family total have the required residue one. For
other conductors there is no norm-two condition. The tensor marginals and
the six diagonal-square totals are exact identities in $`O_K`$.

The smaller target windows with exponent $`h_r+2`$ are $`o(H)`$. Fixed-factor
allocations allow all successive target selections to remain in that
window. Every analytic completion uses three forms; the construction does
not invoke a theorem for a growing system. All rank losses are fixed
logarithmic powers, and all inequalities hold on a complete admissible
tail. Taking the maximum of the two dimensional thresholds is valid.
Ineffectivity, the rational exception/repair, and the distinct normalization
models remain visible in the theorem statement.

## Program review and actual replay

All four new sources were read before execution. The independent checker
imports no producer, search program, or other project module. The
implementations nevertheless share standard mathematical methods: both norm
calculations use integer multiplication matrices and Bareiss determinants,
both ellipsoid enumerators use rational LDL decompositions, and both
irreducibility tests use the finite-field Frobenius criterion. I do not
describe those as different algorithms merely because they have different
authors.

There is substantive independent implementation at important boundaries.
The producer compares real parts against adjacent torsion rotations, while
the checker tests the two boundary sines in a larger exact cyclotomic field.
Both first decide algebraic equality, then refine rational intervals for a
strict sign; equality cannot cause endless refinement. The ellipsoid loops
use different integer interval bounds and exact residual tests. The checker
constructs required lines from varying-coordinate subsets and signs, while
the producer enumerates fixed/forward/reverse coordinate specifications.
Primality acceptance uses complete rational trial division and the exact
quotient-field test, not a probabilistic witness.

The finite checker proves class number one for its example fields from a
Minkowski certificate. Its bound is the floor of a **rational upper bound**
using $`\pi>3`$ and $`\lceil\sqrt{|D_K|}\rceil`$, which is sufficient;
it need not equal the floor of the sharp real Minkowski bound. Every prime
ideal below that bound is independently accounted for by a distinct actual
generator. Complete cutoff counts, including ramified primes for the class
certificate and higher residue degrees for the pool, then prove no ideal
is missing. Once one generator is inside the exhaustive energy ellipsoid,
every better or tied representative of that ideal is also inside it.

Observed runtime: CPython 3.12.14, standard library only. From the
repository root I ran:

    python -B problems/cyclotomic-prime-arrays/code/check_energy_certificate.py --negative-controls problems/cyclotomic-prime-arrays/inputs/energy_m15_cube3.json problems/cyclotomic-prime-arrays/inputs/energy_m15_square4.json problems/cyclotomic-prime-arrays/inputs/energy_m16_cube3.json problems/cyclotomic-prime-arrays/inputs/energy_m16_square3.json problems/cyclotomic-prime-arrays/inputs/energy_m7_cube3.json problems/cyclotomic-prime-arrays/inputs/energy_m7_square4.json problems/cyclotomic-prime-arrays/inputs/energy_m9_square4.json
    python -B problems/cyclotomic-prime-arrays/code/general_unit_certificates.py --output /tmp/cyclotomic-independent-unit-review.json

Both exited zero. The array checker accepted seven arrays, rejected all
101 requested corruptions, and passed 50 common arithmetic controls.

| Conductor | Rank | Array | Exact pool size | Norm cutoff | Complete cutoff classes | Required lines |
|---:|---:|---|---:|---:|---:|---:|
| 7 | 6 | square 4 | 16 | 71 | 20 | 10 |
| 7 | 6 | cube 3 | 27 | 127 | 32 | 49 |
| 9 | 6 | square 4 | 16 | 73 | 19 | 10 |
| 15 | 8 | square 4 | 16 | 61 | 18 | 10 |
| 15 | 8 | cube 3 | 27 | 151 | 30 | 49 |
| 16 | 8 | square 3 | 9 | 49 | 12 | 8 |
| 16 | 8 | cube 3 | 27 | 113 | 30 | 49 |

The differences between the pool sizes and complete cutoff counts show that
partial norm ties are exercised. The K7 cube has prime line residue degrees
1, 2, 3, and 6; the K15/K16 examples also contain higher-degree prime sums.
The negative controls include coherent nonminimal associate replacement in
the pool and complete-cutoff list, not only an obvious isolated array typo.
Other controls cover omitted ideals/ties, incorrect class-number certificates,
bad residue characteristics/degrees, repeated entries, and missing lines.
The common controls include exact boundary inclusion/exclusion, perturbations
within $`10^{-12}`$ relative scale, inert rational primes, split rational
primes, units, zero, ramification, and a proper prime-ideal power.

The unit-utility replay was compared byte for byte with the frozen
general_unit_subgroups.json; it matched exactly. All eight displayed
rational determinant intervals exclude zero. The certified degrees are
6, 6, 10, 8, 8, 8, 8, and 22, for conductors
7, 9, 11, 15, 16, 20, 24, and 23. The interval code rounds outward;
Machin, sine Taylor, and logarithm-series remainders are explicit, and
interval elimination uses only pivots whose intervals exclude zero.
The K23 Gauss sum, quadratic forms, residue degree eleven, and norm-descent
control also replayed. These are independent subgroup certificates, not
claims that the displayed subgroup index is one.

I did not rerun the stochastic array search. Certificate validity does not
depend on reproducing its search history. I did not treat a finite-example
class-number-one driver as an implementation of arbitrary-class-number
enumeration; GN1 is the separate proof of that general algorithm.

After writing this review I ran the required repository integrity command:

    python -B check.py --base 59e00a03e48e71c79a5c1be2cdba66d593cf42a0

It exited zero with all 45 metadata/tool tests passing. This is local
integrity evidence, not mathematical proof or remote fleet CI. A separate
read-only script also recomputed every hash row below and confirmed all
seventeen bindings.

## SHA-256 byte commitments

Paths below are relative to problems/cyclotomic-prime-arrays/.
The analytic hash is a dependency pin and is excluded from independent review.

| File | SHA-256 |
|---|---|
| PROBLEM.md | ad95075405f91ed77e5145f11e7c256bb2c46ada429309585fd91ea0710ee3c0 |
| manuscripts/general_normalization_local.md | 7d21da0fe1d2fcd50ba708c4b555c3e5a12f01c349661e5626fb1a928538e160 |
| manuscripts/general_controller.md | 233027e3650aee504735a197ddb02d24246d0823ee4551eb80baef68a53ab1bd |
| manuscripts/general_composition.md | 53cbd81439c3584b4bb18f390747a6f837f99f646af9aa725e9264ef2eaa2acd |
| manuscripts/general_analytic.md (excluded dependency) | 31da5bf826935c6c08fd3f98c2cc1246a4422ef226ef378354e0c09c232b74d9 |
| code/energy_cyclotomic.py | 66737ed888e7040c13ad820de441e8fae40d1ad8e3f8456b54af9fa9b259604d |
| code/search_energy_arrays.py | 94a78875c236ff12afcf88dac7513ff5c8b823f8e8ef8f96cc05d72c23733f03 |
| code/check_energy_certificate.py | 35d72bc0fa529751d5b8d79651df9b1f21acb5f4ac4069a9f92daa53668f20c6 |
| code/general_unit_certificates.py | 381a3ec7dc8e07c37fe12e87a4dc31fafbd67b775522d103828a56a94f8885e3 |
| inputs/energy_m7_square4.json | b6c618033e5e9c1ed57e10738b82fc0e711ec55a500ee4febeedf9ecc8121960 |
| inputs/energy_m7_cube3.json | ce4463e3b5334e8a78a0b7f93a7c8e46f8cbd63fdf4ec9d9f031d484e3a1b05e |
| inputs/energy_m9_square4.json | 6051c8dbefb5bd6fa745147002beea97fc8039e81688ff232e0e55b78bb2a294 |
| inputs/energy_m15_square4.json | 71ae0203ca786b2cbbc8e20123c1bab8150abddc544364b7d995fdcd3f7128c3 |
| inputs/energy_m15_cube3.json | 1dd38b1a4b0486d4d5bf4833eefff468519da8ce841dc7132941c3576b419a9c |
| inputs/energy_m16_square3.json | 80bdac5f83a454ee24059add450142f099be620e17829af7e1cc79bdbd7605ce |
| inputs/energy_m16_cube3.json | 019024ab4a81b3873cf3d036d964a02d38bdce5a5244dacb3e652773416c5100 |
| inputs/general_unit_subgroups.json | fb6fa2f7aabf37f2def191b3d1eeff1d7d4f559716a6adf024e6b92a0356eb7e |

## Limits of acceptance

The finite runs certify their finite objects and arithmetic controls; the
eventual theorem rests on the reviewed proof composition. This review makes
no claim of an effective cutoff, all-conductor runtime implementation,
uniformity in growing degree, proof-kernel checking, external mathematical
acceptance, or successful remote fleet CI. The separate higher-rank
log-parallelotope boundary algorithm remains unproved here; it is not used
to define the new energy pool. Other normalization models remain different
problems.
