# Independent review of the fixed-conductor composition and finite pipeline

Reviewer: `/root/normalization`, a distinct internal reviewing agent.
Scientific revision: `d9bd9ac92851a9996c14dd2fdf49f1879bcae97b`.
Scientific tree: `85c7e494de3ea0bd3db7d508530541b2f15cbade`.
Review date: 2026-11-03.

This is an internal mathematical and implementation review. It is not an
external referee report, a formal GitHub approval, kernel verification, a
remote CI result, or an integration decision. The source files and fixtures
below were extracted from the exact commit with `git show`; their bytes were
also checked against the files read during the pre-freeze audit. They were
identical. The finite verification command was run from that extracted copy,
without importing code from the mutable working tree.

## Scope and authorship exclusions

The reviewed scientific sources are `general_analytic.md`,
`general_controller.md`, and `general_composition.md`. The implementation
scope is the root-authored `energy_cyclotomic.py` and
`search_energy_arrays.py`, the controller-agent-authored independent
`check_energy_certificate.py`, and the seven energy-model array fixtures
listed below.

I authored `general_normalization_local.md`,
`general_unit_certificates.py`, and its retained unit-subgroup input.
**This record does not independently review those files.** GN1--GN4 are
explicit dependencies here and require the separate nonauthor normalization
review. My earlier authored quartic normalization and checker are also outside
this record. I participated in discussions of the minimum-energy cell and
the symmetric endpoint construction, including the earlier antipodal
observation. Consequently I do not claim an independent authorship-based
review or independent discovery of those shared ideas in general analytic
Sections 2 and 5. I checked their stated interfaces, quantitative uses, and
composition with the other analytic and physical arguments.

I did not author the new prime-box/ternary proof, the rank-dependent physical
controller, the CYC composition, either finite producer/search program, or
the independent energy checker. The finite examples are evidence about their
own exact certificates; they are not evidence for the eventual theorem.

## Exact source bindings

Paths in the tables are relative to `problems/cyclotomic-prime-arrays/`.

| Source | SHA-256 of exact reviewed bytes |
|---|---|
| `manuscripts/general_analytic.md` | `31da5bf826935c6c08fd3f98c2cc1246a4422ef226ef378354e0c09c232b74d9` |
| `manuscripts/general_controller.md` | `233027e3650aee504735a197ddb02d24246d0823ee4551eb80baef68a53ab1bd` |
| `manuscripts/general_composition.md` | `53cbd81439c3584b4bb18f390747a6f837f99f646af9aa725e9264ef2eaa2acd` |
| `code/energy_cyclotomic.py` | `66737ed888e7040c13ad820de441e8fae40d1ad8e3f8456b54af9fa9b259604d` |
| `code/search_energy_arrays.py` | `94a78875c236ff12afcf88dac7513ff5c8b823f8e8ef8f96cc05d72c23733f03` |
| `code/check_energy_certificate.py` | `35d72bc0fa529751d5b8d79651df9b1f21acb5f4ac4069a9f92daa53668f20c6` |

| Finite input | SHA-256 of exact reviewed bytes |
|---|---|
| `inputs/energy_m7_cube3.json` | `ce4463e3b5334e8a78a0b7f93a7c8e46f8cbd63fdf4ec9d9f031d484e3a1b05e` |
| `inputs/energy_m7_square4.json` | `b6c618033e5e9c1ed57e10738b82fc0e711ec55a500ee4febeedf9ecc8121960` |
| `inputs/energy_m9_square4.json` | `6051c8dbefb5bd6fa745147002beea97fc8039e81688ff232e0e55b78bb2a294` |
| `inputs/energy_m15_cube3.json` | `1dd38b1a4b0486d4d5bf4833eefff468519da8ce841dc7132941c3576b419a9c` |
| `inputs/energy_m15_square4.json` | `71ae0203ca786b2cbbc8e20123c1bab8150abddc544364b7d995fdcd3f7128c3` |
| `inputs/energy_m16_cube3.json` | `019024ab4a81b3873cf3d036d964a02d38bdce5a5244dacb3e652773416c5100` |
| `inputs/energy_m16_square3.json` | `80bdac5f83a454ee24059add450142f099be620e17829af7e1cc79bdbd7605ce` |

## Analytic source and hypothesis audit

I reopened the exact primary versions of Kai's
[Mitsui refinement](https://arxiv.org/html/2209.11816v3), Theorem 3.1.1
and Appendices A.5--A.6, and
[linear-pattern paper](https://arxiv.org/html/2306.16983v5), Theorems 6.1
and 12.1 and Remarks 12.2--12.4. The latter theorem permits the fixed
integral basis used here, has a convex-domain error measured by its enclosing
radius, permits coefficients bounded by a fixed logarithmic power, and
requires the stated pairwise finite-cokernel property. The application uses
target ideal O, three forms, and exactly 2r integer variables. The theorem's
normalized affine coefficient size includes its constant term divided by
the enclosing radius; the displayed choices satisfy that condition too.

The following are checks of the new applications, rather than assertions
that either primary source proves the array theorem.

1. **GW keeps the thin-region invoice.** A coefficient box of width
   H=Y/(log Y)^A contains a fixed relative subbox avoiding every embedding
   zero. Its r-dimensional volume remains comparable to H^r, even when
   several coordinates of its center vanish. The Siegel estimate with
   epsilon=1/(2 max(B,1)) makes the exceptional factor small uniformly for
   modulus norm at most (log Y)^B. Connectedness of the complex archimedean
   group makes a real character constant there. The main term dominates
   Y^r exp(-c sqrt(log Y)); no power-scale thin-box estimate is assumed.

2. **The principal-prime density constant is retained.** In the stated log
   coordinates the radial Jacobian is s rho^(r-1). The full log-cell volume
   in the first s-1 coordinates is Reg(K)/2^(s-1), and the angular measure
   is (2 pi)^s/w. Integrating rho from zero to one gives domain volume
   pi^s Reg(K)/w. Its product with Kai's prime-element constant is 1/h_K.
   Thus M(B) is asymptotic to Li(B)/h_K, and B is asymptotic to h_K M log M.
   A norm tie has at most r prime ideals; a cut tie and the finitely many
   omitted ramified classes do not change these limits or the centroid.
   Higher residue degrees remain in every actual total and prefix.

3. **The shared geometry is used with its actual strength.** The first
   moment has the radial factor r/(r+1), first-sector sinc factor, and full
   log-cell average of exp(x1). The other angular means vanish. The proof
   does not place the mean inside the representative support. GE instead
   supplies an open reflected intersection about that mean. Translating
   to the true finite-pool mean uses its convergence and a fixed interior
   margin, not an unproved error smaller than a shrinking box width.

4. **GL does not require principal adaptive moduli.** The additive group
   O/q has size d=N(q), so dO is contained in q. At prime divisors of q,
   lifts preserve the three prescribed nonzero residues; at additional
   prime divisors of dO, the three-unit counts are positive because all
   norm-two primes were already included in q. CRT then lifts the exact
   total. No ideal is added to another in place of adding its generators.

5. **GT verifies the stronger linear-pattern hypothesis.** Each restriction
   of one linear part to another's kernel has image exactly dO. With
   N0 comparable to Y/d, the normalized affine size is O_K(d) and the
   convex preimage volume is comparable to H^(2r)/d^(2r). Taking the
   logarithmic error exponent larger than 2rA and B makes the error small
   relative to that volume. The number of forms stays three, independently
   of how many targets are later chosen.

6. **Every relevant local factor is accounted for.** Away from dO the
   normalized factors are 1-(Q-1)^(-2) when the required total is zero
   modulo the prime ideal, and 1+(Q-1)^(-3) otherwise. At a divisor of
   dO the prescribed residues are units. All norm-two factors are among
   the latter. The product over Q>2 has a positive uniform lower bound.
   O-linear forms permit the factorization into prime-ideal local factors,
   including at ramified rational primes.

7. **Proper prime powers are removed in arbitrary class number.** In an
   enclosing coefficient box of radius O(Y), the number of elements whose
   ideal is a proper prime-ideal power is O_K(Y^(r/2) polylog Y).
   Associate multiplicity for each principal ideal is at most a fixed
   power of log Y. Fixing one bad form value leaves only O_K(Y^r) free
   lattice choices, so their weighted contribution has a power saving
   against the 2r-dimensional main term. This includes principal powers
   of nonprincipal prime ideals. Zero and units have zero Mangoldt weight.

8. **GS handles all coordinates with one prime vector.** Each orbit step
   chooses one prime in the corner opposite the current simultaneous
   discrepancy; bounded orbit weights preserve the discrepancy cap.
   Three constant-coordinate positions have weight one and provide the
   exact final completion. The residue equation is soluble precisely with
   the stated norm-two restriction. This gives uniform lists and tensors
   without a growing-complexity pattern theorem.

9. **GM and GU supply actual disjoint pairs.** The ideal coset count follows
   from dO contained in q and uses L>=d, valid because endpoint widths are
   a positive power of R divided by fixed logarithmic powers. Cross-box
   pigeonholing gives a genuine repeated difference; the disjoint boxes
   make each such family a matching. The full deletion invoice is smaller
   than each endpoint class supply. Modular increments have size O(R),
   which is charged separately from their midpoint error O(eta R).

These uses introduce no class-number-one assumption. They preserve the
ineffectivity of the Siegel input and make no claim uniform in the conductor.

## Physical controller and parameter audit

The spatial imports are the exact ordinary, square, and quadratic revisions
pinned in G2. Their relevant contracts were read in the earlier review
`composition-review.md`, at quartic source
`6f8524253c32db096e38715fd69e880e0fa85fdd`. This review checks their use with
general fixed-rank payloads; it does not replace those imports with an
analogy about a higher-dimensional planar lattice. The imported IT tensor
lemma is the improved linear-remainder version at that same quartic source.

1. DG's pair count, strip exclusion, and conditioning depend on fixed r
   through constants and powers of the density parameter. At seed scale
   H_s comparable to log R, the actual gap matrix G has entries O(ell),
   determinant d_Gamma=O(ell^r), and adjugate inverse norm
   O(ell^(r-1)/d_Gamma). The exact inclusion
   d_Gamma O contained in Gamma is an additive lattice statement. The
   adaptive ideal d_Gamma d2 is consequently contained in Gamma even
   when d2 is nonprincipal; its norm is O(ell^(r^2)).

2. The dyadic prefix leaves an O(H_j) residual at each scale. All new
   gaps belong to d_Gamma O, and the final residual remains in Gamma.
   Its seed-coordinate size is O(ell^r), including the determinant factor.
   O(ell^(r+1)) stages suffice. The chosen P=ceil(ell^(r+10)) envelope
   and global seed matching pay for every independently reserved prefix
   and the actual two/four pairs in rectangle/cuboid stages.

3. The macro support-function estimate gives real containment of a fixed
   multiple of the required box. At an extreme feasible point there are
   at most r fractional coefficients. Rounding them leaves an O_K(R)
   lattice residual which the separately reserved prefix realizes exactly.
   Reference and complementary reference subsets both retain the required
   signed capacity; their native discrepancy is only O(ell). Thus the
   result is exact integer attainability by whole stages.

4. Modular routing acts in d2/(d_Gamma d2), which is a product of r cyclic
   groups of order d_Gamma in any fixed integral basis of d2. Unit-difference
   residues are precisely those allowed by the norm-two factors. The
   original errors satisfy that condition by H4 and the target congruence.
   The routing uses actual macro-size gaps and charges O(d_Gamma R) per
   line; other input elements that are nonunits at adaptive primes remain
   in the prescribed pool and filler.

5. I recalculated the complete exponent regime:

   g=r+10, b=r^2+2, c_box=5g,
   a2=6r^2+50r+102, a1=a2+g, a0=a2+2g,
   a3=a2-g, and h=6r^2+53r+132.

   The total reservation O(M/ell^a2) has 100 logarithmic powers of slack
   against each endpoint-class supply M/ell^(r*c_box+b). One fixed-gap
   matching loses only one more power. Seed demand has ratio
   O(ell^(r+11)/n) to its matching supply. All prefix, residue, and main
   per-line loads are o(n); no rank-dependent physical multiplicity is
   omitted from the constants.

6. Whole-reservoir complementary randomization puts every macro cell at
   its pair midpoint in expectation. Native fluctuations are O(ell),
   transverse fluctuations O(R), and preserved lines have no fluctuation.
   The union bound is over all r coordinates and all required lines, with
   no assumed independence between coordinates or lines. Summing one
   axis partition recomputes the unused-pool mean from the exact T before
   sampling the filler. The midpoint-bias ratio to H is O(ell^(-g)); all
   other concentration/prefix ratios are logarithmic powers divided by
   a positive power of n.

7. Ordinary seed-coordinate flows cost O(ell^r W+ell). IT gives tensor
   cost O(ell^(r+2) W)+O(n ell). The separations between levels have
   margins g-r=10 and g-(r+2)=8. Most decisively,

       (n ell)/(K2 R) = O_K(ell^(a2+1)/R) -> 0

   since R is comparable to n^(D/r)(log n)^(1/r) at every fixed r.
   This remains valid for arbitrarily large fixed degree and does not
   require R>n. It would not justify a growing-rank statement.

8. The final square passes preserve the fixed row/column constraints
   while enforcing both diagonals. The cube passes enforce plane totals,
   two slice axes, the zero-margin vertical tensor, four bodies, and all
   six face families. Fresh body reflection orbits limit face drift to
   O(R); the face passes preserve all axes, bodies, and other face families.
   Every vector demand is decoded once as a subset of whole-element flips.
   No coordinatewise independently assembled arrays appear.

## Composition audit

CYC keeps the original c=5,8,12 logarithmic pools unchanged and uses the
new exact energy model elsewhere. Its conductor reduction is stated before
the theorem. It includes every principal unramified prime ideal, all residue
degrees, and the deterministic final norm tie. There is no restriction on
the class number and no later deletion of an unfavorable input class.

The prime targets are chosen in the required o(H) window by fixing exponent
h+2, using smaller constant factors where two windows are added. A fixed
ramified modulus imposes unit target residues and hence produces unramified
targets. This is a sufficient construction condition; it does not wrongly
classify every divisible element as composite.

For squares, the common row/column target list has exact total T. For cubes,
one symmetric target tensor supplies all three axis families with matching
plane margins. Each of the six slice-diagonal families receives its own
exact total, equal to the corresponding diagonal sum of that tensor. The
four body targets add no extra total identity. The norm-two residue
conditions hold in every completion at odd orders; elsewhere there is no
norm-two prime and the three-unit equation covers every total.

The use of GN3 to prove even-order impossibility at powers of two explicitly
depends on its angular exclusion of all exceptional associates. I did not
independently review that authored dependency here. The composition does not
replace it with an invalid large-height argument. The rational pool that
retains 2 is separately obstructed, and omitting 2 is explicitly a different
repaired model. None of these order classes is defined by already having an
arrangement.

All rate arguments hold for a complete admissible tail at each fixed
conductor; taking the maximum of the square and cube thresholds is valid.
The finite sample driver is not claimed to implement the very large
asymptotic construction or the all-class-number enumeration algorithm.

## Implementation and independent-checker audit

The producer and checker import no algebra system. I checked their exact
ring arithmetic, prime-ideal test, energy enumeration, sector logic,
completeness certificate, and required-line handling.

- Norms are determinants of the integral multiplication map, with exact
  fraction-free elimination. A prime certificate combines norm p^f with
  an irreducible degree-f factor equal to gcd(Phi_c,alpha mod p). The
  quotient field has the same index as (alpha), so this certifies a prime
  ideal; rational-prime norm is not used as a necessary condition.
- The trace-energy matrices use Ramanujan sums. Rational LDL recursions
  enumerate every integer point of the claimed ellipsoid. The producer
  uses exact integer square-root limits; the checker uses an enclosing
  integer radius followed by an exact rational inequality. Comparing all
  points with no larger energy includes every better or tied associate
  once any representative of that ideal appears.
- The producer's sector test compares neighboring torsion rotations and
  settles algebraic zero before refining rational trigonometric intervals.
  The checker instead tests the two boundary rays in Q(zeta_(2w)), with
  exact zero detection and independently implemented rational sine bounds.
  Both implement the lower-included, upper-excluded sector. Floating point
  does not decide any membership or accepted prime certificate.
- Distinct ideal keys and independently computed cyclotomic splitting
  counts certify that every prime ideal through the cutoff is present.
  Small-prime generator certificates and Minkowski's theorem establish
  h=1 in each finite sample field. The field named `bound_floor` is the
  floor of a proved conservative rational upper bound for the Minkowski
  constant, using pi>3 and an upward-rounded square root; it need not be
  the exact floor of the real constant. Its greater coverage is valid.
- The general ring arithmetic does not imply that the finite driver handles
  arbitrary class number. At the reviewed revision that driver explicitly
  restricts its pool method to c=7,9,15,16. The theorem's GN1 enumeration
  for other fields is a separate mathematical algorithm. This separation
  avoids an unannounced endless attempt to certify h=1 in a field with
  nonprincipal ideals.
- The search swaps whole elements. Its floating-point acceptance rule only
  guides heuristic search; certificate acceptance is exact. An optional
  producer cache is not trusted by the independent checker. Exhausting a
  search budget is explicitly not an obstruction. I did not rerun the
  heuristic searches, whose final outputs are independently replayed below.
- The checker reconstructs line sets independently from subsets of varying
  coordinates and signs. It verifies the exact initial prefix, complete
  cutoff ties, associate uniqueness via ideal keys, multiset bijection,
  every line sum and norm, and the exact residue characteristic, degree,
  and irreducible factor. Omitting a slice/body diagonal cannot pass by
  merely reducing the declared line list.

## Observed finite command and results

From the extracted exact-source `problems/cyclotomic-prime-arrays/` directory,
I ran:

```sh
python -B code/check_energy_certificate.py --negative-controls \
  inputs/energy_m7_cube3.json inputs/energy_m7_square4.json \
  inputs/energy_m9_square4.json \
  inputs/energy_m15_cube3.json inputs/energy_m15_square4.json \
  inputs/energy_m16_cube3.json inputs/energy_m16_square3.json
```

Observed exit status: **0**. All seven certificates verified; all 101
fixture mutations were rejected, and all 50 arithmetic controls passed.

| Field | Array | Prefix size | Norm cutoff | Complete ideals through cutoff | Checked lines | Line residue degrees observed |
|---|---:|---:|---:|---:|---:|---|
| c=7 | cube, n=3 | 27 | 127 | 32 | 49 | 1,2,3,6 |
| c=7 | square, n=4 | 16 | 71 | 20 | 10 | 1 |
| c=9 | square, n=4 | 16 | 73 | 19 | 10 | 1 |
| c=15 | cube, n=3 | 27 | 151 | 30 | 49 | 1,2 |
| c=15 | square, n=4 | 16 | 61 | 18 | 10 | 1 |
| c=16 | cube, n=3 | 27 | 113 | 30 | 49 | 1,2 |
| c=16 | square, n=3 | 9 | 49 | 12 | 8 | 1,2 |

The independent scans visited 1681, 2215, 4231, and 3729 ellipsoid points
in c=7,9,15,16 respectively at the stated energy bounds. The mutations
include coherent replacement by a nonminimal unit associate, an omitted
prime class or final norm tie, a deficient energy bound, incorrect
polynomial/discriminant/Minkowski data, repeated entries, a wrong prefix
order, missing required lines, and incorrect prime-ideal data. Arithmetic
controls include exact and near sector boundaries, zero/units, higher-degree
inert prime elements, nonprime prime-power norms, and a squared ramified
prime. Their success is a finite implementation result only.

## Verdict and limits

**No blocking mathematical or finite-certificate defect found in the reviewed
sources at the exact scientific revision above**, under the explicit
GN1--GN4 normalization/local-arithmetic dependency, the pinned ordinary and
quadratic spatial imports, and the stated primary analytic theorems. The
general composition pays the arbitrary fixed-rank losses and retains the
principal-prime class-number factor. No additional unproved analytic or
physical premise was found within this review scope. No scientific source
change was requested after the freeze.

This verdict does not independently certify my authored normalization or
unit utility, establish an effective cutoff, give conductor-uniform bounds,
verify an efficient implementation of the eventual construction, classify
all small orders, or establish remote CI/integration. The finite inputs here
all have separately certified class number one; the arbitrary-class-number
assertion rests on the reviewed composition and its stated dependencies,
not on those examples. Shared geometric contributions and the precise
authorship exclusions above remain part of the review record.
