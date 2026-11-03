# Independent review of the general analytic, local, and composition sources

Reviewer: `/root/controller`.
Review date: 2026-11-03.
Reviewed scientific commit: `d9bd9ac92851a9996c14dd2fdf49f1879bcae97b`.
Definition checkpoint: `a7f841cf1dba596477ffc360e20fef273a14d729`.

## Scope, exact binding, and authorship exclusions

I read all three general manuscripts below and the complete producer, search,
and independent-unit utility sources. The reviewed commit is available in the
local object database. For each source I obtained its exact bytes with
`git show d9bd9ac92851a9996c14dd2fdf49f1879bcae97b:path`, compared them with
the working-tree file, and calculated the following SHA-256 digests.

All paths in this table are relative to `problems/cyclotomic-prime-arrays/`.

| Source | SHA-256 of frozen bytes |
|---|---|
| `PROBLEM.md` | `ad95075405f91ed77e5145f11e7c256bb2c46ada429309585fd91ea0710ee3c0` |
| `manuscripts/general_analytic.md` | `31da5bf826935c6c08fd3f98c2cc1246a4422ef226ef378354e0c09c232b74d9` |
| `manuscripts/general_normalization_local.md` | `7d21da0fe1d2fcd50ba708c4b555c3e5a12f01c349661e5626fb1a928538e160` |
| `manuscripts/general_composition.md` | `53cbd81439c3584b4bb18f390747a6f837f99f646af9aa725e9264ef2eaa2acd` |
| `code/energy_cyclotomic.py` | `66737ed888e7040c13ad820de441e8fae40d1ad8e3f8456b54af9fa9b259604d` |
| `code/search_energy_arrays.py` | `94a78875c236ff12afcf88dac7513ff5c8b823f8e8ef8f96cc05d72c23733f03` |
| `code/general_unit_certificates.py` | `381a3ec7dc8e07c37fe12e87a4dc31fafbd67b775522d103828a56a94f8885e3` |
| `inputs/general_unit_subgroups.json` | `fb6fa2f7aabf37f2def191b3d1eeff1d7d4f559716a6adf024e6b92a0356eb7e` |
| `inputs/energy_m7_square4.json` | `b6c618033e5e9c1ed57e10738b82fc0e711ec55a500ee4febeedf9ecc8121960` |
| `inputs/energy_m7_cube3.json` | `ce4463e3b5334e8a78a0b7f93a7c8e46f8cbd63fdf4ec9d9f031d484e3a1b05e` |
| `inputs/energy_m9_square4.json` | `6051c8dbefb5bd6fa745147002beea97fc8039e81688ff232e0e55b78bb2a294` |
| `inputs/energy_m15_square4.json` | `71ae0203ca786b2cbbc8e20123c1bab8150abddc544364b7d995fdcd3f7128c3` |
| `inputs/energy_m15_cube3.json` | `1dd38b1a4b0486d4d5bf4833eefff468519da8ce841dc7132941c3576b419a9c` |
| `inputs/energy_m16_square3.json` | `80bdac5f83a454ee24059add450142f099be620e17829af7e1cc79bdbd7605ce` |
| `inputs/energy_m16_cube3.json` | `019024ab4a81b3873cf3d036d964a02d38bdce5a5244dacb3e652773416c5100` |

I authored `manuscripts/general_controller.md` and
`code/check_energy_certificate.py`. Both are **excluded from independent
acceptance by this review**, as are my earlier quartic controller and tensor
checker. The composition review treats GC(r) and its imported spatial support
theorems as separately reviewed dependencies. It checks the other authors'
verification of its hypotheses, target compatibility, and theorem scope; it
does not independently approve my own physical proof.

I wrote the energy checker before reading the producer implementation. Its
use in the computational observations below is disclosed author verification
of that checker and independent checking of the other author's certificates.
Another reviewer must assess the checker source itself. This record is an
internal conventional mathematical/source review, not external refereeing,
formal GitHub approval, kernel verification, a novelty judgment, or a CI result.

## Primary sources actually inspected

I opened the cited versions and inspected their actual statements.

* Kai, [arXiv:2209.11816v3](https://arxiv.org/html/2209.11816v3),
  Theorem 3.1.1 and Appendices A.5--A.6: arbitrary fixed field and ideal,
  prime elements, convex enclosing regions, the class-number/regulator
  coefficient, exceptional term, enclosing-volume error, and measure
  conventions. No class-number-one restriction is present.
* Kai, [arXiv:2306.16983v5](https://arxiv.org/html/2306.16983v5),
  Theorem 6.1, Theorem 12.1, and Remarks 12.2--12.4: ineffective Siegel
  separation, normalized affine coefficient bounds, the exact finite-cokernel
  condition, the logarithmic error saving, permitted fixed integral bases,
  and prime-ideal factorization of local factors for O-linear systems.
* Milne, [Algebraic Number Theory, version 3.08](https://www.jmilne.org/math/CourseNotes/ANT.pdf),
  Theorem 4.3, Theorems 5.1 and 5.9, Theorem 6.4, Remark 6.6, and the
  cyclotomic class-number and unit discussions on printed pp.101--102.
  These supply the Minkowski bound, full unit lattice, cyclotomic integral
  basis/ramification/torsion facts, and the K23 norm-descent comparison.
  Milne states the prime-power CM unit-index result but gives its proof
  there only for odd prime powers; I separately checked GN3b's proof for
  powers of two instead of assuming that omitted case was proved there.
* The [official PARI general-number-field documentation](https://pari.math.u-bordeaux.fr/dochtml/html-stable/General_number_fields.html),
  `bnfinit` and `bnfcertify`: full certification and the restricted flag-one
  certificate have the different consequences stated in GN1. No PARI output
  or GRH-dependent computation is used in the present proof.

A pre-freeze locator correction was identified and made by the normalization
author: Milne's cyclotomic material is Chapter 6, not Chapter 7. The K23
locator used in this review is the unambiguous **printed page 101** (PDF
zero-based page index 102). This correction does not change the argument.

## Normalization and local arithmetic

No blocking mathematical defect was found in GN1--GN4 at the frozen source.

1. **Full associate comparison.** The positive rational trace Gram form gives
   a finite coefficient box containing every element of energy at most that
   of a supplied generator. Exact quotient integrality and norm one identify
   all its unit associates in the box. A global energy minimum is therefore
   found without a claimed full free-unit basis. Torsion-sector and coefficient
   ties give one representative, and their decisions are algebraic, including
   equality. This avoids the unresolved higher-rank logarithmic face tests.
2. **Effective bounds and missing unit cosets.** Dovetailing candidate unit
   tuples with certified precision finds a nonzero log determinant because
   the full unit lattice has the required rank. It never has to decide that
   a zero determinant is zero. The independent subgroup gives the bound
   `E(can(alpha)) <= s U |N(alpha)|^(2/r)`. Applying the same argument to
   an arbitrary unit shows that subgroup generators together with every
   unit of energy at most `sU` generate the full group. Unknown finite index
   changes neither the normalization nor its complete search bound.
3. **Regular geometry.** I checked the enclosure `sum t_j <= C=sU` and
   `C^(-(s-1)) <= t_j <= C`, and the resulting finite bound on every unit
   which can beat or tie an energy value in that enclosure. Thus finitely
   many nontrivial algebraic hyperplane equations suffice in the positive
   `t` variables. Strict AM--GM at `(1,...,1)` and positive interpolation
   followed by product-one rescaling prove interior density. Their null
   boundary and unrestricted remaining phases are sufficient for the
   analytic volume approximation. Neither convexity in logarithms nor a
   centroid inside the support is assumed.
4. **Primes and arbitrary class number.** Norm `p^f`, an irreducible degree-f
   polynomial gcd, and equality of quotient indices correctly characterize
   a prime principal ideal in the cyclotomic power basis, including ramified
   primes and higher residue degrees. A nonprincipal ideal gives no element;
   a generator of a proper prime-ideal power fails the test. The finite
   norm box therefore enumerates the intended element pool even when the
   class number is greater than one. Only the explicitly frozen ramified
   classes are omitted.
5. **Norm-two and exceptional associates.** In characteristic two a primitive
   odd-order root retains its order, so a norm-two prime occurs exactly in
   reduced power-of-two conductors. At such a conductor, an odd torsion
   exponent in `v/conjugate(v)` would make `v/(1+zeta)` real with odd
   ramified valuation, impossible for an element of the real subfield.
   This proves the full unit-index assertion needed for the obstruction.
   All ramified-prime associates in the closed first sector lie on its
   boundary; a boundary integral prime must be the omitted ramified class.
   Nonempty sums of retained inputs are strictly interior. Consequently an
   even line divisible by that prime is not zero, a unit, or any of its
   infinitely many prime associates. The argument does not use a false
   coordinate-size bound on such associates.
6. **Rational and nonprincipal controls.** The unique entry 2 forces the
   stated rational obstruction in either parity; removing it is a separately
   named model. In K23 the exact Gauss sum gives the quadratic subfield.
   The norm form excludes a norm-two element, while `(2-omega)=p^3`.
   Order 11 of 2 modulo 23 and relative norm descent show that its two
   extended primes remain nonprincipal of order three. The element 2 has
   no proper principal ideal divisor, so is irreducible, but its ideal is
   composite. This establishes the claimed distinction without computing
   or assuming the full class number of K23.

## Analytic and geometric interfaces

No blocking mathematical defect was found in G, GW, GP, GE, GL, GT, GS,
GI, GM, or GU at the frozen source.

* In GW a fixed-volume subbox avoids all embedding-zero planes. Its norm
  logarithm is comparable to `log Y` even if its center approaches a zero
  embedding. The real exceptional character has trivial archimedean part
  on the connected group `(C*)^s`; its fixed-field Siegel bound controls
  polynomial-logarithmic moduli. The full r-dimensional main volume
  dominates the enclosing-radius error, with the asserted ineffectivity.
* GP's Jacobian is `s rho^(r-1)` in the declared log coordinates. The full
  log-cell covolume is `regulator/2^(s-1)`, giving
  `volume(D_F,1)=pi^s regulator/w` and principal-prime density `1/h`.
  The displayed radial/angular first moment is correct. Finite-box
  approximation, a vanishing small-radius contribution, finite omissions,
  and at most r prime ideals per norm tie justify every exact prefix and
  its actual mean, including an incomplete last tie.
* GE correctly uses `c < max exp(x_1)`, which holds even if `c` is greater
  than one. An interior log point above c and radial contraction provide
  endpoints of opposite remaining phases with exact midpoint `(c,0,...)`.
  Their reflected interior intersection is open in all r real dimensions,
  giving r independent conditioned chords. For s=1 the sector-disk
  neighborhood provides the two directions. Convergence of the actual
  mean suffices because the interior margin is fixed; no polylogarithmic
  rate of mean convergence is smuggled in.
* GL uses the actual inclusion `N(q) O subset q`. Its CRT lifts preserve
  all prescribed unit residues, while added prime divisors admit a
  three-unit complement because every norm-two prime is already included.
  This removes the former need for a balanced principal generator of q.
* GT has exactly three forms on `2r` integer variables. Each restriction
  to another form's kernel has image `dO`, hence finite cokernel. The
  normalized coefficients are `O(d)` and the preimage volume has the
  claimed `H_Y^(2r)/d^(2r)` scale. I recomputed both local factors and their
  positive product bound. The chosen logarithmic error exponent covers
  both the coefficient bound and the relative volume loss. The removal
  of proper prime-ideal powers includes principal powers of nonprincipal
  ideals: bounded generators per ideal are only polylogarithmically many,
  and the resulting `Y^(3r/2)` loss is smaller than the `Y^(2r)` main scale.
* GS uses bounded symmetry-orbit weights and three weight-one positions.
  Adaptive corner choices concern whole prime elements, and every use of
  the analytic theorem still has three forms. Its exact residue total and
  norm-two criterion suffice for the square and cube target systems.
* GI's coset count follows from `dO subset q` and the exact quotient size
  `d^(r-1)`. GM/GU then pigeonhole actual endpoint pairs; a fixed difference
  pairs each endpoint with at most one partner. Their density, deletion,
  conditioning, and midpoint invoices have the stated rank powers. The
  modular gaps are correctly charged at size `O(R)`, not `O(eta R)`.

## Composition review

The coordinator's CYC statement preserves the original three quartic pools
and explicitly defines the distinct energy pool at new reduced conductors.
The all-energy alternative is identified as a separate statement. The
normalization and analytic results above verify GC(r)'s H1--H3, including
the `1/h` density constant; GN3 verifies H4 without further deletions.

I checked the exact-total target construction modulo the fixed ideal of all
ramified primes. A common square list has total T. The symmetric cube tensor
has total T and equal plane marginals; each of the six face-family lists has
the required exact axis-diagonal total. Body targets are independent. At a
norm-two prime, odd n makes every required labeled total and line target
consistent with the actual pool. There is no growing family of simultaneous
analytic forms. All targets are genuine prime elements, with ramified output
associates avoided by an explicit permissible target congruence.

The composition correctly applies the separately reviewed physical theorem
to these targets, with fixed conductor and fixed r. Its statement of the
critical ratio `ell^(a2+1)/R -> 0` and its interpretation as a fixed-rank
limit agree with GC(r)'s declared interface. This comparison is a dependency
check, not independent approval of the reviewer's own controller proof.
The rational obstruction/repair and the qualifications on effectiveness,
finite exceptional orders, different normalizations, and growing conductor
are retained. No additional unresolved hypothesis was found in the scoped
normalization/analytic/composition argument.

## Producer, unit utility, and observed finite evidence

The producer's cyclotomic arithmetic, fraction-free multiplication determinant,
Ramanujan trace form, rational LDL enumeration, exact sector-zero tests,
rational trigonometric enclosures, rational primality acceptance, and Rabin
irreducibility test were read in full. Its sector test compares real parts
against the two adjacent torsion rotations and assigns a tie to the lower
ray. This is equivalent to the declared half-open first sector. Its exact
ellipsoid recursion uses the integer bound on `|q*x-p|`, so it omits no
energy-bounded integral point. Grouping by the actual prime-ideal factor and
comparing every candidate gives energy/lex minima. The Minkowski and cutoff
ideal counts certify completeness, including norm ties and ramification in
the class-number certificate. The sample pool driver explicitly restricts
itself to four certified class-number-one fields; it does not implement or
claim the full arbitrary-class-number algorithm proved in GN1.

The search only swaps whole elements. Affected-line updates use the symmetric
difference of the two cells' incidence sets. Floating point chooses search
acceptance probabilities only; it decides no accepted arithmetic claim.
The output records the exact successful seed/restart/step. Exhaustion is
explicitly not an obstruction. Cached candidate pools are inputs to the
producer, so final independent certificate checking remains essential.

The unit utility's Machin, sine-Taylor, and atanh-log intervals all have
outward rational rounding and explicit tails. Its interval elimination only
divides by certified nonzero pivot intervals. The emitted unit lists certify
independent finite-index subgroups, never an unproved index-one assertion.
The K23 utility's cyclic polynomial arithmetic, reduced-form enumeration,
norm-form checks, and order computation agree with GN4.

Actual observations at the frozen revision:

* Re-running `general_unit_certificates.py` reproduced
  `inputs/general_unit_subgroups.json` exactly as a JSON value for conductors
  7, 9, 11, 15, 16, 20, 24, and 23. Every emitted determinant interval
  excludes zero. An additional exact multiplication-determinant calculation
  verified norm one for all 30 displayed geometric-sum units.
* Separate exact power-basis arithmetic verified `omega^2-omega+6=0` in
  K23, `N_K23(2-omega)=8589934592=8^11`, and rejection of rational 2 by
  the prime-element criterion. The nonprincipality and irreducibility
  conclusions also require the mathematical norm-descent proof reviewed
  above; they do not follow merely from a failed primality test.
* The seven energy array certificates passed the independent implementation
  I authored, with 50 common arithmetic controls and 101 rejected corrupted
  certificates. Those controls include coherent same-ideal replacement by
  a sector-normalized associate of larger energy, omitted class/cutoff ties,
  missing Minkowski generators, hidden unit rescaling, repeated entries,
  missing lines, and incorrect residue/norm/factor data. This is evidence
  about the producer's outputs; independent review of my checker is excluded.
* Re-running the m15 order-four square search without a pool cache, with
  seed 20261103, energy bound 16, 100000 steps and 15 restarts, reproduced
  the complete retained certificate exactly, succeeding at restart 0,
  step 39. The order-three cube examples have all 49 required lines; the
  m7 cube includes line-prime residue degrees 2, 3, and 6 as well as 1.

Reproduction commands, from the repository root:

```sh
python -B problems/cyclotomic-prime-arrays/code/general_unit_certificates.py --output /tmp/cyclotomic-review-units-20261103.json
python -B problems/cyclotomic-prime-arrays/code/search_energy_arrays.py --m 15 --n 4 --D 2 --seed 20261103 --steps 100000 --restarts 15 --energy-bound 16 --output /tmp/cyclotomic-review-m15-square4.json
python -B problems/cyclotomic-prime-arrays/code/check_energy_certificate.py --negative-controls problems/cyclotomic-prime-arrays/inputs/energy_*.json
```

These finite observations do not establish the eventual theorem. No blocking
mathematical or implementation defect was found in the disclosed nonauthor
scope at the exact scientific commit. Independent review of the controller
and checker, repository checks, and coordinator integration are separate
obligations with their own records.
