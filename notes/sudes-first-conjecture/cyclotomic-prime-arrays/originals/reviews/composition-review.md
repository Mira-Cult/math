# Independent analytic, controller, and end-to-end composition review

Reviewer: `/root/normalization`, a distinct internal reviewing agent.
Scientific source reviewed: `6f8524253c32db096e38715fd69e880e0fa85fdd`.
The exact commit object and all three source files were read locally with
`git show`; the primary Kai theorem statements were also opened independently.
This is an internal mathematical review, not a formal GitHub approval,
external refereeing, kernel verification, or an integrity/CI result.

## Authorship boundary

I authored `manuscripts/normalization_local.md` and
`code/check_certificate.py`. **Neither is independently reviewed by this
record.** Their statements are explicit dependencies below and require the
separate nonauthor reviews recorded elsewhere. I also proposed the antipodal
endpoint observation to the other authors; consequently this record does not
claim independent discovery or an independent authorship-based review of that
shared geometric idea. I checked the analytic and physical uses of its stated
endpoint-interior contract, and independently checked all other claims in the
three reviewed files. I did not author the fixed-field prime-box/ternary proof,
DG/PF/Z4 controller, IT tensor lemma, or final composition.

The independent checker implementation and its finite computational outputs
are not evidence for any asymptotic assertion in this review. Later physical
fixtures are outside the reviewed revision and outside this record's scope.

## Exact content bindings

| Source path | SHA-256 of exact reviewed bytes |
|---|---|
| `problems/cyclotomic-prime-arrays/manuscripts/analytic.md` | `5dbe0b8a5f485870274da96b3f80f9d5469174ece1bdb9b5fc384903813724b8` |
| `problems/cyclotomic-prime-arrays/manuscripts/controller.md` | `30904f8f03c150e029662d33f9dfca7fef6babc223d3d972f45883b79e04a8c3` |
| `problems/cyclotomic-prime-arrays/manuscripts/composition.md` | `9b224ea217b03a1b6e7ead46b47edcf4b62a1fcad0ffc1baa4a94a70c01ee636` |

## Analytic checks

1. I inspected Kai, *Notes on Mitsui's Prime Number Theorem with Siegel
   zeros*, arXiv:2209.11816v3, Theorem 3.1.1, and *Linear patterns of prime
   elements in number fields*, arXiv:2306.16983v5, Theorem 12.1 and Remark
   12.2. The applied field is fixed of degree four, the target ideal is O,
   the original power basis is allowed with field-dependent constants,
   and the number of forms/variables is exactly three/eight. No result
   for a growing family of forms is imported.
2. W4 retains the enclosing-radius error. Its smaller convex subbox avoids
   both embedding-zero planes while keeping four-volume comparable to H^4.
   The exceptional character is real and therefore trivial on the connected
   complex archimedean group; the stated Siegel estimate makes its factor
   at most an exponentially small quantity on that subbox for polynomial-log
   modulus norm. The resulting error/main ratio tends to zero. The proof is
   correctly labeled ineffective.
3. P4 uses one representative per prime ideal, including degree-two/four
   ideals and incomplete final ties. Its leading scale is B/log B with
   R=B^(1/4). The measure constant times the displayed domain volume equals
   one. Its moment calculation uses both complex angular coordinates and
   does not infer a nonzero second-embedding mean.
4. In T4 the three affine forms have restrictions to one another's integer
   kernels with image kappa O, of finite cokernel. The convex preimage has
   volume comparable to H^8/N(q)^2 and enclosing radius comparable to
   Y/N(q)^(1/4). Polynomial-log coefficients and arbitrary fixed logarithmic
   error exponent satisfy Kai's actual hypothesis. A binary completion would
   fail that hypothesis, and is not used.
5. I recomputed both local factors: for residue field size Q>=3 they are
   1-1/(Q-1)^2 when T=0 and 1+1/(Q-1)^3 otherwise. The norm-two ideals are
   included in q. At primes dividing q, all fixed form residues are units.
   Their product has a uniform positive lower bound. Prime-ideal powers
   contribute O(Y^6 polylog Y), below the eight-dimensional main term;
   their associate multiplicities are O(log Y). Units and zero have zero
   Mangoldt weight. Degree-two/four prime ideals are not mistakenly removed.
6. S4 chooses one whole prime vector at each corner step and reserves three
   weight-one positions. Its discrepancy bound is coordinatewise simultaneous,
   and its exact remaining total is integral. The three-unit CRT conditions
   are compatible with all orders for m=5,12 and odd orders for m=8.
7. M4/U4 count primes in the actual interior canonical endpoint boxes, then
   pigeonhole over actual differences. Fixed-gap pairs are disjoint because
   the two boxes are disjoint. The worst-case total-deletion allowance is
   smaller than every endpoint count. No unit transformation of physical
   endpoints or fixed-gap prime conjecture enters the argument. Modular
   increments are correctly charged at O(R), even though their midpoints
   are close to the mean.

## Controller and tensor checks

1. DG's same-cube/residue partition provides the stated pair count. Its
   hyperplane-strip bound removes fewer than half the counted pairs after
   choosing rank-dependent constants. Successive gaps have independent
   Gram--Schmidt distances; the determinant and adjugate inverse estimates
   follow. Greedy matchings remain disjoint after all earlier selected
   endpoints are deleted. The seed determinant is O(ell^4), and the integer
   adjugate gives d_Gamma O contained in Gamma without claiming Gamma is
   an ideal.
2. PF's dyadic nearest-integer rounding leaves residual O(H_j), remains in
   Gamma, and has O(ell^4) coefficients per scale. The final seed-basis
   coefficients are integral and O(ell^4), including the determinant factor.
   The ell^100 envelope is ample. Every signed copy is implemented by doubled
   actual finite switches, and the seed matching globally covers the invoice.
3. Z4's support-function lower bound gives genuine real box containment.
   An extreme feasible point has at most four fractional coordinates, and
   rounding them leaves a bounded O(R) residual in Gamma. PF absorbs that
   residual exactly. The reference and complementary reference are both
   attainable and both retain the symmetric correction capacity. This
   establishes integral attainability, rather than only real span.
4. I checked IF directly by cut capacities and integral max-flow. For IT,
   rounding the real tensor solution leaves entry error at most Delta^2/2.
   The first family of integral flows has coefficient bound
   b=ceil(Delta^2/(2h)). Subtracting the column sum from the last column
   preserves its divergence because the residual has zero margins, and
   gives zero row sums with bound (n-1)b. A second integral flow gives the
   asserted additive ceil((n-1)b/h) cost. With Delta=64 and h=8 this is
   precisely 32(n-1). The term is essential at quartic cube radius and is
   fully paid in the composition.
5. I read the pinned quadratic vector-controller Section 5 and checked the
   transfer of its support identities and caps. These are identities of
   additive groups: one pair, two equal-gap pairs, and four equal-gap pairs
   remain the correct physical costs. The earlier rank-two arithmetic and
   planar scale are not imported. The separate-pass load caps and bounded
   transverse intersections are exactly the hypotheses used in concentration.
6. Modular routing reduces coefficients in a fixed integral basis of the
   allowed difference ideal, routes modulo d_Gamma, and leaves every residual
   in q contained in Gamma. Actual macro-size modular jumps cost O(d_Gamma R)
   per line. The successive zero-total/zero-margin requirements are the
   imported incidence identities; no division in the ring is assumed.
7. The entire global deletion bound is O(M/ell^1000), below endpoint counts
   of order M/ell^820 and matchings of order M/ell^821. All prefix and seed
   multiplicities, four arithmetic directions, and physical pair factors fit.
   K3+P+d_Gamma=o(n) validates the imported disjoint-placement conditions.
8. Complementary randomization is performed on whole reservoirs. A native
   line changes by O(ell), a nonnative transverse line by O(R), and preserved
   lines by zero. Four-coordinate union bounds therefore apply without
   claiming independence of coordinates or lines. The unused-pool mean is
   recomputed from the exact total before the filler permutation.

## End-to-end and rate checks

The target construction uses the exact total, symmetric axis tensors, and
all six slice-diagonal-family total identities. The ramified target modulus
is fixed and targets are required to be units there, which is a sufficient
construction condition rather than a false necessary classification for m=12.
The target window with exponent 1122 is o of the controller window with
exponent 1120. The distinct arithmetic and spatial dimensions are preserved.

The centering ratios close: eta K3 R/H=O(ell^-30); prefix and modular terms
are logarithmic powers divided by n; concentration terms are logarithmic
powers divided by sqrt(n). Every basis-conditioning loss is bounded by a
fixed logarithmic power and paid by the 50-power gaps between controller
levels. In the final tensor pass, the real part costs O(ell^6 K1 R), and
the integral correction costs O(ell n). Dividing the latter by K2 R gives
O(ell^1001/R), which tends to zero for both displayed quartic scales.

The square sequence preserves rows/columns while correcting both diagonals.
The cube sequence corrects plane totals, both slice axes, the remaining
zero-margin vertical tensor, four bodies, and all six face families. Body
supports use fresh reflection orbits so their entire spill on a fixed face
line is O(R), and face gadgets preserve axes, bodies, and the other five
face families. The even-order support extension in the pinned quadratic
argument is used only where stated. Thus the complete signed-line family,
not only axes or selected diagonals, is covered by the cited contracts.

The normalization dependency supplies the strict-sector proof that every
retained K8 input is interior and every ramified-prime associate lies on a
boundary. Its use in the composition correctly excludes the infinite-unit
exception before concluding even-order impossibility. I do not independently
review that proof here because I authored it. Zero and units are separately
excluded by the target-primality inputs.

## Verdict and limitations

**No blocking mathematical defect found in the three reviewed sources at the
exact revision above**, under the explicitly cited established scalar/quadratic
support and incidence imports and the separately reviewed normalization/local
arithmetic dependency. The conventional CPA4 proof is coherent across those
interfaces, and no extra unresolved analytic or controller premise was found.

This verdict does not certify the authored normalization or checker, later
physical fixtures, any numerical cutoff, an efficient algorithm, a general
conductor theorem, kernel verification, or remote CI. The proof's thresholds
remain ineffective and its small-order exceptions remain separate questions.
No source change was requested within this review scope. A normalization-map
wording issue reported before this review was already corrected in the frozen
revision; its stale staging copy is not the reviewed source.
