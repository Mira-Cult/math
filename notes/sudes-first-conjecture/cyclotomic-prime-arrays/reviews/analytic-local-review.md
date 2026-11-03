# Independent analytic, normalization, and composition review

Reviewer: `/root/controller` (internal nonauthor review of the files below).
Reviewed scientific commit: `6f8524253c32db096e38715fd69e880e0fa85fdd`.
Review date: 2026-11-02.

## Exact source binding and authorship boundary

The reviewed commit exists in the local object database. I read the three
manuscripts in full, obtained their frozen bytes with `git show`, and checked
that their working-tree copies were byte-identical to the frozen source.

| Repository-relative file | SHA-256 of exact file bytes |
|---|---|
| `problems/cyclotomic-prime-arrays/manuscripts/analytic.md` | `5dbe0b8a5f485870274da96b3f80f9d5469174ece1bdb9b5fc384903813724b8` |
| `problems/cyclotomic-prime-arrays/manuscripts/normalization_local.md` | `e7c4a406da14483b34f451b4fd67e5d589d79a95816a2451781505377437927b` |
| `problems/cyclotomic-prime-arrays/manuscripts/composition.md` | `9b224ea217b03a1b6e7ead46b47edcf4b62a1fcad0ffc1baa4a94a70c01ee636` |

I authored `controller.md` and `tensor_rounding_check.py`; both are **excluded**
from this independent review. I consumed the other authors' normalization and
analytic interfaces when writing the controller, but did not author their
canonical manuscripts. The composition review checks the coordinator's use
of those interfaces and of PC4 as a separately proved input. It is not an
independent review of my own PC4 proof or of all its inherited spatial
support theorems. Those require the other reviewers' recorded scopes.

This review does not cover finite array producer/checker implementations,
physical fixtures subsequently added, repository CI, formal verification,
novelty, or external mathematical acceptance.

## Primary sources actually inspected

I independently opened the following sources, rather than relying solely on
the manuscript's descriptions:

* Kai, [arXiv:2209.11816v3](https://arxiv.org/html/2209.11816v3), Theorem
  3.1.1, including its actual ideal and convex-region hypotheses, coefficient,
  exceptional term, and enclosing-volume error. I also inspected Theorems
  2.3.1--2.3.2 and Appendices A.4--A.6 for the enclosing coordinate bounds,
  Lebesgue-measure convention, and regulator convention.
* Kai, [arXiv:2306.16983v5](https://arxiv.org/html/2306.16983v5), Theorem
  6.1, Theorem 12.1, and Remarks 12.2--12.4. In particular, Theorem 12.1
  allows the stated polynomial-logarithmic coefficient bounds and provides
  an arbitrarily prescribed logarithmic error exponent for fixed numbers
  of forms and integer variables. Its finite-cokernel condition is stronger
  than an informal pairwise-independence slogan.
* Milne, [Algebraic Number Theory, v3.08](https://www.jmilne.org/math/CourseNotes/ANT.pdf),
  Theorem 4.3 (Minkowski ideal-class bound, printed p.70) and Theorem 5.1
  (unit rank, printed p.85), together with the relevant embedding conventions.
* The field records [4.0.125.1](https://www.lmfdb.org/NumberField/4.0.125.1),
  [4.0.256.1](https://www.lmfdb.org/NumberField/4.0.256.1), and
  [4.0.144.1](https://www.lmfdb.org/NumberField/4.0.144.1), as cross-checks of
  discriminants, signatures, class numbers, and the defining-polynomial
  convention. The fifth-root record's printed primitive-tenth-root polynomial
  is correctly distinguished from the manuscript's fifth-root power basis.

The full-unit and unit-index conclusions below were checked from the supplied
exact argument; the database was not substituted for that proof.

## Normalization and local arithmetic findings

No blocking mathematical issue was found in N1--N5 at the frozen revision.

1. The quartic Minkowski bounds are below 2 for discriminants 125 and 144,
   and below 3 for discriminant 256; the latter field's unique norm-two prime
   is principal. Thus the three class-number-one assertions follow. The
   displayed real quadratic units are fundamental by the stated minimality
   argument. For K5 and K8, the odd torsion exponent in `v/conjugate(v)`
   would give odd valuation at the ramified prime for a real-subfield
   element, contradicting the ramification index two. For K12, `1+zeta`
   is a unit with conjugation quotient `zeta`, and its square is a torsion
   multiple of the real fundamental unit. This establishes the necessary
   index two rather than assuming convenient real units suffice.
2. The free-unit change in the log ratio is exactly `2L`. The two half-open
   conventions therefore select exactly one representative, and the sector
   test can be made with real algebraic comparisons. The finite coefficient
   box follows from all embeddings being bounded, including the explicit
   K12 inverse-coordinate formulas. The prime-ideal gcd criterion handles
   norm `p^f`, including `f=2,4`; it does not equate primality with rational-
   prime norm. The minimal-height model remains separately defined, with its
   unproved geometry honestly left open.
3. The K8 even-order obstruction survives infinite units. All associates of
   the ramified generator that lie in the closed first sector lie on its
   boundary. A boundary integral prime would have odd ramified valuation,
   so cannot be one of the retained unramified primes. Ordinary sums of
   retained inputs remain strictly inside the sector. Thus an even line,
   divisible by the norm-two prime, is neither zero, a unit, nor an associate
   of that prime. This proof uses angle and valuation, not a false height
   bound on associates. The manuscript correctly avoids transferring this
   exclusion to the twelfth-root units.
4. The four-dimensional volume element, volume, and first moment give the
   displayed centroid `(c,0)`. The second coordinate vanishes by its full
   circle of phases, not by a claim that each finite prefix is symmetric.
   The uniform rational bounds put `c` strictly between 3/4 and 5/6.
   The antipodal points `(c,c)` and `(c,-c)` are strict interior points with
   that midpoint; their four perturbed gaps have nonzero determinant.
   Hence the missing central support point is repaired without replacing
   the pool or applying units to entries. The prime-measure convergence
   needed to transfer this statement to the actual mean is supplied by P4.

A pre-freeze wording issue was identified and corrected: the two normalization
maps need not commute for K12, although multiplication of units does. The
frozen N2 explicitly performs balancing first and torsion selection second.
No unresolved issue remains from that correction.

## Analytic findings

No blocking mathematical issue was found in W4, P4, T4, S4, E4, M4, or U4.

* W4 retains the exceptional term until the fixed-field Siegel lower bound
  makes it uniformly harmless for the polynomial-logarithmic moduli. The
  archimedean component of a real character is trivial on `(C*)^2`.
  A fixed-fraction subbox avoids both embedding-zero planes and has norm
  at least a constant times `H^4`; this justifies the logarithmic norm
  accounting even when the original center has a zero embedding. Its
  four-dimensional main volume dominates the enclosing `Y^4` error. The
  resulting threshold is correctly stated to be ineffective.
* P4 counts one representative per prime ideal, omits only the frozen finite
  ramified set, and retains higher residue degrees. At most four prime
  ideals occur in a norm tie. Fixed-box approximation and bounded first
  moments justify the limiting centroid and the radius exponent one quarter.
  The regulator `2L` and the volume `2*pi^2*L/w` give the expected main
  density constant.
* T4 uses precisely three forms on eight integer coordinates. Each form
  restricted to the kernel of another has image `kappa O`, hence finite
  cokernel. A balanced generator of the modulus controls all singular
  values and all coefficient sizes. The eight-dimensional main volume and
  error ratio have the displayed powers. I checked the two finite-field
  counts, the positive lower bound on their product, and why all norm-two
  prime ideals must be included in the modulus. The proper prime-ideal-power
  contribution has size `Y^6 polylog(Y)`, negligible against the
  `Y^8/polylog(Y)` domain volume. Higher-residue-degree primes are not
  erroneously removed by that step.
* S4 keeps four discrepancies bounded while choosing one whole prime element
  per symmetry orbit. The three weight-one reserve positions ensure the
  final completion is a fixed-complexity application; the number of array
  targets does not become the number of forms in Kai's theorem.
* E4/M4/U4 use actual canonical prime entries in endpoint boxes strictly
  below the cutoff. Difference pigeonholing produces a matching, with
  determinant and ideal-volume factors in the correct places. The total
  earlier deletion is charged against every new endpoint box. Arbitrary
  modular gaps have size `O(R)`, and this larger cost is acknowledged.

## Composition findings and conclusion

Assuming PC4 and its imported spatial contracts as the separately reviewed
physical input, the coordinator's composition has no blocking gap found in
this review. The fixed target modulus `Q_ram` need not equal the controller's
growing ideal `q`: the final targets only need PC4's congruence modulo
`D`. The common symmetric axis tensor has the required plane marginals;
the six exact list completions give all six diagonal-square identities.
The eighth-root residue conditions hold for odd `n`, and the other two
fields have no norm-two residue condition. Exponent 1122 leaves strict
window slack relative to PC4's exponent 1120 after the fixed-scale changes.
The exact pool total is used throughout, and all target values can be
required to avoid the ramified classes.

**Review result:** no blocking defect found within the disclosed nonauthor
scope at the exact revision above. This records a conventional internal
mathematical review. It is not a formal GitHub approval, an independent
review of my own controller or test code, a kernel check, a successful CI
run, or a claim of publication-level external acceptance.
