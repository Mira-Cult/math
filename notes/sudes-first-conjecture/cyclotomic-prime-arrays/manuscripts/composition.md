# Prescribed cyclotomic prime squares and full signed cubes

Author/coordinator: `/root`. Manuscript-local theorem CPA4. This is the
conventional author proof checkpoint; independent reviews must be pinned to
the exact scientific revision in the recovery record. Mathematical status,
review, finite checking, and integration are distinct.

## 1. The theorem

Use precisely the balanced-log canonical pools, the norm/lexicographic order,
and the omitted ramified classes in [PROBLEM.md](../PROBLEM.md). In particular,
the fifth-root pool includes inert rational prime elements, and all three
pools include prime ideals of residue degree two when present.

**Theorem CPA4.** There exist constants N_5,N_8,N_12 with the following
properties, simultaneously for D=2 and D=3:

- for m=5 or m=12, every integer n>=N_m admits a bijection of the exact
  first n^D prescribed elements to [n]^D with every full signed-coordinate
  line sum a prime element;
- for m=8, the same holds for every odd n>=N_8;
- for m=8, every even n>=2 is impossible, for both dimensions.

For D=2 this is every row, column, and both long diagonals. For D=3 it is
every one of the 3n^2+6n+4 full signed lines, including every slice diagonal
and all four body diagonals. Sums always use coefficient +1, and may repeat.
Every prescribed input occurs exactly once, without unit rescaling. The
constructed targets can additionally be chosen unramified.

The thresholds are ineffective in the present proof. No numerical cutoff,
growing-conductor uniformity, efficient asymptotic algorithm, or assertion
about every small admissible order is included.

## 2. Dependency and geometry audit

The new canonical proofs are:

| Interface | Canonical source | Status used here |
|---|---|---|
| Full unit groups, class number one, exact normalization | [N1-N3](normalization_local.md) | Proved elementary arithmetic |
| Ramified exception exclusion and local difference/triple conditions | [N4](normalization_local.md) | Proved; even m=8 obstruction is necessary |
| Quartic pool scale and centroid | [P4](analytic.md) with N5 | Proved using fixed-field prime distribution |
| Prime boxes and exact-total tensors | [W4,T4,S4](analytic.md) | Proved from Kai's stated theorems; ineffective |
| Actual centered four-direction pairs | [E4,M4,U4](analytic.md) | Proved, with worst-case global deletion |
| Rank-four lattice/prefix/zonotope controller | [PC4,DG,PF,Z4](controller.md) | Proved under the preceding verified inputs |
| Linear-loss integral tensor rounding | [IT](controller.md) | Proved by two integer expander-flow stages |

The spatial support and incidence imports are the immutable ordinary and
quadratic sources specified in [REFERENCES.md](../REFERENCES.md). Their
identities are additive-group identities. Arithmetic rank changes the
payload of a physical transfer, while its required one/two/four actual
equal-gap pairs are still paid separately. The even-order geometric
extension is the one proved in the quadratic local manuscript, not an
unexplained removal of the original rational oddness condition.

Two tempting transfers fail and are repaired in these sources. The mean
in Minkowski coordinates tends to (cR,0), so small endpoint boxes centered
at that mean contain no canonical representatives. Instead, strict interior
endpoints near (cR,+cR) and (cR,-cR) have that midpoint; small perturbations
give four independent gaps. Also, the old tensor rounding remainder of
order n^2 exceeds available quartic cube capacity. IT replaces it by
32(n-1) for the same degree-64, expansion-8 graphs.

## 3. Exact prime targets

Fix a sufficiently large n in the indicated arithmetic order class. Put
M=n^D, let B be the last input norm, R=B^(1/4), T the exact pool total,
m=T/M, and mu=nm. The finite prefix includes its last incomplete norm tie.
N1-N2 and P4 prove the required finite enumeration, boundedness, and
R asymp n^(D/4)(log n)^(1/4). N5/E4 prove the interior endpoint hypothesis
for the actual mean, not merely for its limit. W4 proves the uniform
prime-box input for the polynomial-logarithmic controller moduli.

Take as target modulus the product Q_ram of all ramified prime ideals of
the chosen field. This is fixed. We require every target to be a unit
modulo Q_ram, so it cannot belong to a ramified prime class. At m=5,12
every residue-field size is at least three, and every total is a sum of
three units. At m=8 the only additional condition is the F2 parity
condition. Since n is odd and every input is 1 in F2, T=1 there.

Let Y=C_K nR, with a fixed sufficiently large enclosing constant. Apply
S4 with window exponent 1122 and smaller fixed-factor windows when needed.
For squares, its k=1 instance gives a common row/column list of n prime
targets, of exact sum T. Choose the two diagonal targets by W4 in the
same smaller window. Their residue is 1 at the m=8 norm-two prime.

For cubes, the k=2 instance gives a symmetric n-by-n prime tensor P of
exact labeled total T. Use this same tensor as the target family for
each of the three axis directions, with the corresponding coordinate
labels. Symmetry makes all plane marginals agree. For each of the six
slice-diagonal families, apply the k=1 instance with exact total equal
to the corresponding diagonal sum of P. The mean of that list differs
from mu by at most the earlier smaller target window. The final targets
remain in the asserted window after the fixed-factor allocations. Choose
the four body targets independently by W4.

The relevant F2 sums for these applications are T=1 for the n^2 axis
positions, and n=1 for each n-term face-family total. Thus the unit-pattern
construction in S4 works. For the other fields it works for every n.
These are exact equations in O, including all six diagonal-square
partition identities. No section total is required to be prime.

Every use of the linear-pattern theorem has exactly three forms
b1+kappa*x, b2+kappa*y, T'-b1-b2-kappa*(x+y) on eight integer variables.
Its finite-cokernel condition and every local factor are checked in T4.
The growing target list is handled by bounded-discrepancy corner choices
and one three-position completion, never by a growing system of forms.
Targets may repeat. W4/T4 work even when a center has zero second
embedding, and discard zero, units, and proper prime-ideal powers
explicitly. The target proof does not assume that sums themselves are
balanced canonical representatives.

Since log Y is comparable to log R, the final target window is
o(nR/(log R)^1120). All targets satisfy PC4's congruence condition:
modulo D=O this is vacuous, and at m=8 it is target=n=1 modulo 1-zeta_8.

## 4. One physical permutation and the tail quantifier

PC4 now realizes this entire compatible vector by a permutation of the
exact initial pool. Its explicit asymptotic regime is

    K0=floor(n/(log R)^1100), K1=floor(n/(log R)^1050),
    K2=floor(n/(log R)^1000), K3=floor(n/(log R)^950),
    eta=(log R)^(-200), P=ceil((log R)^100).

Four actual seed directions generate Gamma with determinant O((log R)^4).
The contained ideal q=d_Gamma D has norm at most (log R)^20. Centered
endpoint boxes supply at least a constant times M/(log R)^820 entries
in each needed class, while total global reservation is O(M/(log R)^1000).
Each request retains enough fresh endpoints under arbitrary earlier deletion.
Physical stages use actual one/two/four equal-gap pairs. Prefixes cover
all bounded lattice residuals; zonotope extreme-point rounding leaves
at most four fractional coefficients and its residual is absorbed by
the reserved prefix.

Whole-reservoir complementary randomization, followed by a permutation
of the entire unused pool, gives simultaneous line errors o(nR/(log R)^1120).
The proof explicitly recomputes the unused-pool mean and uses four-coordinate
union bounds over all required lines. Modular routing changes lines by
O(d_Gamma R), not an unjustified smaller gap estimate.

The controller consumes row/column and diagonal demands for squares.
For cubes it consumes plane totals, both slice axes, the final zero-margin
axis tensor, four bodies, and six face families in that order. IT pays the
quartic-specific tensor-rounding loss. The body/face incidence exclusions,
fresh reflection orbits, worst-case loads, and preservation of already fixed
line families are the complete contracts audited in PC4. Four scalar
coefficient flows only specify one vector demand; Z4 decodes that demand
into one subset of whole-element switches. This is not four permutations.

Thus all required sums equal their prime targets. Every limiting inequality
has the field and exponents fixed and holds on a complete integer tail.
Taking the maximum of the two dimension thresholds gives one N_m per field.
No favorable subsequence has been selected. The even m=8 impossibility is
N4's strict-sector and F2 argument. This proves CPA4. QED.

## 5. Scientific limits and the fixed-field roadmap

The arithmetic admissibility classification is now justified by construction
on the stated tails, with the universal even-order obstruction for m=8.
Small exceptions require separate finite certificates. The height-minimal
pool remains a different open model. Conductors 6 and 10 repeat the
Eisenstein and fifth-root fields, but any different normalization must still
be compared explicitly before transferring sums.

For a general fixed number field, the reusable conditional transfer requires
a complete normalized principal-prime pool, correct class-number density,
a bounded full-unit domain with a symmetric interior pair region about its
mean, the relevant finite-quotient unit-difference/triple conditions, fixed
complexity prime-box/target inputs, and geometric capacities with adequate
integer rounding. These hypotheses have been independently proved here
only in the three displayed quartic cases. Nonprincipal ideals do not enter
a prime-element pool, and no addition of ideals is substituted for addition
of elements. General conductors and growing degree are not consequences
of the present theorem without those separate audits.
