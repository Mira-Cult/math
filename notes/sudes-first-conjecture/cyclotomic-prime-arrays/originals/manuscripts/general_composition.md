# Prescribed prime squares and full cubes in every fixed cyclotomic field

Author: `/root`. Manuscript-local theorem CYC. This is the conventional
composition of the new normalization, analytic, and physical proofs. Its
independent reviews are recorded at an exact scientific revision separately
from mathematical status, finite certificates, repository integrity, and
integration. The four frozen quartic manuscripts are unchanged.

## 1. Exact theorem and model

Use the [extended canonical family](../PROBLEM.md#extended-canonical-family).
Reduce a conductor m congruent to 2 modulo 4 to c=m/2, and otherwise put c=m.
The original balanced-log pools are retained at c=5,8,12. At every other
nontrivial reduced conductor c>=3 the representative minimizes full Minkowski
energy over its entire unit-associate class, then uses the first torsion
sector and the exact coefficient-lexicographic tie. Order the representatives
of all principal unramified prime ideals by norm and coefficient tuple.
No other prime class is omitted. Inert and higher-residue-degree principal
prime ideals are included, and every incomplete last norm tie uses that order.

**Theorem CYC (every fixed nontrivial cyclotomic field).** For every fixed
integer m>=3 there is an integer N_m with the following property. If its
reduced conductor c is a power of two, let n be any odd integer at least N_m;
otherwise let n be any integer at least N_m. For each D in {2,3}, the exact
first n^D members of the frozen extended pool admit a bijective placement in
[n]^D for which every full signed-coordinate line sum is a prime element.

For squares all 2n+2 rows, columns, and main diagonals are included. For cubes
all 3n^2+6n+4 axes, slice diagonals, and body diagonals are included. Every
sum has coefficient +1 on its n entries. Target sums may repeat and need
not be canonical representatives. The construction can choose all targets
unramified. Every prescribed input occurs once without later unit rescaling.

When c is a power of two, every even n>=2 is impossible for either dimension.
The admissible order classes in the theorem are therefore independently
specified arithmetic classes; existence is proved on their entire tails.
There is no class-number-one assumption and no fixed upper bound on r=phi(c).

The assertion is **fixed-conductor**, with arbitrary conductor: all constants
and N_m may depend on m. The proof does not provide a uniform threshold for
growing conductors, an effective numerical cutoff, or an efficient algorithm
for finding the asymptotic arrangement. Its threshold inherits an ineffective
Siegel estimate. It does not identify the energy pool with another unit
normalization or classify all smaller orders.

There is also an energy-model version of CYC at every c>=3, including the
quartic fields: the new proof below applies there as well. The extended family
uses the already frozen quartic pools instead, so the prior statements and
finite examples are not silently replaced by that different model.

## 2. Complete dependency map

| Obligation | Canonical result | Status used here |
|---|---|---|
| Exact whole-unit canonical choice, effective complete prefixes | [GN1](general_normalization_local.md) | Proved by finite trace-energy ellipsoids and exact unit tests |
| Bounded regular full-unit domain | [GN2](general_normalization_local.md) | Proved, with a finite algebraic inequality description |
| Norm-two classification and all exceptional associates | [GN3](general_normalization_local.md) | Proved, including the full CM unit-index assertion at powers of two |
| Principal-prime density and exact-prefix mean | [GP](general_analytic.md) | Proved from the fixed-field prime theorem, factor 1/h_K retained |
| Full-rank centered endpoint geometry | [GE](general_analytic.md) | Proved for the energy domain in every fixed degree |
| Prime boxes, exact totals, local factors, actual pairs | [GW,GL,GT,GS,GI,GM,GU](general_analytic.md) | Proved from the precisely stated Kai inputs and elementary lattice counting |
| One permutation attaining every compatible vector | [GC(r)](general_controller.md) | Proved with an explicit rank-dependent parameter regime |
| Previously frozen quartic pools | [CPA4](composition.md) | Retained at its original scientific source |

The external analytic inputs are W. Kai, *Notes on Mitsui's Prime Number
Theorem with Siegel zeros*, arXiv:2209.11816v3, Theorem3.1.1, and *Linear
patterns of prime elements in number fields*, arXiv:2306.16983v5, Theorems6.1
and12.1 with Remarks12.2--12.4. Their applications, hypotheses, multiplicities,
enclosing-volume errors, and ineffectivity are audited in general_analytic.md.

The ordinary incidence/support imports are exactly those pinned in
[GC(r), G2](general_controller.md): ordinary scientific source
`a2445962ec6e06b2a893980fb7a183057eb9bcee`, square support source
`c2118dfad1aeb660d66308dc6a94d6c959f5010c`, and quadratic scientific source
`e6e581efb9b676a7d5bc88b91c01571b087ed5da`, including its even-order geometric
extension. The rank-independent integer tensor correction is IT at the
quartic scientific source `6f8524253c32db096e38715fd69e880e0fa85fdd`.
The geometric imports concern positions and additive-group identities;
prime supply and arithmetic-rank losses are supplied anew in GC(r).

## 3. Normalization and representative geometry for an arbitrary conductor

Fix a reduced c>=3 outside the already frozen quartic cases, let K=Q(zeta_c),
O=Z[zeta_c], r=2s=phi(c), and h=h_K. GN1's normalization compares an input
with every possible better associate in a finite exact ellipsoid for
Tr(alpha*conj(alpha)). It does not assume that convenient cyclotomic units
generate the full group. A deterministically found independent subgroup,
together with a finite energy-bounded unit set, supplies full-group coverage
and an explicit coefficient bound O_K(|N(alpha)|^(1/r)). Every bounded norm
prefix is consequently finite, effective, unique, and complete.

If a prime ideal is nonprincipal it contributes no element. If a principal
ideal is a proper power of a nonprincipal prime ideal, its generator may be
irreducible but is not prime and is excluded by the exact quotient-field
criterion. GN4 gives a concrete such distinction in K23. No addition of
ideals substitutes for addition of elements in the construction.

GN2 identifies the normalized log-shape cell F with the full energy-minimizer
cell of the unit log lattice. It is bounded, regular, and the closure of its
interior. Its nontrivial boundary equalities have measure zero; exact finite
algebraic comparisons settle them for canonical enumeration. Only the first
torsion-sector angle is restricted. The other s-1 phases remain independent
geometric coordinates in the interior.

For M initial entries, largest norm B, R=B^(1/r), and exact average bar p,
GP proves

    M ~ B/(h log B),    B ~ h M log M,
    R ~ (h M log M)^(1/r),    bar p/R -> u=(c0,0,...,0).

Here c0>0 is the explicit radial/angular/log-cell average in GP. The symbol
c0 is a real centroid coordinate, not the conductor c. The zero mean
coordinates are not ignored. GE proves that the reflected support
Omega intersect (2u-Omega) has nonempty full-dimensional interior: if A1 is
the maximum first amplitude of F, then c0<A1. Choose an interior log point
x with exp(x1)>c0 and set rho=c0 exp(-x1)<1. Giving all other embeddings
opposite phases yields two strict interior points with midpoint u and fixed
norm slack. An open neighborhood of their gap contains r independent gaps.
The case s=1 is the same open-neighborhood argument inside the sector disk.

Translate the endpoint centers to the actual finite-pool mean. Its convergence
to u and the fixed domain margin suffice; no unproved rate at shrinking-box
width is required. GW supplies actual canonical prime entries in every needed
unit residue class in these endpoint boxes, uniformly under adaptive choices.
The finite omitted ramified representatives have fixed norm and therefore
cannot enter the positive-norm scaled endpoint boxes once R is large.

This verifies GC(r)'s H1--H3. GN3 shows that every norm-two prime in a
nontrivial cyclotomic field is ramified and omitted; every input is therefore
1 modulo such a prime. This verifies H4 without discarding any extra entry.

## 4. Compatible exact-total prime targets

Let n tend through the arithmetic class in CYC, put M=n^D, let

    T=sum of the exact M entries,    bar p=T/M,    mu=n bar p,
    ell=log R,    h_r=6r^2+53r+132.

Let Q_ram be the product of all ramified prime ideals of K. This fixed ideal
need not be principal. Require every target to be a unit modulo Q_ram.
All exceptional ramified output classes are thereby avoided, without any
claim that a large divisible sum would be composite.

Take Y=C_K nR for a sufficiently large fixed enclosing constant, and use
GS with exponent h_r+2 and suitably smaller fixed-factor windows. Since
log Y is comparable to log R, all resulting targets lie within

    o(H),    H=nR/ell^(h_r),

of the required mean. GT uses only three affine-O-linear forms on 2r integer
variables. For a nonprincipal modulus q it passes to dO subset q with d=Nq,
lifts compatible unit residues, and checks the exact finite-cokernel image
dO and every local factor. Proper prime-ideal powers, including principal
powers of nonprincipal primes, are removed quantitatively. Thus its outputs
are prime elements, with zero and units excluded separately.

For squares, GS at tensor order one gives a common n-term row/column prime
list of exact total T. The two diagonal targets come independently from GW
in the same window. Repeated target values are permitted.

For cubes, GS at tensor order two gives a symmetric n-by-n prime tensor P
of exact labeled total T. Use that same tensor, with the corresponding
coordinate labels, for the three axis families. Symmetry makes their plane
marginals agree. For each of the six slice-diagonal families, use GS at
order one with exact total equal to the appropriate diagonal sum of P.
Its average differs from mu by at most the earlier smaller target window.
Fixed-factor window allocations keep every final target inside o(H).
Choose the four body targets independently by GW. All six diagonal-square
partition identities are exact equations in O; section totals need not be
prime.

It remains to check the only local restriction. If c is not a power of two,
there are no norm-two primes, and every residue at a ramified prime is a
sum of three units. If c is a power of two, n is odd and every input is 1
modulo its unique norm-two prime. Thus T=M=1 there. Both the square n-term
and cube n^2-term target list lengths are odd. Each face-family total is
the sum of n unit axis targets, also 1. The three-unit completion condition
holds in every application, and every final line target is congruent to
n=1 modulo that prime. These are precisely GC(r)'s required congruences.

The target system has a growing number of entries, but no analytic invocation
has a growing number of forms: coordinatewise corner discrepancy choices
leave only three weight-one positions for each exact completion. The number
of simultaneous analytic forms is always three.

## 5. Physical realization, quantitative margins, and complete tails

Apply GC(r) to the compatible prime targets just constructed. For clarity,
its explicit profile is

    g=r+10, b=r^2+2, c_box=5g,
    a2=6r^2+50r+102, a1=a2+g, a0=a2+2g, a3=a2-g,
    Ki=floor(n/ell^ai), eta=ell^(-c_box), P=ceil(ell^(r+10)).

Actual seed differences generate an additive lattice Gamma with index
d_Gamma=O_K(ell^r). The contained ideal q=d_Gamma d2 has norm at most
ell^(r^2+2), where d2 is the product of all norm-two prime ideals. The
containment follows from the adjugate identity; Gamma is never assumed
to be an ideal. Independent-gap density, exact multiscale prefixes, and
centered zonotopes with at most r fractional coefficients give complete
integer attainability. Every stage uses its actual one/two/four disjoint
equal-gap pairs.

Each endpoint residue class has supply at least a fixed multiple of
M/ell^(r*c_box+b), while the global reservation is O_K(M/ell^a2).
The difference a2-(r*c_box+b)=100 pays for arbitrary prior deletion from
each local box. All per-line support loads are o(n). Whole-reservoir
complementary randomization and permutation of every unused entry use the
exact unused-pool mean and give simultaneous rank-r errors o(H)
across all required lines. The union bound includes all r coordinates.
Modular routing pays its actual O_K(d_Gamma R) changes.

The single possible polynomial obstruction in the generalized cube invoice
is the integer tensor remainder. The proved IT lemma replaces the old
quadratic remainder by O(n), which becomes O_K(n ell) after converting
back from seed coordinates. For every fixed r,

    (n ell)/(K2 R) = O_K(ell^(a2+1)/R) -> 0,
    R asymp_K n^(D/r)(log n)^(1/r).

Thus arbitrarily large fixed arithmetic rank is paid: its positive fixed
power of n eventually dominates every fixed logarithmic loss. This is the
specific estimate that would fail to follow if r were allowed to grow with n.

The square stages enforce axes and both diagonals. The cube stages enforce
plane totals, both slice axes, the remaining zero-margin axis tensor, all
four bodies, and all six face families, preserving the previously fixed
identities through the pinned support contracts. Coordinate flows only
specify one vector demand. The zonotope decoder realizes that demand by
one subset of whole-element flips. The result is one permutation of the
entire original pool, with every required line at its prime target.

Every estimate above has the field and its exponents fixed and holds for
every sufficiently large admissible integer, not a selected subsequence.
Take the maximum of the square and cube thresholds. This proves CYC for
the energy model at every c>=3. For the extended family at c=5,8,12 use
the unchanged CPA4 theorem at its frozen source; it gives exactly the same
order classes for those retained pools. GN3 supplies the universal even-order
impossibility at every power of two. The conductor reduction identifies equal
fields without changing their defined pools. This completes the proof. QED.

## 6. Rational case, finite evidence, and precise limitations

For m=1,2 the literal omit-ramified-only pool is the ordinary positive primes,
including 2. GN4 proves impossibility for every n>=2, even if only axis lines
were required. The explicitly named minimal rational repair omits that one
class at the outset and gives the initial odd primes. The existing rational
square and full-cube theorems then apply on the full odd-order tail. This
repair is separate from the nontrivial cyclotomic theorem and makes no
additional omission in those fields.

Concrete energy-model arrays and independent checkers test the new exact
normalization, higher residue degrees, complete prefixes and all required
lines. Certified independent-unit subgroups in degrees through22 supply
reproducible normalization constants; GN1 explains why their index need not
be one. The K23 control explicitly certifies a nonprincipal prime ideal and
an irreducible that is not prime. None of these finite checks is the proof
of the eventual theorem, and a failed finite search is not an obstruction.

No additional unresolved analytic, normalization, geometric, or physical
lemma is retained in CYC beyond the explicitly stated established analytic
theorems and pinned spatial imports. The different arbitrary log-parallelotope
boundary algorithm remains open here, as do equivalence with other pools,
effective thresholds, efficient construction, all finite exceptions, and
uniform growing-conductor statements. Formal verification and external
refereeing are separate from this conventional source and its internal review.
