# Exact normalization and local arithmetic for every fixed cyclotomic field

Author: `/root/normalization`. This continuation uses manuscript-local labels
GN1--GN4. It does not edit or replace the frozen quartic results. The canonical
extended family, reduced-conductor convention, energy objective, sector and
lexicographic tie-break are defined in [PROBLEM.md](../PROBLEM.md), under
“Fixed-conductor continuation”. This file proves their arithmetic and geometric
properties. Distribution and physical realization are separate dependencies.

## 1. Why the general logarithmic prescription needs a repair

For a CM field of degree r=2s, a full independent unit basis gives a lattice
in the hyperplane H={x in R^s:sum x_j=0}. An abstract half-open logarithmic
parallelotope is a valid fundamental domain. Its faces, however, are defined
using the inverse of a matrix of logarithms of algebraic numbers. In unit
rank at least two, equality with such a face can involve determinants or
products of logarithms. Arbitrary-precision intervals decide strict inequality,
but do not decide equality merely by being refined. No general algebraic
boundary test, or proof that all prime generators avoid those faces, is supplied
by the rank-one quartic argument. This is a limitation of that proposed
algorithm, not a claim that the corresponding equality problem is undecidable.

The extended definition therefore uses minimum Minkowski energy for the new
fields. All its comparisons are exact integer or algebraic comparisons, and
its geometry is proved below. Different normalization models are not equated.
For reduced conductors 5,8,12 the already proved balanced-log pools are retained
without change; no high-rank logarithmic comparison is needed for them.

## GN1. Complete effective energy normalization, without a hidden unit index

Fix a reduced conductor c>=3, K=Q(zeta_c), O=Z[zeta_c], r=phi(c)=2s, and
one embedding sigma_j from each conjugate pair, with sigma_1(zeta_c)=exp(2pi i/c).
The fixed power basis has r entries. Let

    E(alpha)=Tr_K/Q(alpha*conj(alpha))/2=sum_j |sigma_j(alpha)|^2.

This is a positive integer for nonzero alpha in O: alpha*conj(alpha) is an
integer of the maximal real subfield, and E is its trace to Q. The roots of
unity have order w=c when c is even and w=2c when c is odd. For odd c a
positive first-phase generator is `-zeta_c^((c+1)/2)`; for even c it is zeta_c.

### Exact finite minimization

**Theorem GN1a.** The energy/sector/lexicographic rule in PROBLEM.md chooses
exactly one representative of every nonzero element associate class. It is
computable by a finite search which tests every potentially better associate,
without assuming that any list of convenient units generates the full group.

**Proof.** For an input alpha, put Q0=2E(alpha). In coefficient coordinates
let A be the positive definite rational trace Gram matrix

    A_ij=Tr_K/Q(zeta_c^(i-j)),  0<=i,j<r.

Its entries are integers, the Ramanujan sums
`sum_{d|gcd(c,i-j)} d*mu(c/d)`. For a coefficient vector b, `b^T A b=2E(beta)`.
Cauchy--Schwarz in this positive definite form gives

    b_i^2 <= (A^(-1))_ii * Q0.                              (GN1.1)

The inverse and every bound on the right are exact rationals. Consequently
all elements beta with E(beta)<=E(alpha) lie in an explicitly finite integral
box. Enumerate it and retain precisely those beta for which beta/alpha is an
integral unit. Exact inversion of alpha's multiplication matrix tests
integrality of the quotient; its exact field norm tests whether it is a unit.
An integral quotient of norm one is a unit in this totally imaginary field.
Equivalently, equality of the two principal ideal lattices is an exact test.

This finite set contains every energy-minimizing associate, including those
from any missing unit-index coset. Each torsion orbit has exactly one member
in the specified half-open first sector, since its first phases differ by
2pi/w. Sector membership is an exact sign test against algebraic boundary
rays; equality is settled by algebraic equality, not by a floating tolerance.
Among all sector-normalized energy minimizers choose the least coefficient
tuple in ascending lexicographic order. The set is finite and nonempty, so
this choice is unique. Any two starting associates yield exactly the same
set of minimizers and the same representative. QED.

The algorithm does not assume the first phase is unchanged by nonreal free
units. Every candidate energy minimizer is sector-normalized before the final
lexicographic comparison. This matters in fields with nontrivial CM unit index.

### A deterministic sufficient unit search

A finite-index subgroup, whose index need not be known, suffices to bound the
height of the representative uniformly in its norm. It is never substituted
for the full group in the minimization.

1. Enumerate integral coefficient tuples by increasing coefficient height and
   lexicographic order, retaining exact norm-one elements.
2. Enumerate tuples of s-1 such units. For each tuple and each increasing
   precision compute certified intervals for the logarithms of their positive
   algebraic embedding absolute values and the determinant of the first s-1
   rows of that log matrix. Dovetail tuple size and precision, so an unresolved
   zero determinant never blocks later candidates.
3. Stop at the first tuple whose determinant interval excludes zero. Dirichlet's
   unit theorem guarantees that one exists. A genuine nonzero real determinant
   is separated from zero by sufficiently fine certified intervals, so this
   deterministic dovetail terminates. Rank-zero fields use the empty tuple.
4. For each selected unit u_i find an integer A_i>=1 bounding all
   `|sigma_j(u_i)|` and all their reciprocals, by exact algebraic comparison.
   Set `U=product_i A_i`, with empty product one.

These steps use only certified strict inequalities, whose termination is
proved; they do not use a logarithmic face-equality test. Let Lambda_0 be the
log lattice generated by this independent tuple. It has full rank in H and
therefore finite index in the full unit log lattice, by Dirichlet's theorem.

**Theorem GN1b (uniform bound and full-group coverage).** The representative
of every nonzero alpha satisfies

    E(can(alpha)) <= s U |N(alpha)|^(2/r).                  (GN1.2)

Moreover the chosen subgroup generators together with every integral unit of
energy at most sU generate the entire unit group. The latter is a finite,
exactly enumerable set. No unproved unit-index assertion is used.

**Proof.** Write `rho=|N(alpha)|^(1/r)` and
`x_j=log(|sigma_j(alpha)|/rho)`, so x belongs to H. Subtract a suitable lattice
vector in Lambda_0 to put x in the centered subgroup parallelotope. Existence
of this choice is elementary real linear algebra; the normalization algorithm
does not need to decide its boundary. Every resulting coordinate has

    |x_j| <= (1/2) sum_i log A_i,

so the associate obtained in this way has energy at most sU*rho^2. The minimum
over all associates is no larger, proving (GN1.2).

Apply the same argument to an arbitrary unit v, for which rho=1. Some product
of v with powers of the selected units has energy at most sU. Thus every
unit belongs to the group generated by the selected units and the finite
energy-bounded unit set. This proves coverage of the full unit group,
including every possible CM unit-index coset. Finiteness and effective
enumeration follow from (GN1.1). QED.

Theorem GN1b provides a full-group certificate by finite generators if one is
desired. A minimal free basis or an exact index is not needed to define or
enumerate the energy pool. An implementation using PARI `bnfinit` instead
must run full `bnfcertify(bnf)` and obtain 1 before treating its class or unit
group as unconditional; `bnfcertify(bnf,1)` is insufficient for a full unit
claim. The present proof and checker do not rely on an uncertified PARI output.

### Effective complete prime prefixes for arbitrary class number

Choose an integer C_K such that

    C_K^2 >= 2sU * max_i (A^(-1))_ii.

Then every canonical element of norm at most B has coefficients bounded by
`C_K ceil(B^(1/r))`, by (GN1.1)--(GN1.2). This supplies a finite complete
coefficient search box. Apply exact norm, prime-element, ramification and
normalization tests; retain distinct representatives and sort as in PROBLEM.md.
Increasing B through the positive integers or powers of two gives every exact
initial prefix, with its last norm tie settled by the stated ordering.

The prime-element test is complete in every class number. If an integral
alpha has absolute norm p^f for a rational prime p, compute

    g=gcd(Phi_c mod p, alpha(X) mod p).

It is prime precisely when g is irreducible of degree f. In that case
`(alpha)` is contained in the prime ideal `(p,g(zeta_c))`, and both quotient
indices are p^f, so the ideals are equal. Conversely a prime principal ideal
has just such an irreducible residue polynomial. Zero and norm-one units fail
before this criterion. This is not a rational-prime-norm-only test.

A nonprincipal prime ideal has no generator and never enters this element
search. An irreducible whose principal ideal is composite is rejected. Thus
no principal-ideal decision oracle and no class-number-one hypothesis are
needed for enumeration. Infinitely many principal prime ideals exist by the
fixed-field prime theorem in the principal class, so the search eventually
finds any requested finite count. The class number h_K enters the asymptotic
law `M(B)~B/(h_K log B)`, proved in the analytic source, not the definition.

Only the prime classes over rational primes dividing the **reduced** conductor
are omitted. They are exactly the ramified rational primes in that field.
This reduction is essential: for example, 2 divides the displayed integer 6
but is unramified in Q(zeta_6)=Q(zeta_3), and its prime class is retained.
All principal residue-degree>1 and inert prime classes remain included.

## GN2. A bounded regular energy fundamental cell

Put `x_j=log(|z_j|/rho)` with `rho=(product_j |z_j|)^(1/s)`, and let
Lambda be the full unit log lattice in H. Apart from its tie boundaries,
energy minimization gives the log-shape cell

    F={x in H: sum_j exp(2x_j) <= sum_j exp(2x_j+2lambda_j)
                       for every lambda in Lambda}.        (GN2.1)

Torsion has zero log vector. Ties between distinct nonzero log vectors are
assigned using the exact sector/lex rule; their geometric measure is zero.

**Theorem GN2.** F is a bounded fundamental cell up to its boundary, has
nonempty interior, is the closure of its interior, and has boundary of
(s-1)-dimensional measure zero in H. In the variables `t_j=exp(2x_j)`,
it is given by finitely many linear inequalities with algebraic coefficients
on `t_j>0`, `product_j t_j=1`, together with an explicit bounded enclosure.
Consequently its radial cone with the first-sector condition has the regular
boundary and phase independence required by the analytic construction.

**Proof.** Set C=sU. The subgroup argument in GN1b applies to every real
x, not just to logs of algebraic elements. Hence every x in F satisfies

    sum_j t_j <= C,     C^(-(s-1)) <= t_j <= C.             (GN2.2)

In particular F is bounded. The energy is coercive on H: an unbounded vector
in H has an unbounded positive coordinate. Every lattice orbit therefore has
an energy minimum, so translates of F cover H. Distinct translates overlap
only on equal-energy loci, apart from the zero log vector.

Only finitely many units matter on the enclosure (GN2.2). If a unit u can
beat or tie the energy at some point of that enclosure, then

    sum_j t_j |sigma_j(u)|^2 <= sum_j t_j <= C,

so every `|sigma_j(u)|^2<=C^s`, and therefore `E(u)<=s C^s`. Enumerating this
finite energy-bounded unit set is exact by GN1a. For every such unit, the
energy comparison is the linear inequality

    sum_j t_j (|sigma_j(u)|^2-1) >= 0.                     (GN2.3)

The coefficients are positive-real algebraic numbers minus one. A unit for
which every coefficient vanishes is torsion, by Kronecker's theorem, and
imposes no condition. Every other equality is a nontrivial analytic
hypersurface of H. There are finitely many relevant equalities, so they
have measure zero. The boundary of the bounding enclosure is also an
analytic measure-zero set when s>1. The rank-zero case H={0} is interpreted
with its usual zero-dimensional measure and is immediate.

At t=(1,...,1), every nontorsion inequality (GN2.3) is strict: the positive
numbers `|sigma_j(u)|^2` have product one and are not all one, so strict
AM--GM gives their sum greater than s. F therefore has nonempty interior.

For any t in F and 0<epsilon<1, form
`t'= (1-epsilon)t + epsilon(1,...,1)` and then divide every coordinate by
`(product_j t'_j)^(1/s)`. Every nontorsion inequality becomes strict before
this common positive scaling and remains strict after it. Concavity of log
gives `product_j t'_j>=1`; the scaling therefore does not increase the
energy. When s>1, C>s and the mixture also lies strictly below the artificial
outer bound C. The resulting log points are interior points of F and converge
to the original x. Thus F is the closure of its interior. QED.

Within the interior, the minimizing log-unit orbit is unique. The phases of
sigma_2,...,sigma_s are unrestricted, and the first phase is exactly the
fixed torsion sector. Nonreal unit phases introduce no additional interior
constraint: their log exponent is chosen first by minimization, followed by
the torsion sector. Boundary lexicographic choices can depend on other phases,
but only on a measure-zero set and with exact algebraic decisions.

This regularity does not assert that F is convex, or that the prime mean lies
inside its support. The general analytic manuscript calculates the actual
centroid and proves the required reflected-support intersection. In particular,
it must pay for zero conjugate mean coordinates rather than deleting them.

## GN3. Norm-two primes and all infinite exceptional associates

**Theorem GN3a.** For a nontrivial cyclotomic field with reduced conductor
c>=3, a prime ideal of norm two exists if and only if c is a power of two.
In that case it is the unique prime `P=(1-zeta_c)`, and it is totally ramified.

**Proof.** Write c=2^a d with d odd. In a residue field of characteristic two,
roots of unity of odd order retain their order: the polynomial X^d-1 is
separable, so its distinct cyclotomic factors have disjoint roots. Thus the
image of a primitive d-th root has order d. If the residue field were F2,
its multiplicative group would have order one, forcing d=1. Conversely, for
c=2^a with a>=2, `Phi_c(X)=X^(2^(a-1))+1=(X+1)^(2^(a-1))` over F2.
There is a unique prime over two, with residue field F2, and
`N(1-zeta_c)=Phi_c(1)=2`; it is the displayed principal prime. The degree
of the field is its ramification index. QED.

The nonexistence of norm-two primes alone is not an array-existence theorem.
It identifies exactly the obstruction in the finite unit-difference/triple
interfaces used by the separate construction.

**Theorem GN3b (full CM unit index and strict sector).** For c=2^a, a>=2,
roots of unity and units of the maximal real subfield generate the entire
unit group. Every canonical unramified prime is strictly inside the first
sector, and no nonempty ordinary sum of such primes is an associate of P.
Every even order n>=2 is therefore impossible for the prescribed squares
and full signed cubes.

**Proof.** For any unit v, `v/conj(v)` is a root of unity by Kronecker's
argument. If its exponent in mu_c were odd, multiply v by a root of unity
to make this quotient zeta_c. Then

    v/(1+zeta_c) belongs to K^+,

because the numerator and denominator have the same conjugation quotient.
The element `1+zeta_c` has P-valuation one, since its norm is
`Phi_c(-1)=2`. Every element of K^+, even a fractional one, has even
P-valuation because K/K^+ has ramification index two at this prime.
This would give v odd valuation, contradicting that it is a unit. Thus
the exponent is even; a torsion adjustment makes v real. This proves the
full unit-index-one assertion, not just a convenient subgroup inclusion.

Every real unit has first phase 0 or pi, already included in the torsion
phase grid. The first argument of `1-zeta_c` is `pi/c-pi/2`, congruent
to pi/c modulo 2pi/c since c is divisible by four. Hence every P-associate
in the closed canonical first sector lies on one of its two boundary rays.

If a nonzero integral alpha lies on either boundary, divide it by a suitable
root multiple of `1-zeta_c` on that ray. The first embedding of the quotient
is real, so the quotient is fixed by conjugation and belongs to K^+.
Its P-valuation is even, and alpha consequently has odd P-valuation.
Integrality makes that valuation positive. A prime element on the boundary
must therefore generate P, a class omitted at the outset. Every retained
prime is strictly interior. The sector angle is less than pi, so a nonempty
ordinary sum remains strictly interior and has positive first real part.
It is nonzero and cannot be any P-associate, regardless of the size of its
unit multiplier.

Every retained input is 1 in O/P=F2. An even-length line sum is divisible
by P. This excludes units; the preceding sector argument excludes zero and
all prime associates of P. The sum is therefore not prime. A single axis
line already proves the asserted square/cube obstruction. QED.

This proof applies both to the retained eighth-root log model and to the
energy model at other powers of two. It does not require the chosen energy
representative itself to stay balanced after sums are taken.

For every finite ideal quotient O/q, a class Delta is a difference of two
units exactly when it vanishes at each residue field F2 dividing q. For
residue field size at least three, avoid the two forbidden classes 0 and
-Delta; for F2 the difference of two nonzero residues is necessarily zero.
Lift to prime-ideal powers and apply CRT. Likewise every residue is a sum
of three units when the residue field size is at least three, whereas a
three-unit sum in F2 must be one. These facts do not require class number
one. The construction must still verify exact totals and all incidence
identities for the actual pool.

At other ramified primes a divisible sum may be a prime associate with an
unbounded unit multiplier. This file does not classify those arbitrary sums
as composite. The eventual construction can instead require its prime
targets to be units at all ramified ideals, a sufficient condition which
avoids all exceptional output classes. Zero and units are separately excluded
by target primality; a large first embedding alone would not exclude units.

## GN4. Rational endpoints and a concrete nonprincipal-prime field

### The unavoidable rational repair

For m=1 or 2 the reduced field is Q, whose ring Z has no ramified rational
prime. The literal omit-ramified-only pool therefore retains 2 and consists
of the ordinary positive primes. For every n>=2 and D=2 or3 this exact pool
has no required array. If n is odd, the axis line containing 2 has even sum
greater than two. If n is even, some parallel axis line does not contain 2,
and its n odd entries also have even sum greater than two. There are at least
two parallel lines and only one entry 2, so the latter line exists. The
singleton is the valid one-entry array [2].

Omitting the single class 2 at the outset is the explicitly named minimal
rational repair. It gives exactly the original odd-prime pool, with the
existing eventual odd-order scalar theorem. This extra omission is not
silently made in the nontrivial cyclotomic fields.

### K23: an irreducible which is not prime

The arbitrary-class-number distinction is already essential for c=23. Let
K=Q(zeta_23) and F=Q(sqrt(-23)). The quadratic Gauss sum

    tau=sum_{a=1}^{22} (a/23) zeta_23^a

satisfies tau^2=-23. Thus `omega=(1+tau)/2` lies in O_K, generates F, and
satisfies `omega^2-omega+6=0`. The finite control evaluates this Gauss-sum
identity by exact cyclic polynomial multiplication and prints omega in the
power basis.

In O_F=Z[omega], the prime ideals `p=(2,omega)` and its conjugate have norm
two. The norm form is

    N_F/Q(a+b omega)=a^2+ab+6b^2=(a+b/2)^2+23b^2/4.

No element has norm two: b=0 would require an integer square equal to two,
and b nonzero gives norm at least 23/4. Therefore p is nonprincipal. The
element `2-omega` has norm eight, is divisible by p and not by its conjugate,
so `(2-omega)=p^3`; the ideal class of p has exact order three. Independently,
the reduced primitive positive binary quadratic forms of discriminant -23
are `(1,1,6)`, `(2,-1,3)`, and `(2,1,3)`, giving h_F=3.

Now `ord_23(2)=11`, so 2 has two prime ideals of residue degree eleven in K.
Since `[K:F]=11` and it already splits into the two primes p and conjugate p
in F, each extends to a prime; in particular

    P=p O_K=(2,omega)O_K,      N_K/Q(P)=2^11.

If P were principal, its relative ideal norm `p^11` would be principal.
But 11 is coprime to the class order three, a contradiction. Thus P and its
conjugate are nonprincipal prime ideals. They contribute **no** members of
the prescribed prime-element pool.

Furthermore the element 2 of O_K is irreducible but not prime. Its ideal is
the product of the two nonprincipal primes above 2, each with exponent one.
A nontrivial element factorization would give a nontrivial proper principal
ideal divisor, necessarily one of those two ideals, which is impossible.
Its ideal is nevertheless composite, so 2 is not a prime element. The
quotient-field test in GN1 rejects it. This concrete control shows why a
class-number-one implementation cannot merely rename “irreducible” as “prime”.

The argument proves that the class number of K23 is divisible by three and
is not one. It does not compute the full K23 class number or use a database
claim about its exact value. The elementary norm-descent argument is also
given in Milne's *Algebraic Number Theory*, version3.08, Chapter6, p.101
(PDF p.102).

## Concrete independent-unit certificates

The standard-library program [general_unit_certificates.py](../code/general_unit_certificates.py)
constructs exact geometric-sum units
`u_a=1+zeta_c+...+zeta_c^(a-1)=(1-zeta_c^a)/(1-zeta_c)`, with gcd(a,c)=1.
Each is integral and has norm one because numerator and denominator are
Galois conjugates. The program certifies their independence using rational
outward intervals: Machin's identity for pi, Taylor bounds for sine, and the
convergent atanh series with an explicit tail for log. Its determinant
interval must exclude zero. No floating value decides acceptance.

| c | r | geometric-sum lengths a | certified integer bounds A_i | U |
|---|---:|---|---|---:|
|7|6|2,3|3,3|9|
|9|6|2,4|3,3|9|
|11|10|2,3,4,5|4,4,4,4|256|
|15|8|2,4,7|5,4,5|100|
|16|8|3,5,7|5,5,6|150|
|20|8|3,7,9|6,6,7|252|
|24|8|5,7,11|5,7,8|280|
|23|22|2,3,4,5,6,7,8,9,10,11|8,7,6,7,6,8,7,7,8,8|354041856|

These are **certified independent subgroups**, not an assertion that their
index is one. GN1b explains exactly why they suffice for the complete energy
normalization bound. The same program replays the K23 Gauss sum, reduced-form
list, prime order, and norm-descent arithmetic. Its finite computations support
these explicit certificates; they do not prove an eventual array theorem.

Reproduce with

```sh
python -B problems/cyclotomic-prime-arrays/code/general_unit_certificates.py \
  --output /tmp/cyclotomic-independent-unit-certificates.json
```

The utility's default candidate lists certify the eight displayed conductors.
The general deterministic dovetail described in GN1 is a proved algorithm,
not a claim that this small utility implements every conductor or the full
unit-group computation. If its bounded candidate list gives no nonzero
certificate it reports that limitation instead of claiming dependence.

## Sources and status

- J. S. Milne, *Algebraic Number Theory*, version3.08, 19 July2020,
  https://www.jmilne.org/math/CourseNotes/ANT.pdf: Chapter5, Theorems5.1 and5.9
  for the full unit log lattice; Chapter6 for cyclotomic integers, roots,
  ramification and splitting; Chapter6 p.101 for the K23 norm-descent example.
- PARI/GP official documentation, “General number fields”, `bnfinit` and
  `bnfcertify`, https://pari.math.u-bordeaux.fr/dochtml/html-stable/General_number_fields.html:
  distinguishes a provisional GRH-based computation from full unconditional
  certification. No PARI runtime was present in this workspace and no PARI
  output is used as evidence here.
- Fixed-field density and the resulting centroid/endpoint supply are proved
  in the companion general analytic manuscript. Prime array realization is
  proved in the companion general controller/composition manuscripts. This
  file supplies their exact arithmetic and regular-domain hypotheses and
  preserves the existing quartic model without change.
