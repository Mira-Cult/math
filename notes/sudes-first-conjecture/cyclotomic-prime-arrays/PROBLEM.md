# Prescribed prime-element arrays in quartic cyclotomic rings

## Statement

Fix m in {5,8,12}, K=Q(zeta_m), O=Z[zeta_m], and the ordered integral
basis (1,zeta_m,zeta_m^2,zeta_m^3). The first complex embedding sends zeta_m
to exp(2 pi i/m); the second sends it to its a-th power, with a=2,3,5,
respectively. Array dimension D is 2 or 3; arithmetic rank is always 4.

### Frozen balanced-log pool

Let (w,rho,u) be

| m | w | rho | u |
|---|---:|---|---|
| 5 | 10 | -zeta_5^3 | -zeta_5^2-zeta_5^3 |
| 8 | 8 | zeta_8 | 1+zeta_8-zeta_8^3 |
| 12 | 12 | zeta_12 | 1+zeta_12 |

Put lambda=|sigma_1(u)|>1. Choose the unique associate alpha satisfying

    -log(lambda) <= log(|sigma_1(alpha)|/|sigma_2(alpha)|) < log(lambda),
    -pi/w <= arg(sigma_1(alpha)) < pi/w.

The full-unit-group proof, exact boundary tests, and comparison with coefficient
height normalization are in [N1-N3](manuscripts/normalization_local.md). Retain one such
representative from every prime-element associate class except those above
rational primes dividing m. Retain inert and higher-residue-degree prime ideals;
conjugate classes are separate. Order by (absolute field norm,a0,a1,a2,a3).
No further class is omitted. This uniquely defines P_m and its finite effective
prefixes, as proved in N2.

For each n, use exactly the first n^D members of P_m, each once. Every line sum
uses coefficients +1. Squares require n rows, n columns, and both diagonals.
Cubes require all deduplicated full signed-coordinate lines, with every
coordinate fixed, t, or n+1-t, and at least one varying. There are 2n+2 square
lines and 3n^2+6n+4 cube lines for n>=2; at n=1 there is one.

## Goals

The [author proof of CPA4](manuscripts/composition.md) establishes eventual
existence at every integer order for m=5,12 and every odd order for m=8,
for squares and full cubes. All even m=8 orders at least two are impossible.
These order classes have an independent arithmetic definition. Independent
review is recorded against exact revisions separately from mathematical status.

Target sums may repeat and need not be canonical representatives. Independently
rescaling input associates, replacing the initial pool, omitting unfavorable
classes, or relaxing diagonal families changes the problem and is forbidden.
Minimal-height representatives constitute a different model unless equivalence
is proved. The primary threshold may be ineffective; no numerical bound is
asserted by this checkpoint.

## Model and scope

Owner/coordinator: /root, branch research/cyclotomic-prime-arrays-20261102.
Only problems/cyclotomic-prime-arrays/ is owned. Other active lanes and the
quadratic foundation are immutable imports. All labels are manuscript-local;
no permanent claim IDs are allocated. Conventional proof, independent internal
review, finite computation, kernel verification, CI, and integration are
distinct statuses. The coordinator controls integration.

## Fixed-conductor continuation (2026-11-03)

The new bounded obligation is to prove the same square and full-cube statement
for every fixed cyclotomic field, allowing arbitrary arithmetic degree and
class number. The four reviewed quartic manuscripts and their pools above
remain unchanged. New manuscript-local results will be separately frozen and
reviewed; no permanent claim IDs are allocated.

### Extended canonical family

For an input conductor m, use the reduced conductor c=m/2 if m is 2 modulo 4,
and c=m otherwise. This identifies equal cyclotomic fields before defining a
pool, so conductors 6 and 10 use exactly the pools for 3 and 5. For c>=3 use
the power basis (1,zeta_c,...,zeta_c^(r-1)), r=phi(c), the first embedding
zeta_c=exp(2 pi i/c), and one embedding from each conjugate pair. The number
of roots of unity is w=c for even c and w=2c for odd c.

For c in {5,8,12}, keep the balanced-log pool already frozen above. For every
other c>=3, define the following distinct energy-minimal model. Among all
unit associates of a nonzero integral element alpha, minimize

    E(alpha)=Tr_K/Q(alpha*conj(alpha))/2
            =sum_{j=1}^{r/2} |sigma_j(alpha)|^2.

Among energy minimizers retain those in the half-open first sector
[-pi/w,pi/w), then choose the lexicographically least power-basis coefficient
tuple. This is a choice of an entire element, with no later unit rescaling.
All comparisons are exact. The finite trace-energy ellipsoid allows exhaustive
comparison against every associate competitor by testing whether beta/alpha
is an integral unit. No equality test between products of logarithms is used.

For either model retain one representative of every principal prime ideal,
omitting precisely the prime ideals over rational primes dividing c. A
nonprincipal prime ideal contributes no prime element; an irreducible which
does not generate a prime ideal does not enter the pool. Retain all principal
higher-residue-degree and inert prime classes. Order by absolute norm followed
by the ascending coefficient tuple, including partial final norm ties.

The proposed arithmetic order classes are positive odd integers when c is a
power of two, and all positive integers otherwise. This is an independent
arithmetic definition; eventual sufficiency is a proof obligation. The array
families and exact n^D input requirement are unchanged.

### Rational edge case and normalization limit

For c=1 the ring is Z. Omitting only ramified prime classes omits nothing and
retains 2; that pool has a parity obstruction at every n>=2. The separately
named rational repair omits 2 at the outset and uses exactly the initial odd
primes, recovering the original rational problem. This extra omission is not
made in any nontrivial cyclotomic field.

An arbitrary higher-rank logarithmic parallelepiped is not assumed effectively
decidable at its boundary. The energy model is the explicit normalization for
new fields; no equivalence with a logarithmic or coefficient-height pool is
claimed. All thresholds may depend on the fixed conductor. Growing-conductor
uniformity and numerical bounds are outside this continuation's primary goal.
