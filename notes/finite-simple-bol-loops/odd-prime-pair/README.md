# Simple left Bol loops of odd two-prime order

**Mira Cult**

A loop has an identity and unique left and right division. It is *left Bol* if
`x(y(xz)) = (x(yx))z`; it is *simple* if its only normal subloops are the
identity and the whole loop. Here we exclude associative loops. Fix distinct odd
primes $`p,q`$ and ask which orders $`p^a q`$ occur and how many loops occur at
the first admissible exponents. Write $`f=\mathrm{ord}_q(p)`$, the
multiplicative order of $`p`$ modulo $`q`$.

## What is known

- **Least exponent and its census.** Some order $`p^a q`$ occurs if and only
  if $`p`$ divides $`q-1`$. For such a pair, the least exponent is
  $`1+\mathrm{lcm}(p,f)`$. At this exponent there is one isomorphism
  type unless $`f`$ is even and $`p`$ does not divide $`f`$. In the exception
  the exact count is an explicit finite orbit formula. See the
  [minimum over all cores](manuscripts/all-core-prime-pair-minimum.md),
  [census for the exceptional case](manuscripts/two-weight-exhaustion-at-the-first-odd-prime-pair-degree.md),
  and [arithmetic count](manuscripts/exact-first-exponent-orbit-count.md).
- **No order at the next exponent.** For every admissible pair there is
  no simple nonassociative left Bol loop of order
  $`p^{2+\mathrm{lcm}(p,f)}q`$. The proofs separate
  [the case where $`p`$ does not divide $`f`$](manuscripts/second-odd-prime-pair-degree-gap.md)
  from [the case where it does](manuscripts/second-degree-gap-with-p-dividing-f.md).
- **A complete restricted census two steps above the minimum.** Set
  $`p=3`$ and suppose $`9`$ divides $`f`$. At order $`3^{f+3}q`$, loops whose
  canonical left multiplication group has elementary abelian normal
  $`3`$-core and whose quotient has a cyclic rotation group of order nine
  [exist](manuscripts/third-degree-ternary-order-nine-top-construction.md)
  and are [classified up to isomorphism](manuscripts/ternary-top-nine-elementary-core-classification.md).
  Put $`f/9=3^e u`$ with $`3`$ not dividing $`u`$. The exact count is
  ```math
  \frac{1}{3(f/9)}\sum_{j=0}^{u-1}3^{2\cdot 3^e\gcd(u,j)}.
  ```
  For $`q=19`$, this gives 15 types of order 198,746,710,857 **in this
  restricted class**.
- **Larger cyclic rotations force two kinds of weights.** For elementary
  abelian normal $`p`$-core and a cyclic rotation group of order $`p^k`$ with
  $`k\ge 2`$, except $`(p,k)=(3,2)`$, both an axial weight (nontrivial on
  exactly one reciprocal axis) and a mixed weight (nontrivial on both)
  must occur. Thus
  ```math
  a\ge k+\mathrm{lcm}(p^k,f)+\frac{f(p^k-1)}2.
  ```
  See the [purely axial obstruction](reviews/arbitrary-cyclic-top-graph-obstruction.md#2-a-no-repair-theorem-for-the-split-elementary-purely-axial-architecture)
  and [both-weight bound](manuscripts/elementary-higher-top-mixed-weight-lower-bound.md).
  The bound does not assert existence or sharpness.

## Why the stabilizer matters

The left translations generate a faithful permutation group $`D`$ with a
distinguished point stabilizer and, in this odd simple setting, an involution
that inverts the translations. In the two-prime reduction the quotient by
the normal $`p`$-core has two reciprocal axes of order $`q`$ and, above
those axes, a cyclic rotation group. This is the
[audited two-axis reduction](reviews/first-degree-prime-pair-upstream-necessity-audit.md). Counting negative directions under the involution gives
a lower bound on the loop order. At the smallest degrees, the **actual**
stabilizer imposes further constraints: it must have the right index,
avoid products of distinct marks, and not give a proper loop quotient.
These conditions distinguish representations that could be realized by
loops from abstract signed representations with the same dimension.

## Nonabelian cores with fixed Frattini subgroup

These results treat canonical nonabelian cores whose Frattini subgroup is
fixed pointwise by the inversion automorphism, with the additional axial
weight assumptions stated separately in each proof.

- [Exact quotient mark multiplicity and single-packet exclusion](manuscripts/0131-frattini-quotient-crowding.md).
  Projected collisions are not necessarily actual collisions.
- [The multiplicity-one branch](manuscripts/0132-fixed-frattini-multiplicity-one.md).
  Even Frobenius degree is excluded for purely axial weights of multiplicity
  one; odd-degree reciprocal pairs have a separate necessary condition.
- [Repeated packets and physical stabilizer phases](manuscripts/0133-fixed-frattini-repeated-packets.md).
  The rank bound allows modular extensions within packets, and the central
  phase calculation distinguishes actual from projected collisions. It does
  not settle the remaining all-even case.

## What remains

For $`p`$ dividing $`f`$, determine the full census at $`a=f+3`$, including
rotation order $`p`$ and non-elementary cores. For larger rotation groups,
construct a genuine elementary-core folder with both types of weight, or
prove an additional obstruction without assuming the linear data alone
gives a transversal. The results here do not classify all odd simple
Bol loops.

[Verification and provenance](VERIFICATION.md) ·
[Earlier odd-order bounds](../odd-degree/README.md) ·
[Bol-loop research index](../README.md)
