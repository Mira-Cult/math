# Independent source-scope audit

Source reviewed: `JoseBrox/diophantine-z-q_improvements` at
`fa09c9c6c97982c13265e7088d95cdb61b3e90cf`.

## Precisely what is being compressed

The asserted property is a projection over rational witnesses:

```math
\{x\in\mathbb Q:\exists y\in\mathbb Q^m\ F(x,y)=0\}=\mathbb Z.
```

It is not an ordinary univariate polynomial vanishing on all integers.
Such a univariate polynomial would vanish identically. The distinguished
input and every auxiliary coordinate are rational; auxiliary integer
quantifiers would change the problem.

The immediately usable, fully specified theorem is Theorem 1.1 of
`papers/quartic/quartic262_20261110_v21.tex`: for every integer
`N >= 9682`, the specified quartic has the desired projection, under the
arithmetic premises in that section. The selected constant is
`A = 149^19365`. Its finite specification is a sum of 234 primitive
quadratic squares in 262 total coordinates and has 3494 collected
monomials. These are source claims; the definition theorem explicitly
retains arithmetic premises.

The 27-variable theorem at `L=20483` is also fully specified. The
25-variable, 226-variable, 13-variable and 87-variable families have
ineffective defining thresholds. Their small displayed fixtures do not
give certified defining polynomials. In particular choosing a visually
short parameter in those families would not solve the requested task.

## Inherited premises

The source explicitly retains all of the following, with the domains
and normalization stated in its papers.

1. For `K = Q(sqrt(2))`, `D=11-6sqrt(2)` and
   `E: y^2=x^3-Dx`, the specified point
   `P=((57-28sqrt(2))/8,(-660+417sqrt(2))/32)` satisfies
   `2E(K)=ZP`, and `h(x([n]P)) >= n^2-6` for nonzero integers `n`.
2. The **full normalized modular realization**, including its
   representation/character, conductor and restricted-trace assertions.
   The source's multiplicity theorem derives its contact-height bound
   from this premise. A numerical check of the height constant is not
   a proof of the premise.
3. Pole obstruction outside `2,3,17`, together with the stated pole
   realization for positive inputs below 17, square reduced denominator,
   and the required local squareclasses and depths. The supporting
   restricted-converse and descent inputs remain inherited.
4. Simultaneous prime patterns, opposite elliptic reduction-order
   separation, finite congruence compatibility and real approximation.

There is no additional abc or Szpiro hypothesis for the selected
262-variable theorem. Calling it simply "unconditional" would hide the
scope explicitly maintained by this repository. A faithful compression
can establish unconditional algebraic equivalence to the source and
inherit its defining conclusion under precisely the same premises.

The arithmetic-dependency paper pins Glazer Version 9 at
`14e8f601fe0d9173d4a5f084aedc3e07066a7688`, incorporating Version 11's
Kato correction at `650b298a2a18fa956f8859f3ca80e9d7c8cedd82`, and Sun
`arXiv:2610.20691v2`, Theorem 4.1. The baseline quartic provenance also
pins Glazer Version 13 at `5bbd74f6a479776a332cbe036809d5dddae63720`.
The upstream repository's current Version 16 asserts its arithmetic
argument and describes its Lean formalization as incomplete. This audit
does not independently reprove those deep arithmetic results.

## Compact construction route

Variable count and degree need not be minimized for this task. The
mathematical rational source in the 262-variable paper can therefore be
used directly, omitting its elaborate quadratic-circuit optimizations.
Use the same scalar certificate and three comparison pole certificates,
with ordinary elliptic formulas and guarded rational operations. Sum
the squares of their cleared rational residuals.

For nonzero doubled elliptic points, the source's square-abscissa chart
uses `x=h^2`, `j^2=h^4-D`, `y=hj`, with `h,j` in `K`. A field coordinate
means a pair of rational coordinates, not a rational variable satisfying
`r^2=2`. For a field residual `e=a+b sqrt(2)`,

```math
\operatorname{Tr}_{K/\mathbb Q}(e^2)=2a^2+4b^2
```

is a rational polynomial vanishing precisely when both components do.
Every denominator must have a nonzero guard. A product of denominator
norms has one rational inverse witness, which can collect all guards.
Extra generic-chart restrictions preserve soundness but require an
explicit completeness argument avoiding the finite exceptional point
equalities.

This route is mathematically more compact than serializing the expanded
quartic, but its precise generator still needs independent verification.

## Source pointers

- `README.md`, section "Main results and arithmetic assumptions".
- `docs/arithmetic_inputs.md`, especially the final verification-scope
  paragraph and "The quartics in 226 and 262 variables".
- `papers/quartic/quartic262_20261110_v21.tex`, Theorem 1.1 and the four
  premises immediately following it.
- `papers/arithmetic_dependencies/arithmetic_dependencies_20261108_v8.tex`.
- `papers/contact_heights/evaluation_of_differentials_20261109_v17.tex`,
  Definition 6.1.
- `papers/contact_heights/multiplicity_and_contact_heights_20261110_v19.tex`,
  section "The arithmetic input" and the subsequent height theorem.

Review scope: independent source-status/quantifier and construction-route
audit, not independent validation of every deep inherited theorem.
