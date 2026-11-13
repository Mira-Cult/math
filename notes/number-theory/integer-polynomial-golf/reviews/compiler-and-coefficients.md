# Compiler and exact-payload review of the frozen PR source

**Disposition:** accepted within the scope below; no blocker found.

**PR:** [Mira-Cult/math-wip #402](https://github.com/Mira-Cult/math-wip/pull/402).

**Reviewed commit:** `1dc330d814a5e57bbd11d93bbb77fd02094bd062`.

**Reviewed tree:** `3c3929a0ba3a62661ae554ccc41e66c3043bca3e`.

**Directory:**
`problems/0151-rational-solution-counts-and-beeping-machines/polynomial-golf/`.

This review is bound to the actual committed bytes, not merely to an
earlier working copy. Each of the four files below was extracted with
`git show 1dc330d814a5e57bbd11d93bbb77fd02094bd062:<path>` into a separate
review directory. The commit's tree ID was independently queried and
matched the stated tree. The extracted bytes were compared with the
working files and were identical. Both committed checkers were then
executed against the extracted committed candidates.

## Reviewed files and identities

| File | ASCII bytes | SHA-256 |
|---|---:|---|
| `code/generate.py` | 2518 | `d94a1ddb453ba515f30e8d08f69403cf609e350033a54f3f9f887e6bf1f45be6` |
| `code/quartic262.py` | 3777 | `2ae94335d638e903b1daa1d7ff5eab5ce4d155856ef0f17ff44f6e713028b6d4` |
| `code/check_compiler.py` | 5155 | `fa835dc76b04fc4fb27424323b6f06445512a7ec116f7e107f72177c578b0408` |
| `code/check_quartic.py` | 3617 | `facce1cc552dabc2327a4003f3cd115aee8514ffdbdc92a06d4ab97873881b4e` |

The two committed checkers are byte-for-byte identical to the separately
written audit checkers used before publication.

## Scope and independence

The exact-payload review is independent of its encoder and compact
decoder implementation: it compares the program's complete result and
each decoded row with separately parsed, hash-pinned upstream JSON.
It imports no code from the upstream repository or payload builder.

The compiler review covers the scalar gate invariant, quadratic-field
arithmetic, denominator guards, polynomial syntax and degree, and
sum-of-squares aggregation. The reviewer did not write the primary
compiler, but suggested its final recursive scalar-power decomposition
and wrote the checking programs. The reviewer also coauthored the
uniform-factor lemma. Consequently this review **does not count as an
independent review of that lemma, of the recursive-power idea, or of the
complete new arithmetic construction**. The latter requires the separate
full-construction review. It does not independently establish the deep
arithmetic premises inherited from the source repository.

## Compiler findings

Each generated arithmetic gate adds a new rational coordinate `z` and
the residual `z-e`. For fixed values of preceding coordinates, this
has exactly one extension, namely `z=e`. Scalar division introduces an
inverse coordinate `u` and the residual `b*u-1`; extension exists exactly
when the denominator is nonzero, and the inverse is then unique.

Quadratic-field elements are represented by rational coordinate pairs
for `a+b*sqrt(2)`. Their multiplication, conjugation and norm implement
the field relation exactly. A quotient is multiplication by the
conjugate followed by scalar division by `a*a-2*b*b`. Over rational
pairs that norm vanishes only at the zero pair. The guard therefore
enforces precisely the required nonzero field denominator. The program
never asks for a rational square root of 2.

The scalar-power implementation reduces every occurring fixed
nonnegative power to multiplication gates. Its base case is the integer
one. The giant fixed constant `149**19365` is a coefficient-expression
string and is not processed by this recursion. Every resulting residual
is an integer polynomial of degree at most two. Squaring and summing
the residuals gives a polynomial over the integers that vanishes over
rational coordinates exactly when all residuals vanish.

The inverse-trace expression uses

```math
\operatorname{Tr}(W^{-1})^{-1}
=\operatorname{Nm}(W)/(2W_0).
```

Its guard `W0 != 0` also implies `W != 0`, since a nonzero rational
coordinate pair is a nonzero element of the field. Thus the expression
does not lose an additional necessary inverse guard. The intended
complete witnesses have positive values at both real embeddings, which
ensures this trace denominator is nonzero.

The point constructor applies the ordinary doubling formula to an
affine elliptic point with nonzero ordinate; the quotient guards enforce
that domain. The subtraction helper implements the ordinary chord
formula for a difference and guards its abscissa denominator. Matching
these generic chart choices to the source's existence proof is part of
the separate full-construction review, rather than an assertion proved
by compiler tests.

### Exact compiler-check result

Execution of the committed `check_compiler.py` on the committed
`generate.py` passed:

- 36 exact rational-pair arithmetic comparisons, including powers,
  conjugation, norms, field division and scalar reverse operations;
- a zero-denominator rejection check;
- independent syntax parsing of every generated residual, allowing only
  integer constants, rational-coordinate names, addition, subtraction,
  multiplication and fixed nonnegative integer powers;
- exact reconstruction of the final output as the sum of the square
  of every generated residual.

The measured committed output has **3779 total rational coordinates**,
including the input `x0`, and **3751 residuals**. Its expression contains
**99396 characters**. The maximum residual degree is two. The polynomial
degree is **exactly four**: at least one residual has a nonzero quadratic
homogeneous part, and the sum of squares of real homogeneous polynomials
cannot vanish identically unless every summand vanishes.

These finite arithmetic cases support the code inspection; the gate
invariant gives the general algebraic argument. They are not finite
tests for the assertion that the rational projection is the integers.

## Exact upstream-payload findings

The upstream source is
`JoseBrox/diophantine-z-q_improvements` at commit
`fa09c9c6c97982c13265e7088d95cdb61b3e90cf`.
The checker enforces these exact source-file hashes:

| Upstream table | SHA-256 |
|---|---|
| `computation/quartic/family262_v21/quadratic-family262-v21.json` | `84c1130856dfda7d3a489f3077d7bc378cd8e594198dd8f3c03fe50463606a93` |
| `computation/quartic/family262_v21/polynomial-family262-v21.json` | `727244236b25c1b1b54f6cc615433f6259440d28215b632de9d60bd4e50e2523` |

Execution of the committed `check_quartic.py` on the committed
`quartic262.py` and these pinned source tables passed. At the fixed
integer coefficient `A=149**19365`:

- all **234 decoded quadratic rows** match the separately parsed source
  rows exactly;
- every coefficient of the expanded sparse polynomial matches the
  separately parsed upstream quartic table exactly;
- no bytes remain unused in the decoded payload;
- the coordinate set is exactly `1,...,262`, with distinguished input
  coordinate **1**;
- the polynomial has exact degree **4** and **3494 nonzero monomials**;
- its largest absolute coefficient is `149**38730+1`, of binary length
  **279599**.

This is an algebraic identity with the source polynomial, not merely a
comparison on sample assignments. The compact code has no network or
upstream-repository dependency; it uses only the Python standard library
and its included payload. The independent checker needs the upstream
tables to verify the identity, but the generator does not.

## Arithmetic qualification

The exact-payload identity is unconditional. The source's conclusion
that the rational input projection is exactly the integers retains its
stated elliptic-group/index-height, full normalized modular-realization,
pole-realization and simultaneous-prime-pattern premises. The new
2518-character generator defines a different polynomial and obtains its
arithmetic conclusion through the separately proved construction, not
through literal coefficient identity with the upstream quartic.

No new abc or Szpiro assumption is needed for the selected source
theorem. Neither successful finite checking nor this component review
constitutes an independent proof of the inherited arithmetic premises.
