# Independent review of the 2,518-byte quartic generator

**Reviewed scientific source commit:**
`1dc330d814a5e57bbd11d93bbb77fd02094bd062` in
[Mira-Cult/math-wip PR #402](https://github.com/Mira-Cult/math-wip/pull/402).

**Reviewer:** `/root/quartic_golf`, an independent sibling research agent.
I did not author the guarded compiler, its multiplication-gate variant, the
uniform-factor lemma, or the transfer proof. My separate contribution was the
exact coefficient-payload baseline. This review concerns the new readable
construction, not that baseline.

**Verdict:** reviewed and accepted as a **conditional construction**, under the
arithmetic premises explicitly retained by the cited upstream source. The
compiler's termination, polynomial output, and preservation of its guarded
rational equations are unconditional. This review does not independently prove
the inherited elliptic rank/index-height, modular-realization, pole-realization,
or simultaneous prime-pattern results.

## Exact files examined

All paths below are relative to
`problems/0151-rational-solution-counts-and-beeping-machines/polynomial-golf/`
in the reviewed commit. I read them from that Git commit, not only from a mutable
working tree. The local commit object was available and identified as a commit.

| File | SHA-256 of the reviewed bytes |
|---|---|
| `code/generate.py` | `d94a1ddb453ba515f30e8d08f69403cf609e350033a54f3f9f887e6bf1f45be6` |
| `proof.md` | `d6ec9b74879faa2def1213f3f5f9aee57b4ef51e0143aaaa0b9305d31ccd47ae` |
| `uniform-factors.md` | `24b098ca908914c9893726eee0ce3dfa5dc308f9eebf77baff670b7158fa98ca` |
| `source-scope.md` | `0d12d00bbc75c92918d8476593354a03e611a32384df75ba2d4f688e4bd1347a` |

The upstream mathematical source is
`JoseBrox/diophantine-z-q_improvements` at
`fa09c9c6c97982c13265e7088d95cdb61b3e90cf`. I checked the relevant arguments in
`papers/quartic/quartic262_20261110_v21.tex`, especially the scalar certificate,
local extraction, integrality before formal congruences, explicit parameter,
and simultaneous completeness sections; and the zero-preparation pole
predicate in
`papers/arithmetic_dependencies/arithmetic_dependencies_20261108_v8.tex`.

## Claim reviewed

The program prints an integer polynomial `F` of degree exactly four, in the
3,779 variables `x0,...,x3778`. Under the explicitly inherited arithmetic
premises,

```math
\{x\in\mathbb Q:\exists x_1,\ldots,x_{3778}\in\mathbb Q,
 F(x,x_1,\ldots,x_{3778})=0\}=\mathbb Z.
```

Every quantified witness is rational; `x0` is the distinguished rational input.
This is a projection of a multivariable zero set, not a univariate polynomial
vanishing on infinitely many isolated points.

The frozen proof has the current quartic counts and explicitly distinguishes
finite-place preparation from large positive real preparation. It does not
retain the earlier degree-20 construction's counts as current results.

## Compiler and polynomial degree

Every scalar arithmetic operation allocates its output and appends the equation
asserting its value. Division allocates an inverse `u`, imposes
`denominator*u-1=0`, then multiplies by `u`; it does not merely clear a possibly
zero denominator. Thus the guarded rational operations and compiled equations
have exactly corresponding rational solutions, with unique gate values.

The scalar-power implementation recursively multiplies. Its exponents are fixed
nonnegative integers, at most ten. Induction on the exponent proves that these
gates compute the same power. Every residual is therefore quadratic or linear.

The field class represents `a+b*sqrt(2)` by its two rational components, with the
literal multiplication, conjugation, and norm formulas. Field division uses the
conjugate divided by its rational norm, with the same inverse guards. Since two
is not a rational square, the norm vanishes exactly on the zero field element.
No variable with an impossible rational equation `r²=2` is introduced.

Every output residual has integer coefficients. Rational constants are compiled
through inverse gates; `149**19365` remains a fixed integer coefficient. The
sum of residual squares vanishes over the rationals if and only if all residuals
vanish. There are genuine quadratic residuals, such as `x4-((x3)*(x1))`.
Their highest homogeneous squares cannot cancel identically over the reals,
so the final degree is exactly four.

## Elliptic point domains and scalar certificate

`point()` imposes the affine curve equation before computing the double, guarding
`2*y`. Under the retained `2E(K)=ZP` premise, the result is a nonzero multiple of
`P`: a zero double would require two-torsion, excluded by that guard. Conversely,
every needed `nP` has a non-torsion preimage `nR0`, with `P=2R0`.

`sub(A,B)` correctly computes `A-B`, using slope
`(y(A)+y(B))/(x(A)-x(B))`. Its extra guard removes `A=±B`. The proof accounts
for these extra affine exclusions. Complete witnesses use
`H=[h]P`, `U_i=[h*n_i]P`, and `V_i=[(h-1)*n_i]P`, with nonzero root indices,
and the source allows arbitrarily large indices in the required progressions
and real neighborhoods. Choosing `h>2` and the scalar index outside the finite
exceptional set satisfies every additional subtraction guard. No needed
identity branch is silently assumed to have an affine representation.

The scalar normalizer and two norm expressions are exactly the source's
mathematical scalar certificate at `N=9682`. Since `beta=51*x0²+2504`, all scalar
contact factors and the normalizer are positive. The reciprocal-abscissa norm
is nonzero, so the scalar pole input is strictly positive. The zero-preparation
pole predicate is used with precisely its original four unrestricted rational
witnesses; no unjustified nonzero-witness premise is added.

## Uniform local products

The replacement product has factors `1+q³*f²` for the ten reciprocal-abscissa
tests and `1+q⁵*c²` for the six comparison tests. At a consumed contact prime,
`v(q)=-nu` with positive odd `nu`. The two terms of each factor have valuations
zero and an odd integer, or the second term vanishes. Hence no tied-minimum
cancellation occurs; each factor has nonpositive valuation, and a factor of
valuation zero has residue one.

For `l=max_{v|p}v(W)`, the reciprocal-trace inequality and retained pole
obstruction give `l>-nu/2`. At a place attaining the maximum, every factor's
valuation is at least `l`. The resulting test bounds are
`v(f)>5*nu/4` and `v(c)>9*nu/4`. These give orders at least two and three,
respectively. The argument works at split and inert unramified primes.
These orders imply all the hypotheses of the source's subsequent formal-group
and logarithmic-ratio argument. The scalar certificate, contact heights,
three height scales, Lucas residual, and numerical threshold are unchanged.

The program's guard `W.x!=0` implies `W!=0` and hence `Norm(W)!=0`; therefore
`tau=Norm(W)/(2*W.x)` is nonzero and equals `1/Tr(W^-1)`. The guard `q+1!=0`
makes the comparison pole input nonzero and excludes `t=1`, which does not
occur in the large-positive complete witnesses. The contact denominator guard
also excludes zero, a contact, so the height-ratio argument has a nonzero
slope. Allowing `q=0` is safe: the new circuit never divides by `q`, and that
scale has no consumed contact primes.

## Completeness transfer

At each selected contact prime the original construction has `v(q)=-1`,
reciprocal-abscissa depths at least two, and comparison depths at least four.
All new factors are therefore one modulo that place. At the opposite place
the parity lemma gives either negative valuation or residue one. The reciprocal
trace is a unit with residue one or two, preserving valuation one for the
comparison pole input at each selected prime.

At the finitely prepared places the source makes the valuation of the contact
parameter sufficiently negative, so `q` becomes arbitrarily small while the
finite list of tests remains bounded below in valuation. The factors tend to
one and the reciprocal trace to two. Thus the prepared squareclasses and
required depths at `2,3,17` persist. Outside selected prime numerators the
contact expression has even valuation; multiplying by a rational square and
dividing by a rational square preserves the square-denominator requirement.

At the real embeddings the source instead chooses a sufficiently large positive
parameter. Then `q>0`, all factors are positive, and the new pole input tends to
`(408/409)²/4`, inside `(0,17)`. The retained simultaneous prime-pattern and
approximation premise supplies these compatible conditions. Pole realization
supplies the rational witnesses, and the compiler extends them uniquely to gate
coordinates. The additional guards are satisfied. Thus completeness is not
being inferred merely from the stronger soundness inequalities.

## Independent finite verification

I independently executed the generator bytes read from the reviewed commit.
The source is **2,518 ASCII bytes including its terminal newline**. It makes
**3,779 variables**, **3,751 residual equations**, and a **99,396-character**
polynomial expression, not counting the newline added by `print`.

A recursive AST inspection of the identical reviewed code found **1,588
quadratic residuals and 2,163 linear residuals**, only integer constants and
polynomial operators, and no remaining divisions. The generated expression's
SHA-256, without the printed terminal newline, is
`8f39f65e99671c23b2ce528b31216b084b5737c977af4ecdc1f8cb6921ed3113`.

These finite checks establish code properties and bind this review to its exact
source. They do not replace the conditional mathematical proof or independently
verify its deep inherited arithmetic inputs. A later minified generator needs
its own exact-output identity check; this review directly covers the source
and proof at the commit named above.
