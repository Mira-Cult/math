# A uniform Fourier entropy bound for affine images of positive forest spectra

**Mira Cult · 16 November 2026**

Every affine spectral image of a positive Boolean forest law satisfies one
uniform FEI bound, with constant
$`4+4/\log_2(5/4)<17`$. The resulting spectra can have arbitrarily large
treewidth and interaction arity. The proof pays entropy using a uniform
spectral subspace whose dimension is controlled by a strengthened integer
tree partition-sum inequality.

The result includes specified affine-subspace supports and all invertible
physical linear changes of positive forest examples. It does not prove FEI
for arbitrary Boolean functions. No publication-priority claim is made
solely from the examples' interaction graphs.

**Review status.** Complete proofs with scoped nonauthor model review of the
scientific revision. The review scope, exact revisions, and limitations are
recorded in [Verification](VERIFICATION.md); this is not human peer review.

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

Scientific source: [math-wip at a17f79e](https://github.com/Mira-Cult/math-wip/blob/a17f79e858c8537587a8d49e2b879f10c59e7677/problems/0298-fourier-entropy-influence-conjecture/manuscripts/affine_forest_entropy.md).

## 1. Main result and its scope

All logarithms are base two. For Boolean sign functions on a uniform binary cube,
write $`p_f(s)=\widehat f(s)^2`$, $`H(f)=\sum_s p_f(s)\log_2(1/p_f(s))`$, and
$`I(f)=\sum_s|s|p_f(s)`$.

Set

```math
 C_{\mathrm{aff}}=4+\frac{4}{\log_2(5/4)}
 =16.42513487802156\ldots\lt 17.
```

**Theorem A.** Let $`g:\{0,1\}^d\to\{-1,1\}`$ be Boolean. Assume all Fourier
coefficients of g are nonzero and its squared Fourier law factors over a
forest. Let $`B:\mathbb F_2^d\to\mathbb F_2^n`$ be any injective linear map, and let
$`a\in\mathbb F_2^n`$. Define the Boolean function

```math
 f(x)=(-1)^{a\cdot x}g(B^{\mathsf T}x).
```

Then

```math
 H(f)\le C_{\mathrm{aff}} I(f).
```

The same numerical constant works for every d,n,g,B,a. Neither the graph
width nor the interaction arity of the resulting Fourier law is bounded.
The strict numerical bound follows from $`5^{13}>2^{30}`$, which gives
$`\log_2(5/4)>4/13`$. If $`d=n`$ and B is invertible, the resulting spectrum remains strictly
positive. If $`d<n`$, its support is the affine subspace $`a+\operatorname{im}B`$; this is a
specified zero-support class, not a reduction for arbitrary zeros. The
zero-dimensional case consists of characters and satisfies $`H=0`$.

This extends the class covered by the positive-forest theorem under all
invertible linear changes of physical coordinates and character
multiplication, at the cost of replacing constant four by $`C_{\mathrm{aff}}`$. The
argument does not preserve forest factorization in the new coordinates.
Its new input is a partition-sum strengthening of the forest energy
argument, proved next. The earlier positive-forest theorem and arithmetic
facts used below are canonical in [the positive-forest proof](positive-forests.md) and
[the arithmetic proof](forest-arithmetic.md).

## 2. A partition-sum estimate for integer tree energies

Let E be an integer quadratic polynomial on binary variables whose minimal
interaction graph is a tree. Every edge coefficient is nonzero. All
binary assignments are allowed. Normalize by subtracting the minimum and
put

```math
 Z(E)=\sum_x4^{E(x)-\min E},\qquad
 \kappa(E)=n-\deg_{\mathbb F_2}\mathbf1[E=\min E].
```

**Theorem B (partition sum and two field comparisons).**

1. Every nonconstant connected integer tree energy, including a nonconstant
   one-variable energy, satisfies

   ```math
   Z(E)\ge 2\,5^{\kappa(E)}.
   ```

2. Fix a root r of any connected integer tree, allowing one vertex.
   For distinct integer fields a,b at that root,

   ```math
   Z(E+b x_r)\ge 5^{\kappa(E+a x_r)}.
   ```

3. If the connected tree has at least two vertices, those same distinct
   root fields satisfy

   ```math
   Z(E+a x_r)Z(E+b x_r)
   \ge5^{\kappa(E+a x_r)+\kappa(E+b x_r)+1}.
   ```

The statements permit arbitrary integer interaction magnitudes and unary
fields. They do not require that Z be a power of two, or that the Gibbs law
have a Boolean Fourier signing. A constant single vertex is excluded from
part 1 and allowed in part 2. Part 3 deliberately excludes a single
vertex: zero and unit fields have product 10, smaller than 25.

### Proof

We prove all three assertions simultaneously by induction on the number
of vertices. For one variable with field t, the normalized partition sum
is $`1+4^{|t|}`$. Its deficiency is one when $`t=0`$, and zero otherwise.
Thus a nonzero field has $`Z\ge 5\ge 2`$. For distinct fields, a target deficiency
one can only come from the zero field; the other field has $`Z\ge 5`$.
Target deficiency zero is immediate. This proves parts 1 and 2 at one
vertex; part 3 has no one-vertex assertion.

For a larger tree root at r. Conditional on the root bit b, each child
subtree has an integer energy $`E_{j,b}`$. Its two root fields differ by the
nonzero edge coefficient. Normalize each child energy to minimum zero,
and define

```math
 Z_b=\prod_j Z(E_{j,b}),\qquad
 \kappa_b=\sum_j\kappa(E_{j,b}).
```

The second identity holds because the conditional ground-set indicator is
a product on disjoint variable blocks. Let $`c_b\ge 0`$ be the conditional
minimum minus the global minimum. At least one $`c_b`$ is zero, and

```math
 Z(E)=4^{c_0}Z_0+4^{c_1}Z_1. \qquad\text{(*)}
```

The inductive cross-field bounds, multiplied over the children, give

```math
 Z_0\ge5^{\kappa_1},\qquad Z_1\ge5^{\kappa_0}. \qquad\text{(1)}
```

A child subtree containing at least two vertices satisfies the inductive
part 3, hence

```math
 Z(E_{j,0})Z(E_{j,1})
 \ge5\,5^{\kappa(E_{j,0})+\kappa(E_{j,1})}. \qquad\text{(2)}
```

For a one-vertex child, its two fields are distinct. If exactly one is zero,
the sum of its deficiencies is one and its product of partition sums is
at least $`2\cdot 5=10=2\cdot 5^1`$. If neither field is zero, both deficiencies
are zero and the product is at least 25. Therefore, if there are h
children,

```math
 Z_0Z_1\ge2^h5^{\kappa_0+\kappa_1}. \qquad\text{(3)}
```

If no singleton child is constant in either branch, the stronger bound

```math
 Z_0Z_1\ge5^h5^{\kappa_0+\kappa_1} \qquad\text{(4)}
```

holds, by (2) for larger children and $`25\ge 5`$ for singleton children.

We first prove part 1 at size n. If there is a unique minimizing root
branch, say $`b=0`$, its global deficiency is $`\kappa_0`$: multiplying its
conditional ground indicator by $`1+x_r`$ raises degree by exactly one.
Here $`c_1\ge 1`$. Thus (*) and (1) give

```math
 Z(E)\ge4Z_1\ge4\,5^{\kappa_0}
 \ge2\,5^{\kappa(E)}.
```

The other unique branch is symmetric.

Suppose the minima tie. Write $`P_0,P_1`$ for the conditional ground
indicators. The full ground indicator is

```math
 P=P_0+x_r(P_0+P_1).
```

If the two degrees differ, or their highest homogeneous parts differ,
then $`\kappa(E)=\min(\kappa_0,\kappa_1)`$. AM--GM and (3) give

```math
 Z(E)=Z_0+Z_1\ge2\sqrt{Z_0Z_1}
 \ge2\,2^{h/2}5^{(\kappa_0+\kappa_1)/2}
 \ge2\,5^{\min(\kappa_0,\kappa_1)}.
```

In the remaining cancellation case, the branch degrees and highest
homogeneous parts agree. Put $`\kappa_0=\kappa_1=m`$; then
$`\kappa(E)=m+1`$. No singleton child can be constant on exactly one side:
its variable would occur in every highest-degree monomial of the product
on exactly that side. Since the child variable blocks are disjoint,
this contradicts equality of the highest homogeneous parts. Thus (4)
applies. For $`n\ge 3`$, choose an internal root, so $`h\ge 2`$. Then

```math
 Z(E)\ge2\sqrt{Z_0Z_1}\ge2\,5^{h/2}5^m
 \ge2\,5^{m+1}.
```

For $`n=2`$ there is a single one-variable child, and cancellation requires
both its fields to be nonzero. Hence $`Z_0+Z_1\ge 5+5=10=2\cdot 5^1`$, while
$`m=0`$. This completes part 1 at the new size.

For part 2, take any root, without an internal-root assumption. Its
normalized child energies, their partition sums, and their ground
indicators are independent of the varied root field. If the target
field a has a unique minimizing branch, its $`\kappa`$ is one of
$`\kappa_0,\kappa_1`$, and (*) at field b together with (1) suffices. If a
ties but has no highest-degree cancellation, its $`\kappa`$ is their minimum
and (1) again suffices.

If a ties with cancellation, write the common deficiency as m. There
is exactly one tying integer root field, so distinct b has a minimum gap
at least one. By (4),

```math
 Z(E+b x_r)\ge\min(Z_0+4Z_1,4Z_0+Z_1)
 \ge4\sqrt{Z_0Z_1}\ge4\,5^{h/2}5^m\ge5^{m+1},
```

because $`h\ge 1`$ and $`4\sqrt5\ge5`$. This proves part 2.

It remains to prove part 3, still using only the assertions on smaller
child subtrees. Let a,b be the distinct fields and use the same $`Z_0,Z_1`$
and $`\kappa_0,\kappa_1`$ for both.

* If both fields have the same unique minimizing branch, say zero,
  their two positive integer minimum gaps are distinct and sum to at
  least three. Their deficiencies both equal $`\kappa_0`$. By (1),
  $`Z_aZ_b\ge4^3Z_1^2\ge64\cdot5^{2\kappa_0}\ge5^{2\kappa_0+1}`$.
* If the fields have opposite uniquely minimizing branches, their
  deficiencies are $`\kappa_0,\kappa_1`$. Then

  ```math
  Z_aZ_b\ge(Z_0+4Z_1)(4Z_0+Z_1)\ge25Z_0Z_1
  \ge25\,2^h5^{\kappa_0+\kappa_1}
  \ge5^{\kappa_0+\kappa_1+1}.
  ```

  The middle scalar inequality expands to
  $`4Z_0^2+17Z_0Z_1+4Z_1^2\ge 25Z_0Z_1`$.
* Otherwise exactly one field ties the minima. Its partition sum is
  $`Z_0+Z_1`$; the other has one integer gap at least one. Thus

  ```math
  Z_aZ_b\ge\min((Z_0+Z_1)(Z_0+4Z_1),
                 (Z_0+Z_1)(4Z_0+Z_1))\ge9Z_0Z_1.
  ```

  If there is no cancellation at the tying field, the sum of the two
  global deficiencies is at most $`\kappa_0+\kappa_1`$. Formula (3) gives the
  desired conclusion, since $`9\cdot 2^h\ge 5`$.
  If cancellation occurs, the common branch deficiency is m, and the
  two global deficiencies are m+1 and m. Formula (4) gives
  $`Z_aZ_b\ge9\cdot5^h\cdot5^{2m}\ge5^{2m+2}`$, since $`h\ge 1`$ and $`45\ge 25`$.

These cases exhaust distinct fields and prove part 3. The simultaneous
induction is complete. QED.

All stated inequalities now involve integers only. The strengthened
pair comparison is the additional slack that permits base five in the
own and cross bounds; omitting it gives the weaker base $`2\sqrt5`$.

## 3. A uniform fair-subspace budget for positive Boolean forests

We recall exactly the arithmetic input from the existing positive-forest
proof. For a positive Boolean Fourier law factoring over a forest, delete
all zero interaction edges. Every isolated spectral bit is independent
and fair. Let q be their number. On each nontrivial connected component C,
its primitive Walsh-magnitude factor is $`2^{v_C}`$, with v_C nonnegative
integer and minimum zero. Write

```math
 Z_C=\sum_{s_C}4^{v_C(s_C)}=2^{2D_C},\quad
 \delta_C=\deg_{\mathbb F_2}\mathbf1[v_C=0],\quad
 \kappa_C=|C|-\delta_C,\quad
 \varepsilon_C=D_C-\kappa_C.
```

Here $`2D_C`$ is an integer. Boolean Walsh inversion, the powers-of-two
arithmetic theorem, and Parseval imply

```math
 \frac q2\ge\sum_C\varepsilon_C. \qquad\text{(5)}
```

For clarity, the mechanism is this. Write the full Walsh magnitude as
$`2^m\prod_C2^{v_C}`$, with isolated fair factors equal to one.
Parseval gives $`m+\sum_CD_C+q/2=d`$. The minimum-layer indicator has
algebraic degree $`\sum_C\delta_C\le m`$. Subtracting these two relations
gives (5). Fairness of isolated bits follows from the fact that
$`1+4^k`$ cannot be a power of two for an integer k>0. No assertion is made
for arbitrary forest probability laws without Boolean realizability.

Set

```math
 \alpha=\frac{\log_2(5/4)}2\gt 0.
```

Theorem B yields, component by component,

```math
 D_C\ge(1+\alpha)\kappa_C+\frac12,
 \qquad \varepsilon_C\ge\alpha\kappa_C.
```

The second inequality deliberately drops a positive additive constant.
Since $`v_C\ge 0`$, its normalized law has entropy

```math
 H(p_C)=2D_C-2\mathbb E v_C\le2D_C
 =2(\varepsilon_C+\kappa_C)
 \le\left(2+\frac2\alpha\right)\varepsilon_C. \qquad\text{(6)}
```

Independence of the components and the q fair bits gives

```math
 H(g)=q+\sum_C H(p_C)
 \le q+\left(2+\frac2\alpha\right)\frac q2
 =\left(2+\frac1\alpha\right)q. \qquad\text{(7)}
```

Equivalently, the entropy is paid entirely by the dimension q of an
independent uniform spectral subspace. This is stronger structural
information than the earlier assertion that at least one fair bit
exists. Indeed $`Z_C\ge 2^{|C|}`$ also gives

```math
 |C|\le2D_C\le\left(2+\frac2\alpha\right)\varepsilon_C,
 \qquad d\le\left(2+\frac1\alpha\right)q. \qquad\text{(8)}
```

Thus at least a universal fraction $`1/(2+1/\alpha)`$ of the original
spectral dimension consists of independent fair directions. The
bound is not asserted sharp.

## 4. Affine invariance of the paid fair directions

Let S be the original spectral sample. Its q fair bits span a q-dimensional
subspace F on which S is uniform independently of the remaining component
coordinates. Under the injective linear map B and shift a, the new sample
is exactly $`T=a+BS`$. Its entropy is H(g), since the map is injective.
At least q output-coordinate functionals are nonzero on B(F): the
restrictions of all output-coordinate functionals span the dual of B(F),
whose dimension is q. Each such coordinate of T is a fair bit, regardless
of the core distribution and affine shift. Consequently

```math
 I(f)=\mathbb E|T|\ge q/2.
```

Combining with (7) proves

```math
 H(f)\le\left(4+\frac2\alpha\right)I(f)
 =\left(4+\frac4{\log_2(5/4)}\right)I(f).
```

The Fourier pushforward identity is exact: expanding g gives
$`f(x)=\sum_s\widehat g(s)(-1)^{(a+Bs)\cdot x}`$, with no collisions because B
is injective. This also proves Boolean realizability and the stated
support cases. There are no mixture labels, reparameterization
denominators, or uncharged amplitude interference terms. QED.

## 5. Interaction width and arity really can grow

Use m independent copies of the previously checked twelve-variable
Boolean function from [forest-arithmetic.md](forest-arithmetic.md), whose four-bit
nonuniform core has primitive log-amplitude

```math
 v(a,b,c,d)=3-2a-2b-c+ab+bc+cd
```

and whose eight remaining spectral bits are independent fair bits. The
canonical source gives the complete Kraft-prefix/bent Boolean construction
and exact Walsh check; that construction is not new here.

On the 4m core coordinates, make an invertible spectral substitution in
which the old a in the first copy is the parity of all 4m new core bits,
while every other old core bit is the corresponding unchanged new bit.
This is invertible because the first new bit occurs with coefficient one
only in that changed old coordinate. Leave the 8m fair bits unchanged.
The transformed log-amplitude is

```math
 v(t_1\oplus\cdots\oplus t_{4m},t_2,t_3,t_4)
 +\sum_{j=2}^m v(t_{4j-3},t_{4j-2},t_{4j-1},t_{4j}).
```

Its real multilinear polynomial has a nonzero monomial on all 4m core
variables. For $`r=4m`$, the coefficient is $`(-1)^r3\cdot2^{r-2}`$: only
$`-2a+ab`$ contributes to that top monomial. Thus every pair of core
variables has a nonzero mixed difference, and the minimal positive
interaction graph contains the clique $`K_{4m}`$. Its treewidth is 4m-1.
The same top monomial proves that no positive factorization with maximum
arity less than 4m is possible. The transformed Fourier law stays
positive and is Boolean-realized by the inverse-transpose physical
linear change. Theorem A has the same constant for all m.

This family demonstrates unbounded interaction size in the theorem's
hypotheses. It does not establish a first FEI bound for those particular
prefix/bent examples: their flat-packet structure already yields constant
four, even after linear changes. The new theorem covers every Boolean
signing with a positive forest law before the affine change, without
assuming an integer flat-packet decomposition or a particular completion.
Whether all such signings possess a stronger known representation is not
proved here. Novelty must therefore be assessed from the structural
partition-sum and fair-subspace theorem, not merely from this graph witness.

## 6. Relationship to uniform FEI and remaining gap

The theorem gives one constant over a class allowing unbounded transformed
width and arity. It does not cover arbitrary positive Boolean laws: it
requires an affine spectral coordinate system in which the law factors
over a forest. No assertion is made that an arbitrary positive law has
such coordinates. Nor does the partition-sum proof extend to cycles: its
child conditional independence and the highest-homogeneous product argument
are both used essentially.

The immediate new structural inequality is $`Z\ge 2\cdot 5^\kappa`$ on connected
integer trees. A stronger candidate $`\mathbb E_p v\ge\kappa`$, under an additional
power-of-two partition-sum hypothesis, was tested but is not proved or
used. The entropy-energy candidate $`\mathbb E_p v+H(p)/3\ge\kappa`$ is likewise not
proved or used. Their continued investigation might improve $`C_{\mathrm{aff}}`$ or
reach beyond affine forest factorization, but neither is needed for
Theorem A.


## Reproducible checks

The accompanying [exact checker](code/check_affine_forest_entropy.py) is mirrored without
changes from the scientific revision. From this note's directory, run:

```bash
python code/check_affine_forest_entropy.py
```

Finite checks verify the identities and examples specified by the checker;
the proofs above establish the universal statements.
Exact runs and review qualifications are recorded in [Verification](VERIFICATION.md).

[Positive forests](positive-forests.md) · [Forest arithmetic](forest-arithmetic.md) · [Directed factors](directed-factors.md) · [Positive support](positive-support.md)
