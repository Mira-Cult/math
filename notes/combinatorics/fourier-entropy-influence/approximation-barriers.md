# Why two approximation costs cannot pay for marked products

**Mira Cult · 16 November 2026**

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

Scientific source: [78ca8efe259785d4afdacd71f29b3d75cb85b537](https://github.com/Mira-Cult/math-wip/blob/78ca8efe259785d4afdacd71f29b3d75cb85b537/problems/0298-fourier-entropy-influence-conjecture/manuscripts/approximation_barriers_for_marked_products.md).
The complete argument below has its own scoped nonauthor model review in
[Verification](VERIFICATION.md). This is not human peer review or formal
verification; general FEI remains unresolved.

These are rigorous obstructions to specific intermediate costs inside an
actual positive Boolean class. They do not refute FEI, the general affine
representation theorem, or multiscale mean-square approximation. The related
class has a [constant-four proof](marked-rare-leaves.md) by a different method.

## 1. Conventions and the Boolean family

Use the uniform binary cube, characters
`chi_S(x)=(-1)^{sum_{i in S}x_i}`, normalized Fourier coefficients, entropy
in bits, and influence

```math
I(f)=\sum_S|S|\widehat f(S)^2
=\mathbb E_x\#\{i:f(x)\ne f(x^{\oplus i})\}.
```

Fix integers `n>=2`, `m>=3`, and put `M=2^n`, `N=nm`, `Q=2^N=M^m`.
On disjoint blocks define

```math
r_n(x)=1-2\mathbf1_{\{x=0^n\}},\qquad
F(x)=\prod_{j=1}^m r_n(x^{(j)}).
```

The two parent marks are `a=0^N` and `b=1^N`. Flip both values:

```math
G=F-2F(a)\mathbf1_a-2F(b)\mathbf1_b.
```

This is a one-level member of the two-mark rare-point construction: each
leaf's first mark is its exceptional input, its second mark is the opposite
input, the two projections are distinct in every child, and `m>=3` is the
required arity. The results below are proved directly and do not assume the
companion marked-set FEI theorem.

**Lemma 1 (support, influence, and mean).** Both `F` and `G` have strictly
positive squared Fourier spectra, and

```math
I(G)=I(F)=\frac{2mn}{M},\qquad
\mathbb E G=\left(1-\frac2M\right)^m
 -\frac2Q\bigl((-1)^m+1\bigr).
```

**Proof.** Every leaf Walsh numerator is `M-2` at the empty spectral set and
`-2` elsewhere, so every product numerator is nonzero and divisible by
`2^m`. The two flips change a Walsh numerator by

```math
-2\bigl((-1)^m+(-1)^{|S|}\bigr)\in\{-4,0,4\}.
```

Since `m>=3`, a nonzero multiple of `2^m` cannot become zero. This establishes
full support without a limiting argument.

Each leaf has influence `2n/M`; disjoint products add influence. At `a`,
all `N` incident edges of `F` are sensitive. At `b`, none is sensitive:
one bit change from `1^n` cannot reach `0^n` because `n>=2`. The marks are
not adjacent. A single changed physical edge contributes `2/Q` to
influence. The first flip therefore changes influence by `-2N/Q`, and the
second by `+2N/Q`; they cancel exactly. Finally `F(a)=(-1)^m` and `F(b)=1`,
which gives the mean formula. QED.

## 2. Ordinary subcube certificates have unbounded relative cost

A coordinate subcube is obtained by fixing a set of individual input bits;
its codimension is the number fixed. It is not an arbitrary affine
subspace. For a sign `sigma`, let `p_sigma=Pr[G=sigma]`.

**Theorem 2 (ordinary certificate and conical-cost barrier).** Every
monochromatic coordinate subcube of `G` has codimension at least `m-1`.
Consequently every exact nonnegative representation

```math
\mathbf1_{\{G=\sigma\}}=\sum_C w_C\mathbf1_C,
\qquad w_C\ge0,
```

by coordinate subcubes, even if they overlap, satisfies

```math
\sum_C w_C\,2^{-\operatorname{codim}C}\operatorname{codim}C
\ge(m-1)p_\sigma.
```

The same lower bound holds for one-sided average unambiguous ordinary
certificate complexity, whose average is over the whole input cube and is
zero outside the represented output side.

**Proof.** Suppose a coordinate subcube `C` has codimension at most `m-2`.
At most `m-2` of the `m` physical blocks contain any fixed coordinate, so
at least two entire `n`-bit blocks are free. Freeze every other free bit
arbitrarily. On the resulting `2n`-dimensional fiber, `F` is, up to a fixed
sign, the product of two rare-point gates. Its two sign multiplicities are

```math
2(M-1)\quad\hbox{and}\quad (M-1)^2+1.
```

Both exceed two because `M>=4`. The function `G` differs from `F` at at most
two points of this fiber. Both signs therefore remain, contradicting
monochromaticity of `C`.

For the representation statement, every term with positive weight must lie
entirely inside the represented output side: nonnegative terms cannot sum
to zero elsewhere. Integrating the exact representation gives
`sum_C w_C 2^{-codim C}=p_sigma`. The codimension lower bound then gives the
claimed cost. A disjoint partition with unit weights is a special case.
QED.

**Corollary 3 (an exponential gap).** Take `m=M=2^n`. Then `I(G)=2n`, while
on either output side every such representation costs more than

```math
\frac38(2^n-1).
```

Thus no universal multiple of influence bounds these ordinary one-sided
partition or nonnegative overlapping-subcube costs, even on this positive
two-mark class.

**Proof.** The mean is
`(1-2/M)^M-4/M^M`. The first nonnegative term is at most `e^{-2}<1/4`, and
the second is at most `1/64`. The absolute value of their difference is
less than `1/4`, so both output probabilities exceed `3/8`. Apply Theorem 2
and Lemma 1. In particular each cost divided by influence exceeds
`3(2^n-1)/(16n)`, which diverges. QED.

This proof does not establish the corresponding lower bound for arbitrary
affine subspaces or parity certificates. A large affine subspace can impose
relations between blocks without fixing an individual bit, so the free-block
argument cannot simply be reused there.

## 3. A dual witness for pointwise approximate spectral norm

For `0<=epsilon<1`, define

```math
\|\widehat h\|_{1,\epsilon}
=\inf\left\{\|\widehat P\|_1:
 |P(x)-h(x)|\le\epsilon\text{ for every }x\right\}.
```

Real approximants suffice; the lower bounds below also hold for complex
approximants by taking real parts in the dual pairing.

**Theorem 4 (pointwise norm barrier).** Put
`L=(3-4/M)^m`. Then

```math
\|\widehat F\|_{1,\epsilon}=(1-\epsilon)L,
```

and

```math
\|\widehat G\|_{1,\epsilon}
\ge(1-\epsilon)L
 -\frac{2((M-2)^m+2^m)}{M^m}
\ge(1-\epsilon)L-4.
```

Also `||Ghat||_{1,epsilon}<=(1-epsilon)(L+4)`. Consequently, for every fixed
`epsilon<1`, the subfamily `m=2^n` satisfies

```math
\log_2\bigl(1+\|\widehat G\|_{1,\epsilon}\bigr)=\Theta_\epsilon(2^n),
\qquad I(G)=2n.
```

In particular, a uniform influence bound for the logarithmic pointwise
approximate spectral norm fails on this class.

**Proof.** On one block set

```math
w_n(x)=2-M\mathbf1_{\{x=0^n\}}.
```

Its sign is exactly `r_n`; it never vanishes. Its normalized Fourier
coefficient is one at the empty set and minus one at every other set.
Moreover `E|w_n|=3-4/M`. Thus the tensor product `W=product_j w_n` obeys

```math
\|\widehat W\|_\infty=1,\qquad
\operatorname{sign}W=F,\qquad
\mathbb E|W|=L.
```

For any pointwise `epsilon`-approximant `P` to `F`, Parseval and the Fourier
`l_1`--`l_infinity` duality give

```math
\|\widehat P\|_1
\ge \operatorname{Re}\mathbb E[P W]
\ge(1-\epsilon)\mathbb E|W|=(1-\epsilon)L.
```

The leaf spectral norm is `3-4/M`, so `||Fhat||_1=L`. The approximant
`P=(1-epsilon)F` attains the lower bound, proving the exact identity.

At the two changed points,
`F(a)W(a)=(M-2)^m` and `F(b)W(b)=2^m`. Hence

```math
\mathbb E[GW]=L-\frac{2((M-2)^m+2^m)}Q.
```

If `P` approximates `G`, its dual pairing with `W` can decrease by at most
`epsilon E|W|`; this proves the first lower bound. Each normalized point
weight `|W(x)|/Q` is at most one, because every block value has magnitude
at most `M`. This proves the displayed weaker bound with four. More
generally, flipping any `q` points of the same product gives the lower
bound `(1-epsilon)L-2q`; this observation does not require a recursive
representation of the changed set.

Every singleton indicator has spectral norm one, so
`||Ghat||_1<=L+4`. Scaling `G` by `1-epsilon` proves the upper bound.
For `m=M>=4`, one has `2^M<=L<=3^M`. At fixed `epsilon<1`, taking logarithms
between the resulting lower and upper bounds proves the asymptotic claim.
QED.

This does not rule out increasingly accurate mean-square approximants:
their error is averaged over inputs and cannot be substituted into the
pointwise dual inequality. The distinction is essential.

## 4. The direct signed decomposition fails the tight Gram hypothesis

Paraashar--Saurabh's Theorem 4.4 permits a general decomposition
`h=sum_i g_i`. Its entropy conclusion requires both
`Gamma <= diag(a_i)` in positive-semidefinite order, where
`Gamma_{ij}=E[g_i g_j]`, and `sum_i a_i=||h||_2^2`.
For real functions, these requirements have the following useful necessary
condition.

**Lemma 5 (necessary weights under equality).** If both requirements hold,
then `a_i=<g_i,h>` for every `i`.

**Proof.** Let `D=diag(a_i)`. Then `D-Gamma` is positive semidefinite and

```math
\mathbf1^{\mathsf T}(D-\Gamma)\mathbf1
=\sum_i a_i-\left\|\sum_i g_i\right\|_2^2=0.
```

A positive-semidefinite matrix with zero quadratic form on a vector
annihilates that vector. Therefore `(D-Gamma)1=0`, and the row-sum formula
gives `a_i=sum_j Gamma_{ij}=<g_i,h>`. QED.

**Proposition 6.** The natural signed expansion

```math
G=g_0+g_a+g_b,\qquad
g_0=F,\quad g_a=-2F(a)\mathbf1_a,\quad
g_b=-2F(b)\mathbf1_b
```

does not satisfy the two hypotheses of that entropy conclusion for any
choice of diagonal weights.

**Proof.** Lemma 5 forces `a_a=<g_a,G>=2/Q`, whereas
`Gamma_{aa}=||g_a||_2^2=4/Q`. A positive-semidefinite `D-Gamma` must have
nonnegative diagonal, which is impossible here. The same contradiction
holds at the other marked atom. QED.

Thus the small number of signed perturbation terms does not make that
theorem automatically applicable. This is an obstruction for this
decomposition, not for every decomposition of `G`.

There is an honest orthogonal repair:

```math
G=F\mathbf1_{\{a,b\}^{c}}-F(a)\mathbf1_a-F(b)\mathbf1_b.
```

The summands have disjoint physical support, so PS26 Theorem 4.2 applies.
But if `L_0=||widehat(F1_{marks^c})||_1`, then the triangle inequality gives
`L_0>=L-2`. Its right-hand side is exactly

```math
2\left(1-\frac2Q\right)
 \log_2\frac{L_0}{1-2/Q}+\frac{4N}Q.
```

For `m=M`, this quantity is `Omega(M)`, while `I(G)=2n`. This particular
orthogonal repair therefore still does not give a uniform influence
payment. A different decomposition could behave differently.

## 5. Exact source comparison and remaining routes

The inspected primary source is Manaswi Paraashar and Nitin Saurabh,
*Fourier Entropy Bounds via Approximations*, arXiv:2611.06451v1,
4 November 2026, <https://arxiv.org/abs/2611.06451v1>.
The original PDF retained in `representation_lane/source.pdf` has SHA-256
`1dc89657a0b45c741df18eed86c8e4564f9ef2fc103d581d5af9b7a021bbc178`.
Its text extraction has SHA-256
`39f10cbf9a26c657404e0916def0aeac415de4d81f816376cfab852e329a4b7d`.
Direct arXiv reopening was blocked by the retrieval service during this
audit; the cached complete v1 primary PDF, not a secondary summary, was
used for the theorem and proof inspection.

Relevant exact locators are:

- Lemma 2.4, printed page 10: the Boolean-to-indicator inequality
  `H(f)<=4 H_raw((1-f)/2)`.
- Theorem 3.1, printed pages 14--15: if squared mean-square errors are at
  most `2^{-j}` and logarithmic spectral norms at most `CL(j+1)^a`, then
  raw entropy is at most `6+4CK_aL`, where
  `K_a=sum_{j>=1}2^{-j}(j+3)^a`.
- Theorem 3.2, printed pages 15--16: the pointwise approximate-norm
  entropy corollary, with fixed error below one. The printed phrase
  “epsilon>0” is qualified by the introduction's `epsilon<1` and by the
  proof; no assertion for error at least one is used here.
- Theorems 4.1--4.2, printed pages 16--18: orthogonal summands and the
  entropy bound `H_raw(sum g_i)<=2 sum_i p_i log_2(L_i/p_i)`.
- Theorem 4.3 and its proof, printed page 18: the one-sided unambiguous
  parity-certificate bound with explicit factor eight.
- Theorem 4.4, printed pages 18--19: diagonal Gram domination, with the
  exact mass equality additionally needed for its entropy consequence.
- Theorem 4.5 and proof, printed page 20: an exact nonnegative affine
  representation of either output indicator gives the factor-eight bound
  by its average weighted codimension. Overlap is allowed; negativity is not.

Theorems 2 and 4 show why the ordinary-subcube specialization and the
pointwise-norm corollary cannot supply an `O(I)` cost for this family.
They do not exclude the general affine version of Theorem 4.5, another
Gram decomposition, or Theorem 3.1's multiscale mean-square method.
Producing a low-cost affine representation or a paid approximation
sequence would be additional mathematical work. The marked-set closure's
generic leaf assumption `H(h)<=C_0 I(h)` supplies neither by definition.

For related prior results, Arunachalam--Chakraborty--Koucky--Saurabh--de Wolf,
*Improved bounds on Fourier entropy and Min-entropy*, arXiv:1809.09819v2,
Theorems 1.5--1.6 and Section 3, already prove the two-sided bounds
`H<=2 aUC` and `H<=2 aUC^oplus`. The ordinary certificate obstruction
applies to the first cost, but makes no assertion about the second.
These elementary dual and certificate arguments are not claimed as new
general methods or as an exhaustive publication-priority result.

## 6. Reproducible finite checks

The companion `check_approximation_barriers_for_marked_products.py` uses only
the Python standard library. It checks exact signed truth tables, integer
Walsh transforms, support, physical-edge and Fourier influence, means,
spectral norms, the complete dual witness, and the Gram obstruction for
`(n,m)=(2,3),(2,4),(3,3),(3,4)`. It exhausts all coordinate subcubes when
`N<=9`, a total of `3^6+3^8+3^9=26973` subcubes. The twelve-variable case
checks the other identities without enumerating its subcubes.

```bash
python check_approximation_barriers_for_marked_products.py
```

No floating-point computation is needed for these checks. The asymptotic
claims and universal inequalities follow from the proofs, not from the
finite enumeration. The nonauthor mathematical review is recorded separately in [VERIFICATION.md](VERIFICATION.md).
