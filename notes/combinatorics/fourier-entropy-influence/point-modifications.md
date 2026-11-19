# Uniform FEI for recursive products with point modifications

**Mira Cult · 16 November 2026**

Recursive disjoint products followed by a modification at one physical point
satisfy a uniform FEI bound with constant $`9/2`$ when the leaves are
rare-point gates on at least two variables. The same constant works for all
depths, node arities, leaf sizes, and total dimensions. A general closure
theorem also converts any positive Boolean leaf class with constant $`C_0`$
into a recursive class with constant $`3C_0/2+17`$.

These classes include spectra with unavoidable interaction arity equal to the
total dimension. They do not contain every Boolean function and do not
resolve general FEI. No publication-priority claim is made solely from
spectral interaction size.

**Review status.** Complete proofs with scoped nonauthor model review of the
scientific revision. The review scope, exact revisions, and limitations are
recorded in [Verification](VERIFICATION.md); this is not human peer review.

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

Scientific source: [math-wip at a17f79e](https://github.com/Mira-Cult/math-wip/blob/a17f79e858c8537587a8d49e2b879f10c59e7677/problems/0298-fourier-entropy-influence-conjecture/manuscripts/recursive_point_interference.md).

## 1. The Boolean class and theorem

All inputs are independent uniform signs; entropy is in bits and influence is
$`I(h)=\sum_S|S|\widehat h(S)^2`$. Each function below has a distinguished physical
input, chosen to be the all-positive point. Physical coordinate complements
allow arbitrary marked points without changing the theorem.

Start with rare-point gates on any number $`n\ge 2`$ of inputs,

```math
r_n(x)=1-2\mathbf1_{\{x=(1,\ldots,1)\}}.
```

Construct new functions recursively as follows. Take any $`m\ge 2`$ previously
constructed functions $`h_1,\ldots,h_m`$ on pairwise disjoint blocks of sizes
$`n_1,\ldots,n_m`$, set $`N=\sum_j n_j`$, and write

```math
F(x)=\prod_{j=1}^m h_j(x^{(j)}),\qquad
c=F(1,\ldots,1),\qquad
G(x)=F(x)-2c\mathbf1_{\{x=(1,\ldots,1)\}}.
```

The new function's distinguished point is the point just modified. Each
construction is finite, but there is no common bound on its depth, on $`m`$, on
leaf sizes, or on $`N`$.

**Theorem 1.** Every function $`h`$ in this class has strictly positive Fourier
spectrum and satisfies

```math
\boxed{H(h)\le\frac92 I(h).}
```

This is a uniform theorem: there exists the single constant $`9/2`$ such that
the inequality holds for every permitted construction and dimension.
Constants and parity characters also satisfy the inequality trivially, but
are not part of this recursive definition because the proof uses positive
spectra. No assertion is made for arbitrary zero-support extensions.

The class can equivalently be described by a rooted tree of disjoint physical
blocks: its phase is the parity of the all-positive point indicators for all
nodes, where each internal node is the union of its children and every leaf
has at least two coordinates. These node sets form a laminar family. This
description is not a claim that arbitrary laminar sign patterns or arbitrary
overlapping families satisfy the theorem.

## 2. The signed point score

For a Boolean function $`h`$ on $`n`$ bits with positive spectrum, a distinguished
point $`x`$, and $`c=h(x)`$, put

```math
\begin{aligned}
B_h(x)
&=c\sum_S\widehat h(S)\chi_S(x)\log_2\widehat h(S)^2
  -2^{-n}\sum_S\log_2\widehat h(S)^2,\\
s_h(x)&=\#\{i:h(x)\ne h(x^{\oplus i})\},\\
t_h(x)&=n-2s_h(x),\qquad \delta_n=2^{1-n}.
\end{aligned}
```

All logarithms are finite because every coefficient is nonzero. The sum in
$`B_h`$ is signed; it is not an entropy of a probability distribution. Its role
is to record the exact cross-entropy change of a physical point modification.

If $`h=\prod_jh_j`$ on disjoint blocks and $`x=(x_1,\ldots,x_m)`$, then

```math
H(h)=\sum_jH(h_j),\quad I(h)=\sum_jI(h_j),\quad
B_h(x)=\sum_jB_{h_j}(x_j),\quad t_h(x)=\sum_jt_{h_j}(x_j).
```

The first two identities follow from the product Fourier law. Sensitivities
add because a coordinate changes the product exactly when it changes its own
factor. For the score, expand $`\log p_h=\sum_j\log p_{h_j}`$ and use
$`\sum_S\widehat h_j(S)\chi_S(x_j)=h_j(x_j)`$ in all other blocks. The uniform spectral
average of that logarithm also adds.

## 3. Exact identities for one point modification

Let $`g=h-2c\mathbf1_x`$ on $`n`$ bits, where $`c=h(x)`$. Then

```math
\widehat g(S)=\widehat h(S)-c\delta_n\chi_S(x).
```

Suppose both spectra are positive. Expanding squared coefficients and using
the definition of relative entropy gives

```math
\boxed{H(g)=H(h)+2\delta_nB_h(x)-D_2(p_g\Vert p_h).}
```

To verify the normalization, $`p_g-p_h=-2c\delta_n\widehat h(S)\chi_S(x)+\delta_n^2`$.
Thus the change of cross-entropy against $`p_h`$ is

```math
2c\delta_n\sum_S\widehat h(S)\chi_S(x)\log_2p_h(S)
 -\delta_n^2\sum_S\log_2p_h(S)
=2\delta_n B_h(x),
```

since $`\delta_n^2=2\delta_n2^{-n}`$. Subtract
$`D_2(p_g\Vert p_h)`$ to obtain the identity. This accounts for all interference
terms from the point modification.

Only the $`n`$ physical edges incident to $`x`$ change sensitivity, and each
contributes $`\delta_n`$ to probability-of-flip influence. Therefore

```math
I(g)=I(h)+\delta_n t_h(x),\qquad t_g(x)=-t_h(x).
```

The score also has a useful exact transformation. Define the aligned
unnormalized Walsh integers

```math
A_S=c\chi_S(x)\,2^n\widehat h(S).
```

Fourier inversion gives $`\sum_SA_S=2^n`$. Consequently

```math
B_h(x)=2^{1-n}\sum_S(A_S-1)\log_2|A_S|.
```

After the flip, the new output at $`x`$ is $`-c`$; alignment with that new output
gives $`A'_S=2-A_S`$. Hence

```math
B_g(x)=-B_h(x)+R_h(x),\qquad
R_h(x)=2^{1-n}\sum_S(A_S-1)
             \log_2\left|\frac{A_S}{A_S-2}\right|.
```

## 4. The arithmetic payment

**Lemma 2.** If every aligned Walsh integer $`A_S`$ is a nonzero multiple of
four, the point-modified spectrum is positive and

```math
0\lt R_h(x)\le6.
```

**Proof.** Every changed unnormalized coefficient is congruent to two modulo
four, so it is nonzero. For a nonzero integer $`A`$ divisible by four, put
$`z=A-1`$; then $`|z|\ge 3`$. The scalar expression in the sum is

```math
z\log_2\left|\frac{z+1}{z-1}\right|
=\frac2{\ln2}\sum_{k=0}^{\infty}
       \frac{|z|^{-2k}}{2k+1}.
```

This is positive and decreases with $`|z|`$. At $`|z|=3`$ it equals
$`3 \log_2 2=3`$, so it is at most three. There are $`2^n`$ summands and the
prefactor is $`2^{1-n}`$, proving $`R\le 6`$. QED.

Every rare-point leaf has all Walsh coefficients nonzero and congruent to
two modulo four. At an internal node, the unnormalized Walsh coefficients
of the disjoint product are products of the children's coefficients. Each
child has at least two coordinates and every Boolean Walsh numerator is
even. With at least two children, the product is therefore divisible by
four; positivity makes it nonzero. Lemma 2 applies and the output again has
positive spectrum. This proves the support assertion inductively.

There is no integer-denominator reparameterization in this argument. The
integer information used is the actual Walsh numerator of the Boolean
product, and its point modification is an actual Boolean function.

## 5. An invariant that survives unbounded arity

Set

```math
C=\frac92,\qquad \alpha=\frac47,\qquad
M_h=C I(h)-H(h),\qquad U_h=2B_h-Ct_h.
```

We prove the stronger pointed inequality

```math
\boxed{M_h\ge\delta_n\left(\alpha+\frac{|U_h|}{3}\right).}
```

The right side is positive, so this implies Theorem 1.

Assume the invariant for all children of an internal node, and put
$`\delta=2^{1-N}`$. Product identities and the point-modification formulas give

```math
\begin{aligned}
U_G&=-\sum_j U_{h_j}+2R_F,\\
M_G&=\sum_jM_{h_j}-\delta\sum_jU_{h_j}
              +D_2(p_G\Vert p_F).
\end{aligned}
```

Every child omits at least two coordinates, so $`n_j\le N-2`$ and
$`\delta_{n_j}\ge4\delta`$. Nonnegativity of relative entropy therefore yields

```math
M_G\ge\delta\left[
4m\alpha+\frac43\sum_j|U_{h_j}|-\sum_jU_{h_j}
\right].
```

On the other hand $`0<R_F\le 6`$ implies

```math
\alpha+\frac{|U_G|}{3}
\le\alpha+\frac13\sum_j|U_{h_j}|+4.
```

The difference of the two bracketed upper/lower targets is

```math
(4m-1)\alpha-4
 +\sum_j\bigl(|U_{h_j}|-U_{h_j}\bigr)\ge0,
```

because $`m\ge 2`$ and $`7 \alpha=4`$. This proves closure with the same constants
for every arity and depth. The crucial payment is local: the child point
probability is at least four times the parent point probability, while the
Walsh arithmetic bounds the new score correction by six independently of
dimension. No count of factors, no width factor, and no unpaid label appears.

## 6. Verification at every leaf

For a rare-point leaf $`r_n`$, write $`\epsilon=2^{1-n}`$, so $`\delta_n=\epsilon`$.
Its distinguished value is $`-1`$, every coordinate is sensitive there, and

```math
\begin{aligned}
I(r_n)&=n\epsilon,& t_{r_n}&=-n,\\
B_{r_n}&=-(2-\epsilon)\log_2\frac{1-\epsilon}{\epsilon},\\
H(r_n)&=-2(1-\epsilon)^2\log_2(1-\epsilon)
 +(2\epsilon-\epsilon^2)(2n-2).
\end{aligned}
```

The score follows by using the empty coefficient $`1-\epsilon`$ and all other
coefficients $`-\epsilon`$ in its definition. Since
$`\log_2((1-\epsilon)/\epsilon)\le n-1`$, one has

```math
U_{r_n}=2B_{r_n}+Cn\ge (C-4)n+4\gt 0.
```

The pointed invariant is thus equivalent to

```math
C\ge C_n^{\rm leaf}
:=\frac{3H(r_n)/(2\epsilon)+B_{r_n}+6/7}{n}.
```

For $`n=2`$, direct substitution gives $`H=2`$, $`\epsilon=1/2`$, $`B=0`$, and
$`C_2^{\mathrm{leaf}}=24/7<9/2`$.

For $`n\ge 3`$, elementary simplification gives

```math
C_n^{\rm leaf}
=4+\frac{
-22/7-2\epsilon(n-1)
 -(3/\epsilon-4+2\epsilon)\log_2(1-\epsilon)
}{n}.
```

The coefficient of the last logarithm is positive. Using
$`-\ln(1-\epsilon)\le\epsilon/(1-\epsilon)`$ and $`\epsilon\le 1/2`$,

```math
\begin{aligned}
&-(3/\epsilon-4+2\epsilon)\log_2(1-\epsilon)\\
&\qquad\le\frac{3-4\epsilon+2\epsilon^2}{(1-\epsilon)\ln2}
 =\frac{2(1-\epsilon)+(1-\epsilon)^{-1}}{\ln2}
 \le\frac3{\ln2}\lt \frac92.
\end{aligned}
```

The penultimate inequality holds because $`2u+1/u\le 3`$ on $`1/2\le u\le 1`$
(equivalently $`(2u-1)(u-1)\le 0`$). The last inequality uses $`\ln2>2/3`$, which
follows from strict convexity of $`1/t`$ and its average on $`[1,2]`$.
Discarding the nonpositive term $`-2\epsilon(n-1)`$ gives

```math
C_n^{\rm leaf}\lt 4+\frac{19}{14n}
\le4+\frac{19}{42}\lt \frac92
\qquad(n\ge3).
```

Thus the invariant holds at every leaf and, by Section 5, at every internal
node. This completes the proof of Theorem 1.

## 7. Strictly unbounded interaction size

The one-level subfamily consisting of a product of rare-point leaves followed
by one point modification has the stronger sharp inequality $`H\le4I`$, proved
in [one-point-products.md](one-point-products.md). That companion proof also establishes
that its full $`N`$-coordinate mixed difference of $`\log p`$ is nonzero. Hence
there is no positive spectral factorization whose arity is below $`N`$, and
its conditional-dependence graph is complete.

For example, use $`m=a2^{n-1}`$ equal $`n`$-bit leaves ($`n\ge 3`$, integer $`a\ge 1`$)
at one node. Then

```math
N=an2^{n-1},\qquad I=an-N2^{1-N},\qquad
0\lt |\mathbb E h|\le e^{-a},\qquad \max_Sp_h(S)\le e^{-2a}.
```

For fixed $`a`$, influence is $`\Theta(\log N)`$ despite necessary arity $`N`$ and
treewidth $`N-1`$. Taking $`a=n`$ makes the mean and maximum atom vanish. The
recursive theorem contains this family and allows its members, and arbitrary
other members of the class, to appear as children of further point-modified
products. Its uniformity is not obtained by fixing a width before choosing
the FEI constant.

## 8. What the theorem does and does not transfer

The construction uses disjoint blocks when taking a product, but the following
point modification depends on all original physical variables. At a deeper
node its point indicator need not be a function of the child outputs: those
outputs do not generally identify their distinguished physical points.
Consequently ordinary Boolean disjoint-gate composition does not automatically
prove the recursive result. This observation alone does not prove publication
novelty; prior classes, tree automata, and laminar formula results still require
comparison. In the one-level two-child case the outer operation is a familiar
read-once Boolean operation, so no first FEI theorem is claimed for that case.

What makes the present closure work is the signed score, its exact
cross-entropy identity, a universal arithmetic correction after a point flip,
and a pointed entropy margin. The same formulas hold more generally for
positive-spectrum functions, but neither the leaf invariant nor a recursive
representation of arbitrary Boolean functions has been proved. Assigning
arbitrary functions as leaves would assume essentially the missing entropy
bound, not solve it.

Allowing one-coordinate leaves would also invalidate the present proof:
their spectra have zeros, the signed logarithmic score is not defined, and
the factor-four ratio between child and parent point probabilities can fail.
These are explicit scope conditions, not a zero-support theorem.

The constant $`9/2`$ is a convenient analytic bound for the invariant, not a
claim of optimality for the recursive class. The scoped nonauthor model
review recorded in [Verification](VERIFICATION.md) addresses the signed score,
Fourier normalization, positive support, pointwise sensitivity, and the fact
that no coefficient in the induction depends on node arity.

## 9. A general closure theorem for positive Boolean leaf classes

The preceding induction is not restricted to rare-point leaves. A universal
bound on the point score converts an ordinary FEI bound for an arbitrary
positive Boolean leaf class into the stronger invariant needed for closure.
The estimate in this section was supplied by the coordinating researcher
and audited by the author of the point-score argument, as credited in the
scientific source. That collaboration is distinct from the subsequent
nonauthor model review recorded in [Verification](VERIFICATION.md).

**Lemma 3 (universal pointed envelope).** Let $`h`$ be any Boolean function on
$`n\ge 2`$ bits with positive spectrum, and let $`x`$ be any physical point. Then

```math
\delta_n|B_h(x)|\le16I(h),\qquad n\delta_n\le I(h).
```

**Proof.** Put $`M=2^n`$, and after an output sign change let $`m`$ be the number
of minority truth-table points, so $`1\le m\le M/2`$. Full support excludes constants
and exactly balanced functions, but the following estimates can retain the
weak endpoint bound $`m\le M/2`$.

Every nonzero Walsh numerator is an even integer. Therefore
$`2^{1-n}\le|\widehat h(S)|\le1`$, and

```math
|B_h(x)|\le2(n-1)(\|\widehat h\|_1+1).
```

Parseval gives $`\lVert\widehat h\rVert_1\le\sqrt M`$. Also write
$`h=1-2\sum_{y\in A}\mathbf1_y`$ for the minority set $`A`$. A single physical point
indicator has Fourier $`L_1`$ norm one, so the triangle inequality gives
$`\lVert\widehat h\rVert_1\le1+2m`$. Consequently

```math
\delta_n|B_h(x)|
\le\frac{4n}{M}\left(\min\{\sqrt M,1+2m\}+1\right).
```

The cube edge-isoperimetric inequality, with probability-of-flip influence,
states

```math
I(h)\ge\frac{2m}{M}\log_2\frac{M}{m}.
```

For completeness, the underlying edge bound
$`|\partial A|\ge m\log_2(M/m)`$ follows by induction on dimension. If the two
halves have sizes $`a,b`$, their internal boundaries contribute at least
$`a\log_2((M/2)/a)+b\log_2((M/2)/b)`$, and cross edges contribute at least
$`|a-b|`$. On writing $`t=\min(a,b)/(a+b)\le1/2`$, the excess over the desired bound
is $`(a+b)(h_2(t)-2t)\ge0`$, by concavity of binary entropy between $`0`$ and
$`1/2`$. The empty-set case is immediate. Multiplying the unoriented edge
boundary by $`2/M`$ gives the displayed influence normalization.

If $`m\le\sqrt M`$, then $`\log_2(M/m)\ge n/2`$ and

```math
\delta_n|B_h(x)|\le\frac{16nm}{M}\le16I(h).
```

Here $`2m+2\le 4m`$ uses $`m\ge 1`$.

If $`m\ge\sqrt M`$, the score bound is at most $`8n/\sqrt M`$. The function
$`2u\log_2(1/u)`$ is concave on $`(0,1)`$. On
$`u=m/M\in[1/\sqrt M,1/2]`$ it is bounded below by the smaller endpoint value,
so

```math
I(h)\ge\min\{n/\sqrt M,1\}\ge\frac{n}{2\sqrt M}.
```

The last step uses $`n\le2\sqrt M`$, valid for every integer $`n\ge 2`$ (it follows
by induction from $`n^2\le 4\cdot 2^n`$). This again proves the factor sixteen.

Finally the same concavity on $`u\in[1/M,1/2]`$ gives
$`I(h)\ge\min(2n/M,1)=2n/M=n\delta_n`$, since $`2n\le 2^n`$ for $`n\ge 2`$. QED.

**Theorem 4 (uniform point-modification closure).** Let $`C_0\ge 0`$. Let
$`\mathcal A`$ be any collection of positive-spectrum Boolean functions, each
on at least two bits and with an arbitrary distinguished physical point,
such that every $`h\in\mathcal A`$ satisfies

```math
H(h)\le C_0 I(h).
```

Close this class under the recursive disjoint-product followed by a
distinguished-point modification from Section 1. Every resulting function has
positive spectrum and satisfies

```math
\boxed{H(g)\le\left(\frac32 C_0+17\right)I(g).}
```

The constant applies simultaneously to all finite construction trees, all
leaf dimensions, all depths, and all node arities. It is paid once, not once
per level.

**Proof.** Put $`C=(3/2)C_0+17`$, retain $`\alpha=4/7`$, and use the same invariant
with $`M_h=C I(h)-H(h)`$ and $`U_h=2B_h-Ct_h`$. At a leaf, Lemma 3 and
$`|t_h|\le n`$ give

```math
\begin{aligned}
\delta_n\left(\alpha+\frac{|U_h|}{3}\right)
&\le\left(\frac\alpha2+\frac{32}3+\frac C3\right)I(h),\\
M_h&\ge(C-C_0)I(h).
\end{aligned}
```

The first line uses $`\delta_n\le I(h)/n\le I(h)/2`$. The difference of the two
coefficients is exactly

```math
(C-C_0)-\left(\frac\alpha2+\frac{32}3+\frac C3\right)
=\frac8{21}\gt 0.
```

Thus every leaf satisfies the pointed invariant. The proof in Sections 3--5
applies without any additional leaf structure and without any change in $`C`$.
Positive support follows because an internal product has nonzero Walsh
numerators divisible by four. QED.

For example, if a separately proved positive Boolean leaf class has constant
four, its entire recursive closure has the single constant twenty-three.
If its constant is below fourteen, the closure constant is below thirty-eight.
This permits the bounded-width or bounded-arity theorems from the checkpoint
to be used as leaf theorems while subsequent point modifications create
unbounded, unavoidable spectral interactions. The hypotheses and constant of
the chosen leaf theorem must still be verified: this is not permission to
insert an arbitrary positive Boolean function as a leaf.

The closure theorem and the sharper rare-point theorem use the same structural
mechanism. The former pays a universal price for preparing an arbitrary
already-controlled positive Boolean leaf; the latter proves a tighter
pointed invariant directly and obtains $`9/2`$ instead of twenty-three.


## Reproducible checks

The accompanying [exact checker](code/check_recursive_point_interference.py) is mirrored without
changes from the scientific revision. From this note's directory, run:

```bash
python code/check_recursive_point_interference.py
```

Finite checks verify the identities and examples specified by the checker;
the proofs above establish the universal statements.
Exact runs and review qualifications are recorded in [Verification](VERIFICATION.md).

[Sharp one-point products](one-point-products.md) · [Directed factors](directed-factors.md) · [Affine forest images](affine-forests.md) · [Positive support](positive-support.md)
