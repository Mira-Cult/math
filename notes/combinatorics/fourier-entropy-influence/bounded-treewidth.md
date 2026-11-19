# Fourier entropy for positive spectra of bounded treewidth

**Mira Cult · 16 November 2026**

Every Boolean function whose positive Fourier distribution factors over a graph
of treewidth at most two satisfies $`H(f)<14I(f)`$ when its influence is positive.
The same bound holds for integer-valued functions, using raw Fourier entropy.
More generally, each fixed treewidth has a dimension-independent constant.
Triangle potentials may depend genuinely on all three bits: the result does not
require pairwise factorization or powers-of-two Fourier magnitudes.

The proof retains bounded-size factors and pays their local entropy using both
amplitude growth and coordinate influence. This removes the unpaid feedback-cut
cost in the earlier treewidth-two attack. General FEI, and constant four for the
entire positive pairwise treewidth-two class, remain open here.

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

## 1. Statements and normalization

All logarithms are base two unless written $`\ln`$. On the uniform sign cube,
write

```math
h(x)=\sum_s\widehat h(s)\chi_s(x),\qquad
H_{\mathrm{raw}}(h)=\sum_s\widehat h(s)^2\log_2\frac1{\widehat h(s)^2},
\qquad I(h)=\sum_s |s|\widehat h(s)^2,\qquad W(h)=\mathbb E h^2.
```

Zero coefficients contribute zero. Raw entropy can be negative. With the
half-difference derivative $`D_i h(x)=(h(x)-h(x^i))/2`$, Parseval gives
$`I(h)=\sum_i\mathbb E(D_i h)^2`$. For Boolean functions, $`W(h)=1`$ and
these are the usual Fourier entropy and total influence.

A **positive graphical law** is positive at every binary vector and factors,
after normalization, into positive potentials on graph cliques. A graph has
treewidth at most $`w`$ if it has a chordal completion with a perfect elimination
order whose later-neighbor sets have size at most $`w`$; equivalently, it has a
tree decomposition with bags of size at most $`w+1`$.

**Theorem 1 (positive treewidth two).** Let $`h`$ be integer-valued, with every
Fourier coefficient nonzero. If its normalized squared Fourier law factors over
a graph of treewidth at most two, then

```math
H_{\mathrm{raw}}(h)\le C_2 I(h),\qquad
C_2=\frac{2(2+\log_2 23)}{\log_2(23/12)}
=13.9006301761\ldots<14.
```

In particular, $`H(f)\le14I(f)`$ for every Boolean function with that spectral
structure. The theorem allows arbitrary positive potentials on triangle bags.
There is no dependence on degree, dimension, variance, number of cycles,
interaction strength, or the size of the integer values of $`h`$.

**Theorem 2 (every fixed treewidth).** Under the corresponding hypothesis with
treewidth at most $`w`$, put $`r=w+1`$. Choose $`t>r`$ and $`q>0`$ such that

```math
d_q=1-\log_2(1+2^{-q})\ge\frac rt,
\qquad B_t=\max\left(1,\frac{4^t}{2et\ln2}\right).
```

Then

```math
H_{\mathrm{raw}}(h)\le \frac{2(B_t+q)}{d_q}I(h).
```

The choices $`t=r+1`$ and $`q=\log_2(2(r+1))`$ always work. Their constant is
$`O(4^{w+1}/(w+1)+\log(w+2))`$. It is independent of dimension for each fixed
$`w`$, and is not a universal FEI constant.

Both theorems also hold whenever the positive integer Walsh magnitude tensor
admits positive integer factors of arity at most three, respectively $`r`$,
even if the graph of those factors has unbounded treewidth. Bounded treewidth
is used to obtain the factorization, not in the entropy estimate.

The [forest and cactus theorems](cycles-and-cacti.md) retain the stronger
constant four on their respective classes. The present argument bypasses the
feedback-cut remainder $`2(k-1-b)`$; it does not improve that remainder by
counting more surviving components.

## 2. Integer factorization along an elimination order

**Lemma 3.** Let $`A:\{0,1\}^n\to\mathbb Z_{>0}`$ factor over a graph of
treewidth at most $`w`$. There are a positive integer $`c`$ and positive
integer-valued factors $`u_\alpha`$, each on at most $`r=w+1`$ coordinates,
such that

```math
A(s)=c\prod_\alpha u_\alpha(s_\alpha).
```

**Proof.** Fix a chordal completion and a perfect elimination order. At one
step, let $`i`$ be the next coordinate, $`B`$ its later neighbors, and $`t`$
all remaining coordinates. The current positive integer tensor still factors
on the remaining chordal graph. Its ratio $`A(0,t)/A(1,t)`$ depends only on
$`t_B`$: factors not involving $`i`$ cancel, and every factor involving $`i`$
uses only $`\{i\}\cup B`$.

For each assignment $`b`$ to $`B`$, write this rational ratio in lowest terms
as $`u(0,b)/u(1,b)`$, with coprime positive integers. It follows that

```math
A(s_i,t)=u(s_i,t_B)M(t),\qquad
M(t)=\gcd(A(0,t),A(1,t)).
```

Thus $`M`$ is positive and integer. It still factors on the remaining chordal
graph: combine the factors involving $`i`$ into a function of
$`\{i\}\cup B`$ and divide that function by $`u`$. The quotient depends
only on $`B`$, which is a clique, so it is an allowed remaining factor.
Iterating produces the claimed factors and a final positive integer scalar.
For $`n=0`$ only the scalar remains. ∎

For an integer-valued function, $`A(s)=2^n|\widehat h(s)|`$ is an integer
because the unnormalized Walsh transform is a sum of integers. Taking positive
square roots of the graphical potentials factors $`A`$ up to a scalar.
Consequently Lemma 3 applies without excluding odd primes or assuming that
Walsh magnitudes are powers of two.

## 3. A local entropy inequality with an influence payment

For positive $`a,b`$, define the uniform two-point entropy in bits by

```math
\mathrm{Ent}_2(a^2,b^2)
=\frac{a^2}{2}\log_2\frac{2a^2}{a^2+b^2}
 +\frac{b^2}{2}\log_2\frac{2b^2}{a^2+b^2}.
```

**Lemma 4.** If $`U,V`$ are positive integers and $`a/b=U/V`$, then

```math
\mathrm{Ent}_2(a^2,b^2)
\le\frac5{32}a^2\log_2 U+b^2.
```

The asymmetry is deliberate: $`b`$ will be the amplitude at the endpoint whose
spectral coordinate is one, so $`b^2`$ is paid by that coordinate's influence.

**Proof.** Define

```math
F(y)=y\log_2\frac{2y}{1+y}+\log_2\frac2{1+y},\qquad F(0)=1.
```

Then $`2\mathrm{Ent}_2(a^2,b^2)/b^2=F(y)`$ for
$`y=(a/b)^2\le U^2`$. The function

```math
G_U(y)=F(y)-\frac5{16}y\log_2 U
```

is convex, since $`F''(y)=1/((\ln2)y(1+y))>0`$. Its maximum on
$`[0,U^2]`$ is attained at an endpoint. The first endpoint is one. For
$`U\ge10`$, the inequalities $`10^5>2^{16}`$ and $`F(U^2)\le U^2`$
give $`G_U(U^2)\le0`$.

For $`U=1,\ldots,9`$, the assertion $`G_U(U^2)\le2`$ is exactly

```math
2^{16(U^2-1)}U^{27U^2}\le(U^2+1)^{16(U^2+1)}.
```

The table records the integer floor of the right side divided by the left
side. Every entry is at least one, giving nine exact certificates.

| $`U`$ | Floor of right side / left side |
|---|---:|
| 1 | 4294967296 |
| 2 | 905567907 |
| 3 | 337051 |
| 4 | 221 |
| 5 | 16 |
| 6 | 2726 |
| 7 | 8322616057 |
| 8 | 2832420683990347645540 |
| 9 | 475348068689013873737817172053634531194 |

Hence $`G_U(y)\le2`$ throughout the interval, proving the lemma. ∎

**Lemma 5 (general arity parameter).** Let $`t>1`$ and let $`U,V\ge1`$
be positive real numbers with $`a/b=U/V`$. Then

```math
\mathrm{Ent}_2(a^2,b^2)
\le \frac{a^2\log_2 U}{2t}+\frac{B_t b^2}{2},
\qquad B_t=\max\left(1,\frac{4^t}{2et\ln2}\right).
```

**Proof.** Put $`x=a/b\le U`$. For $`x\le1`$, $`F(x^2)\le1`$; for
$`x\ge1`$, $`F(x^2)\le x^2`$, since the first logarithm is at most one
and the second is nonpositive. If $`\log_2 U\ge t`$, these bounds already
give

```math
F(x^2)-\frac{x^2}{t}\log_2 U\le1.
```

Otherwise $`x^2\le U^2`$ gives the upper bound
$`\max(1,U^2(1-\log_2 U/t))`$. The maximum of
$`u^2(1-\log_2 u/t)`$ over $`u\ge1`$ is
$`4^t/(2et\ln2)`$, attained at $`u=2^t/\sqrt e>1`$. Multiplication by
$`b^2/2`$ proves the statement. ∎

## 4. Tensorization and absorption

Assume the factorization in Lemma 3, and write

```math
p(s)=\frac{A(s)^2}{Z},\qquad Z=\sum_s A(s)^2,
\qquad L=\mathbb E_p\log_2 A(s),\qquad J=\mathbb E_p|s|.
```

In particular, $`L\ge0`$. Along an edge in coordinate $`i`$, let $`U,V`$
be the products of incident factors evaluated at states zero and one. Common
factors cancel, so $`a/b=U/V`$. Define

```math
L_i(s)=\sum_{\alpha:\,i\in\alpha}\log_2 u_\alpha(s_\alpha).
```

Every term is nonnegative. Averaging Lemma 4 over the other coordinates turns
its first term into

```math
\frac5{16}\mathbb E_{\mathrm{unif}}
 \left[A(s)^2\mathbf1_{\{s_i=0\}}L_i(s)\right],
```

and its second into $`2\mathbb E_{\mathrm{unif}}[A(s)^2\mathbf1_{\{s_i=1\}}]`$.
Dropping the first indicator increases that term. Summing over $`i`$ charges
each logarithmic factor at most $`r`$ times. For $`r\le3`$ this gives

```math
D_2(p\Vert U_n)\le\frac{15}{16}L+2J,
```

where $`U_n`$ is the uniform spectral law.

Here the entropy tensorization has an elementary proof. The average edge
entropy in coordinate $`i`$, divided by $`\mathbb E_{\mathrm{unif}}A^2`$,
is $`1-H(S_i\mid S_{[n]\setminus\{i\}})`$. Conditioning decreases entropy,
so the sum of these expressions is at least $`n-H(S)`$ by the chain rule.
The latter is exactly $`D_2(p\Vert U_n)`$. Thus the displayed estimate uses
no additional logarithmic-Sobolev normalization convention.

Using Lemma 5 instead gives, for general $`r`$,

```math
D_2(p\Vert U_n)\le\frac rt L+B_tJ.
```

Compare $`p`$ with the positive product law

```math
R_q(s)=\frac{2^{-q|s|}}{(1+2^{-q})^n}.
```

Nonnegativity of $`D_2(p\Vert R_q)`$ gives

```math
H(p)\le qJ+n\log_2(1+2^{-q}).
```

Combining the last two inequalities yields

```math
nd_q\le\frac rt L+(B_t+q)J.
```

If $`d_q\ge r/t`$, then $`L\ge0`$ implies

```math
n-L\le\frac{B_t+q}{d_q}J.
```

For $`t=r+1`$ and $`q=\log_2(2(r+1))`$, the inequalities
$`\ln(1+u)\le u`$ and $`\ln2>1/2`$ give

```math
\log_2\left(1+\frac1{2(r+1)}\right)<\frac1{r+1},
```

so the stated general choice is admissible.

For the sharper arity-three bound, take $`q=\log_2 23`$ and
$`d=\log_2(23/12)`$. The exact comparison

```math
23^{16}>2^{15}12^{16}
```

proves $`d>15/16`$. Consequently

```math
n-L\le\frac{2+\log_2 23}{d}J.
```

Finally, with $`A=2^n|\widehat h|`$ and $`W=\mathbb E h^2>0`$,

```math
\frac{H_{\mathrm{raw}}(h)}W=2(n-L),\qquad
\frac{I(h)}W=J.
```

These identities prove both theorems. The inequality $`C_2<14`$ is equivalent
to the exact integer comparison $`23^6>4\cdot12^7`$.

## 5. Constants, zeros and deterministic quotients

The zero function is included separately with entropy and influence zero. An
integer constant $`h=c`$ has $`H_{\mathrm{raw}}(h)=-c^2\log_2(c^2)\le0`$
and $`I(h)=0`$. Integer multiples of characters also satisfy both bounds.
No positive lower bound on variance is needed in these cases.

The theorems pass through [deterministic parity quotients](deterministic-contractions.md)
when the quotient law is positive and has the required treewidth. For
completeness, suppose each deterministic spectral block has the form
$`s_C=a_C\oplus z_C\mathbf1_C`$. Choose the orientation so that $`a_C`$
is not the all-ones vector. Fourier inversion then gives

```math
h(x)=\chi_a(x)g(y),\qquad y_C=\prod_{i\in C}x_i.
```

Surjectivity of the parity map makes $`g`$ integer-valued, and Boolean when
$`h`$ is Boolean. Entropy and norm are preserved. Since
$`|a_C\oplus z_C\mathbf1_C|\ge z_C`$, one has $`I(g)\le I(h)`$.
Fixed spectral coordinates contribute a character and nonnegative extra
influence. Apply the positive theorem to $`g`$.

Genuine three-state edge supports are not covered by this argument. Strict
positivity is used in the elimination ratio and in the positive denominator
factor $`V`$ in Lemma 4. A zero at the bit-one endpoint can leave positive
edge entropy while its proposed influence payment vanishes. No smoothing or
limit that changes Boolean realizability is assumed. The separate
[zero-edge note](zero-edges.md) gives a limited positive result and exact
obstructions to two natural extensions.

## 6. Why the old repairs were insufficient

### A large pairwise integrality defect

On three bits, for $`M\ge1`$, put

```math
v(s)=2-\bigl[(s_1\oplus s_2)+(s_2\oplus s_3)+(s_3\oplus s_1)\bigr],
\qquad A_M(s)=2^{Mv(s)}.
```

The energy is two on the two constant configurations and zero on the other
six. Let $`\Gamma(A)`$ be the minimum $`\log_2 K`$ over positive integers
$`K`$ for which $`KA`$ factors into positive integer unary and pairwise
factors. Then

```math
\Gamma(A_M)=M.
```

For the upper bound, $`v+1`$ is the number of equal pairs on the triangle,
so $`2^MA_M`$ is the product of the three factors
$`2^{M\mathbf1_{\{s_i=s_j\}}}`$. For the lower bound, take two-adic
valuations of any proposed representation of $`KA_M`$. Evaluate its identity
on locally consistent singleton and pair tables with uniform singletons and
perfect anticorrelation on every edge. This defines a linear evaluation of
quadratic functions because shared unary marginals agree. It evaluates
$`v`$ to $`-1`$, so the left side is $`v_2(K)-M`$. Every local valuation
on the right is nonnegative. Thus $`v_2(K)\ge M`$, proving the bound.

This is not a Boolean counterexample: its squared norm is
$`2\cdot16^M+6`$, with a nontrivial odd factor. It disproves free integer
pairwise reparameterization for arbitrary integer tensors. One integer
triangle factor, permitted by Lemma 3, avoids that cost entirely. No claim
that $`\Gamma`$ is uncontrolled for Boolean laws follows.

### A two-bit boundary cannot inherit zero-loss tree induction

For $`E(x,y)=xy`$, the minimum-layer indicator is $`1+xy`$ over
$`\mathbb F_2`$, of degree two. The law proportional to $`4^E`$ has weights
$`(1,1,1,4)/7`$. Minimizing the coordinate-orientation contribution gives

```math
\mathbb E_pE+2\sum_i\min\{P(S_i=0),P(S_i=1)\}=\frac{12}{7}.
```

Adding the two-bit boundary potential $`-xy`$ makes the energy constant,
with minimum-layer degree zero and dimension-minus-degree equal to two.
Since $`12/7<2`$, an unrestricted zero-loss two-coordinate analogue of the
old cross-root-field inequality is false. This excludes that induction
transfer; it does not exclude constant four for positive pairwise treewidth
two or the paid local inequality proved above.

## 7. Connected examples and the remaining problem

The [connected triangle construction](connected-triangles.md) gives Boolean
functions on $`12m`$ variables with full Fourier support, a connected
nonfair core, and feedback vertex number exactly $`m-1`$. For $`m\ge2`$
the core has treewidth exactly two and genuine cubic logarithmic interactions.
It is neither a cactus nor pairwise-factorizable in those coordinates.
For $`m\ge3`$, removing one vertex cannot make it a forest.

The construction is an invertible spectral shear of products of an explicitly
realized path law. Its functions have other FEI proofs; it demonstrates strict
containment of coordinate-defined spectral classes. The theorem here applies
to every Boolean signing compatible with its graphical hypotheses, without
requiring that construction.

The previous [integer-forest proof](integer-forests.md) charged local factor
arity in a Gross logarithmic-Sobolev estimate. At arity three its coefficient
exceeded one, preventing absorption. Lemma 4 repairs that step by keeping an
influence payment. The gcd factorization is a constructive integer version
of elimination on a junction tree. Neither ingredient is a conversion from
an Aaronson–Ambainis fractional certificate.

O'Donnell–Tan's composition theorem uses physical composition on disjoint
blocks and a biased-spectrum hypothesis; it is a different assumption from
spectral graphical factorization. Examples may belong to both classes. The
bounded primary-source comparison in [References](REFERENCES.md) is not an
exhaustive historical-priority certification.

The [standard-library checker](code/check_bounded_treewidth_integer_spectra.py)
verifies the nine scalar certificates and the two constant comparisons using
integer arithmetic. It also checks gcd factorizations, finite Boolean and
ternary tables, and the explicit obstructions. The universal proof is the
argument in Sections 2–4; finite computations audit identities and constants.

The dimension-independent positive treewidth-two target is therefore settled
within this investigation. The remaining questions include constant four on
its pairwise subclass, control uniform in treewidth, genuine three-state
supports, and paid integer or interpolation representations for arbitrary
Boolean functions. No theorem simultaneously proving unrestricted FEI and
Aaronson–Ambainis is obtained.
