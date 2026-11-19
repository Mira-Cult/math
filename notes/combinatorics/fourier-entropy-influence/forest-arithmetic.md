# Boolean forest arithmetic and explicit completions

**Mira Cult · 16 November 2026**

The signed Boolean constraints exclude every odd prime from the nonzero
Walsh magnitudes of a forest-factorizing Fourier law, including laws with
zeros. This arithmetic fact does not force flatness. A credited
Kraft-prefix specialization of the generalized Maiorana–McFarland
construction supplies nonuniform Boolean examples and quantifies the
influence cost of their independent fair completion.

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

Throughout, Walsh coefficients are the unnormalized integers


```math
W_f(s)=\sum_{x\in\{0,1\}^n}f(x)(-1)^{s\cdot x},\qquad \widehat f(s)=2^{-n}W_f(s),
```


for Boolean $`f:\{0,1\}^n\to\{-1,1\}`$. Fourier entropy is in bits and influence is $`I(f)=\sum_s |s|\widehat f(s)^2`$.

## 1. A Boolean cylinder divisibility lemma

**Lemma 1.** Let $`K\subseteq[n]`$, $`|K|=k\ge1`$, let $`a\in\{0,1\}^{K}`$, and let $`p`$ be an odd prime satisfying $`p>2^{k-1}`$. If $`p\mid W_f(a,t)`$ for every $`t\in\{0,1\}^{K^c}`$, then $`W_f(a,t)=0`$ for every such $`t`$.

**Proof.** Define the integer partial Walsh section


```math
G_a(y)=\sum_{x\in\{0,1\}^K}f(x,y)(-1)^{a\cdot x}.
```


It is an even integer, because it is the sum of $`2^k`$ signs, and $`|G_a(y)|\le2^k`$. Its unnormalized Walsh transform on $`K^c`$ is exactly $`W_f(a,t)`$. Walsh inversion modulo the odd prime $`p`$ is valid because $`2^{n-k}`$ is invertible modulo $`p`$. Thus $`p\mid G_a(y)`$ for every $`y`$. A nonzero even multiple of an odd $`p`$ has absolute value at least $`2p>2^k`$. Consequently $`G_a\equiv0`$, proving the assertion. $`\square`$

In particular, **every odd prime works for cylinders fixing one or two coordinates**. This is a genuinely Boolean statement; arbitrary integer-amplitude probability tables need not satisfy it. If $`k=0`$, the elementary substitute is that no odd prime divides all Walsh coefficients, since Walsh inversion would force it to divide $`2^n f(x)`$.

The threshold is sharp at the first excluded odd prime: on three bits, a Boolean AND/OR phase has primitive Walsh amplitudes $`(3,1,1,1,1,1,1,1)`$, so the one-point cylinder of dimension zero at the large coefficient is divisible by $`3`$ but nonzero. Here $`3\le2^{3-1}`$.

## 2. Forest factorization of integer magnitudes can be made rational

By a spectral forest law we mean that $`\widehat f(s)^2`$ factors over a forest as a product of nonnegative unary and edge potentials. This definition includes zeros. Equivalently, each tree component has the usual directed tree factorization and different components are independent. One may connect components by edges with constant potential, so it suffices to discuss a tree.

**Lemma 2.** Let $`A(s)`$ be a nonnegative integer array, not identically zero. If $`A(s)^2`$ factors over a tree, then $`A(s)`$ admits a factorization over the same tree with nonnegative **rational** unary and edge potentials.

**Proof.** Remove a leaf $`i`$, with neighbor $`j`$. For each state $`b`$ of $`j`$ occurring in the support, choose an allowed reference leaf state $`\sigma(b)`$. Tree conditional independence implies that, for any allowed remaining configuration $`r`$ with $`r_j=b`$, the ratio


```math
\frac{A(r,i=c)}{A(r,i=\sigma(b))}
```


is independent of $`r`$. It is a nonnegative rational number, and is zero when $`c`$ is forbidden. Denote it $`q(b,c)`$. The reduced array $`B(r)=A(r,i=\sigma(r_j))`$ is integer valued, and $`A(r,c)=B(r)q(r_j,c)`$. Its squared array still factors over the remaining tree: taking the reference leaf merely changes the unary potential at $`j`$. States of $`j`$ outside the support can be handled arbitrarily, with a zero unary potential. Induction finishes the factorization. $`\square`$

## 3. A min-sum localization fact

**Lemma 3.** Suppose an extended integer energy $`V(s)\in\mathbb Z\cup\{+\infty\}`$ factors additively over a tree into unary/edge costs in $`\mathbb Z\cup\{+\infty\}`$, is finite somewhere, and has global minimum zero. Then it can be reparameterized as


```math
V(s)=R_r(s_r)+\sum_{v\ne r}R_v(s_{\mathrm{par}(v)},s_v),
```


where every cost is a nonnegative integer or $`+\infty`$. In particular, if $`0<V(s)<\infty`$, some one- or two-coordinate cylinder containing $`s`$ has $`V\ge1`$ everywhere.

**Proof.** Combine all unary costs except the root cost with their incoming edge. Write these costs as $`\psi_r(a)`$ and $`\psi_v(b,a)`$. Let


```math
M_v(b)=\min_a\left[\psi_v(b,a)+\sum_{w\text{ child of }v}M_w(a)\right]
```


be the minimum subtree cost conditional on the parent state. On feasible states set


```math
R_v(b,a)=\psi_v(b,a)+\sum_{w\text{ child of }v}M_w(a)-M_v(b),
```


and


```math
R_r(a)=\psi_r(a)+\sum_{w\text{ child of }r}M_w(a).
```


The latter is nonnegative because the global minimum is zero; all edge residuals are nonnegative by their defining minimization. Infeasible patterns may be assigned $`+\infty`$. The finite terms telescope. Every feasible positive-energy assignment therefore uses a strictly positive local residual, and all assignments sharing that local pattern have positive energy or are infeasible. $`\square`$

## 4. Arithmetic rigidity of Boolean spectral forests

**Theorem 4.** If a Boolean function has a spectral forest law, then **every nonzero unnormalized Walsh coefficient has magnitude a power of two**. Equivalently, every nonzero normalized Fourier magnitude is $`2^{-d}`$ for some integer $`d\ge0`$, and every nonzero spectral probability is $`4^{-d}`$.

**Proof.** Put $`A(s)=|W_f(s)|`$. By Lemma 2 it admits rational nonnegative tree potentials. Fix an odd prime $`p`$. Apply the $`p`$-adic valuation to its positive potentials, and assign $`+\infty`$ to a zero potential. This gives an extended integer tree energy


```math
V(s)=v_p(A(s))
```


for nonzero $`A(s)`$, with $`V(s)=+\infty`$ otherwise. All finite values are nonnegative because $`A`$ is integer. Its minimum is zero: an odd prime cannot divide every Walsh coefficient of a Boolean function.

If some nonzero $`A(s)`$ had positive valuation, Lemma 3 would give a one- or two-coordinate cylinder containing $`s`$ on which every Walsh coefficient is divisible by $`p`$, where zero coefficients are included as divisible. Lemma 1 makes that entire cylinder zero, contradicting $`A(s)>0`$. Thus no odd prime divides any nonzero Walsh coefficient. These coefficients are integers, so their magnitudes are powers of two. Since $`|W_f(s)|\le2^n`$, the equivalent normalized statements follow. $`\square`$

The proof also shows why arbitrary integer tables are insufficient. Booleanity enters at the partial Walsh section bound; Parseval alone does not give it.

## 5. A separate odd-amplitude rigidity result for arbitrary pairwise graphs

**Theorem 5.** Let $`A(s)`$ be positive odd integers on $`\{0,1\}^n`$. Suppose $`A(s)^2`$ factors over an arbitrary pairwise graph, and suppose $`\sum_s A(s)^2`$ is a power of two. Then $`A(s)=1`$ for all $`s`$, and $`\sum_s A(s)^2=2^n`$.

**Proof.** Full positivity gives the canonical rational factorization


```math
A(S)=A(\varnothing)\prod_{i\in S}r_i\prod_{\{i,j\}\subseteq S}r_{ij},
```


with $`r_i=A(\{i\})/A(\varnothing)`$ and $`r_{ij}=A(\{i,j\})A(\varnothing)/(A(\{i\})A(\{j\}))`$. Every numerator and denominator is odd. Therefore $`c_F=r_F^2-1`$ has 2-adic valuation at least three for each unary or pairwise factor $`F`$. Expanding


```math
\sum_S A(S)^2=A(\varnothing)^2\sum_{\mathcal J}\left(\prod_{F\in\mathcal J}c_F\right)2^{n-|\cup_{F\in\mathcal J}F|}
```


shows that the empty-family term has 2-adic valuation $`n`$, while every nonempty family $`\mathcal J`$ has valuation at least


```math
3|\mathcal J|+n-|\cup_{F\in\mathcal J}F|\ge n+|\mathcal J|\ge n+1.
```


Hence the entire sum has valuation exactly $`n`$. Being a power of two, it equals $`2^n`$. There are $`2^n`$ positive integer squares in it, forcing all to be one. $`\square`$

This argument uses rational 2-adic arithmetic only with odd denominators, so there is no denominator ambiguity. The pairwise hypothesis cannot be replaced by three-variable factors: $`(3,1,\ldots,1)`$ on three bits has squared norm $`16`$.

## 6. Every powers-of-four law has a Boolean completion with independent fair spectral bits

The tempting strengthening “a full-support Boolean spectral forest is uniform” is false. Its failure can be constructed without guessing Walsh signs.

**Theorem 6 (prefix-cylinder bent completion).** Let $`p_s=4^{-d_s}`$ be a probability law on a finite subset $`\mathcal S\subseteq\{0,1\}^r`$, where each $`d_s`$ is a nonnegative integer. Set $`D=\max_s d_s`$ and $`m=2D`$. There is a Boolean function $`F`$ on $`r+m`$ bits whose exact Fourier law is


```math
\widehat F(s,t)^2=p_s2^{-m}\quad(s\in\mathcal S,\ t\in\{0,1\}^m),
```


and is zero for $`s\notin\mathcal S`$. Thus the spectral sample consists of an independent sample from $`p`$ and $`m`$ fair bits.

**Proof.** Kraft equality $`\sum_s4^{-d_s}=1`$ supplies a complete prefix code over an alphabet of four symbols with codeword lengths $`d_s`$. Identify each four-symbol digit with a pair of bits. In the $`m`$-bit address cube, the codeword for $`s`$ specifies a prefix cylinder $`E_s`$ of codimension $`2d_s`$. These cylinders partition the cube.

There are $`m-2d_s`$ free suffix bits, an even number. On this suffix use the explicit bent phase


```math
b_s(z)=(-1)^{z_{2d_s+1}z_{2d_s+2}+z_{2d_s+3}z_{2d_s+4}+\cdots+z_{m-1}z_m}.
```


Set $`F(x,z)=(-1)^{s\cdot x}b_s(z)`$ for $`z\in E_s`$. For fixed core Fourier index $`s`$, its address function is $`\mathbf1_{E_s}b_s`$. Fixing $`2d_s`$ prefix bits contributes a phase and a factor $`2^{-2d_s}`$, while the free bent suffix has normalized Fourier magnitude $`2^{-(m-2d_s)/2}`$. Consequently


```math
|\widehat F(s,t)|=2^{-2d_s}2^{-(m-2d_s)/2}=2^{-m/2-d_s}
```


for every address frequency $`t`$. Squaring proves the formula. $`\square`$

This theorem also covers $`D=0`$, where the sole positive atom has mass one and no address bits are needed.

The construction always has


```math
H(F)=H(p)+m,\qquad I(F)=\mathbb E_p|S|+m/2.
```


Moreover $`H(p)=2\mathbb E_p d_S\le2D=m`$, so every function constructed this way satisfies $`H(F)\le4I(F)`$. This does not establish the same inequality for all functions having powers-of-four spectra.

## 7. An explicit full-support nonflat Boolean spectral forest

On four core spectral bits, in little-endian mask order, let


```math
v(s)=3-2s_0-2s_1-s_2+s_0s_1+s_1s_2+s_2s_3.
```


Its values are


```math
(3,1,1,0,2,0,1,0,3,1,1,0,3,1,2,1).
```


Put $`A(s)=2^{v(s)}`$. Direct exact summation gives $`\sum_s A(s)^2=256`$. Thus


```math
p_s=4^{v(s)-4}
```


is a strictly positive, nonuniform path-Markov law on $`0-1-2-3`$. Theorem 6, with $`d_s=4-v(s)`$, $`D=4`$, and eight address bits, constructs a 12-bit Boolean function with Fourier law $`p`$ times eight independent fair bits. Its nonzero Walsh magnitudes are $`16,32,64,128`$.

For the unshifted core,


```math
H(p)=89/32,\qquad \mathbb E_p|S|=163/128.
```


Multiplying the resulting Boolean function by the character in core coordinate 3 complements that spectral bit, reducing the core expected weight to $`65/64`$ without changing entropy or the forest property. For this shifted function,


```math
H(F)=345/32,\qquad I(F)=321/64,\qquad H(F)/I(F)=230/107>2.
```


The companion script constructs all 4,096 truth-table values, performs an exact integer Walsh transform, checks the complete spectral law, and verifies these rational quantities.

## 8. Attribution of the completion construction

The function form $`F(x,z)=(-1)^{x\cdot\phi(z)+g(z)}`$ is the established **generalized Maiorana–McFarland construction**, not a new construction family. The standard Fourier formula reduces each row to the Walsh transform of $`(-1)^g`$ restricted to the fiber $`\phi^{-1}(s)`$. See Claude Carlet, *Boolean Functions for Cryptography and Error Correcting Codes*, Section 7.5.1, equations (59)–(60), available at:

- https://www.math.univ-paris13.fr/~carlet/chap-fcts-Bool-corr.pdf
- The expanded book treatment: https://www.math.univ-paris13.fr/~carlet/book-fcts-Bool-vect-crypt-codes.pdf

Theorem 6 is the explicit Kraft-prefix/fiber-bent specialization used here to realize every powers-of-four law after adding independent fair spectral coordinates. No novelty claim is made for the underlying Maiorana–McFarland method or for bent phases on affine fibers. No exhaustive historical priority claim is made for the structural statements.

## 9. Magnitude layers need not be integer packets

The stronger conversion “every Boolean function whose Fourier magnitudes are powers of two has integer-valued packets at each magnitude level” is false. A five-bit example is


```math
f(x)=1-2\mathbf1_A(x),\qquad A=\{0,1,2,3,4,8,16,28\},
```


where integers encode five-bit vectors. Its unnormalized Walsh spectrum has one coefficient 16 (the constant coefficient), twelve coefficients of magnitude 8, and nineteen zeros. The packet containing only the coefficient of magnitude $`1/2`$ is the constant function $`1/2`$, which is not integer valued. The example has $`H(f)=7/2`$ and $`I(f)=13/8`$. This refutes the automatic packet conversion, not FEI. The additional forest hypothesis would have to be used essentially in any successful packet theorem.

## 10. A six-bit path core

For the fair-completion calculation, a second explicit positive path core is

```math
v(s)=5+\sum_{i=0}^{5}h_i s_i+\sum_{i=0}^{4}J_i s_i s_{i+1},
\qquad h=(1,-1,-2,-1,-3,-2),\quad J=(1,1,1,1,2).
```

Its energy values lie in $`\{0,\ldots,6\}`$ with multiplicities
$`(4,15,12,20,6,5,2)`$. Therefore

```math
\sum_s4^{v(s)}=16384=4^7,
\qquad \sum_sv(s)4^{v(s)}=85180.
```

Its zero states, in little-endian mask order, are $`20,22,52,54`$.
Their indicator over $`\mathbb F_2`$ is

```math
\mathbf1[v=0]=s_2s_4(1+s_0)(1+s_3),
```

so its algebraic degree is four. Thus $`D=7`$ and $`\delta=4`$ in the
fair-completion bounds. These two parameters are also checked by
[check_positive_spectral_forest_fei.py](code/check_positive_spectral_forest_fei.py).
The Kraft-prefix construction uses fourteen independent fair spectral bits;
the Boolean minimum-layer bound requires at least twelve. No optimality
claim is made for this six-bit core.

The core law $`p(s)=4^{v(s)-7}`$ is a probability distribution, not a
six-variable Boolean Fourier law: it has amplitude $`2^{-7}`$, below the
granularity of a six-bit Boolean Walsh transform. The completion is an
actual twenty-variable Boolean function. This distinction prevents a
probability-only core from being used as a Boolean FEI counterexample.
