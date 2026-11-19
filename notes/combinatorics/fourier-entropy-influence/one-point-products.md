# A sharp constant-four bound with irreducible spectral interactions of every size

**Mira Cult · 16 November 2026**

A disjoint product of rare-point gates, followed by one physical point flip,
satisfies the sharp uniform bound $`H\le4I`$. Its positive Fourier law
has an interaction involving every variable; no factorization into proper
spectral subsets can remove that interaction. Both assertions are proved
for all block counts and block sizes in the stated class.

This is a particular Boolean construction, not a uniform FEI theorem for
arbitrary functions. Publication priority requires comparison with existing
classes; no novelty claim is made solely from the interaction graph.

**Review status.** Complete proofs with scoped nonauthor model review of the
scientific revision. The review scope, exact revisions, and limitations are
recorded in [Verification](VERIFICATION.md); this is not human peer review.

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

Scientific source: [math-wip at a17f79e](https://github.com/Mira-Cult/math-wip/blob/a17f79e858c8537587a8d49e2b879f10c59e7677/problems/0298-fourier-entropy-influence-conjecture/manuscripts/one_point_product_interference.md).

## 1. Statement

All entropies are in bits and all inputs are independent uniform signs. For
$`n\ge 2`$, let

```math
r_n(x)=1-2\mathbf1_{\{x=(1,\ldots,1)\}}.
```

Choose any $`m\ge 2`$ disjoint nonempty input blocks of sizes $`n_j\ge 2`$, with
$`N=\sum_j n_j`$. Define

```math
F(x)=\prod_{j=1}^m r_{n_j}(x^{(j)}),\qquad
G(x)=F(x)-2(-1)^m\mathbf1_{\{x=(1,\ldots,1)\}}.
```

Thus $`G`$ is obtained from $`F`$ by flipping its truth-table value at the one
point at which every block gate is in its rare state.

**Theorem 1.** Every such $`G`$ has strictly positive Fourier spectrum and obeys

```math
H(G)\le4I(G).
```

The constant is independent of $`N`$, $`m`$, and every $`n_j`$, and is best possible
for this class. Moreover the spectral law of $`G`$ does not admit a direct
positive factorization whose factors all have arity less than $`N`$. Its
conditional-dependence graph is complete, so its minimal graphical treewidth
is $`N-1`$.

The theorem also applies after permuting physical input coordinates,
complementing any of them, or multiplying the output by $`-1`$, since these
operations preserve squared Fourier coefficients and influence. It does not
assert closure under arbitrary changes of the spectral basis.

## 2. A quantitative margin for one rare-point gate

Put $`\epsilon_n=2^{1-n}`$. The coefficients of $`r_n`$ are $`1-\epsilon_n`$ at the
empty set and $`-\epsilon_n`$ elsewhere. Direct counting gives

```math
I(r_n)=n\epsilon_n,\qquad
H(r_n)=-2(1-\epsilon_n)^2\log_2(1-\epsilon_n)
        +(2\epsilon_n-\epsilon_n^2)(2n-2).
```

**Lemma 2.** For every $`n\ge 2`$,

```math
H(r_n)\le4n\epsilon_n(1-\epsilon_n).
```

**Proof.** For $`n=2`$ the Fourier law is uniform on four points, so $`H=2`$ and
the claimed upper bound is also two. For $`n=3`$, the formula is
$`H=4-(9/8)\log_2 3`$, while the upper bound is $`9/4`$. The desired comparison is
$`\log_2 3\ge 14/9`$, certified by the integer inequality $`3^9>2^{14}`$.

For $`n\ge 4`$, the inequality $`-\ln(1-\epsilon)\le\epsilon/(1-\epsilon)`$ yields

```math
\begin{aligned}
4n\epsilon(1-\epsilon)-H(r_n)
&\ge\epsilon\left[
 4-\frac2{\ln2}
 -\left(2n+2-\frac2{\ln2}\right)\epsilon
 \right].
\end{aligned}
```

One has $`2/3<\ln2<1`$, for example by integrating $`1/t`$ on $`[1,2]`$ and using
its strict convexity for the lower bound. Thus $`4-2/\ln2>1`$ and
$`2n+2-2/\ln2<2n`$. Also $`2n \epsilon_n=n/2^{n-2}\le 1`$ for $`n\ge 4`$.
The bracket is strictly positive. QED.

## 3. An exact paid-interference identity

Use the abbreviations

```math
\epsilon_j=2^{1-n_j},\quad
b_j=\frac{1-\epsilon_j}{\epsilon_j}=2^{n_j-1}-1\ge1,\quad
\delta=2^{1-N}.
```

The original law $`p_F`$ is the product of the block spectral laws. For a
spectral set $`S`$, let $`Z_j(S)`$ indicate that $`S`$ intersects block $`j`$.
Then

```math
-\log_2p_F(S)
=-2\sum_j\log_2(1-\epsilon_j)
  +2\sum_j Z_j(S)\log_2 b_j.
```

Every unnormalized Walsh coefficient of $`F`$ is divisible by $`2^m`$, hence by
four. The flip changes each by $`-2(-1)^m`$; therefore every coefficient of $`G`$
is congruent to two modulo four and is nonzero. Both $`p_F`$ and $`p_G`$ are
strictly positive, so their relative entropy is finite.

The Fourier change is the same signed number at every spectral set:

```math
\widehat G(S)=\widehat F(S)-(-1)^m\delta.
```

We claim that for each block

```math
\mathbb E_{p_G}Z_j
=\mathbb E_{p_F}Z_j-\delta(2-\epsilon_j).
```

Indeed, summing Fourier coefficients over the sets avoiding block $`j`$ gives

```math
\sum_{S:S\cap B_j=\varnothing}\widehat F(S)
=(1-\epsilon_j)\prod_{i\ne j}r_{n_i}(1,\ldots,1)
=(1-\epsilon_j)(-1)^{m-1}.
```

There are $`2^{N-n_j}`$ such spectral sets. Expanding squared amplitudes, the
change of their total probability is consequently

```math
-2(-1)^m\delta(1-\epsilon_j)(-1)^{m-1}
 +2^{N-n_j}\delta^2
=2\delta(1-\epsilon_j)+\delta\epsilon_j
=\delta(2-\epsilon_j).
```

Taking cross-entropy against $`p_F`$ now gives the exact identity

```math
\boxed{
H(G)=H(F)-2\delta\sum_{j=1}^m(2-\epsilon_j)\log_2 b_j
          -D_2(p_G\Vert p_F).
}
```

Every subtracted term is nonnegative. This accounts for the amplitude
interference from the selector/point modification; it does not identify the
two squared Fourier laws with a mixture. In particular,

```math
H(G)\le H(F).
```

All $`N`$ physical edges incident to the flipped point were sensitive for $`F`$
and become insensitive for $`G`$. Thus

```math
I(G)=I(F)-N\delta.
```

## 4. The entropy margin pays the decrease of influence

The disjoint Fourier product and Lemma 2 give

```math
H(F)=\sum_jH(r_{n_j})
\le4I(F)-4\sum_j n_j\epsilon_j^2.
```

Since $`m\ge 2`$, some block has size $`r\le N/2`$. Write $`d=N-2r`$, a nonnegative
integer. Then

```math
\frac{r2^{2-2r}}{N2^{1-N}}
=\frac{2r}{2r+d}2^d\ge1,
```

because $`2^d\ge 1+d\ge 1+d/(2r)`$. That single block already shows

```math
\sum_j n_j\epsilon_j^2\ge N\delta.
```

Combining the inequalities and exact influence identity yields

```math
H(G)\le H(F)
\le4I(F)-4N\delta=4I(G).
```

This proves the FEI bound without a width-dependent estimate or an uncharged
interpolation cost.

## 5. No smaller-arity positive factorization exists

We prove the structural claim for every allowed choice of block sizes. On the
spectral cube set $`\rho_j(s_j)=1`$ when the mask in block $`j`$ is empty and
$`\rho_j(s_j)=-b_j`$ otherwise, and let $`R(s)=\prod_j\rho_j(s_j)`$. Write

```math
c=2^m\prod_jb_j,\qquad q=\frac{2(-1)^m}{c}.
```

The unnormalized coefficient of $`F`$ is $`c/R(s)`$, so

```math
\log_2p_G(s)=\log_2p_F(s)+2\log_2(1-qR(s)).
```

Here $`|qR(s)|\le 2^{1-m}<1`$. Let

```math
\Delta_{[N]}K=\sum_{s\in\{0,1\}^N}(-1)^{N-|s|}K(s).
```

The full mixed difference of $`\log p_F`$ vanishes because its logarithm is a
sum of functions on proper disjoint blocks. Expanding the remaining logarithm
in its absolutely convergent power series gives

```math
\Delta_{[N]}\log_2p_G
=-\frac{2(-1)^N}{\ln2}
  \sum_{\ell=1}^{\infty}\frac{q^\ell}{\ell}
        \prod_{j=1}^m\bigl(1-(-b_j)^\ell\bigr).
```

Every nonzero term inside the sum has sign $`(-1)^m`$. For odd $`\ell`$, all
factors in the product are positive and $`q^\ell`$ has that sign. For even
$`\ell`$, all factors are nonpositive, so their product has that sign whenever
it is nonzero, while $`q^\ell`$ is positive. The first term is nonzero.
Therefore the mixed difference cannot vanish. The series is absolutely
convergent since the original log series converges uniformly on the finite
cube; a direct geometric bound is available from $`|qR|\le 2^{1-m}`$.

If $`p_G`$ were a positive scalar times a product of positive potentials each
missing at least one spectral coordinate, its logarithm would be a sum of
functions with zero full mixed difference. This contradiction proves that an
arity-$`N`$ factor is necessary. Any coordinate pair that were conditionally
independent given the others would also force the full mixed difference to
vanish: positivity makes its conditional log odds ratio zero for every value
of the other coordinates. The conditional-dependence graph is thus complete.
This proves the structural assertion in Theorem 1.

## 6. Sharpness and useful parameter regimes

Take $`m=2`$ and both block sizes equal to $`n`$, then let $`n`$ grow. For the
unmodified product, $`H(F)/I(F)=H(r_n)/I(r_n)\to4`$, directly from the seed
formula. The modification changes influence by $`N2^{1-N}`$. The elementary
amplitude-to-total-variation and entropy-continuity bounds in the companion
full-support reduction give

```math
|H(G)-H(F)|\le h_2(2^{1-N/2})+N2^{1-N/2}.
```

That bound by itself is not small relative to $`I(F)`$ when $`m=2`$; use the exact
identity instead. Here $`N=2n`$, $`\delta=2^{1-2n}`$ and the explicit cross-entropy
term is $`O(n \delta)`$. The amplitude ratio satisfies

```math
\left|\frac{\widehat G(S)}{\widehat F(S)}-1\right|
\le 2^{1-m}=\tfrac12.
```

More quantitatively, on this whole class the chi-square divergence is bounded
by

```math
\chi^2(p_G,p_F)
=\delta^2\sum_S
 \left(-2(-1)^m+\frac{\delta}{\widehat F(S)}\right)^2
\le\frac{25}4\,2^N\delta^2
=25\,2^{-N}.
```

Here $`|\widehat F(S)|\ge\prod_j\epsilon_j=2^{m-N}`$, and hence
$`|\delta/\widehat F(S)|\le2^{1-m}\le1/2`$. Since
$`D_2(p_G\Vert p_F)\le\chi^2(p_G,p_F)/\ln2`$, the relative entropy is $`O(2^{-N})`$.
Consequently $`H(F)-H(G)=O(n2^{-2n})=o(I(F))`$, while
$`I(F)=2n2^{1-n}`$. The ratio for $`G`$ tends to four, proving sharpness.

There are also nearly balanced examples with small influence relative to
their unavoidable arity. For $`n\ge 3`$ and integer $`a\ge 1`$, use
$`m=a2^{n-1}`$ equal blocks of size $`n`$. Then

```math
N=an2^{n-1},\qquad I(G)=an-N2^{1-N}.
```

Here $`m`$ is even, and direct coefficient comparison gives

```math
0\lt \mathbb E G\le e^{-a},\qquad\max_Sp_G(S)\le e^{-2a}.
```

For fixed $`a`$, $`I(G)=\Theta(\log N)`$ while the necessary interaction arity is
$`N`$. Taking $`a=n`$ makes the mean and maximum atom tend to zero and recovers
the connected absorption obstruction from the companion note, while this
theorem simultaneously gives its sharp class bound $`H\le4I`$.

## 7. Comparison and remaining gap

The starting product $`F`$ is a read-once composition of rare-point gates and
parity, so its FEI bound is already covered by established composition results.
The construction and proof above account for the one-point modification
explicitly. It is not automatically licensed by disjoint composition, since
the modifying point indicator uses every original variable again.

Relevant comparisons to check before a novelty claim are O'Donnell--Wright--
Zhou's symmetric and constant-part-symmetric theorem; O'Donnell--Tan's
composition theorem with its biased FEI+ hypotheses; Wan--Wright--Wu's
read-$`k`$ decision-tree theorem, whose parameter counts occurrences in the
entire tree; and newer symmetric-gate and approximation results. A graph with
large interaction arity alone does not certify improvement over those classes.
In particular, fixed $`m`$ gives constant-part-symmetric functions, and fixed
small block sizes can have large influence that is easy to bound by other
methods. The regimes with both block sizes and number of blocks unbounded
are the relevant comparison.

The reusable structural gain is the exact paid-interference identity in
Section 3 and its nonnegative relative-entropy correction. It does not extend
to an arbitrary one-point modification merely by positivity: the cross-entropy
term need not have the displayed sign, and an influence-decreasing flip must
be paid by a genuine margin. No claim is made that these conditions hold for
all Boolean functions.


## Reproducible checks

The accompanying [exact checker](code/check_one_point_product_interference.py) is mirrored without
changes from the scientific revision. From this note's directory, run:

```bash
python code/check_one_point_product_interference.py
```

Finite checks verify the identities and examples specified by the checker;
the proofs above establish the universal statements.
Exact runs and review qualifications are recorded in [Verification](VERIFICATION.md).

[Recursive point modifications](point-modifications.md) · [Positive support and absorption obstruction](positive-support.md) · [Directed factors](directed-factors.md)
