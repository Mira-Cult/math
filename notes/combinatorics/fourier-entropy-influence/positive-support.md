# Full-support reduction and a nearly balanced absorption obstruction

**Mira Cult · 16 November 2026**

A universal FEI bound for strictly positive Boolean Fourier spectra would
imply the full conjecture with exactly the same constant. Adding unused
variables and changing one truth-table value gives an explicit
Boolean-preserving reduction, with vanishing entropy and influence errors.

The same construction sharpens the scope of the near-constant obstruction:
tensorized rare-point examples defeat the proposed uniform absorption
inequality even when the mean and largest spectral atom vanish, and after
conditioning away the constant coefficient. These facts do not prove FEI.
The Walsh parity fact behind full support is classical, and no exhaustive
publication-priority claim is made. All logarithms are base two unless
written $`\ln`$.

**Review status.** Complete proofs with scoped nonauthor model review of the
scientific revision. The review scope, exact revisions, and limitations are
recorded in [Verification](VERIFICATION.md); this is not human peer review.

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

Scientific source: [math-wip at a17f79e](https://github.com/Mira-Cult/math-wip/blob/a17f79e858c8537587a8d49e2b879f10c59e7677/problems/0298-fourier-entropy-influence-conjecture/manuscripts/positive_support_reduction.md).

## 1. Conventions

For a sign-valued Boolean function on $`n`$ independent uniform sign coordinates,
write $`a_S=\widehat f(S)`$, $`p_f(S)=a_S^2`$,

```math
H(f)=\sum_Sp_f(S)\log_2\frac1{p_f(S)},\qquad
I(f)=\sum_S|S|p_f(S).
```

Terms of mass zero contribute zero. The unnormalized Walsh coefficient is
$`W_f(S)=2^n\widehat f(S)`$. A *positive spectrum* means that every squared Walsh
coefficient, including the empty coefficient, is strictly positive. In
particular, no exactly balanced Boolean function has a positive spectrum.

The pointwise sensitivity is

```math
s_f(x)=\#\{i:f(x)\ne f(x^{\oplus i})\}.
```

Thus $`I(f)=\mathbb E s_f(X)`$ in the present convention.

## 2. A Boolean full-support approximation

**Theorem 1.** Let $`n\ge 1`$, let $`f`$ be any Boolean sign function on $`n`$ bits,
and choose any physical input $`x_0`$. For every integer $`k\ge 1`$, put $`N=n+k`$,
choose any $`z_0`$ on the $`k`$-cube, and define

```math
F_k(x,z)=f(x),\qquad
G_k(x,z)=F_k(x,z)-2f(x_0)\mathbf1_{\{(x,z)=(x_0,z_0)\}}.
```

Then $`G_k`$ is Boolean and has positive spectrum. With $`\epsilon=2^{1-N}`$,

```math
\widehat G_k(S,T)
=\mathbf1_{\{T=\varnothing\}}\widehat f(S)
 -\epsilon f(x_0)\chi_S(x_0)\chi_T(z_0),
```

and its influence satisfies the exact identity

```math
I(G_k)=I(f)+\epsilon\bigl(N-2s_f(x_0)\bigr).
```

In particular, $`|I(G_k)-I(f)|\le N\epsilon`$. If $`p_f`$ is embedded in the
$`N`$-cube by adding zero mass outside $`T=\varnothing`$, its total variation distance
from $`p_G`$ obeys

```math
\|p_{G_k}-p_f\|_{\rm TV}
 \le\epsilon\bigl(1+\|\widehat f\|_1\bigr)
 \le\epsilon(1+2^{n/2}).
```

Consequently $`H(G_k)\to H(f)`$ and $`I(G_k)\to I(f)`$ as $`k\to\infty`$.

**Proof.** The displayed definition flips precisely one truth-table value, so
it remains sign-valued. A physical point indicator has Fourier coefficient
$`2^{-N}\chi_S(x_0)\chi_T(z_0)`$, proving the Fourier formula.

All $`W_f(S)`$ are even because they are sums of the even number $`2^n`$ of signs.
The unnormalized Walsh coefficients of $`F_k`$ are either zero or
$`2^k W_f(S)`$, and therefore divisible by four. The point flip changes each by
$`+2`$ or $`-2`$. Every $`W_G(S,T)`$ is consequently congruent to two modulo four,
so none is zero. This uses $`k\ge 1`$ and $`n\ge 1`$; constants are included as
functions on a nonempty cube.

For each of the $`N`$ coordinate directions, only the unoriented edge incident
to $`(x_0,z_0)`$ changes its sensitivity. Changing one such edge changes the
probability-of-flip influence by $`2/2^N=\epsilon`$. Among the old $`n`$ directions,
exactly $`s_f(x_0)`$ edges lose sensitivity; the other $`N-s_f(x_0)`$ edges gain
sensitivity. This gives the exact influence identity.

Let $`M=2^n`$. On the old spectral subcube the difference of squared amplitudes
has absolute value at most $`2 \epsilon |a_S|+\epsilon^2`$. Outside that subcube,
all $`2^N-M`$ squared amplitudes equal $`\epsilon^2`$. Hence

```math
\begin{aligned}
\|p_{G_k}-p_f\|_{\rm TV}
&\le \epsilon\sum_S|a_S|+\tfrac12 2^N\epsilon^2\\
&=\epsilon(\|\widehat f\|_1+1).
\end{aligned}
```

Parseval and Cauchy--Schwarz give $`\lVert\widehat f\rVert_1\le\sqrt M`$.

For completeness, distributions $`p,q`$ on an alphabet of size $`K`$ at total
variation distance $`d`$ admit a coupling $`(X,Y)`$ with $`\Pr[X\ne Y]=d`$: match the
common mass $`\min(p_j,q_j)`$ and couple the remaining disjoint supports. Writing
$`E=\mathbf1[X\ne Y]`$, the entropy chain rule gives

```math
|H(p)-H(q)|\le h_2(d)+d\log_2 K.
```

Indeed $`H(X)\le H(Y)+H(E)+H(X\mid Y,E)`$ and the last conditional entropy is at most
$`d\log_2K`$; reverse $`X,Y`$ for the other direction. Here $`K=2^N`$.
For all sufficiently large $`k`$, the bound
$`b_k=\epsilon(1+2^{n/2})`$ is at most one half, so monotonicity of binary entropy
on $`[0,1/2]`$ gives

```math
|H(G_k)-H(f)|\le h_2(b_k)+N b_k\longrightarrow0.
```

No perturbation by non-Boolean values, factorization assumption, or exchange
of limits over an unbounded family is involved. The original $`f`$ is fixed.
The influence bound tends to zero as well. QED.

The extra spectral mass outside the old subcube can also be recorded exactly:

```math
q_k=(2^N-2^n)\epsilon^2
    =2\epsilon-2^n\epsilon^2.
```

It is uniform over that complement and contributes $`q_k(2N-2)`$ to the
unconditioned entropy. This makes the cost of the newly nonzero coefficients
explicit.

**Corollary 2 (same-constant equivalence).** Fix a finite $`C\ge 0`$. The following
two assertions are equivalent:

1. Every Boolean function on every finite cube satisfies $`H(f)\le C I(f)`$.
2. Every Boolean function with positive spectrum on every finite cube satisfies
   $`H(f)\le C I(f)`$.

**Proof.** The first assertion includes the second. For the converse, apply
the second to $`G_k`$ from Theorem 1 and pass to the two proved limits. Constants
have $`H=I=0`$. QED.

Thus the two classes have the same supremum of $`H/I`$ over nonconstant
functions, whether that supremum is finite or infinite. Full support is not an
additional unresolved reduction once an arity-independent positive-spectrum
bound has actually been proved. The construction does not preserve bounded
treewidth, bounded factor arity, pairwise factorization, or arithmetic
power-of-two magnitudes.

## 3. Near balance and sublinear additive errors

**Theorem 3.** Fix $`C\ge 0`$, $`\delta\in(0,1)`$, and a real function $`r(N)`$ with
$`r(N)/N\to 0`$. Suppose that for every $`N`$ and every positive-spectrum Boolean
function $`g`$ satisfying $`|\mathbb E g|\le\delta`$,

```math
H(g)\le C I(g)+r(N).
```

Then every Boolean function satisfies $`H(f)\le C I(f)`$.

**Proof.** Constants are immediate. For nonconstant $`f`$ on $`n\ge 1`$ bits let
$`a=\mathbb E f`$, so $`|a|<1`$, and form the disjoint product $`F_m=f^{\otimes m}`$.
Fourier laws tensorize, giving

```math
H(F_m)=mH(f),\quad I(F_m)=mI(f),\quad E F_m=a^m.
```

Add one dummy bit and flip one truth-table value, obtaining positive-spectrum
$`G_m`$ on $`N_m=mn+1`$ bits. Its mean differs from $`a^m`$ by
$`2^{1-N_m}`$, so eventually $`|\mathbb E G_m|\le\delta`$.

A dimension-uniform continuity estimate is convenient here. If normalized
real amplitude vectors $`u,v`$ have squared laws $`p,q`$, then

```math
\|p-q\|_{\rm TV}
 \le\tfrac12\|u-v\|_2\|u+v\|_2\le\|u-v\|_2.
```

Parseval gives $`\lVert G_m-F_m\rVert_2=2^{1-N_m/2}`$. The entropy continuity proof above
therefore gives $`|H(G_m)-mH(f)|=o(1)`$. The influence difference is at most
$`N_m 2^{1-N_m}=o(1)`$. Applying the hypothesis and dividing by $`m`$ yields

```math
H(f)\le C I(f)+\frac{r(N_m)}m+o(1),
```

and $`r(N_m)/m=(r(N_m)/N_m)(n+1/m)\to0`$. QED.

This is a reduction, not a near-balanced FEI theorem. It warns that neither
positive support nor a fixed nontrivial variance lower bound automatically
makes uniform FEI easier. An exactly balanced function cannot have positive
spectrum because its empty Fourier coefficient is zero.

## 4. Absorption fails even with vanishing mean and no dominant atom

For a positive-spectrum Boolean function $`g`$ on $`N`$ bits, define the checkpoint
quantities

```math
A_g(S)=2^N|\widehat g(S)|,\quad
L(g)=\mathbb E_{p_g}\log_2 A_g(S),\quad
D(g)=D_2(p_g\Vert U_N)=N-H(g).
```

Parseval gives $`H(g)=2(N-L(g))`$ and hence $`D(g)=2L(g)-N`$.

**Theorem 4.** For any fixed $`\eta<1`$ and finite real $`B`$, the inequality

```math
D(g)\le\eta L(g)+B I(g)
```

fails on positive-spectrum Boolean functions with means tending to zero and
maximum spectral atoms tending to zero. It remains false after conditioning
away the empty spectral atom, with the reference law uniform on nonempty
subsets and the influence and logarithmic magnitude averaged under that
conditional law.

**Proof.** For $`n\ge 3`$, set

```math
\epsilon_n=2^{1-n},\qquad
r_n(x)=1-2\mathbf1_{\{x=(1,\ldots,1)\}},\qquad
m_n=n2^{n-1}=n/\epsilon_n.
```

The Fourier coefficients are $`1-\epsilon_n`$ at the empty set and
$`-\epsilon_n`$ elsewhere. Thus every coefficient is nonzero,

```math
I(r_n)=n\epsilon_n,\qquad
L(r_n)=(1-\epsilon_n)^2\log_2(2^n-2)
       +1-(1-\epsilon_n)^2.
```

Since $`\log_2(2^n-2)=n+\log_2(1-\epsilon_n)`$,

```math
\frac{L(r_n)}n\longrightarrow1,\qquad
\frac{D(r_n)}n\longrightarrow1,\qquad
\frac{I(r_n)}n=\epsilon_n\longrightarrow0.
```

Now form $`F_n=\prod_{j=1}^{m_n}r_n(x^{(j)})`$ on disjoint blocks, with
$`N_n=nm_n`$. Fourier laws tensorize, so

```math
L(F_n)=m_nL(r_n),\quad D(F_n)=m_nD(r_n),\quad I(F_n)=n^2.
```

In particular,

```math
\frac{L(F_n)}{N_n}\longrightarrow1,\quad
\frac{D(F_n)}{N_n}\longrightarrow1,\quad
\frac{I(F_n)}{N_n}=\epsilon_n\longrightarrow0.
```

The function retains positive spectrum. Its mean and maximum spectral mass
satisfy

```math
|\mathbb E F_n|=(1-\epsilon_n)^{m_n}\le e^{-n},\qquad
\max_Sp_{F_n}(S)=(1-\epsilon_n)^{2m_n}\le e^{-2n}.
```

The maximum is at the empty set because $`1-\epsilon_n>\epsilon_n`$ for $`n\ge 3`$.
Dividing the proposed inequality by $`N_n`$ and taking limits would give
$`1\le \eta`$, a contradiction. This remains a counterexample if the class is
restricted by any fixed bound $`|\mathbb E g|\le\delta`$ with $`\delta>0`$, or any fixed
positive upper bound on the maximum atom.

To check conditioning explicitly, write $`a_n=p_F(\varnothing)`$, $`v_n=1-a_n`$, and
$`p_{*,n}=p_F(\,\cdot\mid S\ne\varnothing)`$. Put

```math
L_{*,n}=\mathbb E_{p_{*,n}}\log_2 A_{F_n}(S),\quad
J_{*,n}=\mathbb E_{p_{*,n}}|S|=I(F_n)/v_n,
```

and let $`U_*`$ be uniform on the $`2^{N_n}-1`$ nonempty subsets. Then

```math
H(p_{*,n})=\frac{H(F_n)-h_2(v_n)}{v_n},\qquad
D_2(p_{*,n}\Vert U_*)=\log_2(2^{N_n}-1)-H(p_{*,n}).
```

Since $`a_n\le e^{-2n}`$, $`v_n\to 1`$. For Boolean functions every unnormalized
Walsh magnitude is at most $`2^{N_n}`$ and, on this positive spectrum, at least
one. Therefore $`0\le \log_2 A\le N_n`$, and the conditioning changes its mean by at
most $`a_n N_n/v_n`$. It follows that

```math
\frac{L_{*,n}}{N_n}\longrightarrow1,\qquad
\frac{J_{*,n}}{N_n}\longrightarrow0.
```

Also $`H(F_n)/N_n=H(r_n)/n\to 0`$ by the already proved formula for $`L(r_n)`$.
The displayed conditional entropy identity gives

```math
\frac{D_2(p_{*,n}\Vert U_*)}{N_n}\longrightarrow1.
```

Thus the conditioned inequality $`D_2(p_*\Vert U_*)\le\eta L_*+BJ_*`$ fails as well.
Renormalizing amplitudes by $`1/\sqrt{v_n}`$ only shifts $`L_*`$ by
$`-(1/2)\log_2 v_n=o(1)`$ and has no effect on this obstruction. QED.

This does not refute FEI: the same examples have $`H(F_n)/I(F_n)\to 4`$. Indeed
with $`q_n=1-(1-\epsilon_n)^2`$,

```math
H(r_n)=-(1-\epsilon_n)^2\log_2(1-\epsilon_n)^2
         +q_n(2n-2),
```

whose ratio to $`n \epsilon_n`$ tends to four. Tensorization preserves this
ratio. The obstruction targets the strict fractional absorption of $`L`$, even
after mean separation; it does not obstruct an entropy bound with a universal
constant proved by a different invariant.

## 5. A connected obstruction with unavoidable full arity

The independent positive theorem in
[the one-point product manuscript](one-point-products.md),
Sections 1--6, proves the following stronger facts about the needed family.
For $`n\ge 3`$, an integer $`a\ge 1`$, $`m=a2^{n-1}`$ and $`N=nm`$, put
$`F=r_n^{\otimes m}`$ and flip its value at the all-positive physical input,
obtaining $`G`$. It has positive spectrum, obeys the sharp class bound
$`H(G)\le 4I(G)`$, and has no direct positive factorization of arity below $`N`$.
In particular its conditional-dependence graph is complete and its minimal
graphical treewidth is $`N-1`$. The proof of full interaction is canonical in
that manuscript; it does not assume that a chosen graph is minimal.

Its exact influence and useful bounds are

```math
I(G)=an-N2^{1-N},\qquad
0\lt \mathbb E G\le e^{-a},\qquad
\max_Sp_G(S)\le e^{-2a}.
```

For fixed $`a`$, influence is $`\Theta(\log N)`$ despite necessary arity $`N`$.
For $`a=n`$, the function has one connected spectral component, its mean
and largest spectral atom tend to zero, and it retains every normalized
absorption obstruction in Theorem 4, including the nonempty conditioning.
Indeed the point modification changes influence by $`N2^{1-N}=o(1)`$ and
entropy by at most $`h_2(2^{1-N/2})+N2^{1-N/2}=o(1)`$, using Section 3.
Then $`L=N-H/2`$ and $`D=N-H`$ have the same normalized limits. The conditional
argument of Theorem 4 applies because the squared mean still tends to zero.

Thus connected-component bias, maximum atom size, and removing the empty
atom do not repair the fixed strict absorption invariant. The same family
has a proved sharp constant-four FEI bound by the different, paid-interference
argument. This does not refute a mixture or approximation method that
actually pays for its error.

## 6. Sources, exact verification and scope

The elementary Walsh parity fact is classical. Claude Carlet, *Boolean
Functions for Cryptography and Coding Theory*, Section 2.3, printed page 89
(PDF page 89 in the author's 623-page file), explicitly invokes odd Hamming
weight to obtain a nonvanishing Fourier--Hadamard transform. In the sign-valued
Walsh convention used here, the congruence proof in Theorem 1 is self-contained.
Author PDF:
<https://www.math.univ-paris13.fr/~carlet/book-fcts-Bool-vect-crypt-codes.pdf>.
Focused searches for a previously stated FEI full-support reduction did not
identify an exact source; that is not an exhaustive novelty certification.

The entropy continuity estimate is proved directly above rather than relying
on an untracked normalization of a continuity theorem. The tensor-product entropy and influence identities, and removal of an
$`o(n)`$ additive error, are already recorded by O'Donnell--Wright--Zhou,
*The Fourier Entropy--Influence Conjecture for Certain Classes of Boolean
Functions*, Section 1.2, printed page 2. The positive-spectrum and
near-balance restrictions are handled here by the explicit Boolean point flip. The rare-point seed and its obstruction at nonzero mean were
already proved in the [checkpoint's open-problems record](OPEN_PROBLEMS.md); Theorem 4 records its
tensorized, nearly balanced and nonconstant-conditioned consequences.

`check_positive_support_reduction.py` performs independent exact integer Walsh
transforms and physical-edge influence computations for every Boolean function
through three bits, all point choices, and one or two dummy bits. It also tests
all four-bit functions at one fixed point with one dummy bit, verifies exact
spectral total-variation and tail identities, and prints clearly labelled
floating-point diagnostics of the proved asymptotic obstruction. Neither the
finite test nor those diagnostics prove the universal statements; the proofs
above do.

It also constructs four small even-block versions of the family in Section 5, performs
their entire signed Walsh transforms, verifies the complete conditional graph,
and certifies the sign of the full log interaction by comparing two exact
integer products. These finite full-interaction checks use $`(n,m)`$ equal to
$`(2,2),(2,4),(3,2),(3,4)`$; the $`n=2`$ cases are supplementary tests of the
algebraic mechanism outside the stated $`n\ge 3`$ asymptotic family.

No full-FEI bound is claimed here; the companion one-point and recursive
class theorems are separate positive results. The full-support equivalence closes a support
reduction obligation, while the nearly balanced examples eliminate a specific
mean-only repair of the existing absorption mechanism.


## Reproducible checks

The accompanying [exact checker](code/check_positive_support_reduction.py) is mirrored without
changes from the scientific revision. From this note's directory, run:

```bash
python code/check_positive_support_reduction.py
```

Finite checks verify the identities and examples specified by the checker;
the proofs above establish the universal statements.
Exact runs and review qualifications are recorded in [Verification](VERIFICATION.md).

[Sharp one-point products](one-point-products.md) · [Recursive point modifications](point-modifications.md) · [Directed factors](directed-factors.md) · [Affine forest images](affine-forests.md)
