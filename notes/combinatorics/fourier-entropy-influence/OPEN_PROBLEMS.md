# Mathematical targets beyond the proved classes

**Mira Cult · 16 November 2026**

[Overview](README.md) · [Proved results](CATALOGUE.md)

The final target is a dimension-independent constant $`C`$ for
$`H(f)\le CI(f)`$ for every Boolean function, including constants and
unbounded degree. The problems below isolate unpaid costs in the present
proofs. Solving one must not be described as solving general FEI unless
the additional deduction is supplied.

## Universal FEI and the positive-support reduction

The [full-support completion theorem](positive-support.md) now proves that
FEI for **all** positive Boolean spectra is equivalent to full FEI with
exactly the same constant. It uses actual Boolean point modifications,
not a real-valued perturbation. Thus support zeros are no longer a separate
logical obstacle to a prospective all-positive theorem. The argument does
not place the completed function in any restricted graphical or arithmetic
class, and does not prove either universal statement.

The current uniform constants apply to [directed integer factors](directed-factors.md),
[affine forests](affine-forests.md), and [marked-set recursive constructions](marked-set-closure.md).
Their hypotheses allow unbounded interaction size. What remains missing
is a representation or structural payment for arbitrary Boolean spectra.
Putting the whole law in one positive factor does not meet the directed
condition automatically.

## Positive pairwise spectra of treewidth two

The dimension-independent FEI target for positive width-two laws is now
[proved with constant below fourteen](bounded-treewidth.md), even for
genuine triangle potentials. Every fixed width is covered as well.

**Sharper target.** Prove $`H(f)\le4I(f)`$ for every Boolean $`f`$ whose
positive Fourier law factors into unary and pairwise potentials on a graph
of treewidth at most two, or give a Boolean counterexample to this constant.
This target is strictly stronger than the dimension-independent theorem.

Pairwise arithmetic already forces power-of-two Walsh magnitudes. Cacti
and common-feedback-vertex graphs have constant four. The older cutset
bound leaves $`2(k-1-b)`$, and the eleven-vertex path-square graph defeats
the proposed component-count payment. An unrestricted zero-loss two-bit
boundary transfer also fails. Neither is a Boolean counterexample to the
sharper target. A proof must retain a stronger energy invariant or exploit
more Boolean structure than the general integer theorem.

## A uniform payment beyond bounded width

**Target.** Replace the width-dependent entropy payment by a universal
constant for arbitrary positive Boolean Fourier laws, or construct an
explicit diverging family in this class. The proved constant is
$`O(4^{w+1}/(w+1)+\log(w+2))`$ at width $`w`$.

Positive integer factors of any fixed arity already give a constant even when their
factor graph has unbounded treewidth. The missing step is a paid
representation, or a different entropy inequality, for arbitrary Boolean
Walsh tensors. The new directed theorem replaces arity by a statewise
decrease count; the new affine and recursive theorems use different
structure. No one of these hypotheses is proved for arbitrary laws. Grouping a large bag into one factor
retains its arity cost; it does not give a dimension-independent theorem.

## Barriers and more precise next mechanisms

The [directed-load obstruction](directed-factors.md) disproves a universal
cheap integer gauge into factors with a fixed decrease count. For the
$`n`$-bit rare-point law, every such factorization with count at most $`r`$
requires

```math
\log_2K\ge(n/r-1)\log_2(2^{n-1}-1)-1,
```

while influence is $`n2^{1-n}`$. One reduced coefficient repairs that
particular family, but a product of two $`m`$-bit rare-point phases requires
changes at all $`2m`$ singleton spectral states before a one-decrease core
can become possible. A paid multiblock repair must account for the joint
signed sections and denominator; counting or discarding their labels is
insufficient.

The [marked-set closure](marked-set-closure.md) now pays every fixed
$`q\ge2`$ with one constant, including all pair terms and shared marked
edges. The [rare-leaf improvement](marked-rare-leaves.md) retains sharp
constant four across all $`q`$. Thus “more than one marked point” is no
longer the missing step. The concrete boundary is **collision of projected
marks or overlap of physical blocks**: these destroy the product cancellation
or geometric margin. Prove a paid collision term, or find a different
representation with a summable signed score. Arbitrary repeated flips and
changing $`q`$ inside a construction remain unproved. Allowing arbitrary
leaves would merely assume the missing FEI bound at the leaves.

The [approximation barriers](approximation-barriers.md) rule out two cheap
repairs. For the stated two-mark family with $`m=2^n`$ blocks, influence is
$`2n`$, while ordinary nonnegative coordinate-subcube cost is at least
$`3(2^n-1)/8`$ and, for every fixed $`0\le\epsilon\lt1`$,

```math
\log_2\bigl(1+\|\widehat G\|_{1,\epsilon}\bigr)
=\Theta_\epsilon(2^n).
```

The natural signed correction fails the exact Gram-domination assumptions
of the imported entropy theorem; the orthogonal repair is valid but costly.
These are obstructions to the stated conversions, not to affine parity
certificates, mean-square approximations or all interpolation mechanisms.

The [affine proof](affine-forests.md) supplies a fixed fair-direction
fraction for positive Boolean forests. The unrestricted cyclic extension
is false: the [four-cycle energy](cyclic-obstruction.md) has
$`Z=40\lt2\cdot5^2`$. Its odd denominator proves it is not a Boolean Fourier
law; independent fair padding cannot repair it. A cyclic theorem must use
additional Boolean arithmetic or supply a different invariant. A rare-point
law has a unique largest atom and no nonzero translation period, so no
affine change puts it in the positive-forest class. This explains why the
affine and point mechanisms are complementary.

## Absorption still fails after removing the dominant atom

The [stronger Boolean obstruction](positive-support.md) has

```math
 N=n^2 2^{n-1},\qquad I=n^2,\qquad
 |\mathbb Ef|\le e^{-n},\qquad\max_Sp_f(S)\le e^{-2n},
```

and nevertheless $`D_2(p_f\Vert U_N)/N\to1`$ and $`L_f/N\to1`$.
Conditioning on the nonempty spectrum preserves these limits. A single
further point modification makes the minimal positive graph complete and
forces factor arity $`N`$, without changing the contradiction to any fixed
$`D\le\eta L+BI`$, $`\eta<1`$. These examples satisfy $`H\le4I`$.
Near balance, small maximum atom and connectedness therefore do not repair
that particular invariant. A different Boolean-sensitive quantity is needed.

## Uniform absorption fails near constants

The positive-factor proof cannot be extended to arbitrary positive Boolean
spectra by proving the same invariant with fixed coefficients. This already
fails for rare-point phases, independently of any support-zero issue.

**Proposition.** There are no universal constants $`\eta\lt1`$ and finite
$`B`$ such that every positive Boolean Fourier law satisfies

```math
D_2(p_f\Vert U_n)\le\eta L_f+B I(f),
\qquad L_f=\mathbb E_{p_f}\log_2(2^n|\widehat f(S)|).
```

**Proof.** For $`n\ge2`$, let $`f_n(x)=1-2\mathbf1_{\{x=(1,\ldots,1)\}}`$.
Its coefficients and influence are exactly

```math
\widehat f_n(\varnothing)=1-2^{1-n},\qquad
\widehat f_n(S)=-2^{1-n}\quad(S\ne\varnothing),\qquad
I(f_n)=n2^{1-n}.
```

All coefficients are nonzero. Set $`p_0=(1-2^{1-n})^2`$. Its integer
Walsh magnitudes are $`2^n-2`$ at the empty set and $`2`$ elsewhere, so

```math
L_f=p_0\log_2(2^n-2)+(1-p_0),\qquad
H(f_n)=2(n-L_f),\qquad D_2(p_f\Vert U_n)=2L_f-n.
```

Consequently $`L_f/n\to1`$, $`D_2(p_f\Vert U_n)/n\to1`$, and
$`I(f_n)/n\to0`$. Dividing the proposed bound by $`n`$ would give
$`1\le\eta`$. This contradicts the hypothesis. The example is not an FEI
counterexample: $`H(f_n)/I(f_n)\to4`$. ∎

A mean-sensitive repair must therefore change the invariant. The following
standard consequence of edge isoperimetry isolates a cost that can already
be paid. No novelty is claimed for this elementary entropy bound.

**Lemma (the constant-atom label costs at most twice influence).** Let
$`v=\mathrm{Var}(f)`$. If $`v>0`$, let $`p_*`$ be the squared Fourier
law conditioned on $`S\ne\varnothing`$. Then

```math
H(f)=h_2(v)+vH(p_*),\qquad h_2(v)\le2I(f).
```

For $`v=0`$, define the weighted conditional term to be zero; both sides of
the entropy identity are zero. When $`v=1`$, the binary entropy is zero.

**Proof.** After negating $`f`$ if needed, let $`\delta\le1/2`$ be the
probability of its minority value. Then $`v=4\delta(1-\delta)`$. The
automatic identity is the entropy chain rule for the indicator of a
nonempty Fourier set.

In the present sign-function normalization, edge isoperimetry is
$`I(f)\ge2\delta\log_2(1/\delta)`$. One self-contained proof uses the
unordered edge boundary $`b(A)`$ of a subset of the cube. Split it into
halves of sizes $`a,b`$. Induction bounds their internal boundaries by
$`a\log_2(2^{n-1}/a)+b\log_2(2^{n-1}/b)`$, while cross-boundary edges
number at least $`|a-b|`$. With $`m=a+b`$ and
$`t=\min(a,b)/m\le1/2`$, the excess over
$`m\log_2(2^n/m)`$ is $`m[h_2(t)-2t]\ge0`$ by entropy concavity.
Empty sets and the zero-dimensional base are immediate. Since
$`I(f)=2b(A)/2^n`$, the displayed normalization follows.

For $`0<\delta\le1/8`$, monotonicity of binary entropy on $`[0,1/2]`$
and $`h_2(u)\le u[\log_2(1/u)+\log_2 e]`$ imply

```math
h_2(v)\le h_2(4\delta)
\le4\delta[\log_2(1/\delta)-2+\log_2 e]
\le4\delta\log_2(1/\delta)\le2I(f).
```

For $`1/8\le\delta\le1/2`$, concavity of $`\delta\log_2(1/\delta)`$
gives $`4\delta\log_2(1/\delta)\ge3/2`$, while $`h_2(v)\le1`$.
This proves the bound in that range too. Constants were handled separately. ∎

For the rare-point phases, $`p_*`$ is uniform on the $`2^n-1`$ nonempty
sets. Directly from $`v=2^{2-n}(1-2^{-n})`$ one obtains

```math
\frac{h_2(v)}{I(f_n)}\longrightarrow2,\qquad
\frac{vH(p_*)}{I(f_n)}\longrightarrow2.
```

Thus the factor two in the binary-label bound is asymptotically sharp.
The unpaid target is $`vH(p_*)\le C I(f)`$ uniformly. This target is
equivalent to FEI up to adding two to the constant: FEI implies it because
the binary entropy is nonnegative, and the lemma gives the converse with
constant $`C+2`$. The split removes the constant-atom obstruction; it does
not establish the remaining conditional entropy budget.

## Genuine three-state forest edges

**Target.** Prove a dimension-independent FEI bound for every Boolean
Fourier distribution with a unary/edge forest factorization, allowing
arbitrary nonnegative factors, or produce an unbounded-ratio family.

Fixed bits and deterministic equality/complement edges reduce to a positive
quotient and are already covered. Odd-prime exclusion also holds for the
remaining zero cases. What fails is the positive-tree energy inequality:
the explicit Boolean star in [positive forests, Section 4](positive-forests.md#4-a-stronger-entropy-payment-really-fails-when-zeros-are-admitted)
violates it, while still satisfying $`H=2I`$. A successful proof must
charge forbidden-state selection in some additional way. Taking a limit
of arbitrary positive probability models does not suffice, because those
models need not be Boolean-realizable.

The [forbidden-pair theorem](zero-edges.md) now handles a missing pair whose
nonzero sections reduce to positive forests, preserving constant four.
This includes nonproduct forest pieces. The remaining arbitrary-zero
problem must account for two exact failures: a six-bit Boolean forest
produces half-integer sections on its second forbidden-edge cut, and an
integer hard-zero star defeats every positive-proof invariant
$`D_2(p\Vert U)\le\eta L+CJ`$ with $`\eta<1`$. The latter still satisfies
raw FEI. A repair should use Boolean normalization before cutting, track a
stronger norm/lattice invariant, or pay the actual later denominators.


## Pay the local integrality defect

For a positive pairwise integer amplitude array $`A=|W_f|`$, define
$`\Gamma(A)`$ as the least $`\log_2K`$ over positive integers $`K`$ for
which $`KA`$ is a product of positive integer unary and pairwise factors,
including an integer constant factor. Rational local factorization shows
that some finite $`K`$ exists. For forests, $`K=1`$ is possible. The
[integer-factor theorem](integer-forests.md#32-a-paid-local-integrality-defect-on-arbitrary-graphs)
proves

```math
H(f)\le C_FI(f)+2\Gamma(|W_f|),
\qquad C_F=6/\log_2(16/9).
```

**Target.** Prove $`\Gamma(|W_f|)\le CI(f)`$ for all positive pairwise
Boolean Fourier laws, or find an explicit Boolean family disproving this
particular sufficient estimate. A weaker defect with the same entropy
inequality would also be useful.

This would give FEI for all positive pairwise spectra, a larger class than
the current bounded-width and bounded-conditioning results. It would not by itself
cover arbitrary Boolean spectra, which can have zeros and higher-order
logarithmic interactions. A triangle can have arbitrarily large pairwise integer-factor defect as
an abstract integer tensor. The bounded-width theorem bypasses that defect
by allowing integer triangle factors and an influence-paid entropy bound;
it does not bound the Boolean pairwise defect in general.

## Find integer packets with a paid denominator

For a spectral subcube leaf $`L`$, let $`g_L`$ be the actual partial Fourier
section of a Boolean function, with squared norm $`p_L`$. Suppose its
normalized law is a positive forest, or a stated deterministic quotient,
and $`2^{d_L}g_L`$ is integer-valued. Positive bounded-width sections
can now also be used, with their stated larger constant. Applying the arbitrary-integer forest
theorem with its exact scaling cost gives

```math
H(f)\le C_F\mathbb E\bigl[|S\setminus K_L|\bigr]
       +2\mathbb E d_L,
```

where $`C_F=6/\log_2(16/9)`$ and $`K_L`$ is the set of fixed spectral
coordinates. If the actual scaled packets also have power-of-two Fourier
magnitudes, the dyadic theorem gives constant four and its stated component
deficits. No approximation or label term has been omitted in either bound.

**Target.** Construct, for a larger Boolean class or for all Boolean
functions, a partition into suitable actual sections with
$`\mathbb E d_L\le CI(f)`$, or another integer-packet decomposition with
a proved raw entropy bound and a comparable influence payment.

Singleton leaves always exist. With the least nonnegative denominator
exponent, write each nonzero coefficient as $`a_S2^{-d_S}`$ with odd
integer $`a_S`$. Their cost is

```math
2\mathbb E d_S=H(f)+2\mathbb E\log_2|a_S|\ge H(f),
```

with equality when every magnitude is a power of two. This is circular
as a route to FEI. Equal-magnitude Fourier layers need not have integer-valued
inverses, even when every magnitude is a power of two. The
[integer-packet argument](integer-flat-packets.md) cannot be applied to
those layers without paying for the lost integrality. A theorem for a
bounded number of conditioning coordinates is already proved in
[integer forests](integer-forests.md); the unresolved task is a cost that
does not grow with the required number of cuts.

## Low-information mixtures and physical selection

**Mixture target.** Find a class of Boolean Fourier laws $`p_j`$ with a
proved universal entropy–influence bound and a useful decomposition

```math
p_f=\sum_j\lambda_jp_j,
\qquad I(S;J)\le CI(f).
```

The exact chain rule then pays the total entropy. A universal mixture into
Boolean forest laws can be trivial even for three-bit majority: all
positive-weight components must be point masses. Its cost is exactly two
bits, so the example does not disprove an $`O(I)`$ bound. Allowing plateaued
components removes this particular obstruction. The challenge is a
noncircular information estimate from Boolean structure, not existence
of a mixture.

**Physical-tree target.** For an appropriate restriction tree, replace or
pay the half-bit expected-depth cost in

```math
H(f)-4I(f)\le
\mathbb E_L[H(g_L)-4I(g_L)]+\tfrac12\mathbb E D.
```

The actual leaf label has entropy $`\mathbb E D`$. Its coarsening to the
identity of the selected payload does not retain the spectral cost: an
explicit two-payload example violates that replacement. Ordinary convex
combinations of sign-valued functions cannot produce a different
sign-valued function without pointwise agreement, and physical selectors
have Fourier cross terms. The [interpolation proof](interpolation.md)
retains those terms exactly. A universal constant-four closure is
impossible, so a general repair must allow a real additional payment.

## Boolean defects of a tree projection

The tree distribution $`q_T`$ matching selected singleton and edge
marginals satisfies, including support-zero cases,

```math
H(q_T)-H(p_f)=D_2(p_f\Vert q_T),
\qquad \mathbb E_{q_T}|S|=I(f).
```

**Target.** Give a structural Boolean estimate controlling the
realizability defect of $`q_T`$ together with the divergence correction.
The displayed target $`H(q_T)\le CI(f)+D_2(p_f\Vert q_T)`$ alone is only
an equivalent rewriting of FEI. Majority's uniform three-bit projection
is not a Boolean Fourier law, so applying the forest theorem to it is
invalid. Any useful theorem must introduce a separately bounded structural
quantity rather than discard the correction or assume realizability.
