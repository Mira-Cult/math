# A uniform entropy bound from directed integer factors

**Mira Cult · 16 November 2026**

A positive integer factorization of the Walsh magnitudes gives the uniform
bound $`H_{\mathrm{raw}}(h)\le4I(h)`$ when each factor has at most one
decreasing spectral neighbor at each state. The number of factors, their
arity, their overlap, and the graph treewidth are unrestricted. A more
general inequality makes the directed payment and any denominator cost
explicit. A one-atom repair and sharp Boolean obstructions delimit the class.

This extends the [bounded-arity factor argument](bounded-treewidth.md), but
does not prove FEI for every positive Boolean spectrum or for arbitrary
Boolean functions. All logarithms are base two.

**Review status.** Complete proofs with scoped nonauthor model review of the
scientific revision. The review scope, exact revisions, and limitations are
recorded in [Verification](VERIFICATION.md); this is not human peer review.

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

Scientific source: [math-wip at 72102db](https://github.com/Mira-Cult/math-wip/blob/72102dbe92e277f6d616f6a1201d5388992e5dd3/problems/0298-fourier-entropy-influence-conjecture/manuscripts/directional_integer_factors.md).

## 1. Statement: interaction arity does not enter

For a real function $`h`$ on the uniform $`n`$-cube write

```math
H_{\mathrm{raw}}(h)=\sum_s\widehat h(s)^2\log_2\frac1{\widehat h(s)^2},
\qquad I(h)=\sum_s|s|\widehat h(s)^2,\qquad W=\mathbb E h^2.
```

Assume every Fourier coefficient is nonzero and that its Walsh magnitude
tensor has a representation

```math
A(s)=2^n|\widehat h(s)|=c\prod_\alpha u_\alpha(s_\alpha).\qquad\text{(1)}
```

where $`c\ge1`$ and each $`u_\alpha`$ is positive integer-valued. The factors
may overlap arbitrarily and may have arbitrarily many arguments. Neither
a bounded treewidth nor a bounded number of factors is assumed. For a
factor define its directed decrease count at a state by

```math
b_\alpha(s)=\#\left\{i\in\alpha:s_i=0\text{ and }
u_\alpha(s_\alpha)\gt u_\alpha((s^i)_\alpha)\right\}.\qquad\text{(2)}
```

Here $`s^i`$ flips only coordinate $`i`$. Thus only changes from spectral zero
to spectral one are counted. This orientation is fixed by influence;
complementing an arbitrary spectral bit changes influence and is not free.

**Theorem 1 (one decreasing neighbor per factor).** If (1) holds and
$`b_\alpha(s)\le1`$ for every factor and every state, then

```math
H_{\mathrm{raw}}(h)\le4I(h).\qquad\text{(3)}
```

More precisely, the scalar in the given representation supplies the
credit $`H_{\mathrm{raw}}(h)\le4I(h)-2W\log_2c`$.

In particular, (3) is a uniform FEI bound for every Boolean function
satisfying these hypotheses. The same single constant works across all
factor arities and all treewidths. It is a structural class theorem, not
a theorem for every positive Boolean spectrum.

Integer-valued $`h`$ automatically has integer Walsh numerators, but the
factorization with $`c\ge1`$ is an additional hypothesis; integrality of the
whole tensor does not provide it for free. In fact the proof of Theorem 1
requires only representation (1), not integrality of the inverse transform.
Consequently its application to Boolean functions requires a separate
Boolean-realizability hypothesis or construction.

The following broader payment statement makes the cost explicit. Put

```math
p(s)=\frac{A(s)^2}{Z},\qquad L=\mathbb E_p\log_2 A(s),\qquad
J=\mathbb E_p|s|,\qquad
B(s)=\sum_\alpha b_\alpha(s)\log_2 u_\alpha(s_\alpha).
```

**Theorem 2 (paid directed load).** Every representation (1) satisfies

```math
H_{\mathrm{raw}}(h)\le4I(h)+2W(\mathbb E_p B-L).\qquad\text{(4)}
```

The right side is permitted to include a negative correction. Thus
$`\mathbb E_pB\le L`$ suffices for (3), and a sufficient pointwise condition is
$`B(s)\le\log_2A(s)`$ for every state. One may instead use the nonnegative
defect $`\max(0,\mathbb E_pB-L)`$ if a nonnegative error term is preferred.

Theorems 1 and 2 include arbitrary Fourier signs. They do not assert that
an arbitrary law obeying (1) has a Boolean signing.

The constant four is optimal for the integer-valued raw-entropy theorem:
if $`h`$ is the indicator of one physical point, then $`A=1`$ on the full
spectral cube, $`H_{\mathrm{raw}}(h)=2n2^{-n}`$, and $`I(h)=n2^{-n-1}`$. This sharpness
example is not Boolean sign-valued. No optimal constant is claimed for
the Boolean subclass.

## 2. Complete proof

For an edge in direction $`i`$, fix the other bits and write

```math
a=A(0,t),\qquad b=A(1,t),\qquad
U_i(t)=\prod_{\substack{\alpha\ni i\\u_\alpha(0,t)\gt u_\alpha(1,t)}}u_\alpha(0,t).
```

An empty product is one. Every factor not in the product has edge ratio
at most one, while the denominator of each retained factor is at least
one. Therefore

```math
\frac ab\le U_i(t).\qquad\text{(5)}
```

and $`U_i(t)`$ is a positive integer. If $`a>b`$, it follows that $`U_i\ge 2`$,
and hence $`a^2\log_2U_i\ge a^2\ge a^2-b^2`$. If $`a\le b`$, the same final
inequality holds because its left side is nonnegative and its right side
is nonpositive. In all cases,

```math
a^2-b^2\le a^2\log_2 U_i.\qquad\text{(6)}
```

Sum (6) over all assignments to the other coordinates and divide by
$`Z=\sum_sA(s)^2`$. The left side becomes $`1-2\Pr_p[S_i=1]`$; the right side
becomes $`\mathbb E_p[\mathbf1_{\{S_i=0\}}\log_2U_i(S_{-i})]`$. Summing over coordinates yields

```math
\begin{aligned}
n-2J
&\le\mathbb E_p\sum_i\mathbf1_{\{S_i=0\}}\log_2 U_i(S_{-i})\\
&=\mathbb E_p\sum_\alpha b_\alpha(S)\log_2 u_\alpha(S_\alpha)
=\mathbb E_p B.
\qquad\text{(7)}
\end{aligned}
```

The equality in (7) just counts once each factor that strictly decreases
along the specified zero-to-one edge. It remains true when a factor is
increasing in some states and decreasing in others.

By the definition of $`A`$, Parseval gives the exact identities

```math
\frac{H_{\mathrm{raw}}(h)}W=2(n-L),\qquad \frac{I(h)}W=J.\qquad\text{(8)}
```

Subtract $`L`$ in (7), multiply by $`2W`$, and use (8) to obtain (4).
If every $`b_\alpha\le1`$, then pointwise

```math
B(s)\le\sum_\alpha\log_2u_\alpha(s_\alpha)\le\log_2 A(s).
```

where the final inequality uses $`c\ge1`$. Equation (3) follows. This proves
both theorems; retaining $`\mathbb E_pB\le L-\log_2c`$ gives the stronger scalar credit.
There is no entropy tensorization, degree bound, variance
lower bound, or limiting argument in this proof.

For $`n=0`$, (1) says $`|h|=c\prod u\ge1`$, so raw entropy is nonpositive
and (3) still holds. The zero function and integer constants/characters
may be included separately; their nonpositive raw entropy does not
require the full-support hypothesis. Arbitrary zero spectra are not
covered by (1).

## 3. Concrete high-arity factors

The condition in (2) permits more than factors depending adversely on one
fixed coordinate.

* Every coordinatewise nondecreasing positive integer factor has
  $`b_\alpha=0`$, regardless of arity or interaction strength.
* A factor that is nondecreasing in all but one of its coordinates has
  $`b_\alpha\le1`$.
* Let $`C`$ be any subcube of its spectral argument cube, with any pattern
  of fixed zeros and ones. For an integer $`M\ge 1`$, the factor equal to one
  on $`C`$ and equal to $`M`$ outside $`C`$ has $`b_\alpha\le1`$. An outside state
  can enter a subcube by a one-bit change only when exactly one of its
  fixed-coordinate requirements is violated. The responsible coordinate
  is then unique. This includes high-arity negative AND interactions,
  such as $`u(s)=2^{M(1-\prod_i s_i)}`$.

All such factors may coexist and overlap in (1). Their graph may be
complete. For example, if

```math
\log_2 A(s)=\gamma+
\sum_\alpha M_\alpha\prod_{i\in\alpha}s_i+
\sum_\beta N_\beta\bigl(1-\mathbf1_{C_\beta}(s)\bigr),
```

with $`\gamma\ge 0`$ and all $`M_\alpha,N_\beta`$ nonnegative integers, then (3)
holds. Unary descending factors are included by taking one-dimensional
subcubes. The nonnegative scalar and coefficient conditions are real
restrictions, not disposable choices of gauge.

If a paid integer reparameterization gives
$`KA=c\prod_\alpha u_\alpha`$, with $`K\ge 1`$, $`c\ge1`$ and the same
one-decrease condition, apply the proof to $`K h`$ and divide by $`K^2`$:

```math
H_{\mathrm{raw}}(h)\le4I(h)+2W\log_2 K.\qquad\text{(9)}
```

Thus the denominator cost is present explicitly. No assertion that the
cost is always $`O(I/W)`$ is made.

## 4. A spectral-atom repair that pays for the rare-point obstruction

The obstruction proved below concerns multiplicative reparameterization.
Reducing one Fourier coefficient changes the object and gives a different
repair. Its inverse transform need not be integer-valued; the amplitude
factor hypothesis of Theorem 1, rather than integrality of that inverse,
is what makes this repair legitimate.

**Theorem 3 (one exceptional atom).** Let $`f`$ be Boolean with full Fourier
support. Fix a spectral set $`T`$ and $`0<\lambda\le1`$. Define a real function
$`h`$ by retaining every Fourier coefficient of $`f`$ except

```math
\widehat h(T)=\lambda\widehat f(T).
```

Suppose $`A_h(s)=2^n|\widehat h(s)|`$ has representation (1) with
$`b_\alpha(s)\le1`$ everywhere. Then

```math
H(f)\le\left(4+\frac1{\ln2}\right)I(f).\qquad\text{(A1)}
```

If the representation has $`c\ge\sqrt e`$, in particular if its scalar is
an integer at least two, the stronger conclusion holds:

```math
H(f)\le4I(f).\qquad\text{(A2)}
```

The hypotheses are on the modified amplitude tensor; no operation on
the physical truth table is asserted to preserve Booleanity. The actual
function $`f`$ remains Boolean throughout.

**Proof.** Put $`p=\widehat f(T)^2`$, $`q=\widehat h(T)^2=\lambda^2p`$, and
$`\eta(t)=t\log_2(1/t)`$ with its continuous endpoint values. The identities

```math
W_h=1-p+q,\qquad I(h)=I(f)-|T|(p-q)\le I(f),
\qquad H(f)=H_{\mathrm{raw}}(h)+\eta(p)-\eta(q).\qquad\text{(A3)}
```

are exact. Both $`p,q`$ lie in $`[0,1]`$, so $`\eta(q)\ge0`$. For an arbitrary
atom, $`\eta(p)\le(1-p)/\ln2\le W_h/\ln2`$; the first inequality is
$`-p\ln p\le1-p`$. The scalar credit in Theorem 1 therefore gives

```math
H(f)\le4I(h)+W_h\left(\frac1{\ln2}-2\log_2c\right).\qquad\text{(A4)}
```

When $`c\ge\sqrt e`$, the last parenthesis is nonpositive, proving (A2).
This part of the argument uses only normalization $`\lVert f\rVert_2=1`$ in addition
to the amplitude hypotheses, so it also holds for normalized real $`f`$.

For (A1) with only $`c\ge1`$, bound the single-atom entropy by influence.
If $`T`$ is empty, $`\eta(p)\le\operatorname{Var}(f)/\ln2\le I(f)/\ln2`$. If $`T`$ is nonempty,
choose $`i\in T`$. Write $`D_if(x)=(f(x)-f(x^i))/2`$, where $`x^i`$ flips
coordinate i. This Boolean half derivative takes values in
$`\{0,-1,1\}`$, so

```math
|\widehat f(T)|=|\mathbb E[D_i f\,\chi_T]|
\le\mathbb E|D_i f|=\operatorname{Inf}_i(f).
```

Writing $`a=|\widehat f(T)|`$, the elementary maximum
$`\max_{0\le a\le1}a\ln(1/a)=1/e`$ gives

```math
\eta(p)=\frac{2a^2\ln(1/a)}{\ln2}
\le\frac{2a}{e\ln2}\le\frac{I(f)}{\ln2}.
```

Use this estimate, $`\eta(q)\ge0`$, and Theorem 1 in (A3) to prove (A1).
All zero terms in these scalar identities use continuous conventions;
full support itself is retained because $`\lambda>0`$. QED.

For the mandatory family $`f_n=1-2\mathbf1_{\{\text{physical point}\}}`$, $`n\ge 2`$, divide
the exceptional constant Walsh magnitude $`2^n-2`$ by $`2^{n-1}-1`$.
Every resulting Walsh magnitude is exactly two. Thus the core has
$`c=2`$ and no nonconstant factors, and (A2) gives $`H(f_n)\le 4I(f_n)`$.
The same argument applies after multiplying $`f_n`$ by any character;
the exceptional atom then moves to that character's label. This pays
the exceptional atom without the denominator cost that Proposition 4
shows is unavoidable for multiplicative conversion. At $`n=3`$ the
inverse core already takes the noninteger values $`1/2`$ and $`-3/2`$,
illustrating why it would be incorrect to cite only an integer-valued
function theorem instead of the factor proof above.

The same reasoning is a reusable template. If a core class satisfies
$`H_{\mathrm{raw}}(h)\le CI(h)-2W_h\log_2c`$, then one increased coefficient preserves
the same constant $`C`$ whenever $`c\ge\sqrt e`$. The factor version of the
checkpoint's constant below fourteen also has this scalar credit:
apply its factor proof to $`h/c`$ and scale back. Thus the one-atom repair
applies there too. In particular, a positive integer core tensor of
treewidth two with all entries even has gcd scalar at least two in the
checkpoint's elimination factorization. No integer-valued inverse of
that core tensor is needed for this use of its factor proof.

## 5. A related extension of the checkpoint's constant below fourteen

If each factor has $`b_\alpha(s)\le r`$ instead, the [bounded-treewidth checkpoint's](bounded-treewidth.md) scalar
entropy argument improves from maximum arity to maximum directed decrease
count. Specifically its Lemma 4 remains valid whenever $`a/b\le U`$ and $`U`$
is a positive integer: the proof only uses $`0\le a^2/b^2\le U^2`$.
Applying it with $`U=U_i(t)`$ above gives

```math
D_2(p\Vert U_n)\le\frac5{16}\mathbb E_p B+2J
\le\frac{5r}{16}L+2J.\qquad\text{(10)}
```

The first inequality uses precisely the conditional-entropy tensorization
proved in the checkpoint. Therefore, for $`r\le 3`$, its unchanged absorption
with $`q=\log_2 23`$ yields

```math
H_{\mathrm{raw}}(h)\le C_2I(h),\qquad
C_2=\frac{2(2+\log_2 23)}{\log_2(23/12)}\lt 14.\qquad\text{(11)}
```

Every positive integer factor of arity at most three has $`b_\alpha\le 3`$,
so (11) includes the earlier bounded-arity-three theorem and allows
arbitrary additional high-arity factors satisfying the decrease-count
condition. Theorem 1 supplies the stronger constant four when $`r=1`$.
The exact scalar and constant certificates remain those in the existing
bounded-treewidth checker; they are not new numerical evidence.

## 6. An infinite full-support Boolean family with unbounded treewidth

This construction certifies Boolean realizability and unbounded spectral
interaction size. It is deliberately not a claim of the first FEI bound
for these particular functions: the existing integer flat-packet theorem
also gives them constant four.

Let $`\ell\ge 1`$ be odd, let $`d=(d_1,\ldots,d_\ell)`$ be spectral bits, and let
$`\Phi(d)=\mathbf1[\sum_jd_j>\ell/2]`$. It is balanced under the uniform law and is
coordinatewise nondecreasing. On the $`m=\ell+3`$ core spectral coordinates
$`s=(a,b,c,d)`$ define the nonnegative integer energy

```math
v(s)=3-2a-2b-c+ab+bc+c\Phi(d).\qquad\text{(12)}
```

Its possible values are between zero and three. The sums over $`(a,b)`$
of the weights with $`c=0`$ and $`c=1`$ before the last term are 73 and 22,
respectively. Since exactly half the $`d`$ states have $`\Phi=1`$,

```math
\sum_s4^{v(s)}=73\cdot2^\ell+22\bigl(2^\ell+3\cdot2^{\ell-1}\bigr)
=2^{\ell+7}=4^k,\qquad k=\frac{\ell+7}2.\qquad\text{(13)}
```

Put $`D_s=k-v(s)`$. These are nonnegative integers, at most $`k`$, and
$`\sum_s4^{-D_s}=1`$. The elementary Kraft construction therefore supplies
a complete quaternary prefix code with one word of length $`D_s`$ for
each core label $`s`$. Identify each quaternary digit with two bits. The
codeword specifies a subcube $`C_s`$ of a $`2k`$-bit physical address cube,
fixing its first $`2D_s`$ bits. These subcubes partition the address cube.

On the $`2(k-D_s)`$ free address bits choose the quadratic bent sign

```math
\beta_s(y)=(-1)^{\sum_{j=D_s+1}^k y_{2j-1}y_{2j}}.
```

Let $`x`$ be an independent $`m`$-bit physical sign cube. Define the Boolean
function, on $`N=m+2k=2\ell+10`$ physical variables, by

```math
F_\ell(x,y)=\chi_s(x)\beta_s(y)\qquad\text{when }y\in C_s.\qquad\text{(14)}
```

The address cells are disjoint and exhaustive, so (14) is sign-valued.
For every core spectral label $`s`$ and every address spectral label $`t`$,
the fixed coordinates of $`C_s`$ contribute magnitude $`2^{-2D_s}`$, and
the remaining bent block contributes magnitude $`2^{-(k-D_s)}`$. Thus

```math
|\widehat F_\ell(s,t)|=2^{-k-D_s}=2^{-2k+v(s)}.\qquad\text{(15)}
```

In particular every Fourier coefficient is nonzero, and

```math
A_F(s,t)=2^N|\widehat F_\ell(s,t)|=2^{m+v(s)}.
```

The representation

```math
m+v(s)=(m-2)+2(1-a)+2(1-b)+(1-c)+ab+bc+c\Phi(d).\qquad\text{(16)}
```

is of the form in Theorem 1: the first three nonconstant factors are
unary descending factors, and the remaining factors are nondecreasing.
The scalar is $`2^{m-2}\ge 1`$. The fair address spectral bits do not occur
in any factor. Hence $`H(F_\ell)\le4I(F_\ell)`$ uniformly in $`\ell`$ by Theorem 1.

To verify unbounded interaction size, the ordinary real multilinear
polynomial for majority on $`\ell`$ variables has nonzero coefficient

```math
(-1)^{(\ell-1)/2}\binom{\ell-1}{(\ell-1)/2}
```

on $`\prod_jd_j`$. This follows by taking the alternating sum of its
values on the lower faces. Consequently $`\log p_F`$ has a nonzero
coefficient on $`c\prod_jd_j`$. In a positive graphical factorization,
every monomial in the sum of the log potentials lies in some clique.
The graph must therefore contain the clique $`\{c,d_1,\ldots,d_\ell\}`$, of
size $`\ell+1`$; its treewidth is at least $`\ell`$. The minimum factor arity
also grows at least as $`\ell+1`$. This is not a bounded-width family with
the width hidden in its notation.

For comparison, direct calculation gives

```math
\mathbb E_{p_{\mathrm{core}}}v=\frac{167}{64},\qquad
H(F_\ell)=2\ell+\frac{281}{32},\qquad
I(F_\ell)=\ell+\frac{1061}{256}+\frac{33}{128}\alpha_\ell,\qquad
\alpha_\ell=\frac{\ell}{2^\ell}\binom{\ell-1}{(\ell-1)/2}.\qquad\text{(17)}
```

Here $`\alpha_\ell`$ is the excess of the mean Hamming weight in the majority
half over $`\ell/2`$. The three core bits have total marginal $`165/256`$;
the majority output has marginal $`161/256`$; and the $`2k`$ address bits
contribute influence $`k`$. These identities verify (17). They are not
needed in the proof of Theorem 1. At $`\ell=1`$ the entropy/influence ratio
is $`92/45>2`$, so the class does not collapse to the immediate bound
$`H\le2I`$ for globally coordinatewise increasing spectral laws.

## 7. Mandatory obstruction and the remaining general problem

For the rare-point Boolean function on $`n\ge 3`$ bits, its Walsh magnitude
tensor is $`A(0)=2^n-2`$ and $`A(s)=2`$ otherwise. Put $`M=2^{n-1}-1`$. The
natural single factor after extracting scalar two is $`u(0)=M`$, $`u(s)=1`$
otherwise. At the all-zero state it has $`b(0)=n`$, violating the
one-decrease condition. In fact no change of factorization removes the
following obstruction at bounded denominator cost.

**Proposition 4 (all representations pay on the rare-point family).**
Fix any positive integer $`r`$. If

```math
K A(s)=c\prod_\alpha u_\alpha(s_\alpha),
```

with $`K\ge 1`$, $`c\ge1`$, positive integer factors, and $`b_\alpha(s)\le r`$ at
every state, then

```math
\log_2K\ge\left(\frac nr-1\right)\log_2M-1.\qquad\text{(18)}
```

Consequently, for every fixed $`r`$ and finite $`B`$, a denominator payment
$`\log_2K\le BI(f_n)`$ is impossible for all sufficiently large $`n`$.

**Proof.** For any positive tensor define the intrinsic downward load

```math
G_A(s)=\sum_{i:s_i=0}\left[\log_2\frac{A(s)}{A(s^i)}\right]_+.
```

Multiplying $`A`$ by a scalar does not change this load. The factor
inequality (5), applied at each such edge, shows pointwise that

```math
G_A(s)\le\sum_\alpha b_\alpha(s)\log_2u_\alpha(s_\alpha)
\le r\log_2(KA(s)).\qquad\text{(19)}
```

At $`s=0`$ the rare-point tensor has $`G_A(0)=n\log_2M`$ and
$`\log_2A(0)=1+\log_2M`$. Substituting these values into (19) proves (18).
Its lower bound is quadratic in $`n`$ for fixed $`r`$, whereas
$`I(f_n)=n2^{1-n}`$ tends to zero. This proves the proposition. QED.

The obstruction also survives optimization of the expected-load defect
over arbitrary positive integer factors, with no restriction on their
individual decrease counts. The first inequality of (19) is always
valid, so for any representation of $`A`$ itself,

```math
\mathbb E_p B-L\ge\mathbb E_p G_A-L
=p(0)(n-1)\log_2M-1.\qquad\text{(20)}
```

Here $`G_A`$ vanishes away from zero and
$`L=1+p(0)\log_2M`$. The right side of (20) is again quadratic in $`n`$.
Thus even replacing the sufficient pointwise condition by an expected
condition cannot give a uniform influence payment on this family.
These are obstructions to the entire specified representation-payment
route, not to FEI. The rare-point family itself has bounded FEI ratio.

**Proposition 5 (one shaved atom is not universal).** For every $`m\ge 3`$,
the product of two rare-point signs on disjoint $`m`$-bit blocks cannot be
put into Theorem 1's factor class by reducing just one Fourier magnitude.
In fact at least $`2m`$ distinct Fourier magnitudes must be reduced before
such a representation can become possible.

**Proof.** In the tensor $`A`$ for that product, put $`M=2^{m-1}-1`$. At
each of the $`2m`$ singleton spectral states $`e_i`$, one block has its
nonempty magnitude two and the other has empty magnitude $`2M`$. Thus
$`A(e_i)=4M`$. Flipping any of the $`m`$ zero coordinates in the other
block changes that magnitude to four, giving

```math
G_A(e_i)\ge m\log_2M\gt 2+\log_2M=\log_2A(e_i).\qquad\text{(21)}
```

The strict inequality follows from $`(m-1)\log_2M>2`$, already true at
$`m=3`$. A one-decrease representation with $`c\ge1`$ necessarily satisfies
$`G_A(s)\le\log_2A(s)`$ by (19) with $`r=K=1`$.

Now reduce any collection of Fourier magnitudes. At any state whose
own magnitude was not reduced, its outgoing-edge denominators only
decrease, so its intrinsic load $`G_A(s)`$ cannot decrease, while
$`\log_2 A(s)`$ is unchanged. Every singleton state in (21) must therefore
itself be reduced before the necessary condition can hold. This proves
the proposition. QED.

These product functions already satisfy constant-four FEI by disjoint
tensorization of the rare-point bound. Proposition 5 separates a useful
one-atom repair from a universal decomposition and illustrates why
disjoint products or a proved recursive closure are a materially
different next mechanism.

The general gap is now precise: arbitrary high-arity factors may have
many outgoing decreases at the same state, and a scalar/denominator
conversion to a fixed-decrease-count class cannot always have cost
$`O(I)`$, even on actual Boolean spectra. A repair must change the object
being paid, for example by separating atoms or scales, using interference
with an explicit cost, or retaining compensating negative contributions.
A cleverer gauge within (18) alone cannot suffice. The theorem for the
directed class supplies no such repair for an arbitrary positive Boolean
spectrum.

## 8. Relation to prior classes and review scope

The bounded-arity checkpoint pays a log factor once for each incident
coordinate. The present proof counts only strict decreases, and its
one-decrease case avoids entropy absorption entirely. Theorem 1 applies
to every Boolean signing compatible with (1), not just to (14).

Physical read-once composition and the O'Donnell--Tan biased FEI+
hypotheses are different assumptions. The structural theorem does not
assume a physical composition or a signed physical partition. Nevertheless
the explicit witness (14) is a flat-packet construction already covered
by the [integer flat-packet theorem](integer-flat-packets.md). It establishes breadth of the new
spectral hypothesis, not a priority claim for the example's inequality.

A bounded search on 17 November 2026 UTC used both search engines with
the phrases "Fourier entropy integer factorization", "Fourier entropy
spectral treewidth", "Fourier entropy monotone spectra factor", and
"Fourier entropy influence log supermodular spectra". No matching
directed-factor theorem was located. This is not a certification that
none exists. The primary Paraashar--Saurabh abstract, arXiv:2611.06451,
concerns physical nonnegative affine-subspace representations and
approximants; it does not state the spectral multiplicative hypothesis
used here. The earlier OWZ and OT source comparisons remain those of
[References](REFERENCES.md). The exact-source nonauthor model review is recorded in
[Verification](VERIFICATION.md). An exhaustive applicability and priority
audit is still required before stronger novelty claims. General FEI, including the full positive-spectrum class,
remains unresolved here.


## Reproducible checks

The accompanying [exact checker](code/check_directional_integer_factors.py) is mirrored without
changes from the scientific revision. From this note's directory, run:

```bash
python code/check_directional_integer_factors.py
python code/check_directional_integer_factors.py --boolean-ell 5
```

Finite checks verify the identities and examples specified by the checker;
the proofs above establish the universal statements. The second command includes the signed Boolean witness on twenty variables.
Exact runs and review qualifications are recorded in [Verification](VERIFICATION.md).

[Bounded treewidth](bounded-treewidth.md) · [Affine forest images](affine-forests.md) · [Recursive point modifications](point-modifications.md) · [Positive support and obstruction](positive-support.md)
