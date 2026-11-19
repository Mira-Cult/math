# Forbidden spectral pairs: an integral cut and two limits of iteration

**Mira Cult · 16 November 2026**

A missing two-coordinate Fourier pattern has a useful Boolean consequence:
the corresponding two-coordinate partial Fourier transform is integer-valued,
with no rescaling cost. For a Boolean parent whose Fourier law factors
over a forest, this gives a constant-four extension when a forbidden pair
leaves positive forest sections after the stated deterministic reductions.

The cut does not iterate freely, even for an actual Boolean function with a
forest Fourier law. A second obstruction shows that the positive-factor
entropy-production estimate cannot extend unchanged to all integer forest
spectra with genuine zeros. Neither obstruction disproves FEI.

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

## 1. Normalization and the forbidden-pair lemma

Use the uniform sign cube. For integer-valued $`h`$ on $`n`$ variables, put

```math
W_h(s)=2^n\widehat h(s),\qquad w=\mathbb E h^2,
\qquad H_*(h)=\sum_s\widehat h(s)^2\log_2\frac1{\widehat h(s)^2},
\qquad I(h)=\sum_s|s|\widehat h(s)^2.
```

Raw entropy $`H_*`$ may be negative. For $`h\ne0`$, let
$`p_h(s)=\widehat h(s)^2/w`$. Then

```math
\frac{H_*(h)}w=H(p_h)-\log_2 w.
```

The [integer-forest theorem](integer-forests.md) gives
$`H_*(h)\le C_F I(h)`$, with $`C_F=6/\log_2(16/9)<7.229`$, for positive
forest laws and their stated deterministic quotients. The
[dyadic integer-forest theorem](spectral-conditioning.md#2-integer-forest-packets-with-unrestricted-amplitude-spread)
gives constant four when all nonzero Fourier magnitudes are powers of two.

**Lemma 1 (forbidden pair).** Let $`f`$ be Boolean and $`i,j`$ distinct
coordinates. Suppose some pattern $`a_*\in\{0,1\}^2`$ never occurs in its
Fourier support. Define the four partial Fourier sections

```math
g_a(y)=\frac14\sum_{x_i,x_j\in\{-1,1\}}
 f(x_i,x_j,y)\chi_a(x_i,x_j).
```

Every $`g_a`$ is integer-valued. More precisely, at each physical point
$`y`$, exactly one section equals $`1`$ or $`-1`$, and the other three are
zero. The section $`g_{a_*}`$ is identically zero.

**Proof.** The absent spectral cylinder makes the entire Fourier transform
of $`g_{a_*}`$ zero, hence $`g_{a_*}=0`$. Fix $`y`$. Multiply the Boolean
two-bit function $`f(\cdot,y)`$ by a character so that its absent coefficient
is the $`x_ix_j`$ coefficient. The resulting function has the form
$`a+bx_i+cx_j`$. Its square is one on all four inputs. Comparing coefficients
gives

```math
ab=ac=bc=0,\qquad a^2+b^2+c^2=1.
```

Exactly one coefficient is therefore $`1`$ or $`-1`$, and the others are
zero. Character multiplication only permutes the four coefficients, proving
the assertion in the original orientation. ∎

The omitted pattern need not be $`(1,1)`$. The proof changes neither entropy
nor any influence outside the two removed coordinates.

**Corollary 2 (free pair conditioning).** If every nonzero section in Lemma 1
belongs to an integer-function class satisfying $`H_*(h)\le CI(h)`$, then

```math
H(f)\le C\sum_{k\notin\{i,j\}}\mathrm{Inf}_k(f)\le CI(f).
```

**Proof.** The sections partition the Fourier coefficients. Consequently

```math
H(f)=\sum_a H_*(g_a),\qquad
\sum_a I(g_a)=\sum_{k\notin\{i,j\}}\mathrm{Inf}_k(f).
```

Sum the assumed raw inequalities. These exact identities retain the label
entropy through raw normalization; no extra normalization term is discarded. ∎

For example, $`C=C_F`$ applies to positive forest sections with the permitted
quotients. The [bounded-treewidth theorem](bounded-treewidth.md) supplies the
same type of consequence for larger positive conditional classes, with its
stated constants.

## 2. Constant four through one dominating forbidden edge

**Corollary 2a.** Suppose $`f`$ is Boolean and its squared Fourier law factors
over a forest, with zeros allowed. Let $`i,j`$ have a missing support pattern.
Assume that every nonzero partial Fourier section on $`\{i,j\}`$, after
removing fixed spectral coordinates and contracting deterministic
equality/inequality blocks, has a strictly positive forest law. Then

```math
H(f)\le4\sum_{k\notin\{i,j\}}\mathrm{Inf}_k(f)\le4I(f).
```

**Proof.** The [Boolean forest arithmetic theorem](forest-arithmetic.md#4-arithmetic-rigidity-of-boolean-spectral-forests)
applies with zeros and proves that every nonzero Fourier magnitude of $`f`$
is a power of two. Lemma 1 makes the partial sections integer-valued. Their
coefficients inherit the same magnitude property, so each section satisfies
the [dyadic integer-forest theorem](spectral-conditioning.md#2-integer-forest-packets-with-unrestricted-amplitude-spread)
after its permitted quotient. Corollary 2 finishes the proof. ∎

A sufficient graph condition is that the endpoints of one forbidden edge meet
every genuine three-state edge of the forest. After conditioning on those
endpoints, each such constraint becomes an individual fixed-state condition.
Propagate forced states, contract deterministic blocks, and discard zero-mass
sections. Every remaining edge factor is positive. The reduced conditional
law is therefore a positive forest law. This includes arbitrarily many
hard-zero edges meeting a central pair, with arbitrary positive forest pieces
attached. There is no degree or zero-edge-count parameter in the bound.

The common-center case was already covered by one-bit spectral conditioning:
a one-bit section of a Boolean function is always integer-valued. An earlier
result in this investigation also established constant four for adaptive
spectral trees of depth at most two with **product** leaf laws; that already
covers pure double-stars; its exact historical source is recorded under
[the earlier product-leaf theorem](REFERENCES.md#earlier-depth-two-product-leaf-bound).
The additional scope of Corollary 2a is conditional
**forest** pieces that need not be product laws, and the stronger influence
bound outside the cut. The generic two-bit dyadic cut paid an additional two;
the forbidden-cylinder argument removes that payment here.

No free iterative decomposition is asserted when many zero edges remain
beyond every such pair.

### An explicit Boolean witness outside the positive and star classes

On four spectral bits $`(a,b,c,d)`$, let $`\mathcal S`$ consist of the eight
states satisfying

```math
(b,c)\ne(1,1),\qquad b=1\Longrightarrow a=0,
\qquad c=1\Longrightarrow d=0.
```

The uniform law on $`\mathcal S`$ factors into three zero-edge indicators
on the path $`a-b-c-d`$. There are four states with $`(b,c)=(0,0)`$, two
with $`(1,0)`$, and two with $`(0,1)`$. Its coordinate means are
$`3/8,1/4,1/4,3/8`$, and its entropy is three.

Enumerate the states in increasing little-endian order and let
$`\phi:\{0,1\}^3\to\mathcal S`$ be this bijection. On four physical
bits $`x`$ and three address bits $`y`$, define

```math
F(x,y)=(-1)^{\phi(y)\cdot x}.
```

Its Fourier coefficients satisfy

```math
\widehat F(s,t)=2^{-3}\sum_{y:\,\phi(y)=s}(-1)^{t\cdot y}.
```

Thus there are 64 nonzero coefficients, all of magnitude $`1/8`$. The
spectral law is the uniform path law times three independent fair bits.
Therefore

```math
H(F)=6,\qquad I(F)=\frac54+\frac32=\frac{11}{4},
\qquad \frac{H(F)}{I(F)}=\frac{24}{11}>2.
```

All three forbidden edges meet the central pair $`\{b,c\}`$, so Corollary
2a applies. Products with fresh bent functions give an infinite family with
the same support obstruction. This witness is plateaued and already has an
FEI proof; it demonstrates strict containment of support classes, not a first
entropy bound for the example.

## 3. Why free forbidden-edge cuts do not iterate

The integer-valued function $`h(x,y)=(x+y)/2`$ has no constant or $`xy`$
Fourier coefficient, but its $`x`$ and $`y`$ sections equal $`1/2`$. It
arises as the first section of the Boolean selector

```math
F(z,x,y)=\frac{(1+z)x+(1-z)y}{2}.
```

The two first sections $`(x+y)/2`$ and $`(x-y)/2`$ are integer-valued and
have disjoint physical supports. Their signed-partition property alone does
not justify a second integral cut.

The next example shows the failure even when both cuts use genuine forbidden
edges of a Boolean forest law.

### A six-bit Boolean example with two genuine hard-zero stars

On three physical bits $`y`$, in increasing little-endian truth-table order,
put

```math
h=(-1,-1,-1,0,0,0,0,1),\qquad
k=(0,0,0,-1,1,1,1,0).
```

Their supports are disjoint and $`h^2+k^2=1`$ pointwise. Their unnormalized
Walsh transforms are

```math
W_h=(-2,-2,-2,2,-4,0,0,0),\qquad
W_k=(2,2,2,-2,-4,0,0,0).
```

Both norms squared equal $`1/2`$, and their normalized spectral laws coincide.
Call the common law $`p_Y`$. It assigns probability $`1/8`$ to each state
with $`s_2=0`$, and probability $`1/2`$ to $`(s_0,s_1,s_2)=(0,0,1)`$.
All other atoms vanish. This is a genuine three-state star centered at
$`s_2`$, with forbidden pairs $`(s_2,s_i)=(1,1)`$ for $`i=0,1`$.

For three fresh physical sign bits $`a,b,v`$, define

```math
F(y,a,b,v)=ah(y)+k(y)\left[\frac{1+v}{2}+b\frac{1-v}{2}\right].
```

Where $`h`$ is nonzero, this equals $`ah`$; where $`k`$ is nonzero, the
bracket is either one or $`b`$. Hence $`F`$ is Boolean. Its nonzero Fourier
coefficients are

```math
\widehat F(t;1,0,0)=\widehat h(t),\qquad
\widehat F(t;0,\beta,\gamma)
=\frac12(-1)^{\beta\gamma}\widehat k(t),
\quad\beta,\gamma\in\{0,1\}.
```

Its spectral law is exactly $`p_Y\times q`$, where $`q`$ assigns mass
$`1/2`$ to $`(S_a,S_b,S_v)=(1,0,0)`$ and mass $`1/8`$ to each of the
four states with $`S_a=0`$. The auxiliary law is another genuine three-state
star, centered at $`S_a`$. Thus the full law is a product of two genuine
hard-zero stars.

Cut the forbidden pair $`\{a,b\}`$ first. The section at spectral pattern
$`(1,0)`$ is exactly $`h(y)`$, independent of $`v`$, and is integer-valued.
Now cut its forbidden pair $`\{y_0,y_2\}`$. With $`y_1`$ left free, the
three nonzero sections, in pair-frequency order $`00,10,01`$, are

```math
(-1/2,0),\qquad(0,-1/2),\qquad(-1/2,-1/2).
```

They are not integer-valued. The original function was Boolean, and both
cuts were made at genuine forbidden edges. This excludes the inference that
every successive forbidden-edge packet remains integral. It does not exclude
a paid recursive argument. In this example the displayed product law gives
$`H(F)=4`$ and $`I(F)=2`$ directly. No smallest-counterexample claim is made.

## 4. A limit on linear positive-forest energy slack

For spectral bits $`r,x_1,\ldots,x_N`$, $`N\ge1`$, consider the genuine
star energy

```math
v(r,x)=(1-r)\left(1+\sum_{j=1}^N(1-x_j)\right).
```

Its minimum is zero, attained exactly when $`r=1`$. The minimum-layer
indicator has degree one over $`\mathbb F_2`$, so its dimension-minus-degree
is $`\kappa=N`$. Let $`p\propto4^v`$ and

```math
B=\mathbb E_p\left[v+2\left(r+\sum_jx_j\right)\right],\qquad
\theta=\frac{4\cdot5^N}{4\cdot5^N+2^N}.
```

The branch $`r=0`$ has weight $`4\cdot5^N`$, mean energy $`1+4N/5`$,
and mean leaf weight $`N/5`$. The branch $`r=1`$ has weight $`2^N`$,
zero energy, and mean total coordinate weight $`1+N/2`$. Therefore

```math
B-\kappa=\theta\left(1+\frac N5\right)+(1-\theta)2.
```

No universal bound $`B-\kappa\ge an-O(1)`$ for positive integer forest
energies can have $`a>1/5`$, where $`n=N+1`$. Even the exact candidate
$`B-\kappa\ge1+(n-1)/5`$ fails for every $`N>5`$, with deficit

```math
(1-\theta)\left(\frac N5-1\right)>0.
```

This is an energy-level obstruction. No Boolean signing or Boolean-compatible
normalization is asserted for these Gibbs laws. The existing one-unit component
slack remains valid; a weaker linear slack or a different influence payment
is not excluded.

## 5. A hard-zero star defeats uniform entropy-production absorption

The [positive bounded-treewidth proof](bounded-treewidth.md) obtains a bound
on spectral relative entropy by a coefficient strictly below one times expected
logarithmic magnitude, plus a fixed multiple of mean spectral size. The next
family shows that this intermediate estimate cannot hold for all integer
forest spectra with genuine zeros.

**Theorem 3.** There are no constants $`\eta<1`$ and $`C<\infty`$ such
that every nonzero integer-valued function with a forest Fourier law satisfies

```math
D_2(p_h\Vert U_n)
\le\eta\,\mathbb E_{p_h}\log_2|W_h(S)|+C\,\mathbb E_{p_h}|S|.
```

Zero coefficients are omitted from the expectation. The failure persists when
all nonzero Walsh magnitudes are powers of two and every support constraint is
a genuine three-state edge of a star.

**Proof.** For even $`N>0`$, use the quadratic bent function, in physical
zero-one notation,

```math
b_N(y)=(-1)^{\sum_{j=1}^{N/2}y_{2j-1}y_{2j}}.
```

The two-bit factor $`(-1)^{ab}`$ has four Fourier coefficients of magnitude
$`1/2`$. Taking products proves
$`|\widehat b_N(T)|=2^{-N/2}`$ for every $`T`$. For an integer $`M\ge1`$
and a fresh sign bit $`u`$, put

```math
h(y,u)=b_N(y)+Mu.
```

Its nonzero coefficients are precisely

```math
\widehat h(T,0)=\widehat b_N(T)\quad(T\subseteq[N]),
\qquad \widehat h(\varnothing,1)=M.
```

With $`w=1+M^2`$, its normalized law has the nonnegative star factorization

```math
p_h(s,z)=\frac{(2^{-N})^{1-z}(M^2)^z}{1+M^2}
 \prod_{i=1}^N\mathbf1_{\{\text{not }(z=1\text{ and }s_i=1)\}}.
```

All three allowed states occur on every edge. The support is neither a
coordinate subcube nor a deterministic parity quotient of one.

Write $`n=N+1`$, $`L=\mathbb E_{p_h}\log_2|W_h|`$, and
$`J=\mathbb E_{p_h}|S|`$. There are $`2^N`$ equal atoms with total mass
$`1/w`$, and one singleton atom with mass $`M^2/w`$. Thus

```math
\begin{aligned}
H(p_h)&=h_2(1/w)+N/w,\\
D_2(p_h\Vert U_n)&=N+1-h_2(1/w)-N/w,\\
L&=N+1+\frac{M^2\log_2M-N/2}{w},\\
J&=\frac{N/2+M^2}{w}.
\end{aligned}
```

Choose $`M=2^t`$, $`N=2^{4t}`$, $`t\ge1`$. The nonzero Walsh magnitudes
are $`2^{N/2+1}`$ and $`M2^{N+1}`$, both powers of two. Since
$`0\le h_2\le1`$,

```math
\frac{D_2(p_h\Vert U_n)}N\longrightarrow1,\qquad
\frac LN\longrightarrow1,\qquad
\frac JN\longrightarrow0.
```

The proposed inequality, divided by $`N`$, would imply $`1\le\eta`$ in
the limit. This contradicts $`\eta<1`$. ∎

This is a failure of that entropy-production estimate, not of FEI. The same
family satisfies

```math
H_*(h)=N-2M^2\log_2M,\qquad I(h)=N/2+M^2,
\qquad H_*(h)\le2I(h).
```

For the chosen parameters its raw entropy is positive for all sufficiently
large $`t`$. The function is not Boolean when $`M>1`$. Normalizing its norm
does not make it Boolean. Its norm contains the odd factor $`1+M^2`$, which
is absent from the pure-power Boolean normalization used in the forest
arithmetic argument. No Boolean FEI counterexample follows.

## 6. What remains and how to reproduce the calculations

The forbidden-pair cut gives a real integrality payment, but not an arbitrary
depth decomposition. The integer star shows why adding a support-boundary term
to the positive-factor argument and seeking the same absorption coefficient
$`\eta<1`$ for all integer forest sections cannot work. Possible repairs must
use additional information, such as Boolean normalization before cutting,
norm and raw entropy together, or a paid denominator only where later sections
become nonintegral. None of those repairs is proved here.

The [exact checker](code/check_forest_slack_continuation.py) checks every Boolean
function through four variables, yielding 65,814 truth tables and 89,480
admissible physical sections. It also checks twelve rational star-energy
cases, the integer star at $`N=16,M=2`$ on 131,072 physical inputs, the
seven-bit path witness and its integral central cut, and the six-bit Boolean
two-star obstruction. The finite computations supplement the complete proofs;
they are not evidence for a universal inequality beyond the stated results.
