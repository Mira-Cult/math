# Uniform FEI closure with an unbounded number of marked inputs

**Mira Cult · 16 November 2026**

A Boolean leaf class with full Fourier support and FEI constant C0 remains controlled after
recursive products and simultaneous marked-input flips, with constant
(5/4)C0+7. One constant applies across all permitted marked-set sizes, depths,
branching numbers and dimensions. The projection and branching hypotheses
below are essential; no representation theorem for arbitrary functions is
asserted. The separately stated rare-point specialization has a sharper bound.

The complete proof received exact-source nonauthor model review, recorded in
[Verification](VERIFICATION.md). This is not human peer review or a proof of
general FEI. Its scientific source is
[72102dbe92e277f6d616f6a1201d5388992e5dd3](https://github.com/Mira-Cult/math-wip/blob/72102dbe92e277f6d616f6a1201d5388992e5dd3/problems/0298-fourier-entropy-influence-conjecture/manuscripts/marked_set_closure.md).

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Code](code/README.md)

## 1. Construction and statements

All cubes have the uniform measure, Fourier characters take values in
`{-1,1}`, all logarithms are base two, and

```math
H(h)=\sum_S\widehat h(S)^2\log_2\frac1{\widehat h(S)^2},
\qquad I(h)=\sum_S|S|\widehat h(S)^2.
```

Positive spectrum means `hhat(S) != 0` for every `S`. A marked Boolean
function consists of a Boolean function `h` on `n>=2` coordinates and an
ordered list `P=(x_1,...,x_q)` of distinct physical inputs. Fix an integer
`q>=2`. A construction node has

```math
m\ge 2+\lceil\log_2q\rceil
\qquad\text{(1)}
```

children on disjoint blocks. Child `j` has marks
`x_{j,1},...,x_{j,q}`, all distinct within that child. Define the product,
the parent marks, and the new Boolean function by

```math
F=\prod_{j=1}^m h_j,\qquad
X_a=(x_{1,a},...,x_{m,a}),\qquad
G=F-2\sum_{a=1}^q F(X_a)\mathbf1_{X_a}.
\qquad\text{(2)}
```

Thus every parent mark projects to the correspondingly indexed mark of
every child, and every pair of parent marks differs in every child block.
The marks of `G` are again `(X_1,...,X_q)`. The construction may be iterated
through an arbitrary finite tree. The same `q` is used at every node; node
arities and leaf dimensions need not agree. Since every child contains at
least two coordinates, `N=sum_j n_j>=2m` at an internal node.

**Theorem 1 (uniform finite-set closure).** Let `C_0>=0`. Let `A` be any
class of positive-spectrum Boolean functions, on at least two coordinates,
for which `H(h)<=C_0 I(h)` for every `h in A`. For each integer `q>=2`,
choose any `q` distinct marked inputs on each leaf used from `A`, and close
under (1)--(2). Every function so constructed has positive spectrum and
satisfies

```math
\boxed{H(G)\le\left(\frac54 C_0+7\right)I(G).}
\qquad\text{(3)}
```

The same displayed constant applies to the union over all `q>=2` of these
classes. It is independent of `q`, dimension, depth, and all node arities.
The constant is paid once, not at every internal node. The theorem permits
only leaves with enough physical inputs for the chosen number of distinct
marks. It does not permit changing `q` within a construction without an
additional argument.

**Theorem 2 (sharp constant four for a two-point class).** Fix `q=2`.
As leaves take any rare-point functions

```math
r_n=1-2\mathbf1_x,\qquad n\ge2,
\qquad\text{(4)}
```

whose first mark is the exceptional point `x` and whose second mark is any
different point. Close these marked functions under (2), with `m>=3` at
every node. All resulting functions have positive spectrum and

```math
\boxed{H(G)\le4I(G).}
\qquad\text{(5)}
```

Four is the least constant for this entire class. It remains the least
constant if one requires the construction to have an internal node.

Theorem 1 extends the mechanism of the previously proved single-point closure by allowing
an unbounded number of simultaneous modifications, with a uniform constant.
Its hypotheses on distinct projections and arity are substantive. Theorem 2
uses an additional exact cancellation at rare-point leaves; it is not an
application of Theorem 1 with its less efficient constant.

## 2. The necessary interaction and shared-edge corrections

Write `M=2^n`, `delta=2/M`, `c_a=h(x_a)`, and `p_S=hhat(S)^2`.
For a positive-spectrum Boolean function, use the established single-point
score

```math
B_h(x)=h(x)\sum_S\widehat h(S)\chi_S(x)\log_2 p_S
       -\frac1M\sum_S\log_2 p_S.
\qquad\text{(6)}
```

Also let `s_h(x)` be the physical sensitivity at `x` and put
`t_h(x)=n-2s_h(x)`. Define

```math
\begin{aligned}
K_h(P)
 &=\delta\sum_{a\lt b}c_ac_b
       \sum_S\chi_S(x_a)\chi_S(x_b)\log_2 p_S,\\
P_h(P)&=\sum_a B_h(x_a)-K_h(P),\\
E_h(P)&=\sum_{\substack{a\lt b\\d_H(x_a,x_b)=1}}c_ac_b,\\
T_h(P)&=\sum_a t_h(x_a)-2E_h(P).
\end{aligned}
\qquad\text{(7)}
```

Here `P_h` denotes a signed score; `P` without a subscript is the marked
list. Neither `P_h` nor `K_h` is the entropy of a probability distribution.
The signs in these definitions are essential.

The quantity `T_h` is the sum of `h(u)h(v)` over the unoriented physical
edges with exactly one endpoint in the marked set. Indeed, summing the
`t_h(x_a)` counts every internal edge twice, so `2E_h` must be removed.
Consequently

```math
|T_h|\le qn.
\qquad\text{(8)}
```

Ignoring internal edges already fails on two coordinates: for
`h=1-2 1_{00}` and marks `00,01`, one has `t_h(00)=-2`,
`t_h(01)=0`, and `E_h=-1`. Thus `T_h=0`, as it must: flipping both
marks only moves the exceptional point and leaves total influence unchanged.
The uncorrected sum of the two `t` values is `-2`.

The spectral correction is also real. For a rare-point function on three
coordinates with marks at its exceptional point and any other point,
`K_h=-(1/2)log_2 3`, whereas `P_h=0`. In a product of such children,
the parent cross term vanishes but the child cross terms do not. Therefore
one cannot simply declare the total score additive. Section 5 gives the
correct replacement.

## 3. Exact changes under a marked-set modification

Let `g=h-2 sum_a c_a 1_(x_a)` be the Boolean function obtained by changing
all marked signs, and put

```math
d_S=\sum_a c_a\chi_S(x_a),\qquad A_S=M\widehat h(S).
\qquad\text{(9)}
```

Orthogonality of distinct characters in the spectral variable gives

```math
\sum_S d_S^2=Mq,\qquad |d_S|\le q,
\qquad \widehat g(S)=\widehat h(S)-\delta d_S.
\qquad\text{(10)}
```

Expanding `d_S^2` shows directly from (6)--(7) that

```math
P_h=\sum_S d_S\left(\widehat h(S)-\frac\delta2d_S\right)
                   \log_2 p_h(S).
\qquad\text{(11)}
```

Suppose both spectra are positive. Expanding squared coefficients and using
the definition of relative entropy proves the exact formula

```math
\boxed{H(g)=H(h)+2\delta P_h-D_2(p_g\Vert p_h).}
\qquad\text{(12)}
```

Indeed `p_g-p_h=-2delta d_S hhat(S)+delta^2 d_S^2`, so the change of
cross entropy against `p_h` is `2delta P_h`. No Fourier interference term
has been discarded. The finite relative entropy is nonnegative.

Only boundary edges of the marked set change sensitivity. Each such
unoriented edge contributes `delta` to total probability-of-flip influence.
This proves

```math
\boxed{I(g)=I(h)+\delta T_h,\qquad T_g=-T_h.}
\qquad\text{(13)}
```

The internal edge products do not change: `E_g=E_h`. Since the new
`d_S` equals `-d_S`, (11) gives the exact score transformation

```math
\boxed{P_g=-P_h+R_h,\qquad
R_h=\delta\sum_S d_S(A_S-d_S)
            \log_2\left|\frac{A_S}{A_S-2d_S}\right|.}
\qquad\text{(14)}
```

All these identities hold for arbitrary distinct marks; no product
assumption has yet been used.

## 4. Integer Walsh separation gives a uniform local payment

**Lemma 3.** If `|A_S|>=4q` for every `S`, then the modified spectrum
is positive and

```math
0\lt R_h\le6q,\qquad
\left|\log_2 p_g(S)-\log_2 p_h(S)\right|\le2.
\qquad\text{(15)}
```

**Proof.** By `|d_S|<=q`, one has
`|A_S-2d_S|>=|A_S|/2>0`. The ratio of new and old squared coefficients
lies between `1/4` and `9/4`, proving the logarithmic bound. If `d_S=0`
the summand in `R_h` is zero. Otherwise put `z=(A_S-d_S)/d_S`. Then
`|z|>=3`, and

```math
\begin{aligned}
d_S(A_S-d_S)\log_2\left|\frac{A_S}{A_S-2d_S}\right|
 &=d_S^2 z\log_2\left|\frac{z+1}{z-1}\right|,\\
z\log_2\left|\frac{z+1}{z-1}\right|
 &=\frac2{\ln2}\sum_{k\ge0}\frac{|z|^{-2k}}{2k+1}
 \ \in(0,3].
\end{aligned}
```

The latter expression decreases with `|z|` and equals three at `|z|=3`.
Thus (10) implies `0<R_h<=3delta Mq=6q`. QED.

At every internal node the unnormalized Walsh coefficients of `F` are
products of the children's coefficients. Any nonzero Boolean Walsh
coefficient on at least one coordinate is an even nonzero integer.
Therefore positivity of the children and (1) give

```math
|2^N\widehat F(S)|\ge2^m\ge4q.
\qquad\text{(16)}
```

Lemma 3 applies. This proves positivity inductively at every depth. It also
specifies the congruences needed in repeated constructions: old numerators
are multiples of `2^m`, and new ones are `A_S-2d_S`, still even and
nonzero. Since `d_S` has the parity of `q`, an odd `q` gives new
numerators congruent to two modulo four, while an even `q` gives new
numerators divisible by four. The proof requires neither case to retain
one exact valuation at the next level; nonzero even numerators suffice.

For `q=2`, exactly half of the spectral indices have `|d_S|=2` and
the other half have `d_S=0`. At an internal node the former new
numerators are congruent to four modulo eight and the latter remain
nonzero multiples of eight. This will distinguish a concrete two-point
family from the earlier one-point construction.

## 5. Product formulas with all cross terms retained

Fix `C>=0` and abbreviate

```math
M_h=C I(h)-H(h),\qquad U_h=2P_h-C T_h,
\qquad V_h=K_h-C E_h.
\qquad\text{(17)}
```

Consider one node of (2). The usual product identities give
`H(F)=sum_j H(h_j)` and `I(F)=sum_j I(h_j)`. Also
`B_F(X_a)=sum_j B_(h_j)(x_(j,a))` and
`t_F(X_a)=sum_j t_(h_j)(x_(j,a))`: the first follows by expanding the
product Fourier law and the logarithm of that law; the second by checking
physical sensitivity in each block.

Every two parent marks differ in every child block. Hence each pair has
Hamming distance at least `m>=3`, so `E_F=E_G=0`. The logarithmic
cross terms of the product also vanish, pair by pair. In a summand
`log p_(h_j)` of `log p_F`, an untouched block `k!=j` contributes

```math
\sum_{S_k}\chi_{S_k}(x_{k,a})\chi_{S_k}(x_{k,b})=0
```

because the projected marks are distinct. Therefore `K_F=0`, and (7)
yields

```math
P_F=\sum_j(P_{h_j}+K_{h_j}),\qquad
T_F=\sum_j(T_{h_j}+2E_{h_j}),\qquad
\boxed{U_F=\sum_jU_{h_j}+2\sum_jV_{h_j}.}
\qquad\text{(18)}
```

For the new function, (12)--(14) imply

```math
U_G=-U_F+2R_F,\qquad
M_G=\sum_jM_{h_j}-\delta_N U_F+D_2(p_G\Vert p_F).
\qquad\text{(19)}
```

Finally, for each pair of marks the contribution to `K_F` is zero and
the output product `F(X_a)F(X_b)` is unchanged by flipping both signs.
The logarithmic bound (15) thus gives

```math
|K_{G,ab}|
\le\delta_N\sum_S|\log_2p_G(S)-\log_2p_F(S)|\le4.
```

Summing the pairs and using `E_G=0` proves

```math
\boxed{|V_G|\le2q(q-1).}
\qquad\text{(20)}
```

The uniform theorem uses this safe bound. For `q=2` the active-half
observation in Section 4 improves it to `|V_G|<=2`, but this improvement
is unnecessary for either theorem.

## 6. One invariant for all fixed marked-set sizes

For the chosen `q>=2`, put

```math
r=4q^2,\qquad \alpha=\frac1{20},\qquad
\beta=\frac1{4q^2-1}.
\qquad\text{(21)}
```

We will prove the stronger marked inequality

```math
\boxed{M_h\ge\delta_n\left(\alpha+\beta|U_h|+2\beta|V_h|\right).}
\qquad\text{(22)}
```

Assume (22) for all children. Their probability scales satisfy

```math
\frac{\delta_{n_j}}{\delta_N}=2^{N-n_j}
\ge4^{m-1}\ge4q^2=r,
\qquad\text{(23)}
```

using two coordinates in every omitted block and (1). Nonnegativity of
relative entropy, (18), and (19) therefore give

```math
M_G\ge\delta_N\left[
rm\alpha+r\beta\sum_j|U_j|+2r\beta\sum_j|V_j|
-\sum_jU_j-2\sum_jV_j\right].
\qquad\text{(24)}
```

By (15), (19), and (20), the bracket required on the right side of (22)
for `G` is at most

```math
\alpha+\beta\sum_j|U_j|+2\beta\sum_j|V_j|
+\beta(12q+4q(q-1)).
\qquad\text{(25)}
```

Subtracting (25) from the bracket in (24), and using `(r-1)beta=1`,
leaves

```math
(rm-1)\alpha-\frac{4q^2+8q}{4q^2-1}
+\sum_j(|U_j|-U_j)+2\sum_j(|V_j|-V_j).
\qquad\text{(26)}
```

The sums are nonnegative. For every `q>=2`, `m>=3` and `r>=16`, while

```math
\frac{4q^2+8q}{4q^2-1}\le\frac{32}{15}
```

because the numerator of the difference after clearing positive
denominators is `4(q-2)(17q+4)`. Consequently the constant in (26) is
at least

```math
\frac{47}{20}-\frac{32}{15}=\frac{13}{60}\gt 0.
\qquad\text{(27)}
```

This proves closure of (22), without any further assumption on `C`.
It remains to prepare leaves. The two theorems differ only in that step.

## 7. Preparing an arbitrary already-controlled positive leaf

We use the following previously proved envelope, with exactly the present
normalizations:

```math
\delta_n|B_h(x)|\le16I(h),\qquad n\delta_n\le I(h)
\qquad\text{(28)}
```

for any positive-spectrum Boolean function on `n>=2` coordinates and any
physical point. The source is Lemma 3, Section 9, of
[the single-point closure proof](point-modifications.md),
at scientific revision `a17f79e858c8537587a8d49e2b879f10c59e7677`,
source SHA-256
`528d51fb7493be8c3b6165fe7fc1a0f9cd22d4d98602c4d93a1d3a89262d2d85`.
That source proves (28) from cube edge isoperimetry, Walsh integrality, and
`||hhat||_1<=min(sqrt(2^n),1+2a)` for minority truth-table size `a`.
Thus (28) is an unconditional Boolean estimate, not an FEI assumption.
Only the ordinary leaf bound `H<=C_0 I` in Theorem 1 is supplied by the
chosen leaf class.

For every nonzero Boolean Walsh numerator,
`delta_n<=|hhat(S)|<=1`, so `|log_2p_h(S)|<=2(n-1)`. Each pair term
in `K_h` has absolute value at most `4(n-1)`. Hence (28) implies

```math
\begin{aligned}
\delta_n|K_h|&\le2q(q-1)I(h),\\
\delta_n|P_h|&\le(2q^2+14q)I(h),\\
\delta_n|T_h|&\le qI(h).
\end{aligned}
\qquad\text{(29)}
```

The number of internal marked edges is at most both `qn/2` and
`q(q-1)/2`. Therefore

```math
\delta_n|E_h|\le e_q I(h),\qquad
e_q=\min\left\{\frac q2,\frac{q(q-1)}4\right\}.
\qquad\text{(30)}
```

Together these bounds give

```math
\delta_n\left(\alpha+\beta|U_h|+2\beta|V_h|\right)
\le\left[
\frac1{40}+\frac{8q^2+24q+C(q+2e_q)}{4q^2-1}
\right]I(h).
\qquad\text{(31)}
```

For `q=2`, the fraction equals `16/3+C/5`. For `q>=3`, `e_q=q/2`,
and both

```math
\frac{8q^2+24q}{4q^2-1}\le\frac{16}3,
\qquad \frac{2q}{4q^2-1}\le\frac15
\qquad\text{(32)}
```

hold. The first reduces to `8(q-2)(5q+1)>=0`; the second to
`4q^2-10q-1>=0`. Thus (31) is at most
`(1/40+16/3+C/5)I(h)` for every `q>=2`.

Set `C=(5/4)C_0+7`. At a permitted leaf,
`M_h>= (C-C_0)I(h)`, and the difference between this coefficient and
the last upper bound is exactly

```math
(C-C_0)-\left(\frac1{40}+\frac{16}3+\frac C5\right)
=\frac{29}{120}\gt 0.
\qquad\text{(33)}
```

Every leaf satisfies (22). Section 6 proves it at all nodes, and Section 4
proves positive support. This completes the proof of Theorem 1.

For example, the checkpoint's positive treewidth-two Boolean leaf theorem
has `C_2<14`; its finite-set recursive closure therefore has the single
constant `(5/4)C_2+7<49/2`. The positive Boolean directed-factor class with
constant four has closure constant twelve. The positive (invertible-map)
part of the affine-forest theorem, with
`C_aff=4+4/log_2(5/4)<17`, has closure constant
`(5/4)C_aff+7<28`. Each application retains all hypotheses of the chosen
leaf theorem. In particular an affine embedding with spectral zeros cannot
be inserted as a leaf under Theorem 1 merely because its FEI bound is known.

## 8. Rare-point leaves prepare the sharper constant four

Take a leaf (4), with marks `x` and `y!=x`, and put
`epsilon=delta_n=2^(1-n)`, `b=(1-epsilon)/epsilon=2^(n-1)-1`.
Changing these two values merely moves the exceptional point from `x` to
`y`. The squared Fourier law and total influence are unchanged. Directly,

```math
\begin{aligned}
B_h(x)&=-(2-\epsilon)\log_2b,\\
B_h(y)&=(2-3\epsilon)\log_2b,\\
K_h&=-2\epsilon\log_2b,\qquad P_h=0,\qquad T_h=0.
\end{aligned}
\qquad\text{(34)}
```

These formulas include `n=2`, where `b=1` and all displayed scores
vanish. If the two marks are adjacent, `E_h=-1`; otherwise `E_h=0`.
For `C=4`, therefore,

```math
U_h=0,\qquad V_h=-2\epsilon\log_2b
             +4\mathbf1_{\{d_H(x,y)=1\}},\qquad |V_h|\le5.
\qquad\text{(35)}
```

Indeed `log_2b<=n-1` and `(n-1)2^(1-n)<=1/2` for every `n>=2`.
At `q=2`, the right side of (22) is consequently at most

```math
\epsilon\left(\frac1{20}+\frac{10}{15}\right)
=\frac{43}{60}\epsilon\lt \epsilon.
\qquad\text{(36)}
```

The exact leaf entropy and influence are

```math
I(h)=n\epsilon,\qquad
H(h)=-2(1-\epsilon)^2\log_2(1-\epsilon)
       +(2\epsilon-\epsilon^2)(2n-2).
\qquad\text{(37)}
```

Since `-ln(1-epsilon)<=epsilon/(1-epsilon)`, these imply

```math
\begin{aligned}
4I(h)-H(h)
&=4\epsilon+2(n-1)\epsilon^2
 +2(1-\epsilon)^2\log_2(1-\epsilon)\\
&\ge\left(4-\frac2{\ln2}\right)\epsilon
 +\left(2n-2+\frac2{\ln2}\right)\epsilon^2
\gt \epsilon.
\end{aligned}
\qquad\text{(38)}
```

The strict last inequality uses `ln2>2/3`, for example from the first
term of its atanh series. Equations (36)--(38) prove the leaf invariant
with `C=4`. The unchanged induction of Section 6 proves Theorem 2.

For sharpness, (37) gives `H(r_n)/I(r_n)->4`. This already proves that
four is the least constant for the full class. To see sharpness among
functions having an internal node, take three copies of `r_n`, with
first mark `0^n` and second mark `1^n`, for `n>=2`. In (34) each child
has `T_h=0` and `E_h=0`; hence the product and modified parent have the
same influence, namely `3n2^(1-n)`. If `F` is the product and `G` its
two-point modification on `N=3n` bits, Parseval and Cauchy--Schwarz give

```math
\|p_G-p_F\|_{\mathrm{TV}}
\le\|\widehat G-\widehat F\|_2
=\|G-F\|_2=\sqrt{8/2^N}.
\qquad\text{(39)}
```

For probability laws on at most `2^N` atoms with total variation `t`,
`|H(p)-H(q)|<=h_2(t)+tN`: couple them with mismatch probability `t`,
condition on that indicator, and bound each conditional entropy by `N`.
Thus the entropy error here is `O(N2^(-N/2))`, which divided by
`3n2^(1-n)` tends to zero. As `H(F)=3H(r_n)`, the parent ratio also
tends to four. This completes the sharpness assertion.

## 9. Explicit unavoidable interactions of unbounded size

The new class is not contained in the earlier rare-point one-point
construction: all numerators in the earlier construction are congruent to
two modulo four, whereas every internal two-point function has numerators
divisible by four, with exactly half having valuation exactly two.
Physical coordinate permutations, coordinate complements, and output sign
changes preserve this distinction. This is a comparison between these two
specific constructions, not a noncontainment claim about all known FEI
classes.

There is also a concrete positive-spectrum family with unavoidable
full-dimensional interaction. Take `m>=3` two-coordinate rare-point leaves
and mark, in every leaf, `00` and `11`. The total dimension is `N=2m`.
For a spectral index `s`, let

```math
\sigma(s)=(-1)^{\#\{j:s^{(j)}\ne00\}},\quad
\epsilon=(-1)^m,\quad \kappa(s)=\epsilon\sigma(s),\quad
\chi(s)=(-1)^{|s|},\quad \lambda=2^{2-m}.
```

The product's unnormalized Walsh coefficient is `2^m sigma(s)`, and
the two-point modification changes it by `-2(epsilon+chi(s))`.
Accordingly

```math
\log_2p_G(s)
=-N+(1+\epsilon\chi(s))(a+b\kappa(s)),
\qquad\text{(40)}
```

where

```math
a=\frac12\log_2(1-\lambda^2)\lt 0,\qquad
b=\frac12\log_2\frac{1-\lambda}{1+\lambda}\lt 0.
```

To check (40), the coefficient changes only on
`chi(s)=epsilon`; on that half it is multiplied by
`1-lambda kappa(s)>0`. Expanding the two possible logarithms gives
the displayed formula.

Under the uniform law on spectral indices,
`E kappa=2^(-m)` and `E(kappa chi)=epsilon 2^(-m)`: for each
two-bit block, the means of its nonempty-sign function and its product
with block parity are respectively `-1/2` and `1/2`. Hence the full
`N`-coordinate Walsh coefficient of `log_2p_G` is

```math
\mathbb E[\chi(s)\log_2p_G(s)]
=\epsilon\bigl(a+2^{1-m}b\bigr)\ne0.
\qquad\text{(41)}
```

If a positive law factors into potentials depending on proper subsets of
the variables, its logarithm is a sum of functions on those subsets and
has zero full-coordinate Walsh coefficient. Thus these laws require a
factor of arity `N`. Moreover the nonzero full monomial forces the
conditional-dependence graph to contain every pair: vanishing mixed
discrete difference for a conditionally independent pair would eliminate
every logarithmic monomial containing that pair. Their pairwise Markov
graphs are complete and have treewidth `N-1`.

This witness establishes growing necessary interaction size, not novelty
of its FEI inequality by itself: in this simple family `I=m` (the original
product is bent and its boundary score is zero), while always `H<=N=2m`.
The new mathematical content is the uniform closure invariant for
arbitrary admissible leaf classes, simultaneous changes of arbitrarily
many points, and unrestricted recursion. Theorem 2 also covers the
low-influence sharpness family of Section 8.

## 10. Relation to earlier work and the remaining obstruction

The source single-point closure has constant `(3/2)C_0+17` for controlled
positive leaf classes and `9/2` for its particular rare-point recursion.
The present operation is different: it changes `q>=2` physical points at
once, requires at least `2+ceil(log_2q)` children, and retains their pair
interactions and internal edges. The constant `(5/4)C_0+7` is uniform
across `q`; no comparison allowing the old two-child, one-point operation
without its own argument is asserted.

O'Donnell--Tan's composition theorem (arXiv:1304.1347v1, main composition
theorem and its biased corrected-entropy hypothesis) is a theorem about
one Boolean child output per disjoint physical block. At a deeper node
here, that output need not determine whether the physical input is one of
the marked points, or which marked point it is. Consequently direct
application on this construction tree does not account for the operation.
This is an applicability distinction, not an exhaustive priority claim.
The workspace's earlier primary-source comparison of OWZ11, OT13,
WWW14, and the stated threshold-formula results remains relevant. No claim
of first publication is made without an additional targeted literature
audit of this precise finite-set closure.

The theorem pays three previously missing quantities: the cross-entropy
change `P_h`, its new arithmetic correction `R_h`, and the inherited
pair/internal-edge correction `V_h`. The ratio of child and parent point
probabilities is at least `4q^2`; this pays the `O(q^2)` number of new
pair terms while the final FEI constant remains independent of `q`.

The restrictions still block general FEI. An arbitrary positive Boolean
function has not been decomposed into this separated-mark recursion with
already-controlled leaves. Distinct projected marks are what make the
product cross terms vanish; without that condition, their survival has
not been paid by (22). Likewise, reducing the number of children loses
(23), and allowing zeros makes the logarithmic scores undefined. Invoking
the general positive-support reduction from the workspace would help only
after a uniform theorem for *all* positive Boolean functions; this class
theorem does not meet that premise. Allowing arbitrary Boolean functions
as leaves would assume the missing FEI estimate rather than prove it.

## 11. Reproducible verification and review scope

The companion [code/check_marked_set_closure.py](code/check_marked_set_closure.py) uses integer truth tables and
Walsh transforms, exact physical edge counts, and rational intervals for
all logarithms. It checks the Fourier changes, support and congruences,
the shared-edge correction, product identities, the signed-score update,
the invariants, and the full-interaction calculation on its stated finite
cases. The logarithm intervals use the atanh series and an explicit tail
bound; PASS assertions do not use floating-point tolerances.

The general proofs above do not depend on finite computation. Independent
review should specifically check (7), (14), (18), the dependence on `q`
in (23)--(33), the arbitrary adjacent second mark at the leaves of
Theorem 2, and the distinction between full-support preservation and any
unproved zero-support extension. Exact source hashes and completed review
results should be recorded only after those checks occur.

The author run of
`python -u notes/combinatorics/fourier-entropy-influence/code/check_marked_set_closure.py` passed:
136 positive Boolean functions on two or three coordinates, every marked
subset of size at least two (31,704 cases); every rare-point second mark
through seven coordinates; 298 rare-leaf instances and 15 internal nodes,
with maximum dimension 15; generic nodes with `q=2,3,4,5,8`; and the exact
full logarithmic interaction formula for `m=3,4,5,6`. Rational substitutions
also check the displayed scalar constants for `2<=q<=1000`. The algebraic
proof in Section 6, not that last finite range, establishes uniformity over
all integers `q>=2`.
