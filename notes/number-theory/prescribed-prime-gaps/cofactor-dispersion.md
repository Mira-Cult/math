# Cofactor averaging with exact moving cutoffs

**Mira Cult**

The [signed endpoint remainder](signed-endpoint-transfer.md) involves a
growing range of cofactors and exact divisor cutoffs. This note proves an
unconditional transfer inequality: a sufficiently strong estimate for one
explicit family of twisted squares controls that entire cofactor range.
Divisor moments pay the multiplicities, and a sine integral pays the moving
cutoffs. The independent base-cancellation and marking-removal estimates
needed for prime gaps are not proved here. No historical priority is claimed.

## 1. The actual squares before a determinant replacement

Let $`X\ge3`$, $`L=\log(3X)`$, $`1\le g\le X`$, and
$`2\le Y\le X^{1/64}`$. Let $`\mathcal A`$ be any subset of the integers
in $`[Y,4Y]`$ with $`(A,g)=1`$ for every $`A\in\mathcal A`$.
Suppose $`|w_A|\le W`$. The logarithmic-saving corollaries below take
$`W`$ fixed; the transfer inequality records its dependence explicitly.
A fixed covering modulus and
residue may be arbitrary subject to the endpoint conditions in the predecessor.
They enter only through the following exact coefficient sequence:

```math
G(n)=\mathbf1_{X\lt n\le2X}\,
     \mathbf1_{n\equiv a\pmod Q}
     \sum_{\substack{uv=n\\u\in I, v\in J}}\alpha_u\beta_v,
\qquad |\alpha_u\beta_v|\le L^b .
\qquad\text{(D1)}
```

The supports $`I,J`$ may have further restrictions. Everything proved below
only uses $`|G(n)|\le L^b\tau(n)`$ and its indicated support. Thus these
inequalities are uniform in $`Q,a`$ and in all such restrictions.

For real $`t`$ define the base row and its square by

```math
F_t(k)=\sum_{A\in\mathcal A}w_A A^{it}G(Ak-g),
\qquad E(t)=\sum_{k\ge1}|F_t(k)|^2.
\qquad\text{(D2)}
```

The rows vanish for $`k\gt H:=3X/Y`$. For a real cutoff
$`0\le D\le3X`$ and any cofactor $`c\ge1`$, put

```math
B_{c,D}(h)=\sum_{A\in\mathcal A}w_A G(cAh-g)\mathbf1_{Ah\gt D},
\qquad Q_{c,D}=\sum_{h\ge1}|B_{c,D}(h)|^2.
\qquad\text{(D3)}
```

These are the actual nonnegative squares after extracting the auxiliary
factor $`A`$ and applying Cauchy in $`h`$. They retain both
$`X\lt cAh-g\le2X`$ and $`Ah\gt D`$. The covering residue is inside
$`G`$. Restrictions on $`c`$, such as $`(c,Qg)=1`$, may simply reduce
the cofactor set. Additional restrictions on $`h`$ can be retained in the
outer coefficient before Cauchy and then discarded from its nonnegative bound.

Explicitly, (D3) expands as

```math
\begin{aligned}
Q_{c,D}
={}&\sum_{h\ge1}\sum_{A,B\in\mathcal A}
 w_A\overline{w_B}\,
 \mathbf1_{Ah\gt D}\mathbf1_{Bh\gt D}\\
&\quad\cdot\sum_{\substack{u,r\in I,\ v,s\in J\\
 uv=cAh-g,\ rs=cBh-g\\
 X\lt uv,rs\le2X\\uv\equiv rs\equiv a\pmod Q}}
 \alpha_u\beta_v\overline{\alpha_r\beta_s}.
\end{aligned}
```

Both the $`A=B`$ and $`A\ne B`$ parts are retained. Every term
satisfies $`Buv-Ars=g(A-B)`$, but the common-quotient equations are
the defining conditions: they are not replaced by the determinant equation
and a single congruence. This avoids the coprimality exception in that
replacement, as well as leaving both endpoint residues and moving boundaries
visible.

Before the moving cutoff is inserted, there is an exact identity:

```math
Q_{c,0}=\sum_{c\mid k}|F_0(k)|^2,
\qquad
\sum_{c\in\mathcal C}Q_{c,0}
=\sum_k\tau_{\mathcal C}(k)|F_0(k)|^2,
\quad
\tau_{\mathcal C}(k)=\#\{c\in\mathcal C:c\mid k\}.
\qquad\text{(D4)}
```

This follows by $`k=ch`$. In particular, no character modulo a growing
$`c`$ is introduced. Nor is $`(A,c)=1`$ required. That coprimality was
needed by the earlier determinant-plus-one-congruence replacement, not by
the exact common-quotient formulation (D2)--(D4).

## 2. An elementary divisor-weighted square bound

### Lemma D1. Uniform divisor moments in the required progression

For $`r=2,4`$, uniformly for $`A\in[Y,4Y]`$ with $`(A,g)=1`$,

```math
\sum_{\substack{1\le k\le H\\Ak-g\gt0}}\tau(Ak-g)^r
\ll H L^{2^r-1},
\qquad
\sum_{k\le H}\tau(k)^r\ll H L^{2^r-1}.
\qquad\text{(D5)}
```

The constants are absolute for each displayed value of $`r`$.

**Proof.** Write $`d_j(n)`$ for the number of ordered factorizations of
$`n`$ into $`j`$ positive factors. The elementary inequality
$`\tau(n)^r\le d_{2^r}(n)`$ follows prime by prime: given $`r`$
divisors of a prime power, partition its exponent levels according to the
subset of those divisors in which that level occurs. This injects the
choices into the ordered $`2^r`$-factor decompositions.

Put $`j=2^r`$. Delete a largest factor in each ordered $`j`$-factor
decomposition of $`Ak-g`$. The product of the other factors is at most
$`Z_j=(12X)^{1-1/j}`$. There are at most
$`j d_{j-1}(d)`$ choices with that product equal to $`d`$.
If $`d\mid Ak-g`$, then $`(d,A)=1`$, because $`(A,g)=1`$.
Thus $`k`$ lies in one residue class modulo $`d`$, and the sum is at most

```math
j\sum_{d\le Z_j}d_{j-1}(d)(H/d+1)
\ll H L^{j-1}+Z_jL^{j-2}.
```

Here the elementary ordered-factor sums give
$`\sum_{d\le Z}d_s(d)/d\le(1+\log Z)^s`$ and
$`\sum_{d\le Z}d_s(d)\le Z(1+\log Z)^{s-1}`$.
For $`j\le16`$ and $`Y\le X^{1/64}`$, the second term is absorbed
by the first. The unshifted assertion follows from the same ordered-factor
bound. $`\square`$

Define the absolute row

```math
F_{\rm abs}(k)=\sum_{A\in\mathcal A}|w_A|\,|G(Ak-g)|.
```

### Proposition D2. A paid divisor-weighted envelope

Uniformly under the preceding hypotheses,

```math
\sum_{k\ge1}\tau(k)^2 F_{\rm abs}(k)^2
\ll W^2XYL^{2b+15}.
\qquad\text{(D6)}
```

**Proof.** There are at most $`4Y`$ possible values of $`A`$.
Cauchy in $`A`$ and (D1) give

```math
F_{\rm abs}(k)^2
\le4Y W^2 L^{2b}\sum_{A\in\mathcal A}\tau(Ak-g)^2,
```

with nonpositive arguments omitted. For each $`A`$, another Cauchy inequality
and the fourth moments in (D5) give

```math
\sum_{k\le H}\tau(k)^2\tau(Ak-g)^2
\le
\left(\sum_{k\le H}\tau(k)^4\right)^{1/2}
\left(\sum_{\substack{k\le H\\Ak-g\gt0}}\tau(Ak-g)^4\right)^{1/2}
\ll HL^{15}.
```

Sum over $`A`$ and use $`H=3X/Y`$. $`\square`$

Consequently, for every real $`t`$,

```math
\sum_k\tau(k)|F_t(k)|^2
\le E(t)^{1/2}
\left(\sum_k\tau(k)^2|F_t(k)|^2\right)^{1/2}
\ll E(t)^{1/2}(W^2XYL^{2b+15})^{1/2}.
\qquad\text{(D7)}
```

This interpolates a signed base-square estimate with a proved positive
envelope. Using a worst-case bound for $`\tau(k)`$ would lose a
subpower of $`X`$ and fail to preserve arbitrary logarithmic savings;
(D6)--(D7) avoid that loss.

## 3. Exact moving cutoffs cost only logarithms

### Theorem D3. Full cofactor-square transfer

Let

```math
E_* = \sup_{|t|\le X^{10}}E(t),\qquad J_b=2b+15.
```

For every subset $`\mathcal C`$ of the positive integers and every
$`0\le D\le3X`$,

```math
\sum_{c\in\mathcal C}Q_{c,D}
\ll
L^2 E_*^{1/2}(W^2XYL^{J_b})^{1/2}
+X^{-18}W^2XYL^{J_b}.
\qquad\text{(D8)}
```

Only cofactors $`c\le H`$ have a nonzero square. The inequality is
uniform in the covering modulus and in the cutoff; it has no growing
cofactor modulus hypothesis. The displayed $`W`$ factors account explicitly
for the marking normalization. The implied constant in (D8) is absolute.

**Proof.** Put $`U=\lfloor D\rfloor+1/2`$. Since $`Ah`$ is an integer,
$`Ah\gt D`$ is equivalent to $`Ah\gt U`$. On the support of (D3),
$`1\le Ah\le3X`$, and therefore

```math
|\log(Ah/U)|\gg X^{-1},\qquad
|\log(Ah/U)|\ll L.
```

Use the elementary truncated sine-integral identity

```math
\mathbf1_{z\gt0}
=\frac12+\frac1\pi\int_{t_0}^{T}\frac{\sin(tz)}t\,dt
+O\left(t_0|z|+\frac1{T|z|}\right),
\quad z\ne0,
\qquad\text{(D9)}
```

with $`t_0=X^{-10}`$ and $`T=X^{10}`$. The full integral follows by
exponential damping and $`\arctan(z/\epsilon)`$; integration by parts
bounds the tail, and $`|\sin(tz)|\le t|z|`$ bounds the small interval.
Thus the error on the present integer support is $`O(X^{-9})`$.

Expanding the sine gives, with $`k=ch`$,

```math
B_{c,D}(h)=\frac12F_0(k)
+\frac1{2\pi i}\int_{t_0}^{T}
 \left\{(h/U)^{it}F_t(k)-(h/U)^{-it}F_{-t}(k)\right\}\frac{dt}{t}
+\mathcal E_{c,h},
\quad |\mathcal E_{c,h}|\ll X^{-9}F_{\rm abs}(k).
\qquad\text{(D10)}
```

Apply Minkowski in the finite Hilbert space with coordinates
$`(c,h)`$, $`c\in\mathcal C`$, $`ch\le H`$.
The factors $`(h/U)^{\pm it}`$ have modulus one. By (D4) and (D7),
each phase vector has squared norm at most

```math
\sum_k\tau(k)|F_t(k)|^2
\ll E_*^{1/2}(W^2XYL^{J_b})^{1/2}.
```

The integral of $`dt/t`$ is $`20\log X\ll L`$.
The error vector has squared norm at most
$`X^{-18}\sum_k\tau(k)F_{\rm abs}(k)^2`$,
which is bounded by (D6). Squaring the resulting norm inequality gives
(D8). All lower bounds and all product boundaries in (D3) have been retained.
$`\square`$

In particular, if for every requested $`A_0\gt0`$ the base family satisfies

```math
E_*\ll_{A_0}XYL^{-A_0},
\qquad\text{(D11)}
```

then for every $`B_0\gt0`$,

```math
\sum_{c\in\mathcal C}Q_{c,D}\ll_{B_0}XYL^{-B_0}.
\qquad\text{(D12)}
```

It suffices to use (D11) with
$`A_0\ge2B_0+2b+19`$. This controls the sum over all cofactors from a fixed-slope base-square
hypothesis, without a separate pointwise relative bound for each cofactor. It does not prove that hypothesis.
Uniformity in the auxiliary phase is a real requirement. For example,
$`\mathcal A=\{3,5\}`$, $`g=2`$, $`w_3=w_5=1`$ and a sequence
with $`G(10)=1`$, $`G(18)=-1`$ and all other values zero give
$`F_0(k)=0`$ for every $`k`$. Yet the row $`c=1,h=4,D=12`$
in (D3) equals $`-1`$. An estimate for $`E(0)`$ alone cannot pay
arbitrary moving cutoffs. This is an algebraic example, not an example in the
asymptotic parameter range of (D8).

### Corollary D3.1. Maximal interval cutoffs

In fact the same right-hand side as in (D8) bounds

```math
\sum_{c\in\mathcal C}\sum_{h\ge1}
 \max_{0\le D_-\le D_+\le3X}
 \left|\sum_A w_A G(cAh-g)
             \mathbf1_{D_-\lt Ah\le D_+}\right|^2.
\qquad\text{(D8a)}
```

**Proof.** For each pair $`(c,h)`$, choose an interval giving its maximum.
There are only finitely many distinct selected subsets of $`\mathcal A`$,
so a maximum exists. Write its indicator as the difference of two lower-cutoff
indicators and apply (D9) at the corresponding half-integer boundaries.
The phases $`(h/U_{c,h}^{\pm})^{it}`$ may depend on the row, but have
modulus one in every coordinate of the Hilbert space used above. The norm
bound (D7), Minkowski's inequality and the uniform error estimate therefore
give (D8) again, with a different absolute constant. $`\square`$

Thus no additional maximal-interval estimate is required. The cutoff may vary
with both $`c`$ and $`h`$, and all those choices are paid simultaneously.

### Corollary D3.2. Exact product windows from a rectangular base

The same assertions hold, with constants additionally depending on a fixed
$`C_0\ge2`$, if the base coefficient is instead

```math
\widetilde G(n)=\mathbf1_{n\equiv a\pmod Q}
        \sum_{\substack{uv=n\\u\in I,v\in J}}\alpha_u\beta_v,
\qquad uv\le C_0X\quad(u\in I,\ v\in J),
```

with no further product window. Use
$`H=(C_0+1)X/Y`$ and replace $`3X`$ by $`(C_0+1)X`$ in
the permissible cutoff range. The proofs of (D5)--(D8a) use only a fixed
constant multiple of $`X`$ as the upper support bound; every displayed
logarithmic exponent is unchanged.

In particular, all three actual restrictions

```math
Ah\gt D,\qquad X\lt cAh-g\le2X
```

are retained by taking

```math
D_-(c,h)=\max\{D,(X+g)/c\},\qquad
D_+(c,h)=(2X+g)/c,
```

and declaring the row empty if $`D_-\ge D_+`$.
Consequently the base estimate may use the source's rectangular coefficient
supports. There is no need to remove the product window absolutely or introduce
additional Mellin phases in the long coefficient variables in order to handle
that window.

### Corollary D4. Summing the marked switched columns

Let $`|\zeta_{c,h}|\le1`$, and write
$`T_c=\sum_h\zeta_{c,h}B_{c,D}(h)`$.
There are at most $`3X/(cY)`$ possible $`h`$ on the support. Hence

```math
\sum_{c\in\mathcal C}(\log c)|T_c|
\ll
\left(\frac XY\sum_{1\le c\le H}\frac{(\log c)^2}{c}\right)^{1/2}
\left(\sum_{c\in\mathcal C}Q_{c,D}\right)^{1/2}.
\qquad\text{(D13)}
```

The first harmonic sum is $`O(L^3)`$. Under (D11) this is
$`O_A(XL^{-A})`$ for every fixed $`A`$, after increasing the precision
in (D11). With the Type II coefficient size $`b=1`$, a base exponent
strictly greater than $`27+4A`$ pays the displayed losses for a target
$`XL^{-A}`$. Auxiliary-scale and Vaughan decomposition losses must also
be paid by increasing that exponent. The choice
$`\zeta_{c,h}=\mu(h)\rho^{\omega(h)}`$ is permitted.

## 4. Diagonal and shared-prime mass

The literal $`A=B`$ diagonal in the expanded square does not prevent
the proposed logarithmic bound. Even after averaging every cofactor and
retaining arbitrary moving cutoffs, its absolute contribution is at most

```math
\sum_{A\in\mathcal A}|w_A|^2
 \sum_k\tau(k)|G(Ak-g)|^2
\ll W^2X L^{2b+9}.
\qquad\text{(D14)}
```

Indeed, use Cauchy with the second moment of $`\tau(k)`$ and fourth
moment of $`\tau(Ak-g)`$ in (D5). Their logarithmic exponents average
to $`9`$, and $`\#\mathcal A\cdot H\ll X`$.
For the source's auxiliary scale, $`Y`$ exceeds every fixed power of
$`L`$, so (D14) is smaller than $`XYL^{-A}`$ for every fixed $`A`$.
This is an upper bound on diagonal mass, not an inference that a signed
square must be at least its formal diagonal.

Suppose now that every prime divisor of an auxiliary product belongs to
a finite set $`\mathcal P`$ of primes at least $`P_0\gt2`$.
Let $`Z(k)`$ be the absolute part of the base square contributed by
product pairs with $`(A,B)\gt1`$. There are at most

```math
16Y^2\sum_{p\in\mathcal P}p^{-2}
\ll Y^2/P_0
```

such pairs. For a fixed pair, Cauchy and the second-moment case of (D5)
bound its row sum by $`O(W^2HL^{2b+3})`$.
Thus

```math
\sum_k Z(k)\ll W^2XYL^{2b+3}/P_0.
```

Since $`Z(k)\le F_{\rm abs}(k)^2`$, (D6) and Cauchy then give

```math
\sum_k\tau(k)Z(k)
\ll W^2XYL^{2b+9}/\sqrt{P_0}.
\qquad\text{(D15)}
```

All cutoff indicators can be discarded in this absolute estimate.
Consequently shared auxiliary primes remain negligible after full cofactor
averaging when $`P_0=\exp((\log X)^{0.1})`$, as in the source.

## 5. Paying the pre-Cauchy coprimality removal globally

For the actual marking expansion, $`A`$ selects one prime from each of
$`K`$ disjoint auxiliary sets. Let $`0\lt\rho\lt1`$ and
$`V_i=\sum_{p\in\mathcal P_i}1/p\ge v_0\gt0`$, with $`v_0`$
fixed. The exact extraction $`d=Ah`$ initially has $`(A,h)=1`$.
The following estimate pays removal of that condition simultaneously for
all switched columns; it does not assume $`(A,c)=1`$.

For each fixed $`d`$, the total absolute selected-prime weight is bounded:

```math
\sum_{\substack{A\mid d\\A\ {\rm selects\ one\ prime\ per\ set}}}
 \left(\prod_iV_i^{-1}\right)\rho^{\omega(d/A)}
\le
\prod_i\frac{\omega_i(d)\rho^{\omega_i(d)-1}}{V_i}
\le (M_\rho/v_0)^K,
\qquad M_\rho=\sup_{m\ge1}m\rho^{m-1}\le(1-\rho)^{-2}.
\qquad\text{(D16)}
```

The inequality uses $`\omega(d/A)\ge\omega(d)-K`$; a zero factor
$`\omega_i(d)`$ means the selection sum is empty. If $`(A,h)\gt1`$,
then $`p^2\mid d`$, hence $`p^2\mid n+g`$, for some auxiliary prime.
Any auxiliary dyadic cutoff bounded by one may be inserted in this estimate;
a larger supremum norm multiplies the bound by that norm.
After summing all $`c\mid n+g`$, and using $`\log c\ll L`$, the total
absolute error is bounded by a constant times

```math
L^{b+1}\sum_{\substack{X\lt n\le2X\\
  \exists p\in\mathcal P: p^2\mid n+g}}
  \tau(n)\tau(n+g).
\qquad\text{(D17)}
```

Assume $`\mathcal P\subset[P_0,P_1]`$ and $`P_0P_1\le X`$.
The exceptional set has size
$`O(X\sum_{p\ge P_0}p^{-2}+P_1)=O(X/P_0)`$.
The global fourth-moment divisor bounds and Cauchy give

```math
\sum_{X\lt n\le2X}\tau(n)^2\tau(n+g)^2\ll XL^{15}.
```

Applying Cauchy once more to (D17) proves

```math
\text{total coprimality-removal error}
\ll (M_\rho/v_0)^K X L^{b+9}/\sqrt{P_0}.
\qquad\text{(D18)}
```

The bound holds with the exact product interval, moving divisor cutoff and
covering congruence retained or dropped, because it is absolute. The source
values of $`P_0,P_1`$ satisfy its hypothesis for sufficiently large $`X`$.
It gives arbitrary logarithmic saving when the covering data and the marking
parameters $`K,\rho,v_0,b`$ are fixed. If those parameters vary, the explicit
factor in (D18) must separately beat the requested logarithmic power. No relative
estimate at all growing covering moduli is inferred from this absolute bound.
The elementary dependence on $`K,\rho,V_i`$ is explicit in (D18);
this does not give uniformity in those parameters for the independent source
operator or base-energy estimates.

## 6. Why the required phase family fits the source interfaces

This paragraph identifies an additional *algebraic* compatibility, not a new
certification of the entire external proof. In Lü--Wang--Wu,
arXiv:2610.20242v1, equations (4.5), (4.68), (4.71)--(4.72) and Section 4.6
encode a base square by endpoint vectors with

```math
P=(D_{\rm aux}Bu,s),\qquad P'=(D_{\rm aux}Ar,v).
```

Their position function $`G_0(P_1)`$ extracts the part of $`P_1`$
supported on the auxiliary primes, so on the indicated support
$`G_0(P_1)=D_{\rm aux}B`$ and
$`G_0(P'_1)=D_{\rm aux}A`$.
Replacing the endpoint vector $`f(P)`$ by

```math
f_t(P)=G_0(P_1)^{it}f(P)
```

inserts exactly $`(A/B)^{it}`$ in its sesquilinear pairing. Every norm,
supremum bound and support is unchanged, and list-permutation invariance is
preserved. Thus auxiliary-product Mellin phases do not require new derivatives
of the smooth dyadic cutoff or a growing list-dependent projection.

On the major-arc side, the same phase shifts the argument of the
auxiliary-prime polynomial. The source's Lemma 5.2 explicitly gives uniformity
in this arbitrary real frequency shift, and (5.15)--(5.16) use that
uniformity. The phase does not shift the frequency at which the long Möbius
coefficient is estimated. Hence phase uniformity in (D11), once the relevant
fixed-shift/fixed-covering base proof is supplied, introduces no new cofactor
modulus or frequency barrier at these stated interfaces.

The exact product window in (D1) is also paid: Corollary D3.2 transfers a
rectangular-support base estimate to that window using the same auxiliary
phases. The long Möbius coefficient receives no additional phase from this
operation. This avoids silently replacing the exact window by an unrestricted
prefix, while keeping the input in the form of the source's rectangular
coefficient interface.

## 7. What is repaired and what is still unproved

Theorem D3, Corollaries D3.1--D4, the divisor-moment estimates, the diagonal/shared-prime
bounds, the global coprimality excision and the endpoint phase identity are
unconditional mathematical statements under their displayed elementary
hypotheses. They establish the following implication:

> A fixed-shift, fixed-covering base-square estimate with arbitrary logarithmic
> saving and the specified phase uniformity pays the entire growing cofactor
> range and the actual divisor cutoff, without a separate $`1/c`$ signed-moment
> theorem for each affine slope.

A separate pointwise bound with a relative factor $`1/c`$ is therefore
unnecessary for this averaged route. The proved transfer pays that obligation
from (D11).

The base estimate (D11) for the required shift, covering data and source
coefficients is **not proved in this note**. The original source has shift 2.
The fixed-$`g`$ root-counting extension and its residue densities are now proved
in [Primitive-root counting](root-counting-moduli.md); the complete transferred
operator and major-arc argument is still required. The independent marking-removal problem
also remains. None of the estimates here asserts that the marked sum accurately
approximates the original endpoint remainder at its required relative scale.
For growing $`Q,g`$, one must additionally supply base constants and all errors
relative to $`\kappa(Q,g)X`$. Thus the prime-gap target remains unresolved.

The source's stated square estimate is compatible with its diagonal mass; it
is not refuted by (D14). Conversely, the elementary positive envelopes in this
note cannot create its signed cancellation. They transfer cancellation once
available, and remove a distinct quantitative cofactor obstacle.

## References and verification scope

- [Signed endpoint mass](signed-endpoint-transfer.md), especially its exact
  cofactor form (14), defines the prime-gap application.
- Guangshi Lü, Zhiwei Wang and Jie Wu, *On the Hardy--Littlewood--Chowla
  Conjecture*, [arXiv:2610.20242v1](https://arxiv.org/html/2610.20242v1),
  14 October 2026. Inspected interfaces: Section 4.1, especially (4.4)--(4.8)
  and Lemma 4.1; Section 4.6 endpoint vectors; (4.68), (4.71)--(4.76);
  Lemma 5.2; (5.15)--(5.16); Proposition 2.2.
- The divisor-moment and truncated sine-integral facts used above are proved
  here, so no unrecorded distribution or exceptional-character hypothesis is
  needed for D1--D4.

The accompanying [finite script](code/cofactor_dispersion_checks.py) checks
the exact grouping identities and their moving cutoffs on signed integer
coefficient examples, including retained terms with $`(A,c)\gt1`$.
It also checks a counterexample to omitting the old adapter's coprimality
hypothesis, cancellation examples showing that a square need not dominate its
formal diagonal and that an untwisted energy alone cannot pay cutoffs, and the
endpoint unit-phase identity. It does not verify
(D11), any asymptotic estimate or any new prime-gap occurrence. Run it in both
normal and optimized Python; all verification branches use explicit exceptions.
