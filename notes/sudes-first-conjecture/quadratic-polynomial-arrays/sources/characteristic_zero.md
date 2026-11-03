# Prescribed quadratic polynomial arrays over the rationals

## Scope and main result

This manuscript concerns the exact fixed-degree ordering in
[the problem statement](../README.md#exact-pool-and-geometry): primitive integer polynomials,
positive leading coefficient, height first and then ascending-coefficient
lexicographic order. Constant primes are excluded. The representatives are
never rescaled. All theorem labels here are manuscript-local; no permanent
repository claim identifiers have been allocated.

**Theorem Q2.** Fix an integer $`D\ge2`$. For every integer


```math
n\ge N_Q(2,D):=2^{1024(D+1)},
```


the first $`n^D`$ prescribed degree-two polynomials admit a bijective
placement in $`[n]^D`$ whose every full signed-coordinate line sum is
irreducible over $`\mathbb Q`$. Both parities of $`n`$ are covered. The
geometry is exactly that in the problem statement; no extra sums are
required. This is a sufficient cutoff, with no assertion of optimality.

The distribution estimates below and the permutation local-lemma interface
give the proof. The proof is effective: enumerating all permutations and
testing quadratic discriminants is a terminating construction above the
stated cutoff. No efficient running time is claimed.

This theorem does **not** assert primitive line sums, so it does not yet
prove the corresponding $`\mathbb Z[x]`$ target. Section 8 proves a
quantitative obstruction to obtaining primitivity from unconstrained random
mixing. That obstruction concerns a proof method, not the existence of
arrays. Degree one over $`\mathbb Q`$ is elementary: every sum still has
positive leading coefficient and degree one, so every permutation works.

## 1. Elementary height counts, including the incomplete shell

Use ascending coefficient vectors $`(c,b,a)`$ for $`a x^2+b x+c`$, with


```math
B_H=\{(c,b,a)\in\mathbb Z^3: |b|,|c|\le H,\ 1\le a\le H\},
 \qquad V_H=|B_H|=H(2H+1)^2.
```


Let $`A`$ be the first $`N=n^D`$ elements of the canonical quadratic pool,
and let $`H`$ be its largest coefficient height. In particular, $`A`$
contains every primitive irreducible in $`B_{H-1}`$, and is contained in
$`B_H`$. Nothing in the argument randomizes the last shell or assumes it
complete.

### Lemma 1.1: reducible height count

For every integer $`H\ge2`$, the number of quadratics in $`B_H`$ that are
reducible over $`\mathbb Q`$ is at most


```math
R(H):=40H^2(1+\log(2H)).                         \qquad\text{(1)}
```


Here and throughout, unmarked logarithms are natural. This count includes
nonprimitive quadratics; that harmless overcount is useful.

**Proof.** By Gauss's lemma, write a reducible quadratic as a positive
integer content times two primitive integer linear polynomials, orienting
both leading coefficients positively. If


```math
(u x+v)(w x+z)=a x^2+b x+c,
```


then the product of the two factor heights is at most twice the height
of the product. To see this without a height theorem, the cases where
both maxima are leading coefficients or both are constant coefficients
give the stronger bound $`H`$. In a mixed case put
$`R=u|z|`$, $`r=|v|w\le R`$. Then
$`Rr=|ac|\le H^2`$ and $`R-r\le|b|\le H`$. If $`R\gt 2H`$, both
$`r\gt H`$ and $`Rr\gt 2H^2`$, a contradiction. The other mixed case is
identical.

Choose the primitive factor of smaller height and put the content into
the other factor. Its height $`t`$ is at most $`\sqrt{2H}`$, and the
cofactor height is at most $`2H/t`$. There are at most $`4t`$ integer
linear polynomials of exact height $`t`$ with positive leading
coefficient. There are at most $`10H^2/t^2`$ possible cofactors: here
$`t\le\sqrt{2H}\le H`$. Consequently the number of products is at most


```math
40H^2\sum_{1\le t\le\sqrt{2H}}\frac1t
 \le40H^2(1+\log(2H)).
```


Overcounting products with two choices of factor does not affect the
upper bound. QED.

### Lemma 1.2: density and means for every prefix

If $`H\ge2^{20}`$, then


```math
|A|\ge \frac{23}{32}V_H,
 \qquad 2H^3\le |A|\le9H^3.                    \qquad\text{(2)}
```


For $`E=A`$ or $`E=A\setminus\{z\}`$, with $`z\in A`$, its coordinate
means satisfy


```math
\mu_a(E)\ge H/8,
 \qquad |\mu_b(E)|,|\mu_c(E)|
       \le100(1+\log(2H)).                       \qquad\text{(3)}
```


**Proof.** A union bound over all integer common divisors $`k\ge2`$,
not merely primes, bounds the number of nonprimitive vectors in $`B_H`$
by


```math
\begin{aligned}
 \sum_{k=2}^H\lfloor H/k\rfloor(2\lfloor H/k\rfloor+1)^2
 &\le H^3+4H^2+H(1+\log H).
 \end{aligned}                                  \qquad\text{(4)}
```


For example, $`\sum_{k\ge2}k^{-3}\le1/4`$,
$`\sum_{k\ge2}k^{-2}\le1`$, and the harmonic sum is at most
$`1+\log H`$. The missing final shell has at most


```math
V_H-V_{H-1}=12H^2-4H+1\le12H^2                 \qquad\text{(5)}
```


points. Subtract (1), (4), and (5) from $`V_H`$. For $`H\ge2^{20}`$
their sum is at most $`(9/8)H^3`$; this follows already from


```math
\frac{56+40\log(2H)}{H}
       +\frac{1+\log H}{H^2}\lt \frac18.
```


Both terms decrease in this range, and replacing $`\log H`$ by
$`\log_2H`$ verifies the inequality at $`2^{20}`$. Since
$`V_H\ge4H^3`$, the first inequality in (2) follows. The other two are
weaker consequences, using $`V_H\le9H^3`$.

All primitive vectors in the complete box have total $`b`$-coordinate
and total $`c`$-coordinate zero, by sign reflection. Deleting the
reducible vectors and an arbitrary part of the final shell changes
either total by at most $`H(R(H)+12H^2)`$; deleting $`z`$ changes it by
at most a further $`H`$. Division by the density lower bound proves
the two lower-coefficient bounds in (3).

After one deletion the density is still at least $`2/3`$ in $`B_H`$.
At most $`V_H/4`$ vectors have $`a\le H/4`$. Thus at least $`5/8`$ of
$`E`$ have $`a\gt H/4`$, giving the stronger leading-coefficient bound
$`\mu_a(E)\gt 5H/32`$. QED.

The bounds in (2), with $`N=n^D`$, will be used in the convenient form


```math
\frac{n^{D/3}}3\le H\le n^{D/3}.               \qquad\text{(6)}
```


The left-hand inequality already holds for every $`H\ge1`$, since
$`N\le V_H\le9H^3`$; it can therefore establish $`H\ge2^{20}`$
before invoking Lemma 1.2.

## 2. A uniform Fourier estimate for a dense lattice box

No irreducibility statistic for independently uniform coefficients is
being applied to a subset sum. Instead we prove a local concentration
estimate for the actual prescribed pool.

Write $`\|t\|_{\mathbb T,\infty}`$ for the largest distance of a
coordinate of $`t\in\mathbb R^3`$ to the nearest integer, and put
$`\gamma=2^{-50}`$.

### Lemma 2.1: dense-box spectral gap

If $`H\ge2^{20}`$, $`E\subset B_H`$, and
$`|E|\ge(2/3)V_H`$, then its normalized characteristic function
$`\phi_E(t)=|E|^{-1}\sum_{v\in E}e^{2\pi i\,t\cdot v}`$
satisfies


```math
1-|\phi_E(t)|^2
 \ge\gamma\min\{H^2\|t\|_{\mathbb T,\infty}^2,1\}.
                                                        \qquad\text{(7)}
```


**Proof.** Put $`h=\lfloor H/32\rfloor\ge H/64`$. For every
$`v\in[-h,h]^3\cap\mathbb Z^3`$, the union $`B_H\cup(B_H+v)`$
has cardinality at most


```math
(1+1/32)(1+1/64)^2V_H\lt \frac{13}{12}V_H.
```


Hence $`|E\cap(E+v)|\ge V_H/4`$. Expanding the square of the
characteristic function gives


```math
1-|\phi_E(t)|^2
 \ge\frac{(2h+1)^3}{4V_H}
    \left(1-\prod_{j=1}^3 D_h(t_j)\right),       \qquad\text{(8)}
```


where $`D_h(u)=(2h+1)^{-1}\sum_{k=-h}^h e^{2\pi iku}`$ is real.
The prefactor is at least $`2^{-21}`$.

For completeness, the elementary Dirichlet-kernel estimate needed here is


```math
1-|D_h(u)|\ge\frac1{200}
       \min\{h^2\|u\|_{\mathbb T}^2,1\}.        \qquad\text{(9)}
```


If $`\theta=\|u\|_{\mathbb T}\ge1/h`$, the sine formula and
$`\sin(\pi\theta)\ge2\theta`$ give $`|D_h(u)|\lt 1/4`$.
If $`0\le\theta\le1/h`$, expand $`1-|D_h(u)|^2`$ using two independent
uniform integers in $`[-h,h]`$, and retain the differences
$`\pm k`$, $`1\le k\le\lfloor h/2\rfloor`$. Their combined probability
is at least $`1/(3h)`$. On this range
$`1-\cos(2\pi\theta k)\ge8\theta^2 k^2`$, and
$`\sum_{k\le\lfloor h/2\rfloor} k^2\ge h^3/81`$. This proves
$`1-|D_h(u)|^2\ge h^2\theta^2/32`$, stronger than (9) after dividing
by $`1+|D_h(u)|\le2`$.

Choose a coordinate having largest torus distance. Then
$`1-\prod_jD_h(t_j)\ge1-|D_h(t_j)|`$. Combining (8), (9), and
$`h\ge H/64`$ proves (7), with considerable room in the choice
$`\gamma=2^{-50}`$. QED.

## 3. Sampling without replacement and a specified included entry

Let $`S`$ be the coefficient sum of a uniform $`n`$-element subset of
$`A`$. We also need, uniformly for every prescribed $`z\in A`$, the
conditional law $`S\mid z\in S_{\mathrm{entries}}`$. In this conditional law
write $`S=z+S'`$, where $`S'`$ is the sum of a uniform $`(n-1)`$-element
subset of $`A\setminus\{z\}`$. The symbol $`S_{\mathrm{entries}}`$ denotes
the chosen entries, avoiding confusion between a subset and its sum.

### Lemma 3.1: local concentration

For $`n\ge40`$, $`H\ge2^{20}`$, both laws above satisfy


```math
\sup_{w\in\mathbb Z^3}\Pr(S=w)
 \le\frac{2^{87}}{H^3 n^{3/2}}
       +\exp(-n/2^{53}).                        \qquad\text{(10)}
```


**Proof.** A uniform $`r`$-subset of a finite set can be generated by
selecting $`2r`$ distinct entries in a uniform order, pairing successive
entries, and independently choosing one endpoint of each pair. Symmetry
under all permutations of the entry labels proves that the output is a
uniform subset. Here $`r=n`$, or $`r=n-1`$ after excluding $`z`$.

Every residual population during pair selection has density at least
$`2/3`$ in $`B_H`$: by (2) the available margin is $`5V_H/96`$, while


```math
2n+1\le\frac5{96}n^2\le\frac5{96}V_H
 \qquad(n\ge40).
```


For a pair of distinct uniform entries $`a,b\in E`$, Cauchy--Schwarz gives


```math
\begin{aligned}
 \mathbb E\left|\cos\bigl(\pi t\cdot(a-b)\bigr)\right|
 &\le\left(\frac{1+\mathbb E\cos(2\pi t\cdot(a-b))}{2}\right)^{1/2}\\
 &\le\left(\frac{1+|\phi_E(t)|^2}{2}\right)^{1/2}\\
 &\le\exp\left[-\frac\gamma4
       \min\{H^2\|t\|_{\mathbb T,\infty}^2,1\}\right].
 \end{aligned}                                  \qquad\text{(11)}
```


The middle inequality uses the exact distinct-pair identity
$`\mathbb E\cos(2\pi t\cdot(a-b))=(|E||\phi_E(t)|^2-1)/(|E|-1)`$.
Conditional on all pairs, the characteristic function from the independent
endpoint choices has absolute value the product of these cosine absolute
values. Sequential conditioning in pair order therefore proves the bound


```math
|\phi_S(t)|\le\exp\left[-\frac{\gamma r}{4}
       \min\{H^2\|t\|_{\mathbb T,\infty}^2,1\}\right].       \qquad\text{(12)}
```


The extra fixed entry contributes only a unit complex factor. Fourier
inversion, a Gaussian integral, and $`r\ge n/2`$ give


```math
\sup_w\Pr(S=w)
 \le\left(\frac{12\pi}{\gamma rH^2}\right)^{3/2}
       +e^{-\gamma r/4}
 \le\frac{2^{87}}{H^3n^{3/2}}+e^{-n/2^{53}}.
```


For the integral, inside $`H\|t\|_{\mathbb T,\infty}\le1`$ use
$`\|t\|_\infty^2\ge\|t\|_2^2/3`$, and outside use the constant
exponential bound. QED.

### Lemma 3.2: concentration around the actual means

For either law, each coordinate sum differs from its own expectation by
more than


```math
u=H\sqrt{40n\log n}
```


with probability at most $`2n^{-20}`$. The probability of any of the
three coordinate exceptions is at most $`6n^{-20}`$.

**Proof.** For a sample of $`r`$ bounded numbers without replacement,
the exponential moment is at most the corresponding with-replacement
moment. An elementary proof is the normalized elementary-symmetric-mean
inequality applied to the positive numbers $`e^{t x_j}`$. Averaging two
of these numbers with their sum fixed increases the elementary symmetric
polynomial, since its dependence on the pair is
$`ab e_{r-2}+(a+b)e_{r-1}+e_r`$; iterating proves the inequality.
For one bounded variable in an interval of length $`2H`$, the centered
log moment generating function is at most $`t^2(2H)^2/8`$: its second
derivative is a tilted variance, at most $`(2H)^2/4`$, and its value and
first derivative at zero vanish. Chernoff optimization consequently gives


```math
\Pr(|S_j-\mathbb ES_j|\gt u)
       \le2\exp\{-u^2/(2rH^2)\}\le2n^{-20}.
```


The leading-coefficient interval is shorter, but the same bound suffices.
A fixed included entry only translates the distribution. QED.

## 4. Reducible quadratics in the sum window

### Lemma 4.1: translated-window count

Suppose $`M\ge1`$, $`s\ge\sqrt M`$, and $`J\subset\mathbb R`$ is an
interval of length at most $`2s`$. The number of reducible integer
quadratics


```math
A x^2+B x+C,
 \quad A\in J\cap[s,M],\quad |B|,|C|\le s,
```


is at most


```math
60s^2(1+\log M).                               \qquad\text{(13)}
```


**Proof.** Every real root has absolute value at most $`2`$, since
$`|B|,|C|\le A`$. For a reducible quadratic write its primitive part as
a product of two primitive integer linear factors, orienting both leading
coefficients positively. Choose a factor $`u x+v`$ whose leading
coefficient is the smaller of the two; then
$`1\le u\le\sqrt A\le\sqrt M`$. Put the entire content in the other
factor $`w x+z`$. The root bound gives $`|v|\le2u`$.

For each $`u`$ there are at most $`5u`$ numerators $`v`$. The condition
$`uw=A\in J`$ leaves at most $`2s/u+1`$ possibilities for $`w`$.
For each of these, $`uz+vw=B\in[-s,s]`$ leaves at most $`2s/u+1`$
possibilities for $`z`$. The condition on $`C=vz`$ can now be discarded.
Writing $`m=\lfloor\sqrt M\rfloor`$, the total is at most


```math
\begin{aligned}
 \sum_{u=1}^m5u(2s/u+1)^2
 &\le20s^2(1+\log m)+20s m+\frac52m(m+1)\\
 &\le60s^2(1+\log M),
 \end{aligned}
```


because $`s\ge\sqrt M`$. This also covers $`C=0`$, repeated factors,
and nonprimitive sums. QED.

## 5. Uniform conditional bad-subset estimate

Let $`b`$ be the failure probability for a uniform $`n`$-subset, and let
$`b_z`$ be its failure probability conditioned on including $`z\in A`$,
where failure means reducibility over $`\mathbb Q`$. Put
$`\beta=\max(b,\max_z b_z)`$.

**Theorem 5.1.** For every fixed $`D\ge2`$ and every integer
$`n\ge2^{1024(D+1)}`$,


```math
\boxed{\quad
 \beta\le 2^{104}(D+3)(\log n)^2
              n^{-D/3-1/2}+n^{-10}.\quad}        \qquad\text{(14)}
```


In particular $`\beta=o_D(1/n)`$. The one-entry conditioning is
essential for the permutation local lemma; it is not inferred from the
unconditional bound.

**Proof.** Take


```math
M=nH,\qquad s=16H\sqrt{n\log n}.
```


All the elementary numerical conditions used next are verified in
Section 7. By (3), the absolute expectation of each lower-coefficient
sum is at most $`100n(1+\log(2H))+H\le u`$. The leading expectation
is at least $`nH/16`$, also in the conditioned law. Outside the three
exceptions of Lemma 3.2, the lower coefficients therefore lie in
$`[-s,s]`$; the leading coefficient lies in an interval of length
$`2u\le2s`$, is at least $`nH/32\ge s`$, and is at most $`M`$.
Also $`s\ge\sqrt M`$.

Multiply (13) by (10) and add the exceptional probability. Enlarging
constants harmlessly gives


```math
\begin{aligned}
 \beta\le{}&18n^{-20}
   +\frac{2^{101}\log n(1+\log(nH))}{H\sqrt n}\\
 &+2^{16}H^2 n\log n(1+\log(nH))e^{-n/2^{54}}.   \qquad\text{(15)}
 \end{aligned}
```


Use (6) and $`1+\log(nH)\le(D+3)\log n`$, valid for $`n\ge2`$.
The second term is at most
$`2^{103}(D+3)(\log n)^2n^{-D/3-1/2}`$. The last term is at most
$`n^{-20}`$ by Section 7. Finally $`19n^{-20}\le n^{-10}`$ for
$`n\ge2`$, proving the slightly enlarged bound (14). QED.

For squares, (14) is $`O(n^{-7/6}\log^2n)`$, and hence even the simple
union bound over $`2n+2`$ lines eventually proves existence. For cubes,
it is $`O(n^{-3/2}\log^2n)`$. The cube union bound would multiply this
by $`3n^2+6n+4`$ and does not close. The permutation local lemma is a
substantive extra ingredient in the cube and higher-dimensional results.
The argument never treats disjoint lines in a random permutation as
independent.

## 6. Applying the permutation interface

Let $`r_D=(3^D-1)/2`$. A cell lies on at most $`r_D`$ full signed-coordinate
lines: choose a nonempty set of varying coordinates, and its relative
signs, giving at most
$`\sum_{k=1}^D\binom Dk2^{k-1}=r_D`$ descriptions through a cell.
Some descriptions fail to contain that cell, which only reduces the
number. Therefore $`L_D(n)n\le r_D n^D`$.

The [permutation local-lemma interface](permutation_bridge.md#permutation-theorem)
states the following sufficient condition for a family of $`n`$-element
cell sets of maximum cell incidence $`r_D`$:


```math
8n r_D\beta\lt 1.                                 \qquad\text{(16)}
```


The interface uses bad partial bijections and bounds dependencies both
through common positions and through common prescribed entries; (14)
provides exactly the required conditional estimate. No independent-line
assumption is used. Section 7 verifies (16) throughout the stated tail.
The resulting arrangement has positive leading coefficient in every line
sum, so each irreducible sum is genuinely of degree two. This proves Q2.

## 7. An explicit whole-tail verification

The numerical cutoff is deliberately conservative, so the verification can
remain elementary and transparent. Write


```math
x=\log_2 n\ge1024(D+1)\ge3072.
```


For all such $`x`$,


```math
\log_2x\le x/64,\qquad D\le x/1024-1,
 \qquad\log n\le x.                             \qquad\text{(17)}
```


The first inequality holds at $`3072`$, and its difference has positive
derivative thereafter. These bounds prove each condition used above:

1. **Pool size and pair depletion.** The unconditional counting bound
   $`N\le9H^3`$ first gives
   $`H\ge n^{2/3}/3\ge2^{2048}/3\gt 2^{20}`$, and $`n\ge40`$.

2. **The means fit the concentration window.** Inequality (17) implies
   $`n^{1/6}\ge100(D+2)\sqrt{\log n}`$. Using (6),
   $`1+\log(2H)\le(D+2)\log n`$, and $`D\ge2`$,

   
```math
\frac{100n(1+\log(2H))+H}{H}
    \le300(D+2)n^{1/3}\log n+1
    \le\sqrt{40n\log n}=u/H.
```


   For the first inequality, the exponent $`1-D/3\le1/3`$ is used.
   For the last, the sufficient bound on $`n^{1/6}`$ leaves a factor
   greater than two, absorbing the added $`1`$.

3. **Leading coefficient and factor window.** We have
   $`n\ge2^{18}\log n`$, hence
   $`s=16H\sqrt{n\log n}\le nH/32`$. In particular $`u\le nH/32`$
   and $`s\ge\sqrt{nH}`$.

4. **The Fourier exponential tail.** The last term of (15) is at most
   $`n^{-20}`$ once

   
```math
n/2^{54}\ge(2D/3+21)\log n+2\log\log n
                   +\log(2^{16}(D+3)).
```


   By (17) its right side is below $`2x^2`$, whereas
   $`2^{x-54}\ge2x^2`$ follows from $`x-55\ge2\log_2x`$.

5. **Permutation local lemma.** Since $`r_D\lt 2^{2D}`$,
   $`D+3\le2^{D+1}`$, and $`D/3-1/2\ge1/6`$, it suffices that

   
```math
n^{1/6}\gt 2^{108}r_D(D+3)(\log n)^2,
   \qquad n^9\gt 16r_D.
```


   The logarithm to base two of the first right side is at most
   $`109+3D+2\log_2x\le106+3x/1024+x/32\lt x/6`$, by (17) and
   $`x\ge3072`$. The second inequality is immediate from
   $`9x\gt 4+2D`$. Thus the two terms of $`8nr_D\beta`$ are each less
   than $`1/2`$, proving (16).

Every comparison holds for all real $`x\ge1024(D+1)`$, so the calculation
establishes the full integer tail, including the incomplete height shells.
It is not a check only at a sequence of powers of two.

## 8. The additional content problem is quantitatively real

### 8.1. The eventual residue support

**Proposition 8.1.** Fix a rational prime $`\ell`$. Every nonzero
vector in $`(\mathbb Z/\ell\mathbb Z)^3`$ occurs as the coefficient
vector of a primitive irreducible quadratic of height at most $`3\ell^2`$.
The zero vector never occurs in the primitive pool. Consequently, once
$`n^D\ge243\ell^6`$, the canonical prefix has residue support exactly
$`(\mathbb Z/\ell\mathbb Z)^3\setminus\{0\}`$.

**Proof.** Write the desired ascending residues as $`(c_0,b_0,a_0)`$.
If $`a_0\ne0`$, set $`a=a_0\in\{1,\ldots,\ell-1\}`$,
$`b=b_0\in\{0,\ldots,\ell-1\}`$, and choose, by the elementary
Chinese remainder theorem,


```math
c\equiv c_0\pmod\ell,\quad c\equiv1\pmod a,
 \quad\ell^2\le c\lt \ell^2+a\ell\le2\ell^2.
```


The resulting quadratic is primitive since $`\gcd(a,c)=1`$, and its
discriminant is negative since $`b^2\lt \ell^2\le ac`$. If $`a_0=0`$,
set $`a=\ell`$, $`b=b_0`$, and choose
$`\ell^2\le c\lt \ell^2+\ell`$ in the desired residue class. At least
one of $`b_0,c_0`$ is nonzero, so $`\gcd(a,b,c)=1`$, and again the
discriminant is negative. All heights are below $`3\ell^2`$.
Finally, there are at most $`9(3\ell^2)^3=243\ell^6`$ coefficient
vectors up to that height. A prefix with at least that many entries
therefore contains all these representatives. QED.

This rules out a persistent obstruction in which every entry has one
common coefficient vector modulo a fixed prime. It does not solve the
overlapping-line residue problem or alter the exact residue multiplicities.
Over the additive group $`(\mathbb Z/\ell\mathbb Z)^3`$, any prescribed
total is a sum of any number $`k\ge2`$ of nonzero vectors: choose the
first $`k-2`$ arbitrarily, and then choose the penultimate vector outside
the at most two forbidden values $`0`$ and the residual total. Thus the
abstract requirement that a disjoint parallel class have nonzero residue
sums creates no total-sum obstruction by itself. Availability of the
required cell residues remains a separate constraint.

### 8.2. Unconstrained random mixing has positive content failure density

**Proposition 8.2.** Assume $`n\ge40`$ and $`H\ge2^{20}`$. For a uniform
$`n`$-subset of the canonical quadratic pool and any integer
$`2\le\ell\le H`$,


```math
\left|\Pr(S\equiv(0,0,0)\pmod\ell)-\ell^{-3}\right|
 \le e^{-n/2^{52}}.                             \qquad\text{(18)}
```


**Proof.** Apply (12) with $`r=n`$ to the nontrivial characters
$`t\in\ell^{-1}\mathbb Z^3/\mathbb Z^3`$. Each has
$`\|t\|_{\mathbb T,\infty}\ge1/\ell`$, and $`H\ge\ell`$, so the
minimum in (12) equals one. Finite Fourier inversion on
$`(\mathbb Z/\ell\mathbb Z)^3`$ gives (18). QED.

In particular, if $`b_Z(A,n)`$ is the fraction of subsets failing the
primitive-and-irreducible target, then


```math
b_Z(A,n)\ge\frac18-e^{-n/2^{52}}.                \qquad\text{(19)}
```


All coefficient sums divisible by two have content at least two, and the
leading coefficient is positive. Consequently neither the simple union
bound nor the small-bad-event permutation argument above can directly
prove the primitive target. This is a proved limitation of those
unconstrained random-mixing estimates. It is **not** an obstruction to an
arrangement: a construction can bias every line away from the zero residue
vector. Finite primitive examples are recorded separately in the exact
computation certificates.

A Z strengthening therefore needs additional arithmetic control, such as
a permutation construction that enforces coprimality before applying the
irreducibility estimates. Deleting entries, rescaling representatives, or
replacing them by monic polynomials would change the problem and is not
used here.

## 9. Boundaries and next obligations

The Q2 proof is specific to fixed degree two. Its reducibility-window
argument uses rational linear factors and their small denominators. It
does not supply a uniform estimate as degree grows and therefore does
not address the secondary all-degree enumeration. Nor is a theorem for
every fixed degree $`d\ge3`$ claimed.

The major remaining Track A obligation is primitive content control for
the exact initial segment. For degree two the irreducibility part is now
available with one-entry-conditioned estimates, which can be reused if a
residue-controlled random permutation law preserves a suitable version
of Lemma 3.1. Any such repair must pay for all lines and the actual
prescribed representatives.

## Source and proof provenance

All quantitative estimates in Sections 1--5, 7, and 8 are proved above.
Gauss's lemma is the standard primitive-factorization fact; the primary
algebra source is Milne, *A Primer of Commutative Algebra*, Section 4,
as pinned in [the source audit](../REFERENCES.md). The permutation
negative-dependence/local-lemma import belongs to the
[permutation manuscript](permutation_bridge.md) and its exact source audit. No density theorem
for random integer polynomials, local central limit theorem, unproved
subset-sum equidistribution hypothesis, or prime-pattern conjecture is
an assumption of Q2.

Mathematical status: complete conventional
argument, subject to independent review at a frozen scientific revision.
Computational verification and independent review must be recorded
separately; no formal verification or external acceptance is asserted.
