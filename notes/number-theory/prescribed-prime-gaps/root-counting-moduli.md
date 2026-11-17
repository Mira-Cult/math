# Primitive-root counting for arbitrary moduli

**Mira Cult**

We prove a uniform estimate for normalized determinant-one completions of
primitive integer vectors, for every positive modulus, and compute the
unit-ratio densities for any prescribed shift. The key CRT factor assigns
the full prime-power factor of the modulus to the coordinate that supports
its prime. This removes a squarefree restriction in the root-counting
interface of Lü–Wang–Wu, arXiv:2610.20242v1, Appendix A.

The note credits that source's root-counting architecture and elementary
Kloosterman fourth moment, checks the arbitrary-modulus extension, and gives
its own smoothing budget. No historical priority is claimed. These are
root counts; the complete signed base estimate for the prime-gap application
remains unproved.

## 1. The counting theorem

For positive coprime integers $`u,v`$ with $`u,v\gt1`$, let

```math
G(u,v)=\begin{pmatrix}u&c\\v&d\end{pmatrix},
\qquad ud-vc=1,\qquad 0\le c\lt u.
```

This determines $`c,d`$ uniquely. Let $`U,V\ge2`$, put
$`T=\min(U,V)`$, and take intervals $`I_1,I_2\subset[1,16]`$ and
a half-open interval $`I_3\subset[0,1)`$. Endpoint conventions do not
affect the estimates below. For any integer $`S\ge1`$ and any
$`G_0\in\mathrm{SL}_2(\mathbb Z/S\mathbb Z)`$, write $`N_S(G_0)`$
for the number of such pairs satisfying

```math
u/U\in I_1,\qquad v/V\in I_2,\qquad c/u\in I_3,
\qquad G(u,v)\equiv G_0\pmod S.
```

**Theorem RC1.** Uniformly in all these data,

```math
N_S(G_0)=
\frac{UV|I_1||I_2||I_3|}
 {\zeta(2)\,|\mathrm{SL}_2(\mathbb Z/S\mathbb Z)|}
+O\!\left(UV S^2T^{-1/32}\right),
\qquad
|\mathrm{SL}_2(\mathbb Z/S\mathbb Z)|
=S^3\prod_{p\mid S}(1-p^{-2}).
\qquad\text{(RC1)}
```

The implied constant is absolute. For large $`S`$ the error can exceed the
main term; the theorem asserts no relative asymptotic in that range.

### A complete exponential-sum input

For $`m\ge2`$, define

```math
K_m(h,k)=\sum_{y\in(\mathbb Z/m\mathbb Z)^\times}
 e\!\left(\frac{hy+ky^{-1}}m\right),\qquad e(t)=e^{2\pi i t}.
```

We shall use the elementary bound

```math
|K_m(h,k)|\ll_\epsilon
m^{3/4+\epsilon}(h,k,m)^{1/4}.
\qquad\text{(RC2)}
```

Here is a proof, including nonprimitive frequencies and arbitrary moduli.
Orthogonality identifies the sum of the fourth powers over $`h,k\bmod m`$
with $`m^2`$ times the number of quadruples of units having equal sums and
equal sums of inverses. Eliminating the fourth variable shows that their
remaining three variables satisfy

```math
m\mid (y_1+y_2)(z_1-y_1)(z_1-y_2).
```

The linear map to these three factors has a kernel of size at most two:
its kernel is $`(t,-t,t)`$ with $`2t=0\pmod m`$. Distribute the prime
power factors of $`m`$ among the three factors of the product. There are
$`d_3(m)`$ ordered choices $`m=m_1m_2m_3`$, and each choice permits at
most $`m^2`$ triples. Thus the fourth-moment sum is at most
$`2m^4d_3(m)`$.

The pairs $`(hs,ks^{-1})`$ for units $`s\bmod m`$ all have the same
Kloosterman sum. Their number is
$`\varphi(m/(h,k,m))`$: the stabilizer is the kernel of reduction to
the units modulo $`m/(h,k,m)`$. Consequently

```math
|K_m(h,k)|^4\le
\frac{2m^4d_3(m)}{\varphi(m/(h,k,m))}.
```

The elementary estimates $`d_3(m)\ll_\epsilon m^\epsilon`$ and
$`m/\varphi(m)\ll_\epsilon m^\epsilon`$, with the parameter adjusted,
prove (RC2). Each follows by bounding all but finitely many prime factors
by a small power of that prime. This argument uses no RH input.

### The modulus factorization that removes squarefreeness

Write $`G_0=(\begin{smallmatrix}u_0&c_0\\v_0&d_0\end{smallmatrix})`$
and fix $`u\equiv u_0\pmod S`$. Consider the pairs $`(c,v)\bmod uS`$
such that

```math
c\equiv c_0\pmod S,\qquad v\equiv v_0\pmod S,
\qquad cv\equiv ud_0-1\pmod{uS}.
\qquad\text{(RC3)}
```

Call this set $`\mathscr R_u`$. It describes exactly the required matrix
class after $`d=(1+cv)/u`$ is recovered. Every permitted $`c`$ is a
unit modulo $`u`$. Of the $`u`$ lifts of $`c_0\bmod S`$, the primes
dividing both $`u`$ and $`S`$ exclude none, since $`c_0`$ is already
a unit at those primes. The remaining primes dividing $`u`$ exclude their
usual proportion. For each permitted $`c`$, the substitution
$`v=v_0+Sj`$ determines one $`j\bmod u`$. Therefore

```math
|\mathscr R_u|=u\prod_{p\mid u,\ p\nmid S}(1-1/p).
\qquad\text{(RC4)}
```

Set

```math
S_1=\prod_{p\mid u}p^{v_p(S)},\qquad S_2=S/S_1.
\qquad\text{(RC5)}
```

Empty products equal one. Then $`(S_2,uS_1)=1`$, and all primes dividing
$`S_1`$ divide $`u`$. In particular, $`ud_0-1`$ is a unit modulo
$`uS_1`$. This factorization is valid without a squarefree assumption.
Using $`S_1=(u,S)`$ instead would fail, for example, at $`u=2,S=4`$.

Modulo $`S_2`$, both coordinates in (RC3) are fixed. Modulo $`uS_1`$,
they satisfy $`cv=ud_0-1`$ and $`c=c_0\pmod{S_1}`$; the latter
conditions also force $`v=v_0\pmod{S_1}`$, because $`c_0`$ is a
unit there and $`u\equiv u_0\pmod{S_1}`$.

Choose $`\gamma S_2\equiv1\pmod{uS_1}`$. CRT and the additive
orthogonality expansion of $`c=c_0\pmod{S_1}`$ imply

```math
\left|\sum_{(c,v)\in\mathscr R_u}
 e\!\left(\frac{hc+kv}{uS}\right)\right|
\le\frac1{S_1}\sum_{j\bmod S_1}
 \left|K_{uS_1}(\gamma h+ju,
                  \gamma k(ud_0-1))\right|.
\qquad\text{(RC6)}
```

For a nonzero frequency pair of size at most $`H=u^{1/8}`$,

```math
(\gamma h+ju,\gamma k(ud_0-1),uS_1)
\le S_1(h,k,u)\le S_1H.
```

Apply (RC2) with $`\epsilon=1/100`$. The right side of (RC6) is

```math
\ll u^{3/4+1/100}S_1^{1+1/100}H^{1/4}
\ll u^{633/800}S^2.
\qquad\text{(RC7)}
```

### From Fourier sums to rectangles

We spell out a smoothing budget so no unproved discrepancy estimate is
hidden here. Put $`\Delta=u^{-1/32}/100`$. A circle interval has smooth
upper and lower approximations obtained by enlarging or contracting it
by $`2\Delta`$ and convolving with a nonnegative smooth probability
density supported within $`\Delta`$. Their zeroth Fourier coefficients
differ from its length by $`O(\Delta)`$, their supremum norms are at
most one, and for every fixed integer $`j\ge1`$ their coefficients obey

```math
|\widehat f(h)|\ll_j(1+\Delta|h|)^{-j}.
```

For an interval shorter than $`4\Delta`$, use zero for the lower
approximation; for one whose enlargement fills the circle, use one for
the upper approximation. Thus these bounds cover all intervals, including
boundary points. They give

```math
\sum_h|\widehat f(h)|\ll\Delta^{-1},\qquad
\sum_{|h|\gt H}|\widehat f(h)|\ll\Delta^{-6}H^{-5}.
```

For the product of two such approximations, the zeroth-frequency error
is $`O(u\Delta)`$. The sum over nonzero frequencies bounded by $`H`$
is at most (RC7) times $`O(\Delta^{-2})`$. The remaining frequencies
cost at most $`O(u\Delta^{-7}H^{-5})`$, using $`|\mathscr R_u|\le u`$.
The three powers of $`u`$ are respectively $`31/32`$, $`683/800`$
and $`19/32`$. We obtain, for any two circle intervals $`J_1,J_2`$,

```math
\sum_{(c,v)\in\mathscr R_u}
 \mathbf1_{J_1}(c/(uS))\mathbf1_{J_2}(v/(uS))
=|\mathscr R_u||J_1||J_2|+O(u^{31/32}S^2).
\qquad\text{(RC8)}
```

### Summing the first coordinate

Suppose first that $`U\le V`$. The interval $`c/u\in I_3`$, with
$`0\le c\lt u`$, has normalized length $`|I_3|/S`$ on the circle
in (RC8). Divide the $`v`$ interval into periods of length $`uS`$.
There are $`O(V/u+1)`$ pieces. Its total normalized length is
$`V|I_2|/(uS)`$. Equations (RC4) and (RC8) give the fixed-$`u`$ count

```math
\frac{V|I_2||I_3|}{S^2}
 \prod_{p\mid u,\ p\nmid S}(1-1/p)
+O\!\left((V/u+1)u^{31/32}S^2\right).
```

The errors sum to $`O(UVS^2U^{-1/32})`$. For the main term, expansion
into squarefree divisors yields

```math
\begin{aligned}
\sum_{\substack{u/U\in I_1\\u\equiv u_0\pmod S}}
 \prod_{p\mid u,\ p\nmid S}(1-1/p)
&=\sum_{\substack{\ell\le16U\\(\ell,S)=1}}
 \frac{\mu(\ell)}\ell
 \left(\frac{U|I_1|}{\ell S}+O(1)\right)\\
&=\frac{U|I_1|}{S\zeta(2)}
 \prod_{p\mid S}(1-p^{-2})^{-1}+O(\log(2U)).
\end{aligned}
```

These congruences are compatible because $`(\ell,S)=1`$; no assumption
on $`(u_0,S)`$ is needed. Extending the convergent series costs
$`O(1/S)`$. The additional error $`O(V\log(2U)/S^2)`$ is absorbed
in the displayed error in RC1.

For completeness, the group order in RC1 is valid for arbitrary $`S`$.
Modulo $`p^e`$, the first column has
$`p^{2e}(1-p^{-2})`$ primitive possibilities. The determinant map in
the second column is surjective and has exactly $`p^e`$ preimages of
one. CRT multiplies these counts.

If $`V\lt U`$, use the normalized completion

```math
\widetilde G=\begin{pmatrix}v&v-d\\u&u-c\end{pmatrix},
\qquad \frac{v-d}{v}=1-\frac cu-\frac1{uv}.
```

The matrix transformation is an involution, including modulo $`S`$.
Its root coordinate differs from $`1-c/u`$ by at most $`1/(UV)`$.
Upper and lower intervals enlarged by that amount reduce the estimate to
the already proved order of scales. The main-term change is $`O(1)`$,
which RC1's error absorbs. This completes the proof. $`\square`$

## 2. Exact fixed-gap residue densities

Let $`g\ge2`$, fix a unit $`r\bmod g`$, and let $`S`$ be squarefree
with $`(S,g)=1`$. For each $`p\mid S`$, fix a projective line
$`\ell_p\in\mathbb P^1(\mathbb F_p)`$. Impose

```math
(uv,g)=1,\qquad v\equiv ru\pmod g,
\qquad \ker((u,-gc):\mathbb F_p^2\longrightarrow\mathbb F_p)
=\ell_p\quad(p\mid S).
```

**Corollary RC2.** The number of pairs with these restrictions and the
three interval restrictions of RC1 equals

```math
\frac{UV|I_1||I_2||I_3|}{\zeta(2)}
 \frac1{g\prod_{p\mid g}(1+1/p)}
 \prod_{p\mid S}\frac1{p+1}
+O\!\left(UV(gS)^5T^{-1/32}\right).
\qquad\text{(RC9)}
```

**Proof.** Apply RC1 at modulus $`gS`$. Modulo $`g`$, there are
$`\varphi(g)`$ permitted first columns, namely $`(u,ru)`$ with
$`u`$ a unit, and $`g`$ determinant-one completions of each. The
proportion is

```math
\frac{g\varphi(g)}{g^3\prod_{p\mid g}(1-p^{-2})}
=\frac1{g\prod_{p\mid g}(1+1/p)}.
```

For each $`p\mid S`$, multiplication of the second coordinate $`c`$
of the first row by $`-g`$ permutes the nonzero first rows. A fixed kernel line
has $`p-1`$ such rows, and each has $`p`$ completions. Its proportion
is therefore $`p(p-1)/[p(p^2-1)]=1/(p+1)`$. CRT gives the product
of the proportions. There are at most $`(gS)^3`$ permitted classes;
summing their errors proves (RC9). $`\square`$

For $`g=2,r=1`$, the density factor is $`1/3`$, exactly the odd-coordinate
component in the inspected source. The formula also treats prime powers
in $`g`$ without deleting their residue conditions.

The fixed-gap conjugacy sends the root coordinate to
$`\{-gc/u\}`$. If the interval condition is imposed on this transformed
coordinate instead, its inverse image consists of $`g`$ circle intervals,
of total length $`|I_3|`$. Cutting at zero gives at most $`g+1`$
ordinary pieces, with the endpoint conventions retained. Thus the same main term
holds with error
$`O(UVg(gS)^5T^{-1/32})`$. The extra factor is explicit; a growing
$`g`$ cannot silently be absorbed in a fixed constant.

More generally, any specified finite set of matrix classes modulo an
additional modulus can be handled by RC1 at the least common multiple,
with its exact class proportion and the corresponding number of errors.
This observation does not evaluate a prime-weighted correlation.

## 3. Parameter ranges and the remaining analytic obligation

For fixed $`g`$, if $`T\ge X^\delta`$ and
$`S\le\exp(C(\log X)^\sigma)`$ with fixed $`\delta,C\gt0`$ and
$`\sigma\lt1`$, RC9 has normalized error

```math
O_g\!\left(\exp(5C(\log X)^\sigma)
                    X^{-\delta/32}\right).
```

It is a power saving for sufficiently large $`X`$. The same conclusion
holds for the transformed root coordinate. For growing $`g`$, the
explicit factors $`g^5`$, or $`g^6`$ after that coordinate change,
must also be paid, and a relative estimate must account for the smaller
main density. No relative growing-cover theorem is asserted here.

This proves the root-counting and finite-residue-density portion of the
fixed-$`g`$ extension. It does not prove that the remaining operator
projection, endpoint coefficients, major arcs, and all error terms combine
to give the phase-uniform base-energy estimate in
[Cofactor averaging](cofactor-dispersion.md), equation (D11).
In particular, it gives no cancellation of the unmarked endpoint sector
and no lower bound for $`C_g(X)`$.

## Sources and verification

The comparison source is Guangshi Lü, Zhiwei Wang and Jie Wu,
*On the Hardy–Littlewood–Chowla Conjecture*,
[arXiv:2610.20242v1](https://arxiv.org/html/2610.20242v1),
14 October 2026, Appendix A, Lemma A.1 and (A.2)–(A.5).
Its squarefree factorization is replaced by (RC5); its odd-coordinate
density is the special case $`g=2`$ of RC9. This note neither assumes
the paper's principal theorem nor certifies its complete proof.

The finite checks in
[root_counting_checks.py](code/root_counting_checks.py) independently
enumerate the relevant modular sets and verify their exact cardinalities,
the full-prime-power factorization, the CRT Fourier reduction, and the
unit-ratio/projective-line densities for specified small moduli.
They do not verify the asymptotic error bound or any prime-gap theorem.
The scope of mathematical review is recorded in [Verification](VERIFICATION.md).
