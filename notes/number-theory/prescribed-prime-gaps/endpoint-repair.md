# Endpoint parity and the Chen repair

**Mira Cult**

After an endpoint-safe congruence cover, the missing requirement is that both
endpoints are prime. We construct an explicit comparison sequence with the
correct local densities and a nonnegative prime-free parity companion that
retains them. We also derive the exact localized Liouville estimate that
would turn a Chen-type almost-prime weight into a prime-pair lower bound.

This is a contextual version of classical Selberg parity, not a historical
novelty claim or a counterexample to the prime-pair conjecture. The uniform
extension covers $`Qg\le(\log x)^H`$ for fixed $`H`$, with ineffective
constants. The actual endpoint signed estimate remains open.

### Short alternative-route screen

| Proposed repair | What must be gained | Result of this investigation |
| --- | --- | --- |
| Chen prime plus at most two prime factors | Remove semiprime endpoint mass | ER4 gives the exact localized Liouville inequality needed. The positive Chen total by itself does not give it. |
| Average over several protected residue classes | Create endpoint correlation from divisor statistics | ER1–ER3 preserve the local densities and every fixed protected class in a prime-free parity model. A fixed finite nonnegative mixture does not remove this obstruction. |
| Higher factorial moments or a bilinear sieve | Control a second prime constraint after squaring | Section 5 derives the affine two-prime correlation that appears. Individual prime progression errors do not evaluate this term. |
| A very short extra Type II range | Break parity using minimal bilinear information | Ford–Maynard [FM, Theorem 2.1] already gives abstract prime-free examples with such information. The exact range and coefficient class matter. |

The exact signed remainder that would suffice for the actual endpoints
remains the one in
[signed-endpoint-transfer.md](signed-endpoint-transfer.md), Theorem 1 and
Corollary 2.

## 1. A comparison sequence with the correct local densities

Fix even integers $`g\gt0`$ and $`Q\ge2`$, and an integer $`a`$ such that
$`(a(a+g),Q)=1`$. Write $`b\equiv a+g\pmod Q`$ and $`r=Qg`$.
The initial propositions keep $`Q,g,a`$ fixed; Corollary ER3u gives an
explicit growing-parameter range. Let $`x\gt4g`$ and
restrict all sequences to $`x/2\lt n\le x`$. The use of the right endpoint
as the variable is only a change of coordinates from the companion
manuscripts.

Use the canonical singular product

```math
K(r)=\prod_{p\mid r}\frac p{p-1}
      \prod_{p\nmid r}\frac{p(p-2)}{(p-1)^2}.
```

Since $`2\mid r`$, this product is positive. Define

```math
F_s(n)=\prod_{\substack{p\mid n\\p\nmid s}}\frac{p-1}{p-2},
\qquad
H_s=\prod_{p\nmid s}\left(1+\frac1{p(p-2)}\right)
\quad(2\mid s),
```

and put

```math
\rho_g=\prod_{\substack{p\mid g\\p\nmid Q}}\left(1-\frac1p\right),
\qquad
C=\frac{\varphi(Q)}Q K(r).
```

The comparison sequence and the actual shifted-prime sequence are

```math
\begin{aligned}
B(n)&=CQ\,\mathbf1_{n\equiv b\pmod Q}
                   \mathbf1_{(n,g)=1}F_r(n),\\
A(n)&=\varphi(Q)\,\vartheta(n-g)
                   \mathbf1_{n\equiv b\pmod Q},
\qquad \vartheta(m)=\mathbf1_{\mathbb P}(m)\log m.
\end{aligned}
\qquad\text{(1)}
```

These sequences have the same natural mean, asymptotic to $`x/2`$.
On the support of either sequence, $`(n,r)=1`$. For $`A`$, this uses
$`n-g\gt g`$: a prime dividing both $`n`$ and $`g`$ would have to equal
the prime $`n-g`$, which is impossible.

Two elementary normalization identities will be used repeatedly:

```math
C\rho_gH_r=1,
\qquad
F_r(d)\frac{H_{rd}}{H_r}=\frac d{\varphi(d)}
\quad\text{if }(d,r)=1.
\qquad\text{(2)}
```

The first follows by grouping the factors at primes dividing $`Q`$,
dividing $`g`$ but not $`Q`$, and dividing neither. For the second, the
factor contributed by $`p\mid d`$ is

```math
\frac{p-1}{p-2}\left(1+\frac1{p(p-2)}\right)^{-1}
=\frac p{p-1}.
```

**Proposition ER1 (explicit divisor calibration).** For every real interval
$`J\subset(x/2,x]`$ and every integer $`1\le d\le x`$,

```math
\sum_{\substack{n\in J\\d\mid n}}B(n)=
\begin{cases}
0,&(d,r)\gt1,\\[2mm]
\displaystyle\frac{|J|}{\varphi(d)}
 +O_{Q,g}\!\left(F_r(d)(1+\log(2x/d))^3\right),&(d,r)=1.
\end{cases}
\qquad\text{(3)}
```

Here $`|J|`$ is the real length of $`J`$; the error includes endpoint
rounding. In addition,

```math
\sum_{x/2\lt p\le x}B(p)
\sim K(r)\frac{x}{2\log x}.
\qquad\text{(4)}
```

**Proof.** The zero case follows from the support. For $`(d,r)=1`$, set
$`n=dm`$ and $`N=x/d`$. Since $`F_r(dm)=F_r(d)F_{rd}(m)`$, expand

```math
F_s(m)=\sum_{k\mid m}\rho_s(k),\qquad
\rho_s(k)=
\begin{cases}
\displaystyle\prod_{p\mid k}\frac1{p-2},
   &k\text{ squarefree and }(k,s)=1,\\
0,&\text{otherwise}.
\end{cases}
\qquad\text{(5)}
```

If $`\rho_{rd}(k)\ne0`$, then $`(k,Qg)=1`$. The substitution $`m=k\ell`$
and inclusion-exclusion over the primes dividing $`g`$ but not $`Q`$ give

```math
\#\left\{\ell: dk\ell\in J,
       \ dk\ell\equiv b\pmod Q,\ (\ell,g)=1\right\}
 =\frac{|J|\rho_g}{dQk}+O_g(1).
\qquad\text{(6)}
```

The prime factors of $`g`$ that divide $`Q`$ are already excluded by the
unit residue class. Every congruence remaining in this inclusion-exclusion
has coprime moduli.

Uniformly in even $`s`$ and $`N\ge1`$,

```math
\sum_{k\le N}\rho_s(k)\ll(1+\log(2N))^3,
\qquad
N\sum_{k\gt N}\frac{\rho_s(k)}k
     \ll(1+\log(2N))^2.
\qquad\text{(7)}
```

Indeed, $`\rho_s(k)\le3^{\omega(k)}/k\le\tau_3(k)/k`$ on its
squarefree support. The first bound follows by expanding $`\tau_3`$ as a
triple divisor sum. For the second, use
$`\sum_{k\le t}\tau_3(k)\le t(1+\log t)^2`$ and partial summation.
Applying (6), extending the main sum to infinity, and using (7) gives

```math
\sum_{\substack{n\in J\\d\mid n}}B(n)
 =C\rho_gF_r(d)H_{rd}\frac{|J|}{d}
   +O_{Q,g}\!\left(F_r(d)(1+\log(2N))^3\right).
```

Equation (2) proves (3). For a sufficiently large prime $`p`$,
$`F_r(p)=(p-1)/(p-2)=1+O(1/p)`$. The fixed-modulus prime number theorem
in the reduced class $`b\pmod Q`$ then proves (4). $`\square`$

## 2. What the actual primes supply unconditionally

For a sequence $`U`$ on this dyadic interval and $`0\lt\gamma\lt1`$,
write

```math
\mathcal T_{\gamma,B_0}(U;x)=
\sum_{d\le x^\gamma}\tau(d)^{B_0}
 \sup_{J\subset(x/2,x]}
 \left|\sum_{\substack{n\in J\\d\mid n}}U(n)\right|,
\qquad B_0\ge0,
\qquad\text{(8)}
```

where the supremum is over intervals. This is a divisor Type I norm;
it contains no joint-primality input.

**Proposition ER2 (fixed-cover Type I comparison).** For every fixed
$`0\lt\gamma\lt1/2`$, $`A_0\gt0`$ and $`B_0\ge0`$,

```math
\mathcal T_{\gamma,B_0}(A-B;x)
\ll_{Q,g,\gamma,A_0,B_0}x(\log x)^{-A_0}.
\qquad\text{(9)}
```

**Proof.** For $`(d,r)=1`$, the conditions on $`n`$ specify one reduced
class for the prime $`n-g`$ modulo $`Qd`$. Its expected contribution to
$`A`$ is
$`\varphi(Q)|J|/\varphi(Qd)=|J|/\varphi(d)`$.
The noncoprime terms vanish. Maximal Bombieri–Vinogradov gives an arbitrary
power of logarithmic saving in the sum of the unweighted progression
errors for $`Qd\le Qx^\gamma`$; translating $`J`$ by $`g`$ causes no loss.
One may pass from von Mangoldt weights to $`\vartheta`$ at cost
$`O(\sqrt x(\log x)^2)`$ per modulus; its sum is harmless for
$`\gamma\lt1/2`$.

For completeness, the divisor weight in (8) does not require a stronger
distribution theorem. Let $`E_d`$ be the maximal nonnegative progression
error. For fixed $`Q,g`$ and $`d\le x^\gamma`$,

```math
E_d\ll_{Q,g}\frac{x\log x}{d},
\qquad
\sum_{d\le x^\gamma}E_d\ll_{Q,g,T}x(\log x)^{-T}.
```

The first inequality follows by counting integers in the progression and
using $`d/\varphi(d)\ll\log(2d)`$. Cauchy–Schwarz yields

```math
\sum_{d\le x^\gamma}\tau(d)^{B_0}E_d
\le
\left(\sum E_d\right)^{1/2}
\left(\sum\tau(d)^{2B_0}E_d\right)^{1/2}.
```

The second factor is $`O_{Q,g,B_0}(x^{1/2}(\log x)^{c(B_0)})`$ by
the elementary harmonic divisor-moment bound. Taking $`T`$ large enough
gives the required saving. Finally, the weighted sum of the errors in
ER1 is $`O_{Q,g,B_0}(x^\gamma(\log x)^{c'(B_0)})`$, because
$`F_r(d)\le\tau(d)`$. This is smaller than every fixed logarithmic
multiple of $`x`$. $`\square`$

This proposition only repackages classical prime distribution with the
endpoint's correct local densities. It is not a new distribution theorem.
Corollary ER3u below tracks its uniformity for polylogarithmic $`Qg`$.

## 3. A parity companion preserving the covering progression

Let $`\lambda(n)=(-1)^{\Omega(n)}`$ be the Liouville function, with prime
factors counted with multiplicity. Define

```math
Z(n)=B(n)(1+\lambda(n)).
\qquad\text{(10)}
```

**Proposition ER3 (protected-progression parity model).** The sequence
$`Z`$ is nonnegative, has exactly the same congruence and coprimality
restrictions as $`B`$, and satisfies $`Z(p)=0`$ for every prime $`p`$.
For every fixed $`0\lt\gamma\lt1`$, $`A_0\gt0`$ and $`B_0\ge0`$,

```math
\mathcal T_{\gamma,B_0}(Z-B;x)
\ll_{Q,g,\gamma,A_0,B_0}x(\log x)^{-A_0}.
\qquad\text{(11)}
```

Consequently, fixing the covering progression and knowing all these
ordinary divisor estimates, even for every fixed exponent below $`1`$,
cannot force positive prime mass for an arbitrary nonnegative sequence.

**Proof.** Nonnegativity and vanishing at primes are immediate. It remains
to prove (11). We use the classical fixed-modulus cancellation bound

```math
\sum_{\substack{k\le t\\k\equiv c\pmod L}}\lambda(k)
\ll_{L,A} t(\log(2t))^{-A},\qquad(c,L)=1,
\qquad\text{(12)}
```

for each fixed $`L`$ and $`A\gt0`$. Here is its precise input and reduction.
The character-twisted Möbius estimate in [K, Exercise 12.1, printed
p. 127] gives the corresponding fixed-modulus bound for $`\mu`$ by
character orthogonality. Use

```math
\lambda(k)=\sum_{u^2v=k}\mu(v).
```

On a unit class modulo $`L`$, both $`u`$ and $`v`$ are units. Split at
$`u=t^{1/4}`$. In the first part the length $`t/u^2`$ is at least
$`\sqrt t`$, so the Möbius progression estimate gives
$`O_{L,A}(t(\log(2t))^{-A})`$ after summing $`u^{-2}`$.
The tail is $`O(t^{3/4})`$. This proves (12), uniformly over the finitely
many reduced classes. The dependence on $`L`$ is retained; no uniform
assertion over growing moduli is being made.

For $`(d,r)=1`$, the divisor sum of $`Z-B`$, after setting $`n=dm`$,
is

```math
CQF_r(d)\lambda(d)
\sum_{\substack{m\in J/d\\dm\equiv b\pmod Q\\(m,g)=1}}
       \lambda(m)F_{rd}(m).
\qquad\text{(13)}
```

There is an exact convolution identity

```math
\lambda(m)F_s(m)
  =\sum_{h\mid m}\mu(h)\rho_s(h)\lambda(m/h).
\qquad\text{(14)}
```

Both sides are multiplicative. At $`p^j`$ with $`p\nmid s`$ the right
side equals
$`(-1)^j-(p-2)^{-1}(-1)^{j-1}
 =(-1)^j(p-1)/(p-2)`$; at $`p\mid s`$ it is simply $`(-1)^j`$.
Moreover,

```math
\sum_{h\ge1}\frac{\rho_s(h)}{\sqrt h}
 \le\prod_{p\ge3}\left(1+\frac1{(p-2)\sqrt p}\right)
 \lt\infty,
\qquad\text{(15)}
```

uniformly in even $`s`$.

Let $`L=\operatorname{lcm}(Q,\operatorname{rad}(g))`$ and $`N=x/d`$.
The conditions in (13) are a union of at most $`L`$ unit residue classes
modulo this fixed $`L`$. If $`\rho_{rd}(h)\ne0`$, multiplication by $`h`$
permutes the unit classes. Insert (14) and split at $`h=\sqrt N`$.
For $`h\le\sqrt N`$, the inner interval is contained in
$`(N/(2h),N/h]`$, with endpoints at least $`\sqrt N/2`$.
Equation (12), applied to its two endpoints, bounds its sum by

```math
O_{Q,g,A}\left(\frac{N}{h(\log(2N))^A}\right).
```

Summing this bound against $`\rho_{rd}(h)`$ is harmless by (15).
For $`h\gt\sqrt N`$, trivial estimation and (15) give

```math
N\sum_{h\gt\sqrt N}\frac{\rho_{rd}(h)}h
\ll N^{3/4}.
```

Thus the inner sum in (13) is
$`O_{Q,g,A}(N(\log(2N))^{-A})`$, uniformly in $`d`$ and $`J`$.
Noncoprime $`d`$ contribute zero. Since $`d\le x^\gamma`$,
$`\log(2N)\gg_\gamma\log x`$, and therefore

```math
\mathcal T_{\gamma,B_0}(Z-B;x)
\ll_{Q,g,A,\gamma}x(\log x)^{-A}
    \sum_{d\le x^\gamma}\frac{\tau(d)^{B_0}F_r(d)}d.
```

The final sum is at most a fixed power of $`\log(2x)`$, since
$`F_r(d)\le\tau(d)`$. One direct verification is to replace
$`B_0+1`$ by a larger integer $`k`$ and bound the Euler product whose
local factor is
$`1+2^k/p+O_k(p^{-2})`$.
Increasing $`A`$ proves (11). $`\square`$

**Corollary ER3u (uniformity for polylogarithmic covers).** Fix
$`H\gt0`$, $`A_0\gt0`$, $`B_0\ge0`$ and $`0\lt\gamma\lt1`$.
Allow $`Q,g,a`$ to vary with $`x`$, subject to the same parity and unit
conditions and

```math
Qg\le(\log x)^H.
\qquad\text{(15u)}
```

Then (11) holds with an implied constant depending only on
$`H,\gamma,A_0,B_0`$. If $`\gamma\lt1/2`$, the same is true of (9).
These uniform logarithmic-saving statements are unconditional but
ineffective; no numerical starting point is asserted.

**Proof.** The elementary error constant in (3) can be bounded by
$`O(r^3)`$ times an absolute constant, where $`r=Qg`$. Indeed,
$`K(r)\le r/\varphi(r)\le r`$, $`CQ\le r^2`$, and the
inclusion-exclusion error in (6) is at most $`2^{\omega(g)}\le g\le r`$.
The Euler tails in (7) are uniform. Thus the total weighted error from
ER1 is at most $`r^3x^\gamma`$ times a fixed power of $`\log x`$.

For ER3, $`L=\operatorname{lcm}(Q,\operatorname{rad}(g))\le r`$.
The character-twisted estimate in [K, Exercise 12.1] is uniform for
moduli bounded by any fixed power of the logarithm. The square-divisor
argument proving (12) consequently gives, for each fixed $`H',A\gt0`$,

```math
\sum_{\substack{k\le t\\k\equiv c\pmod L}}\lambda(k)
 \ll_{H',A} t(\log(2t))^{-A}
 \quad\text{if }L\le(\log t)^{H'},\ (c,L)=1.
```

In the small-$`h`$ part of (14), the interval endpoints satisfy
$`t\ge\sqrt N/2\ge x^{(1-\gamma)/2}/2`$. Hence
$`L\le(\log x)^H\le(\log t)^{H+1}`$ for all sufficiently large
$`x`$, uniformly in the permitted parameters. Summing at most $`L`$
unit classes and multiplying by $`CQ`$ costs at most $`r^3`$.
This is a fixed logarithmic power under (15u), absorbed by taking the
input saving $`A`$ larger. The tail estimate from (15) remains uniform.

For ER2, the moduli $`Qd\le(\log x)^Hx^\gamma`$ stay below the
Bombieri–Vinogradov range for any fixed $`\gamma\lt1/2`$.
Multiplication by $`\varphi(Q)`$, removal of prime powers and the
elementary comparison error cost only fixed logarithmic factors or
$`x^{\gamma+1/2}`$ times such factors. The divisor-weight absorption
argument is unchanged. All are absorbed in the prescribed saving.
The ineffectivity of Siegel–Walfisz and Bombieri–Vinogradov is retained.
$`\square`$

### Scope of the countermodel

The actual sequence $`A`$ is supported where $`n-g`$ is prime;
$`Z`$ generally is not. ER3 is therefore not an arithmetic counterexample
to a prime-pair conjecture. It proves that these Type I statistics do not
encode enough information to exploit the first endpoint's primality and
force the second one. Additional structure of $`A`$ remains available to
a different argument.

The construction also respects a fixed finite family of protected
progressions. Apply ER3 to each member, multiply by a fixed nonnegative
coefficient and add. The resulting sequence is nonnegative and still
vanishes at primes, while the Type I error is bounded by the finite sum
of the errors. The family, coefficients, moduli and gaps must remain
fixed as $`x\to\infty`$. This says nothing about an unbounded family
with a proved new cancellation estimate.

No quasi-RH premise was used. Classical fixed-modulus cancellation is
sufficient. Possible exceptional Dirichlet characters are included in
the fixed-modulus constants in (12); the proof does not discard an
exceptional character or claim an effective uniform threshold.
Corollary ER3u uses the classical ineffective uniform theorem rather
than assuming exceptional characters are absent. It addresses growing
moduli only in (15u), and proves an obstruction there, not endpoint
primality. No larger uniform range is established in this manuscript.

The classical comparison is important: Selberg's sequence
$`1+\lambda(n)`$ already shows the basic Type I obstruction. Ford–Maynard
[FM, Section 1] records this example; their Theorem 2.1 is stronger in a
different direction. For every $`\gamma\lt1`$ there is a positive
$`\nu_0(\gamma)`$ such that their Type I and Type II conditions, with
Type II width $`\nu\le\nu_0(\gamma)`$, admit bounded nonnegative
sequences having zero prime mass. Their comparison is $`b_n=1`$ and
their theorem is not asserted here for our specific $`B`$. The present
calculation verifies the correct protected-class local factors rather
than claiming a new general parity obstruction.

## 4. Chen-type endpoint repair and its exact signed requirement

Assume a nonnegative weight $`w(n)`$ has been constructed with support
on $`n\equiv b\pmod Q`$, with $`n-g`$ prime and $`\Omega(n)\le2`$.
Since $`n\gt1`$, only $`\Omega(n)=1,2`$ can occur. The first condition
may include all interior-compositeness requirements of the fixed cover.
No theorem providing such a weight with any specified uniformity is
assumed here.

**Proposition ER4 (exact prime projection on a Chen support).** Put

```math
T=\sum_n w(n),\qquad L_w=\sum_n w(n)\lambda(n).
```

Then

```math
\sum_{n\in\mathbb P}w(n)=\frac{T-L_w}{2}.
\qquad\text{(16)}
```

In particular, a lower bound $`T\ge T_0\gt0`$ produces prime-pair mass
at least $`\epsilon T_0/2`$ if one additionally proves

```math
L_w\le(1-\epsilon)T
\quad\text{for some fixed }\epsilon\gt0.
\qquad\text{(17)}
```

**Proof.** On this support, $`(1-\lambda(n))/2`$ is exactly the prime
indicator. This includes prime squares correctly: they have
$`\Omega(n)=2`$ and $`\lambda(n)=1`$. Summation proves both assertions.
$`\square`$

This is an identity, not a new conditional prime theorem. It isolates
what a Chen-plus-sign strategy must actually estimate. Replacing
$`\lambda`$ with $`\mu`$ without first excluding prime squares would
change the identity.

The primary source [HL, Section 2, equations (2)–(3)] makes the remaining
semiprime contribution explicit. Their positive Chen functional is
bounded by contributions from three classes. After a negligible
squareful class is separated, one class contains both primes and
semiprimes whose two factors exceed $`x^{1/3}`$; the other contains
semiprimes with one smaller factor. Thus improving that positive total
alone does not distinguish the two possibilities inside the first
class. This observation concerns the actual weighted construction in
[HL], rather than only the wording of Chen's theorem.

A penalty depending only on divisibility by primes at most $`x^{1/3}`$
takes identical values on a prime and on a semiprime whose factors both
exceed $`x^{1/3}`$. Extending a roughness test to $`\sqrt x`$ would
distinguish them, but proving a positive count after that extension is
precisely the missing prime-detection step.

Nor does cancellation of $`\lambda`$ on a larger unweighted set imply
(17) on this support. Even in a finite measure space, all the selected
mass can lie on sign $`+1`$ while an unselected set balances the global
signs. A transfer must control the correlation with the actual Chen
weight. This finite-measure observation makes no assertion that such a
configuration occurs for the primes.

There is also no finite local admissibility obstruction to the competing
semiprime configuration. To check this, choose a prime $`q\nmid Qg`$
and $`c\pmod Q`$ with $`qc\equiv b\pmod Q`$. The two forms

```math
L_1(t)=Qt+c,\qquad L_2(t)=q(Qt+c)-g
\qquad\text{(18)}
```

are admissible. At a prime dividing $`Q`$ both are constant units; at
$`q`$, $`L_2\equiv-g\not\equiv0`$ and $`L_1`$ has one root. At any
other prime, there are at most two roots, and this prime is at least
$`3`$. Thus no prime divides the product for every $`t`$. If both forms
were prime for a sufficiently large $`t`$, then
$`n=qL_1(t)`$ would be a semiprime right endpoint, $`n-g=L_2(t)`$ would
be a prime left endpoint, and the original interior covering would
still hold. This verifies compatibility only; it does not assume or
prove simultaneous primality of (18).

## 5. Attempted bilinear repair: the new correlation after squaring

The explicit comparison $`B`$ makes it possible to state a genuine next
analytic input without confusing a prime progression estimate with it.
Let $`W=A-B`$. A Type II sum has the form

```math
\sum_{m\sim M}\sum_{n\sim N}\alpha_m\beta_nW(mn),
\qquad MN\asymp x,
\qquad\text{(19)}
```

with suitable interval restrictions and uniformly bounded or
divisor-bounded coefficients. ER2 evaluates the part where one divisor
is short and the other coefficient is an interval indicator. It does
not evaluate (19) for two independent arbitrary coefficient sequences.

Applying Cauchy–Schwarz and expanding the square brings in off-diagonal
terms containing

```math
\sum_{m\sim M}
    \vartheta(mn_1-g)\vartheta(mn_2-g),
\qquad n_1\ne n_2,
\qquad\text{(20)}
```

together with the fixed residue restrictions and the comparison terms.
The two potential prime values satisfy

```math
n_2p_1-n_1p_2=g(n_1-n_2),
\qquad p_i=mn_i-g.
\qquad\text{(21)}
```

For each fixed pair $`n_1,n_2`$, an error estimate for a single prime in
one arithmetic progression does not evaluate the product in (20).
An average over $`n_1,n_2`$ could conceivably supply cancellation; the
point is to identify the actual averaged two-prime obligation, not to
declare it impossible. A bound only for a special Möbius coefficient or
only for polylogarithmic cofactors is not the full Type II hypothesis
with arbitrary divisor-bounded coefficients in [FM].

The genuinely parity-sensitive alternatives left by this investigation
are therefore a one-sided bound for the signed remainder in
[signed-endpoint-transfer.md](signed-endpoint-transfer.md), the
localized Chen correlation (17), or sufficiently strong bilinear
information for the actual $`A-B`$. None is established here. The
covering size and admissibility are already solved inputs in this
workspace; improving them alone does not supply any of these endpoint
estimates.

## Sources and proof dependencies

- **[K]** D. Koukoulopoulos, *The Distribution of Prime Numbers*, Graduate
  Studies in Mathematics 203, AMS, 2019,
  DOI [10.1090/gsm/203](https://doi.org/10.1090/gsm/203). Inspected
  [author-hosted preliminary version](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf),
  367 PDF pages: Exercise 12.1, printed p. 127 (PDF page 138), supplies
  character-twisted Möbius cancellation; the surrounding discussion
  records the exceptional-character and ineffectivity issue. Its
  fixed-modulus consequence is used in ER3 and its polylogarithmic
  uniformity in ER3u. The reduction from Möbius to Liouville
  cancellation is proved above.
- **[FM]** K. Ford and J. Maynard, *On the theory of prime-producing
  sieves*, [arXiv:2407.14368](https://arxiv.org/abs/2407.14368), first
  submitted 19 July 2024. Inspected
  [author-hosted PDF](https://www.ford126.web.illinois.edu/wwwpapers/prime-producing-sieves.pdf),
  107 pages, printed date 16 July 2024: Section 1, conditions (I)–(II)
  and the Selberg example; Theorem 2.1, printed p. 3. This is a
  literature comparison, not a theorem applied to $`A`$ or $`B`$ here.
  The inspected author PDF is distinguished from an independently
  byte-verified arXiv version; the latter was not obtained in this pass.
- **[HL]** R. Heath-Brown and X. Li, *Almost prime triples and Chen's
  theorem*, inspected [arXiv:1504.00533v2](https://arxiv.org/pdf/1504.00533v2),
  5 October 2015, Section 2, equations (2)–(3) and the definitions of
  $`\mathcal A^{(0)},\mathcal A^{(1)},\mathcal A^{(2)}`$ on printed
  p. 2. Used to inspect the actual Chen functional and its surviving
  semiprime class, not as a uniform theorem for arbitrary covers.
- **Internal dependency.** The definition of $`K(Qg)`$ and the exact
  signed lower-bound obligation are canonical in
  [signed-endpoint-transfer.md](signed-endpoint-transfer.md). ER1–ER3
  use only elementary multiplicative identities, fixed-modulus prime
  and Möbius distribution, and Bombieri–Vinogradov. They use no
  unreviewed quasi-RH claim. ER4 is an elementary identity.

The exact scope of nonauthor mathematical review is recorded in
[Verification](VERIFICATION.md).
