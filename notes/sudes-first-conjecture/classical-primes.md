# Classical prime supplies for the explicit bound

This file supplies the numerical analytic inputs to the
[explicit-bound proof](explicit-bound.md). Its local arguments are complete
here; its imported results are the stated estimates of Rosser–Schoenfeld,
Bennett–Martin–O'Bryant–Rechnitzer (BMOR), and McCurley, with exact primary
source locators in [References](REFERENCES.md#classical-estimates-for-the-explicit-bound).
Their published computational inputs remain part of those imports.

Write $`\varphi`$ for Euler's totient function,
$`\theta(x;q,a)=\sum_{p\le x,\ p\equiv a\pmod q}\log p`$, and
$`\psi(x;q,a)=\sum_{m\le x,\ m\equiv a\pmod q}\Lambda(m)`$.
All logarithms in analytic estimates are natural. Decimal constants are
exact terminating decimals. The BMOR constant is $`R_1=9.645908801<10`$.
The conventional proof and review boundary are recorded in
[Provenance](PROVENANCE.md).

The Rosser–Schoenfeld bounds used below are $`\pi(x)>x/\log x`$ for
$`x\ge17`$, $`\pi(x)<1.25506x/\log x`$ for $`x>1`$, and
$`\pi(x)<(x/\log x)(1+3/(2\log x))`$ for $`x>1`$.

## Elementary size and mean bounds

The following estimates use RS62 only and have no progression-modulus
dependence. With $`X=p_{n^2+1}`$, one has $`X<n^3`$ for $`n\ge64`$:
$`\pi(n^3)>n^3/(3\log n)>2n^2`$, because $`n>6\log n`$ holds at 64
using $`\log64<6`$, and $`n-6\log n`$ increases thereafter.
The elementary bound $`X\ge n^2`$ holds for every positive $`n`$.

For $`X\ge2^{256}`$, put $`u=\log X\ge128`$, $`N=\pi(X)-1`$, and
$`I=\int_2^X\pi(t)\,dt`$. The exact identity for the odd-prime pool is



```math
T=XN+X-I-2.                                            \qquad\text{(M0.1)}
```



For $`t\ge X/16`$, RS62 (3.2) and $`\log16<4`$ give



```math
\pi(t)\le At,\qquad
 A=\frac{1+3/[2(u-4)]}{u-4},\qquad Au\le65/62.
```



For the remaining integral use $`\pi(t)\le\pi(X/16)\le AX/16`$.
Consequently $`I\le(257/512)AX^2`$. Also
$`N>X/u-1\ge(63/64)X/u`$, because $`u/X\le1/64`$; that last inequality
holds at $`2^{256}`$ using $`u<256`$ and persists since $`\log X/X`$ decreases.
It follows that



```math
\frac{I}{XN}\le\frac{257}{512}\frac{65}{62}\frac{64}{63}
 =\frac{16705}{31248}<\frac35.
```



On the other hand, RS62 (3.5) on $`[X/16,X]`$ gives
$`I\ge(255/512)X^2/u`$, while (3.2) gives
$`N\le(65/64)X/u`$. Since $`N\ge64`$, (M0.1) proves



```math
\frac25<\frac{m}{X}\le1+\frac1{64}-\frac{255}{520}<\frac35,
 \qquad m=T/N.                                         \qquad\text{(M0.2)}
```



The distinction between $`\pi(X)`$ and $`N=\pi(X)-1`$ is included in
(M0.1), rather than silently adding the prime 2 to the pool.

## E1. A numerical all-scale seed supply from consecutive primes

For integer $`X\ge2^{32}`$, put



```math
\ell=\lceil\log_2X\rceil,
 \qquad G=16\ell,
 \qquad Q=\left\lfloor\frac{X}{2048\ell^3}\right\rfloor.
```



**E1.** There are an even $`2\le g\le G`$, a reduced residue class
$`a\pmod g`$, and at least $`Q`$ vertex-disjoint pairs of primes
$`(p,p+g)`$, with all endpoints in $`[X/4,3X/4]`$ and all lower endpoints
congruent to $`a\pmod g`$. The selected gap and class may vary with $`X`$.

**Proof.** Write $`t=\log X`$. Since $`\log2>1/2`$, $`t\ge16`$.
The RS62 inequalities give



```math
M:=\pi(3X/4)-\pi(X/4)
 >\left(\frac34-\frac{125506}{100000}\frac27\right)\frac Xt
 =\frac{68497}{175000}\frac Xt
 >\frac{X}{4\ell}.                                      \qquad\text{(E1.1)}
```



Here $`\log4<2\le t/8`$, so
$`\log(X/4)\ge7t/8`$, while $`\log(3X/4)\le t`$ and $`t\le\ell`$.
List these primes increasingly and pair positions (1,2), then (3,4),
and so on. These pairs are disjoint before any pigeonhole step. Their gap
sum is at most $`X/2`$. Fewer than $`X/(32\ell)`$ of their gaps exceed
$`16\ell`$, so more than



```math
\frac{X}{8\ell}-1-\frac{X}{32\ell}
 =\frac{3X}{32\ell}-1
 \ge\frac{X}{16\ell}                                  \qquad\text{(E1.2)}
```



short pairs remain. The last inequality uses $`X\ge32\ell`$.
Their gaps are positive and even. All endpoints exceed $`16\ell`$, because
$`X>64\ell`$, hence each endpoint is coprime to its gap.
The number of possible pairs of labels $`(g,a\bmod g)`$ is at most



```math
\sum_{j=1}^{8\ell}2j=8\ell(8\ell+1)\le72\ell^2.
```



One label therefore has more than $`X/(1152\ell^3)`$ pairs, which implies
the claimed weaker integer bound. The inequalities $`X>64\ell`$ persist
through all larger $`X`$: on each dyadic band use $`X>2^{\ell-1}`$, and
$`2^{\ell-1}/\ell`$ is increasing for integer $`\ell\ge2`$. The endpoint
$`X=2^{32}`$ is checked directly. $`\square`$

The residue pigeonhole loss is paid explicitly, after the disjoint pairs
have already been selected.
For $`X=p_{n^2+1}`$, every endpoint is an odd prime at most $`X`$, hence lies
in the exact pool; E1 neither adds primes nor prescribes a new pool.

## E2. Retaining the exceptional term in explicit smoothing

Let $`q\ge10^5`$, $`(a,q)=1`$, and



```math
x\ge\exp(4R_1\log^2q),\qquad
 v=\sqrt{\log x/R_1},\quad H=e^v/q,\quad
 \delta=2/H,\quad h=\delta x.
```



There is at most one exceptional zero amongst the characters modulo $`q`$,
in the sense of BMOR Definition 6.1. If it exists, denote it by $`\beta`$
and its character by $`\chi_0`$; put



```math
M_{q,a}(x)=\frac{x-\chi_0(a)x^\beta/\beta}{\varphi(q)}.
```



If no such zero exists, omit that term and put $`M_{q,a}(x)=x/\varphi(q)`$.
The character is real, the zero is simple, and $`\beta\ge0.99`$ on this domain.

**E2.** On this domain,



```math
\left|\theta(x;q,a)-M_{q,a}(x)\right|
 \le 2xv e^{-v}+10qx e^{-v}
      +2\log q\log x+q\log q+2\sqrt{x}.                 \qquad\text{(E2.1)}
```



**Proof.** This is a refinement of
the absolute-value conclusion of BMOR Lemma 6.10, obtained by keeping one zero
term until after smoothing. The refinement is proved here; it is not quoted as
that lemma's statement.

Use the two positive averages



```math
A_h^\pm f(x)=h^{-2}\int_0^h\int_0^h
       f(x\pm u\pm w)\,du\,dw.
```



Monotonicity gives $`A_h^-\psi(x;q,a)\le\psi(x;q,a)\le
A_h^+\psi(x;q,a)`$, including prime-power endpoints. Since
$`H\ge q\ge10^5`$, both averaging intervals are contained in $`(2,2x)`$.
We first prove, with the required zero-set convention, the remainder bound



```math
E_0=\frac{\log q\log x}{\log2}+0.2516q\log q.          \qquad\text{(E2.2)}
```



For a character $`\chi\pmod q`$, let $`\chi^*`$ be its primitive inducing
character, of conductor $`q^*\mid q`$, and put
$`r_\chi=\#\{p:p\mid q,\ p\nmid q^*\}`$. Write
$`\psi(t,\chi)=\sum_{m\le t}\chi(m)\Lambda(m)`$. The exact identity



```math
\psi(t,\chi)=\psi(t,\chi^*)-J_\chi(t),\qquad
 J_\chi(t)=\sum_{\substack{p\mid q\\p\nmid q^*}}
       \sum_{p^j\le t}\chi^*(p)^j\log p
```



gives $`|J_\chi(t)|\le r_\chi\log t`$ for $`t\ge2`$. No zero on the
imaginary axis needs to be estimated after this replacement.

Here is the primitive averaged explicit formula used next. Let
$`\varepsilon_\chi=(1-\chi^*(-1))/2`$, let $`m_\chi`$ be the order of
$`L(s,\chi^*)`$ at zero, and let $`b_\chi`$ be the constant term in its
logarithmic derivative there. The nonspectral function for $`\chi^*`$ is



```math
f_{\chi^*}(t)=
 \sum_{j\ge1}\frac{t^{-(2j-\varepsilon_\chi)}}{2j-\varepsilon_\chi}
 -m_\chi\log t-b_\chi.                                  \qquad\text{(E2.2b)}
```



MCC84 Lemmas 3.1--3.2 give this formula after averaging, by the same
characterwise Perron residue calculation used in their proofs. In particular,
(3.4)--(3.5) give the coefficient $`-m_\chi`$ of $`\log t`$ and the
constant $`-b_\chi`$ in (3.10). The poles at the negative integers give
the displayed absolutely convergent trivial-zero series. The primitive
principal character has $`L=\zeta`$, $`m_\chi=0`$, and
$`b_\chi=\log(2\pi)`$; it contributes the pole at one. For every other
primitive character, $`m_\chi`$ is one for even parity and zero for odd
parity. Its nonzero zeros in $`\Re s\ge0`$ are exactly those with
$`0<\Re s<1`$. Thus this primitive use of MCC84's identity involves exactly
BMOR's set $`Z(\chi^*)=Z(\chi)`$, with multiplicities. Two integrations
give absolute convergence of the spectral series. Ordinary versus half-weight
values at prime-power endpoints do not change any of the averages.

We bound $`b_\chi`$ with the ambient modulus $`q`$, even when $`q^*<10^5`$.
For a nonprincipal primitive character, the primitive form of BMOR (6.14)
omits the term $`q\log q/4`$. The full-zero bound (6.16) applies to the
induced character modulo $`q`$, whose critical-strip zeros are the same, so



```math
|b_\chi|<B(q):=
 \frac{\sqrt q\log^2q}{40}+3.4596\log^2q+15.01\log q+19.126
 <0.01q\log q.                                          \qquad\text{(E2.2c)}
```



For the first inequality we used
$`|\zeta'(2)/\zeta(2)|<2`$; indeed
$`\sum_{m\ge2}\Lambda(m)/m^2\le\sum_{m\ge2}\log m/m^2
\le\int_1^\infty\log(t+1)t^{-2}\,dt=2\log2<2`$.
For the second inequality divide by $`q\log q`$. All four resulting
positive terms decrease for $`q\ge10^5`$. At $`q=10^5`$, use
$`10<\log(10^5)<12`$ and $`\sqrt{10^5}>300`$ to bound their sum by



```math
\frac{12}{40\cdot300}
 +\frac{3.4596\cdot12}{10^5}
 +\frac{15.01}{10^5}
 +\frac{19.126}{10^6}<\frac1{100}.
```



The logarithm bounds follow, for example, from
$`e<3`$, $`e>8/3`$, $`3^{10}<10^5`$, and $`8^{12}>10^5\,3^{12}`$.
For the primitive principal character, the separate bound
$`|b_\chi|=\log(2\pi)<3<0.01q\log q`$ suffices.

For $`t\ge2`$, the trivial series in (E2.2b) is less than
$`\sum_{j\ge1}t^{-j}/j<1`$. Moreover



```math
m_\chi+r_\chi\le\omega(q).
```



For a nonprincipal inducing character this follows from
$`m_\chi\le1\le\omega(q^*)`$ and
$`r_\chi=\omega(q)-\omega(q^*)`$; for the principal inducing character
$`q^*=1`$ and $`m_\chi=0`$. It follows that on either averaging interval



```math
\begin{aligned}
 |f_{\chi^*}(t)-J_\chi(t)|
 &\le\omega(q)\log(2x)+0.01q\log q+1\\
 &\le\frac{\log q\log x}{\log2}+0.01002q\log q
 <E_0.                                                   \qquad\text{(E2.2d)}
 \end{aligned}
```



The last step uses $`\omega(q)\le\log q/\log2`$ and
$`\log q+1\le2\log q\le0.00002q\log q`$ for $`q\ge10^5`$.

Averaging the primitive identities over the $`\varphi(q)`$ characters,
with the usual coefficients $`\overline\chi(a)`$, now proves



```math
A_h^\pm\psi(x;q,a)
 =\frac{x\pm h}{\varphi(q)}
  -\frac1{\varphi(q)}\sum_{\chi\bmod q}\overline\chi(a)
       \sum_{\rho\in Z(\chi)} A_h^\pm(x^\rho/\rho)
  +R_\pm,\qquad |R_\pm|\le E_0.                         \qquad\text{(E2.2a)}
```



Here $`R_\pm=\varphi(q)^{-1}\sum_\chi\overline\chi(a)
A_h^\pm(f_{\chi^*}-J_\chi)(x)`$. Bound (E2.2d) proves its stated size,
without importing a remainder with a different spectral normalization.
Separate the single term with $`\rho=\beta`$ from this series and retain its
exact sign through smoothing.

For each remaining low zero, concavity of $`t^{\Re\rho}`$, with
$`0<\Re\rho<1`$, gives



```math
|A_h^\pm(x^\rho/\rho)|
 \le(1+\delta)x^{\Re\rho}/|\rho|.
```



For the high zeros the second finite difference of
$`x^{\rho+2}/[\rho(\rho+1)(\rho+2)]`$ gives BMOR's factor



```math
A_2(\delta)=4/\delta^2+12/\delta+18+10\delta
            =H^2+6H+18+20/H.
```



The lower average has a no-larger numerator. BMOR Lemmas 6.8 and 6.9 bound
the two sums, per character, by $`0.5001ve^{-v}`$ and
$`0.511ve^{-v}H^{-2}`$, respectively, after dividing by $`x`$. Thus, after
averaging over the characters, their total contribution is at most



```math
xve^{-v}\bigl(0.5001(1+2/H)+
    0.511(1+6/H+18/H^2+20/H^3)\bigr)
 <2xve^{-v},                                             \qquad\text{(E2.3)}
```



since $`H\ge q\ge10^5`$. The zero $`1-\beta`$, when present, is included
in the remaining low-zero estimate, just as in Lemma 6.8.

The principal main term changes by exactly $`h/\varphi(q)`$ under either
average. On $`[x-2h,x+2h]\subset(2,\infty)`$, the derivative of
$`t^\beta/\beta`$ is $`t^{\beta-1}\le1`$. Its average therefore differs
from its central value by at most (2h), and in particular by at most (4h).
The combined allowance $`5h/\varphi(q)`$ is consequently valid. This is
$`10qx e^{-v}/\varphi(q)\le10qx e^{-v}`$.

Combining the two monotonic brackets proves the corresponding $`\psi`$
estimate with error $`2xve^{-v}+10qx e^{-v}+E_0`$. The source domain implies
$`x>10^{500}`$; BMOR Lemma 6.11 bounds the proper-prime-power contribution
by $`1.001\sqrt{x}<2\sqrt{x}`$. Finally $`\log2>1/2`$ and
$`0.2516<1`$ give (E2.1). This removes prime powers rather than treating
positive von Mangoldt weight as a primality certificate. $`\square`$

## S40 parameters

All logarithms without a subscript are natural. Fix the exact integer



```math
Y_* = 2^{\,2^{40}},\qquad U=2^{39}.                       \qquad\text{(S40.1)}
```



The weak parameters are exactly $`A=3,C=5`$. The strong parameters in BMOR
Proposition 6.16 are exactly



```math
Z_{\rm src}=8,\qquad \kappa_1=1,
 \qquad \kappa_2=\kappa_3=2^{20}.                         \qquad\text{(S40.2)}
```



## S40. Common domain inequalities

Let $`Y\ge Y_*`$, put $`u=\log Y`$, and let $`x`$ range through $`[Y/2,2Y]`$.
The elementary expansion



```math
\log2=2\sum_{j\ge0}\frac{3^{-(2j+1)}}{2j+1}
```



gives $`\log 2>2/3`$. Bounding the denominators in the tail by 3 gives



```math
\log2<\frac23+\frac1{36}=\frac{25}{36}<\frac7{10}.
```



Consequently



```math
u>U,\qquad
 \log x\ge(2^{40}-1)\log2
 >\frac23(2^{40}-1)>U,\qquad
 u/2\le\log x\le2u.                                    \qquad\text{(S40.3)}
```



These hold throughout the whole $`Y`$-tail. The stronger middle inequality
is needed for the strong estimate; merely assuming $`u\ge U`$ would not give
$`\log (Y/2)\ge U`$.

The weak argument needs



```math
u\ge720(\log u)^2,\qquad 3\log u\le u.                 \qquad\text{(S40.4)}
```



At $`u=U`$, the first follows from
$`2^{39}>720\cdot 39^2`$, because $`\log U<39`$. It persists since
$`u/(\log u)^2`$ increases for $`\log u>2`$. The second follows at $`U`$ from
$`2^{39}>3\cdot 39`$ and persists since the derivative of $`u-3\log u`$ is positive
for $`u>3`$. All of these initial comparisons are exact integer inequalities.

## S40-W. The weak progression interface

**S40-W.** Let $`Y\ge Y_*`$, $`u=\log Y`$, $`1\le q\le u^3`$, and $`\gcd(a,q)=1`$.
Every interval $`(b,c]`$ contained in $`[Y/2,2Y]`$, of length
$`H=c-b\ge Y/u^5`$, contains at least



```math
\frac{H}{2\varphi(q)u^6\log(2Y)}                       \qquad\text{(S40.5)}
```



primes in the class $`a\pmod q`$. The estimate is uniform in every such
modulus, residue, interval, and real scale $`Y`$.

**Proof.** Lift $`q<10^5`$ to $`Q=q\cdot 2^j`$ with
$`10^5\le Q<2\cdot 10^5`$; otherwise set $`Q=q`$. In either case $`Q\le u^3`$, and
the primes in the original class and interval partition into
$`d=\varphi(Q)/\varphi(q)\le 2\cdot 10^5`$ reduced classes modulo $`Q`$. The possible prime
2 is outside the interval. For every endpoint $`x`$, (S40.4) gives



```math
\log x\ge u/2\ge40\cdot9(\log u)^2
 \ge4R_1(\log Q)^2,
```



so E2 applies, with $`R_1=9.645908801<10`$.

For each reduced class modulo $`Q`$, retain the possible exceptional term
in E2's function $`M`$. BMOR Proposition 1.11 gives



```math
1-\beta\ge\frac{40}{\sqrt Q(\log Q)^2}
 \ge\frac{40}{Q^{3/2}}.
```



The last inequality uses $`(\log Q)^2<Q`$ for $`Q\ge 10^5`$: the quotient
decreases beyond $`e^2`$, and at $`10^5`$ it is bounded by $`12^2/10^5<1`$.
At every $`t`$ in the interval,



```math
(1-\beta)\log t\ge20u^{-7/2}\ge2u^{-6}.
```



Since $`1-\exp(-z)\ge \min(z/2,1/2)`$ for $`z\ge 0`$, and $`u^6\ge 2`$, the
unfavorable exceptional sign still leaves



```math
M'_{Q,a}(t)\ge\frac{u^{-6}}{\varphi(Q)}.                \qquad\text{(S40.6)}
```



The absent-exceptional-zero case and the other sign have a larger derivative.

We bound the E2 error directly at the stated starting point.
For $`x`$ in $`[Y/2,2Y]`$, write $`v=\sqrt{\log x/R_1}`$. Then
$`\sqrt u/8\le v\le 2u`$, $`Q\le u^3`$, and $`\log Q\le u`$, using (S40.3)--(S40.4).
The E2 error is therefore at most



```math
E(Y)=28Yu^4e^{-\sqrt u/8}+12u^5+3\sqrt Y.               \qquad\text{(S40.7)}
```



Indeed its exponential terms are at most
$`(8Yu+20Yu^3)\exp(-\sqrt u/8)\le 28Yu^4\exp(-\sqrt u/8)`$, its
polynomial terms are at most $`4u^2+u^4\le 12u^5`$, and
$`2\sqrt{2Y}<3\sqrt Y`$.

The two endpoint errors summed over the lifted classes are at most
$`4\cdot 10^5 E(Y)`$. They are less than $`Y/(2u^{14})`$, and hence less than
$`H/(2\varphi(q)u^6)`$, provided



```math
22400000u^{18}e^{-\sqrt u/8}
 +9600000u^{19}e^{-u}
 +2400000u^{14}e^{-u/2}<1.                              \qquad\text{(S40.8)}
```



Each summand is less than $`1/4`$ at $`u=U=2^{39}`$. Use $`e>2`$, the
coefficient bounds $`22400000<2^{25}`$, $`9600000<2^{24}`$, and
$`2400000<2^{22}`$, and the exact comparisons



```math
2^{16}>25+39\cdot18+2,\qquad
 2^{39}>24+39\cdot19+2,\qquad
 2^{38}>22+39\cdot14+2.                                \qquad\text{(S40.9)}
```



The first uses $`\sqrt U/8>2^{16}`$; the other two use $`U`$ and $`U/2`$.
The summands continue to decrease: their logarithmic derivatives are
negative respectively when $`\sqrt u>16\cdot 18`$, $`u>19`$, and $`u>2\cdot 14`$.
All three hold at $`U`$ and thereafter. Thus (S40.8) holds on the entire
tail, with the strict margin $`3/4<1`$.

Summing (S40.6) over the lifted classes gives the weighted main increment
$`H/(\varphi(q)u^6)`$. Subtracting the errors leaves at least half. Dividing
by the maximum prime weight $`\log (2Y)`$ proves (S40.5). The estimate concerns
$`\theta`$, so proper prime powers have already been removed in E2. $`\square`$

## S40-S. The strong progression interface

**S40-S.** Let $`Y\ge Y_*`$, $`u=\log Y`$, and
$`1\le q\le 32\lceil\log_2Y\rceil`$. Every reduced class modulo $`q`$ contains at least



```math
\frac{H}{2\varphi(q)\log(2Y)}                          \qquad\text{(S40.10)}
```



primes in every interval $`(b,c]`$ contained in $`[Y/2,2Y]`$ of length
$`H\ge Y/u^5`$.

**Proof.** First prove the following endpoint estimate for every
$`t=\log x\ge U`$ and $`10^5\le Q\le 256t`$:



```math
\left|\theta(x;Q,a)-\frac{x}{\varphi(Q)}\right|
 \le\frac{x}{4(\log x)^8}.                             \qquad\text{(S40.11)}
```



Use the exact parameters (S40.2) in BMOR Proposition 6.16. Its three
conditions (6.23) hold by the strict rational lower bounds



```math
\frac{460.516}{13.087}>\frac{460}{14}>8,
```




```math
\frac{\sqrt{2^{20}/R_1}-0.85317}{\log(2^{20})}-\frac12
 >\frac{255}{20}-\frac12>8,
 \qquad
 \frac{2^{20}-6.44}{2\log(2^{20})}
 >\frac{2^{20}-7}{40}>8.                               \qquad\text{(S40.12)}
```



Here $`R_1<16`$ gives $`\sqrt{2^{20}/R_1}>256`$, and $`\log 2<1`$ bounds the
denominators. The remaining source hypothesis is



```math
t\ge\max\{\sqrt Q(\log Q)^3,2^{20}\}.                 \qquad\text{(S40.13)}
```



Since $`Q\le 256t`$, it is enough to show



```math
\sqrt t\ge16(\log256+\log t)^3.                        \qquad\text{(S40.14)}
```



At $`t=U=2^{39}`$, use $`\sqrt2>7/5`$ and $`\log 2<7/10`$. The exact starting
comparison is



```math
2^{19}\frac75>16\left(\frac{329}{10}\right)^3,
 \qquad 329/10=47\cdot7/10.                            \qquad\text{(S40.15)}
```



For the full tail, $`\sqrt t/(\log 256+\log t)^3`$ has positive derivative
when $`\log 256+\log t>6`$; at $`U`$ this quantity is $`47\log 2>94/3>6`$.
Also $`U>2^{20}`$. Thus (S40.13) holds for all these endpoints and moduli,
and the source theorem proves (S40.11).

Return to the required modulus $`q`$. The bound on $`\log 2`$ gives
$`\lceil\log_2Y\rceil\le 2u`$ and so $`q\le 64u\le 128\log x`$ at both endpoints.
For $`q<10^5`$, lift to $`10^5\le Q<2\cdot 10^5`$ as above. The lifted modulus
also satisfies $`Q\le 256\log x`$, because $`\log x\ge U>2\cdot 10^5`$.
The number of lifted classes is at most $`2\cdot 10^5\le \log x`$. Thus the
summed endpoint error from (S40.11) is at most $`x/(4(\log x)^7)`$.
For unlifted moduli that weaker estimate is immediate. The prime 2, if
present in an odd-modulus class, cancels between the two endpoints; no
incorrect equality of the individual small-modulus $`\theta`$ functions is
asserted.

The total error in the interval increment is consequently at most



```math
2^7Y/u^7.
```



Relative to its main term $`H/\varphi(q)`$, this is at most
$`64\cdot 2^7/u<1/2`$, since $`u\ge U>2^{14}`$. The resulting $`\theta`$ increment
is at least $`H/(2\varphi(q))`$; division by $`\log (2Y)`$ gives (S40.10).
The endpoint and monotonicity arguments cover every larger real scale.
$`\square`$
