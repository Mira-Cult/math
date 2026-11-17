# Rough endpoints and quantitative marking removal

**Mira Cult**

For the actual prime measure in a protected progression, the calibrated
small-divisor main term concentrates on endpoints avoiding a subpower band
of auxiliary primes. We prove this localization and a lower bound for the
unsigned error budget of removing any divisor marker that vanishes on the
empty divisibility pattern. The latter retains the squarefree Möbius
divisors and the cofactor logarithm.

These results rule out an absolute-error route to marking removal. They do
not lower-bound the signed removal error; its cancellation remains possible
and unproved. Fixed-parameter results use classical distribution. Growing
moduli are treated only under the explicit progression hypothesis below.
No historical priority is asserted.

## 1. Actual arithmetic mass of the unmarked sector

Use $`Q,g,a,\vartheta,S_{Q,a,g},K(Qg),\kappa(Q,g)`$ from
[Section 1 of the companion manuscript](signed-endpoint-transfer.md#1-a-calibrated-endpoint-decomposition).
Thus $`Q,g`$ are positive even integers, $`(a(a+g),Q)=1`$, $`X\gt g`$,
$`\vartheta(n)=\mathbf1_{\mathbb P}(n)\log n`$, and
$`\kappa(Q,g)=K(Qg)/\varphi(Q)`$. Unless explicitly stated otherwise,
$`Q,g,a`$ are fixed as $`X\to\infty`$.

Write $`L=\log X`$ and fix

```math
0\lt \alpha\lt \beta\lt 1,\quad \lambda\gt 0,\quad
z_0=\exp(L^\alpha),\quad z_1=\exp(\lambda L^\beta).
```

Let $`\mathcal P=\{p:z_0\lt p\le z_1,\ p\nmid Qg\}`$, and define

```math
W=\prod_{p\in\mathcal P}p,\quad U(N)=\mathbf1_{(N,W)=1},\quad
H=\sum_{p\in\mathcal P}\frac1{p-1},\quad
V=\prod_{p\in\mathcal P}\left(1-\frac1{p-1}\right).
\qquad\text{(1)}
```

The enormous product $`W`$ is never assumed to be $`X^{o(1)}`$.
Only products of $`O(\log L)`$ selected auxiliary primes become moduli.
Mertens' theorem gives

```math
H=(\beta-\alpha)\log L+\log\lambda+o(1),\qquad
V=(\lambda^{-1}+o(1))L^{\alpha-\beta}.
\qquad\text{(2)}
```

Use the actual prime measure

```math
\nu_X(n)=
\frac{\vartheta(n)\mathbf1_{X\lt n\le2X,\ n\equiv a\pmod Q}}{\Theta(X)},
\qquad
\Theta(X)=\sum_{\substack{X\lt n\le2X\\n\equiv a\pmod Q}}\vartheta(n).
\qquad\text{(3)}
```

### Proposition 1: arithmetic density

For every fixed $`A\gt 0`$,

```math
\Theta_U(X):=\sum_{\substack{X\lt n\le2X\\n\equiv a\pmod Q}}
             \vartheta(n)U(n+g)
=\frac X{\varphi(Q)}V+O_{A,Q,g}(XL^{-A}).
\qquad\text{(4)}
```

Consequently $`v_X:=\mathbb E_{\nu_X}U(n+g)=V+O_{A,Q,g}(L^{-A})`$.

**Proof.** Write $`\omega(N)=\#\{p\in\mathcal P:p\mid N\}`$ and
$`B_k(\omega)=\sum_{j=0}^k(-1)^j\binom{\omega}{j}`$. The exact identity
$`B_k(\omega)=(-1)^k\binom{\omega-1}{k}`$ for $`\omega\gt 0`$ implies

```math
|\mathbf1_{\omega=0}-B_k(\omega)|\le\binom{\omega}{k+1}.
\qquad\text{(5)}
```

Choose $`k=\lceil C_A\log L\rceil`$ sufficiently large. Since
$`H=O(\log L)`$, the quantity

```math
\frac{H^{k+1}}{(k+1)!}
\le\left(\frac{eH}{k+1}\right)^{k+1}
\qquad\text{(6)}
```

is smaller than any prescribed fixed power of $`L^{-1}`$, by increasing
$`C_A`$. Every squarefree $`r\mid W`$ with $`\omega(r)\le k+1`$ satisfies

```math
r\le z_1^{k+1}=\exp(O_A(L^\beta\log L))=X^{o(1)}.
\qquad\text{(7)}
```

The conditions $`r\mid n+g`$ and $`n\equiv a\pmod Q`$ specify one reduced
class modulo $`Qr`$. Bombieri--Vinogradov evaluates all terms of the
expansion and its positive remainder, using each modulus once.
The main term is the truncated product for $`V`$; its error is bounded
by (6). This proves (4). The same estimate without $`U`$ evaluates
$`\Theta(X)`$. $`\square`$

Ford's stronger shifted-prime model includes this basic density
phenomenon; see Section 8. The direct proof supplies the arithmetic
measure and modulus accounting needed for the weighted application.

## 2. Overlapping and nonlinear marking: the exact optimum

Let $`Z`$ be any complex marker on the primes in (3), allowing overlapping
prime sets, signed coefficients and nonlinear functions of divisibility.
Suppose

```math
Z(n)=0\text{ when }U(n+g)=1,\qquad \mathbb E_{\nu_X}Z=1.
\qquad\text{(8)}
```

### Proposition 2: optimal support bound

Every such marker satisfies

```math
\mathbb E_{\nu_X}|1-Z|^2\ge\frac{v_X}{1-v_X},
\qquad
\mathbb E_{\nu_X}|1-Z|\ge2v_X.
\qquad\text{(9)}
```

Both bounds are attained by the normalized union marker

```math
Z_{\rm union}=\frac{1-U(n+g)}{1-v_X}.
\qquad\text{(10)}
```

Without normalization, the optimal squared and absolute errors both
equal $`v_X`$, attained by $`Z=1-U`$.

**Proof.** Cauchy gives
$`1=|\mathbb E[Z(1-U)]|^2\le(1-v_X)\mathbb E|Z|^2`$.
Subtract 1 to obtain the squared bound. On $`U=1`$ the absolute defect
has mass $`v_X`$; on its complement the integral of $`Z-1`$ equals $`v_X`$,
giving the second bound. Direct substitution proves the remaining
assertions. $`\square`$

The full band containing the Lü--Wang--Wu supplies has
$`\alpha=1/10`$, $`\beta=1/5`$, $`\lambda=2`$.
Its optimum squared error is $`(1/2+o(1))L^{-1/10}`$.
Thus nonlinear or correlated marking can improve the previous
$`1/\log L`$ disjoint-block variance floor. It still cannot give
arbitrary logarithmic precision while vanishing on this set.

The exact formula

```math
\mathbf1_{\omega\gt 0}
=\int_0^1\omega\rho^{\omega-1}\,d\rho
\qquad\text{(11)}
```

connects the union marker to the source's damped marks. It does not
supply the source's analytic estimate uniformly as $`\rho\to1`$ or for
one broad prime band. Those uniformities and the integral of the
constants remain unpaid.

## 3. Calibration with an enormous excluded prime product

For even $`r`$, write

```math
A_r(y)=\sum_{\substack{d\le y\\(d,r)=1}}\frac{\mu(d)}{\varphi(d)},
\qquad
B_r(y)=\sum_{\substack{d\le y\\(d,r)=1}}
                  \frac{\mu(d)}{\varphi(d)}\log\frac yd.
```

The companion manuscript factors their series as

```math
\sum_{\substack{d\ge1\\(d,r)=1}}
  \frac{\mu(d)}{\varphi(d)d^s}
=\frac{H_r(s)}{\zeta(1+s)},\qquad
h_r(p^j)=
\begin{cases}
p^{-j},&p\mid r,\\
-p^{-j}/(p-1),&p\nmid r.
\end{cases}
\qquad\text{(12)}
```

Here $`h_r`$ are the coefficients of $`H_r`$.

### Lemma 3: uniform depletion estimate

Put $`\eta=1/\log z_1`$, and let $`r=r_0W`$. For fixed $`r_0=Qg`$,

```math
\mathcal H_r:=\sum_{m\ge1}|h_r(m)|m^\eta\ll_{r_0}V^{-1}.
\qquad\text{(13)}
```

Uniformly for even $`r_0\le X^{C_0}`$, with its prime divisors excluded
from $`\mathcal P`$, one has instead

```math
\mathcal H_{r_0W}\ll_{C_0}V^{-1}\log L.
\qquad\text{(14)}
```

For every fixed $`B\gt 2`$ and $`u\ge2`$,

```math
\begin{aligned}
|A_r(u)|&\ll_B\mathcal H_r
 \bigl((\log(2u))^{-B}+u^{-\eta/2}\bigr),\\
|B_r(u)-K(r)|&\ll_B\mathcal H_r
 \bigl((\log u)^{1-B}+\eta^{-1}u^{-\eta/2}\bigr).
\end{aligned}
\qquad\text{(15)}
```

**Proof.** The local factors outside $`r`$ are absolutely convergent
and uniformly bounded for $`\eta\le1/4`$.
For primes in $`W`$, compare
$`\prod(1-p^{-1+\eta})^{-1}`$ with $`\prod(1-p^{-1})^{-1}`$.
The logarithmic ratio is $`O(1)`$: its first-power terms are bounded by
$`O(\eta\sum_{p\le z_1}(\log p)/p)=O(1)`$, and the higher-power terms
have bounded sum. The second product is $`\asymp V^{-1}`$, because
its logarithmic difference from $`V^{-1}`$ is
$`O(\sum_{p\gt z_0}p^{-2})`$.

For (14), the factors with $`p\mid r_0`$, $`p\le L^2`$, have product
$`O(\log L)`$ by Mertens and the same comparison. There are
$`O_{C_0}(L/\log L)`$ prime divisors of $`r_0`$ above $`L^2`$, and their
total $`p^{-1+\eta}`$ is $`O_{C_0}(L^{-1+o(1)}/\log L)`$. Their product
is bounded. This proves (13)--(14).

The classical zero-free region gives, for every fixed $`B`$,
$`\sum_{m\le y}\mu(m)/m=O_B((\log(2y))^{-B})`$, with a globally
bounded left side. Convolving (12) and splitting the $`h_r`$-sum at
$`\sqrt u`$ proves the first line of (15).
The identity $`B_r(u)=\int_1^u A_r(t)\,dt/t`$ proves convergence.
For each finite $`r`$, letting $`s\downarrow0`$ in (12) identifies the
limit as $`H_r(0)=K(r)`$. Integrating the bound for $`A_r`$ from $`u`$
to infinity gives the second line, with $`2/\eta`$ in the power tail.
$`\square`$

For $`u\ge X^\delta`$, this tail is a polynomial in $`L`$ times
$`\exp(-c_\delta L^{1-\beta})`$, smaller than every fixed power of
$`L^{-1}`$. No factor $`(QgW)^\epsilon`$ has been hidden.

## 4. Full main-term localization

Define the exact polynomials

```math
t_D(N)=\sum_{\substack{d\mid N\\d\le D}}\mu(d)\log(N/d),
\quad
r_D(N)=\sum_{\substack{d\mid N\\d\gt D}}\mu(d)\log(N/d),
\quad \Lambda(N)=t_D(N)+r_D(N).
\qquad\text{(16)}
```

Choose a fixed $`\gamma`$ with $`\beta\lt \gamma\lt 1`$ and take

```math
D=\left\lfloor\frac{\sqrt X}{Q}e^{-L^\gamma}\right\rfloor.
\qquad\text{(17)}
```

For fixed $`Q`$, $`D=X^{1/2+o(1)}`$. With $`k=O_A(\log L)`$,
$`QD z_1^{k+1}\le\sqrt X e^{-L^\gamma/2}`$ for large $`X`$.

### Theorem 4: localization on actual primes

For every fixed $`A\gt 0`$,

```math
\begin{aligned}
T_D^U &:=
 \sum_{\substack{X\lt n\le2X\\n\equiv a\pmod Q}}
 \vartheta(n)U(n+g)t_D(n+g)
 =\kappa(Q,g)X+O_{A,Q,g}(XL^{-A}),\\
T_D^{1-U}&=O_{A,Q,g}(XL^{-A}),\\
R_D^{1-U}&:=
 \sum_{\substack{X\lt n\le2X\\n\equiv a\pmod Q}}
 \vartheta(n)(1-U(n+g))r_D(n+g)
 =O_{A,Q,g}(XL^{-A}).
\end{aligned}
\qquad\text{(18)}
```

Thus $`R_D=R_D^U+O_{A,Q,g}(XL^{-A})`$.

**Proof: paying the signed Bonferroni remainder.**
On $`U(N)=1`$ every divisor of $`N`$ is coprime to $`W`$, so replace
$`t_D`$ there by

```math
t_D^0(N)=
\sum_{\substack{d\mid N\\d\le D\\(d,W)=1}}\mu(d)\log(N/d).
```

Positive Bonferroni inequalities cannot be applied directly to this
signed polynomial. Instead use (5) and

```math
|t_D^0(N)|\le\log(3X)
  \sum_{\substack{d\mid N\\d\le D\\(d,W)=1}}|\mu(d)|.
\qquad\text{(19)}
```

The positive remainder has moduli $`Qdr`$, where $`d`$ is coprime to
$`W`$ and $`r\mid W`$, $`\omega(r)=k+1`$.
The integer $`dr`$ determines $`d,r`$ uniquely. On prime support
$`(dr,Qg)=1`$, so each gives one reduced class.
Bombieri--Vinogradov sums each modulus once, and an extra factor
$`O(L)`$ pays (19). The positive main part is at most

```math
\frac{X\log(3X)}{\varphi(Q)}
 \sum_{d\le D}\frac1{\varphi(d)}
 \frac{H^{k+1}}{(k+1)!}
\ll_Q XL^2\frac{H^{k+1}}{(k+1)!}.
\qquad\text{(20)}
```

Here $`\sum_{d\le y}1/\varphi(d)\ll\log(2y)`$ follows by expanding
$`1/\varphi(d)=d^{-1}\sum_{e\mid d}\mu^2(e)/\varphi(e)`$.
Choose $`k=C_A\log L`$ large enough to pay (20).

**Proof: paying the uniform coefficient.**
The truncated expansion has main term

```math
\frac1{\varphi(Q)}\int_X^{2X}
 \left(\sum_{\substack{d\le D\\(d,QgW)=1}}
 \frac{\mu(d)}{\varphi(d)}\log\frac{t+g}{d}\right)dt
 \left(\sum_{\substack{r\mid W\\\omega(r)\le k}}
                  \frac{\mu(r)}{\varphi(r)}\right).
\qquad\text{(21)}
```

The second factor is $`V`$ with arbitrarily small logarithmic error.
Lemma 3 gives, uniformly for $`t\in[X,2X]`$,

```math
\log\frac{t+g}{D}A_{QgW}(D)+B_{QgW}(D)
=K(QgW)+O_{A,Q,g}(V^{-1}L^{-A}),
\qquad\text{(22)}
```

after increasing the precision parameter in (15). Adjoining
$`p\in\mathcal P`$ multiplies $`K`$ by $`(p-1)/(p-2)`$, so

```math
V K(QgW)=K(Qg)
\qquad\text{(23)}
```

exactly. This proves the first line of (18). The same calibration
without $`W`$ works at cutoff (17); subtraction proves the second line.

If $`(N,W)\gt 1`$, $`\Lambda(N)=0`$ unless $`N`$ is a proper prime power:
a prime $`N\in(X,3X]`$ cannot belong to $`W`$, whose primes are $`X^{o(1)}`$.
Proper prime powers contribute $`O(\sqrt X L^3)`$ to the weighted sum.
Apply (16) on this sector to obtain the last line of (18).
$`\square`$

The localization of $`R_D`$ is signed; it is not a bound for
$`\sum\vartheta\,|r_D|`$. At a prime endpoint $`N\gt D`$, its only large
divisor is $`d=N`$, with cofactor $`c=1`$ and weight $`\log c=0`$.
Thus $`r_D(N)=0`$. The retained difficulty in $`R_D^U`$ lies on
composite band-free endpoints.

### Corollary 5: concentration compensates for sparsity

Under the actual prime measure,

```math
\mathbb E_{\nu_X}[U(n+g)t_D(n+g)]=K(Qg)+o(1),\qquad
\|t_D\|_2\ge(1+o(1))K(Qg)/\sqrt V.
\qquad\text{(24)}
```

For every normalized marker in (8),

```math
\|1-Z\|_2\,\|t_D\|_2\ge(1+o(1))K(Qg).
\qquad\text{(25)}
```

Consequently a separated Cauchy estimate cannot remove the marker
from this small-divisor polynomial with error $`o(K(Qg))`$.
For the optimal union marker there is an actual error identity:

```math
\mathbb E_{\nu_X}[(1-Z_{\rm union})t_D]=K(Qg)+o(1).
\qquad\text{(26)}
```

Indeed, both $`\mathbb E t_D`$ and $`\mathbb E[Ut_D]`$ equal $`K(Qg)+o(1)`$;
substitution of (10) proves (26). These assertions concern $`t_D`$,
not the norm or signed mean of $`r_D`$.

## 5. An unsigned obstruction for the actual Möbius remainder

The switched remainder, omitting the zero term $`c=1`$, is exactly

```math
R_D(X)=\sum_{2\le c\le(2X+g)/D}\log c
 \sum_{\substack{d\gt D\\X\lt cd-g\le2X\\cd\equiv a+g\pmod Q}}
                         \mu(d)\vartheta(cd-g).
\qquad\text{(27)}
```

Let $`M_c(d)`$ be arbitrary complex markers, depending on the parameters,
subject only to

```math
(d,W)=1\ \Longrightarrow\ M_c(d)=0.
\qquad\text{(28)}
```

This includes any signed, overlapping, or higher-order combination
of divisibility tests using primes in $`\mathcal P`$ that vanishes
at the empty pattern. Define the unsigned removal budget

```math
\mathcal E_{\rm abs}(X)=
\sum_{2\le c\le(2X+g)/D}\log c
 \sum_{\substack{d\gt D\\X\lt cd-g\le2X\\cd\equiv a+g\pmod Q}}
 \mu^2(d)\vartheta(cd-g)|1-M_c(d)|.
\qquad\text{(29)}
```

It bounds the absolute value of the signed removal error, not its value.

### Theorem 6: failure of absolute marking removal

Fix $`Q,g,a,\alpha,\beta,\lambda`$, and suppose $`D=X^{1/2+o(1)}`$.
Uniformly in every family satisfying (28),

```math
\mathcal E_{\rm abs}(X)\gg
XV^2L^2\asymp XL^{\,2-2(\beta-\alpha)},
\qquad\text{(30)}
```

with constants depending on the fixed parameters.
In particular $`\mathcal E_{\rm abs}/(\kappa(Q,g)X)\to\infty`$.
For the full source band the lower bound is a constant times
$`XL^{9/5}`$. An $`o(\kappa X)`$ bound obtained by taking absolute values
in (29), or by a separated Cauchy estimate dominating it, is therefore
impossible for this entire class of markers.

**Proof.** Fix $`0\lt \xi\lt 1/2`$, put $`C=X^\xi`$, and restrict to

```math
2\le c\le C,\quad (c,QgW)=1,\quad (d,W)=1.
\qquad\text{(31)}
```

Then $`d\gt X/C\gt D`$ for large $`X`$, and $`|1-M_c(d)|=1`$.
Because $`(c,W)=1`$, the condition $`(d,W)=1`$ is $`U(cd)=1`$.
It suffices to lower-bound

```math
J(X)=\sum_{\substack{2\le c\le C\\(c,QgW)=1}}\log c
 \sum_{\substack{X\lt n\le2X\\n\equiv a\pmod Q\\c\mid n+g}}
 \vartheta(n)U(n+g)\mu^2\!\left(\frac{n+g}{c}\right).
\qquad\text{(32)}
```

Dropping $`\mu^2`$ would not prove the theorem. Instead use
$`\mu^2(d)=\sum_{s^2\mid d}\mu(s)`$, truncated at $`S=L^B`$.
The absolute tail is at most

```math
\begin{aligned}
&L\sum_{c\le C}\log c
 \sum_{S\lt s\le\sqrt{3X/c}}
       \left(\frac X{cs^2}+1\right)\\
&\hspace{15mm}\ll \frac{XL^3}{S}+\sqrt{XC}\,L^2.
\end{aligned}
\qquad\text{(33)}
```

This follows by bounding $`\vartheta\le\log(2X)`$ and counting integer
multiples; no prime cancellation is used. Choose $`B\gt A+4`$ to make
it $`O_A(XL^{-A})`$.

For $`s\le S`$ the auxiliary primes exceed $`S`$, so $`(s,W)=1`$.
On prime support $`(s,Qg)=1`$ too. Apply (5) to $`U`$ with
$`k=O_A(\log L)`$. The moduli satisfy

```math
Qcs^2r\le QC S^2 z_1^{k+1}=X^{\xi+o(1)}.
\qquad\text{(34)}
```

A modulus determines its $`W`$-supported factor $`r`$ uniquely; the
remaining part determines $`c`$ after $`s\le S`$ is chosen.
Multiplicity is therefore at most $`S`$, a fixed logarithmic power.
The coefficient $`\log c`$ costs one further factor $`O(L)`$.
Bombieri--Vinogradov with larger fixed precision pays all errors.

The positive Bonferroni remainder has main term at most

```math
\frac X{\varphi(Q)}
 \sum_{c\le C}\frac{\log c}{\varphi(c)}
 \sum_{s\ge1}\frac1{s\varphi(s)}
 \frac{H^{k+1}}{(k+1)!}
\ll_Q XL^2\frac{H^{k+1}}{(k+1)!}.
\qquad\text{(35)}
```

We used
$`\varphi(c)/\varphi(cs^2)\le1/(s\varphi(s))`$ for squarefree $`s`$,
and the convergence of the $`s`$-sum. Terms with nonsquarefree $`s`$
have $`\mu(s)=0`$. Thus the signed squarefree expansion is also paid
by an absolute remainder estimate. We obtain

```math
J(X)=\frac{XV}{\varphi(Q)}
 \sum_{\substack{2\le c\le C\\(c,QgW)=1}}
 \frac{\log c}{\varphi(c)}
 \sum_{\substack{s\le S\\(s,Qg)=1}}
       \frac{\mu(s)\varphi(c)}{\varphi(cs^2)}
 +O_{A,Q,g}(XL^{-A}).
\qquad\text{(36)}
```

The infinite inner sum has absolutely convergent Euler factors

```math
1-\frac{\varphi(c)}{\varphi(cp^2)}
=
\begin{cases}
1-p^{-2},&p\mid c,\\
1-[p(p-1)]^{-1},&p\nmid c,
\end{cases}
\qquad p\nmid Qg.
\qquad\text{(37)}
```

Since $`2\mid Qg`$, their product is bounded below uniformly in $`c`$ by

```math
b_0=\prod_{p\ge3}\left(1-\frac1{p(p-1)}\right)\gt 0.
\qquad\text{(38)}
```

The tail after $`S`$ is at most
$`\sum_{s\gt S}1/(s\varphi(s))=o(1)`$ uniformly in $`c`$.
The inner sum in (36) is therefore at least $`b_0/2`$ for large $`X`$.

Finally,

```math
\sum_{\substack{2\le c\le C\\(c,QgW)=1}}
                   \frac{\log c}{\varphi(c)}
\gg_{Q,g}V(\log C)^2.
\qquad\text{(39)}
```

To prove this, replace $`1/\varphi(c)`$ by $`1/c`$ and restrict to
$`C^{1/2}\lt c\le C`$. The same truncated inclusion--exclusion, now for
integers, gives uniformly for $`C^{1/2}\le t\le C`$

```math
\#\{c\le t:(c,QgW)=1\}
=t\frac{\varphi(Qg)}{Qg}
 \prod_{p\in\mathcal P}(1-p^{-1})+O_A(tL^{-A}).
\qquad\text{(40)}
```

The rounding error is $`O_{Q,g}(z_1^{k+1})=X^{o(1)}`$, and (6)
pays the tail. The product in (40) is $`(1+o(1))V`$.
Partial summation with $`(\log t)/t`$ proves (39).
Equations (36)--(39) give $`J\gg XV^2L^2`$, proving (30).
$`\square`$

This is an arithmetic lower bound for unsigned total variation,
with actual primes and actual squarefree Möbius divisors.
Large signed cancellation inside this set remains possible.

## 6. Exact error criterion and uniform covering moduli

### 6.1 The transfer estimate that is really needed

Let $`R_D^M`$ be (27) with $`M_c(d)`$ inserted. Its exact difference is

```math
R_D-R_D^M=\sum_{c\ge2}\log c
 \sum_{\substack{d\gt D\\X\lt cd-g\le2X\\cd\equiv a+g\pmod Q}}
 \mu(d)\vartheta(cd-g)(1-M_c(d)).
\qquad\text{(41)}
```

A sufficient two-sided transfer bound is
$`(41)=o(\kappa(Q,g)X)`$ uniformly in the claimed parameter range.
A one-sided prime-gap theorem needs only the corresponding
one-sided lower estimate. Density or variance alone proves neither.

For example, let $`H_c`$ be the inner sum of
$`\mu^2(d)\vartheta(cd-g)`$, and let $`\delta_c`$ be the mean of
$`|1-M_c(d)|^2`$ under those weights, taking zero when $`H_c=0`$.
Cauchy would give the sufficient condition

```math
\sum_{c\ge2}(\log c)H_c\sqrt{\delta_c}=o(\kappa X).
\qquad\text{(42)}
```

The left side dominates (29). Theorem 6 proves that this condition
cannot hold under (28); normalization of the markers does not help.
For comparison, for fixed $`Q,g`$ and
$`c\le X^{1/2+o(1)}`$, Brun--Titchmarsh gives
$`H_c\ll_{Q,g}X/\varphi(c)`$ on the possible coprime columns.
The usual uniform-error bookkeeping would demand
$`\sup_c\delta_c=o(L^{-4})`$, since
$`\sum_{c\le Y}(\log c)/\varphi(c)\ll(\log(2Y))^2`$.
Theorem 6 proves failure of this absolute/Cauchy architecture,
rather than merely finding an inadequate known upper bound.

### 6.2 Conditional uniform localization

Assume, uniformly in the moduli and reduced residues used, that

```math
\theta(t;q,b)=\frac t{\varphi(q)}
 +O_\sigma(t^\sigma\log^2(3qt)),\qquad
(b,q)=1,\qquad 1/2\le\sigma\lt 1.
\qquad\text{(43)}
```

Fix $`C_0,\delta,\epsilon\gt 0`$ and suppose

```math
Qg\le X^{C_0},\quad g\lt X,\quad D\ge X^\delta,\quad
QD\le X^{1-\sigma-\epsilon}.
\qquad\text{(44)}
```

For every fixed $`A\gt 0`$, the proof of Theorem 4 gives uniformly

```math
T_D^U=\kappa(Q,g)X+
 O\!\left(\frac X{\varphi(Q)}L^{-A}\right),\qquad
T_D^{1-U},R_D^{1-U}
=O\!\left(\frac X{\varphi(Q)}L^{-A}\right).
\qquad\text{(45)}
```

Constants can depend on the displayed fixed parameters and (43).
Indeed there are at most $`D z_1^{k+1}`$ distinct moduli, and partial
summation costs $`O(L)`$. Their distribution errors total
$`D z_1^{k+1}X^\sigma O_{C_0}(L^3)`$, which is
$`X^{-\epsilon+o(1)}O(L^3)`$ relative to $`X/\varphi(Q)`$.
Lemma 3 uses only the additional factor $`\log L`$ in (14).
Proper prime powers cost relatively at most
$`QX^{-1/2}L^3\le X^{-\delta-\epsilon}L^3`$.

Proposition 1 also holds uniformly with error
$`O(XL^{-A}/\varphi(Q))`$. Excluding prime divisors of $`Qg`$ changes
(2) negligibly: at most $`O_{C_0}(L^{1-\alpha})`$ such primes lie in
the band, each exceeding $`\exp(L^\alpha)`$.

The additional analytic input is exactly (43). Lemma 3 uses only
classical Mertens bounds. A fixed-character zero-free result does
not supply (43), and an exceptional real zero cannot be ignored
when deriving it. No new certification of (43) from the quasi-RH
repository is asserted here.

### 6.3 Conditional uniform unsigned obstruction

Under (43)--(44), the same argument proves

```math
\mathcal E_{\rm abs}\gg
\frac X{\varphi(Q)}\,\frac{V^2L^2}{\log L}.
\qquad\text{(46)}
```

Since $`K(Qg)\ll_{C_0}\log L`$,

```math
\frac{\mathcal E_{\rm abs}}{\kappa(Q,g)X}
\gg \frac{L^{\,2-2(\beta-\alpha)}}{(\log L)^2}\longrightarrow\infty.
\qquad\text{(47)}
```

Here are the uniform details. In Theorem 6 take
$`C=X^{\delta/2}`$ and $`S=L^B`$.
The moduli cost
$`QCS^2z_1^{k+1}\le
X^{1-\sigma-\epsilon-\delta/2+o(1)}`$,
so (43) pays them even if counted separately.
In the squarefree tail retain the congruence modulo $`Q`$.
Since $`(cs,Q)=1`$ on prime support, the number of allowed $`d`$ is at
most $`X/(Qcs^2)+1`$, improving (33) to

```math
O\!\left(\frac{XL^3}{QS}+\sqrt{XC}\,L^2\right).
\qquad\text{(48)}
```

Its second term is relatively small because
$`Q\le X^{1/2-\delta-\epsilon}`$. The local squarefree factor (38)
is still absolute.

For (39), first remove prime divisors of $`Qg`$ up to $`L^2`$.
Their Euler product is at least a constant times $`1/\log L`$;
truncated inclusion--exclusion still uses products $`X^{o(1)}`$.
Prime divisors above $`L^2`$ have reciprocal sum
$`O_{C_0}(1/(L\log L))`$ and number $`O_{C_0}(L/\log L)`$.
Removing their multiples from $`[1,t]`$, $`t\ge C^{1/2}`$, costs
$`O(t/(L\log L)+L/\log L)=o(tV/\log L)`$,
because $`\beta-\alpha\lt 1`$. Thus (39) becomes
$`\gg V L^2/\log L`$. The bound for $`K(Qg)`$ follows from the same
small/large prime split as (14). These facts prove (46)--(47).

For $`\sigma=7/8`$, the example
$`Q\le X^{1/16}`$, $`D=X^{1/32}`$ has positive margin in (44).
It localizes the signed obligation uniformly but does not estimate
it; its cofactor range is much longer than a square-root range.

## 7. Repairs that retain the omitted sector

### 7.1 Mark only the Möbius cofactor

This is already included in (27)--(30). An exact identity explains
what complete depletion retains. Write $`N=ab`$, where every prime
factor of $`a`$ is in $`W`$ and $`(b,W)=1`$. Then

```math
\sum_{\substack{d\mid N\\(d,W)=1}}\mu(d)\log(N/d)
=\begin{cases}
\log N,&b=1,\\
\Lambda(b),&b\gt 1.
\end{cases}
\qquad\text{(49)}
```

Indeed the divisors are precisely those of $`b`$; expand
$`\log(N/d)=\log a+\log(b/d)`$.
Thus a smooth-factor partition exposes a prime or prime-power
rough cofactor rather than evaluating its endpoint correlation.

For a related exact diagnostic, let squarefree $`A\mid N`$, write
$`N/A=m_A m_0`$, where all primes of $`m_A`$ divide $`A`$ and
$`(m_0,A)=1`$. Pairing $`d=Ae`$ gives

```math
\sum_{\substack{d\mid N\\A\mid d}}\mu(d)\log(N/d)
=\mu(A)\{\Lambda(m_0)+\mathbf1_{m_0=1}\log m_A\}.
\qquad\text{(50)}
```

Only $`(e,A)=1`$ contributes. Such $`e`$ divides $`m_0`$, so the same
divisor identity proves (50). A plain marker
$`\sum_{A\mid d}\omega_A`$ therefore converts the full convolution
to explicit rough-cofactor terms. This is an elementary algebraic
identity, not a correlation estimate for the source's damped marks.

A Buchstab decomposition can retain the rough part explicitly.
The part of (27) with $`d\gt D`$ itself prime is

```math
-\sum_{c\ge2}\log c
 \sum_{\substack{d\gt D\ {\rm prime}\\X\lt cd-g\le2X\\
                 cd\equiv a+g\pmod Q}}\vartheta(cd-g).
\qquad\text{(51)}
```

This is a correlation of the two prime forms $`d`$ and $`cd-g`$.
It need not be bounded separately to solve the signed problem, but
it cannot be discarded or evaluated by a one-prime progression
estimate.

### 7.2 Off-endpoint marks on $`d+b`$

This escapes the support restriction and deserves a separate test.
If $`A\mid d+b`$, set $`d=Ah-b`$. The summand becomes

```math
\mu(Ah-b)\vartheta(cAh-cb-g).
\qquad\text{(52)}
```

For $`b\ne0`$, Möbius multiplicativity no longer extracts a common
factor independent of $`A`$. Cauchy in $`h`$ instead leaves the actual
prime-weighted kernel

```math
\sum_{h\in I_{A,B}}
 \mu(Ah-b)\mu(Bh-b)
 \vartheta(cAh-cb-g)\vartheta(cBh-cb-g)
 \mathcal W_{A,B,c,Q}(h),
\qquad\text{(53)}
```

with the interval, covering masks and inherited weights retained.
Unweighted two-point Möbius cancellation does not allow an arbitrary
prime multiplier to be inserted into it.

Vaughan factorization of the prime variables yields

```math
uv+(cb+g)=cAh,\quad rs+(cb+g)=cBh
\quad\Longrightarrow\quad
Buv-Ars=(cb+g)(A-B).
\qquad\text{(54)}
```

The new determinant shift is $`cb+g`$.
The factors $`\mu((uv+g)/c)`$ and $`\mu((rs+g)/c)`$ remain coupled
across the primitive endpoints used in the existing operator.
They are not separate endpoint coefficients of that operator.

An average in $`b`$ does not produce the actual shift average in
Lichtman's theorem. For every interval $`I`$ of $`d`$,

```math
\sum_{b=0}^{A-1}\sum_{\substack{h\\Ah-b\in I}}
 \mu(Ah-b)\vartheta(c(Ah-b)-g)
=\sum_{d\in I}\mu(d)\vartheta(cd-g).
\qquad\text{(55)}
```

It merely partitions the original sum into residue classes.
The determinant of the two original affine forms in (52) is
$`-Ag`$, independent of $`b`$. Their intercepts are locked together.

This is a test of the repair, not a proof that it is impossible.
A bound for (53), uniform in growing auxiliary products and with
the cofactor summation paid, would be additional input. Neither
the source's unweighted fixed-form theorem nor the averaged-shift
theorem examined in Section 8 provides it.

### 7.3 Center before absolute values

A centered factor
$`\mathbf1_{p\mid d}-1/(p-1)`$ is nonzero on the empty pattern, so
a direct centered operator is a materially different architecture.
For weights $`w_p`$, put

```math
\mathcal B(d)=\sum_{p\in\mathcal P}w_p\mathbf1_{p\mid d},
\qquad h_{\mathcal B}=\sum_{p\in\mathcal P}\frac{w_p}{p-1}.
```

Require $`h_{\mathcal B}\ne0`$. One precise signed transfer obligation is

```math
\sum_{c\ge2}\log c
 \sum_d\mu(d)\vartheta(cd-g)
       (\mathcal B(d)-h_{\mathcal B})
=o(|h_{\mathcal B}|\kappa X),
\qquad\text{(56)}
```

with the product and progression constraints of (27).
Together with a marked bound $`R_D^{\mathcal B}=o(|h_{\mathcal B}|\kappa X)`$,
the identity $`R_D^{\mathcal B}-h_{\mathcal B}R_D=(56)`$ recovers
$`R_D=o(\kappa X)`$ by division by $`h_{\mathcal B}`$.
These are proposed analytic estimates, not consequences of the local mean
or prime distribution. If an auxiliary prime divides the cofactor $`c`$,
the appropriate local mean changes;
such columns require separation or their own exact centering.

The ordinary two-point source below illustrates taking centered
residue averages before absolute values. Its dilation identities
use bounded multiplicative factors. The prime mask and the total
cofactor weight in (56) are additional requirements. Our lower
bounds leave this signed architecture open, while ruling out its
replacement by the absolute removal step (29).

## 8. Sources, dependencies and permitted conclusions

The standard-library script
[rough_endpoint_checks.py](code/rough_endpoint_checks.py) checks 61,741
finite algebra and modulus-accounting cases, including formal prime-logarithm
identities, the squarefree factors, Bonferroni remainders and the off-endpoint
residue partition. Both normal Python and Python with optimization enabled
passed. These are exact finite checks, not verification of an asymptotic
estimate or a prime-gap theorem.

| Input or comparison | Exact source and locator | Role and limit |
|---|---|---|
| Endpoint calibration | [Signed endpoint mass](signed-endpoint-transfer.md), Section 1 | Canonical definitions and decomposition. The changed cutoff and enormous excluded product are paid above. |
| Classical distribution | Maynard, [arXiv:1311.4600](https://arxiv.org/abs/1311.4600), Section 2; Kedlaya, [Chapter 17, Theorem 17.1](https://kskedlaya.org/ant/chap-bombieri.html) (proof in Chapter 18) | Bombieri--Vinogradov is used below its square-root threshold with sufficient margin. Passing from prime powers to primes is paid. |
| Shifted-prime factor model | Ford, [arXiv:2408.03803v4](https://arxiv.org/html/2408.03803v4), Theorem 1 and Hypothesis $`Z(\gamma)`$; Theorem 2 | The model has zero probability $`1-1/(p-1)`$ and total-variation error $`O(e^{-\alpha_0u\log u}+(\log x)^{-A})`$, with $`\alpha_0\lt \gamma`$, $`u=\log x/\log y`$. $`Z(1/2)`$ follows from Bombieri--Vinogradov. This gives the arithmetic density baseline, not a signed prime-pair correlation. |
| Damped marking | Lü--Wang--Wu, [arXiv:2610.20242v1](https://arxiv.org/html/2610.20242v1), Proposition 2.3 and proof | Its truncated binomial expansion and Bombieri--Vinogradov step are adapted here with the actual divisor and squarefree weights. Its fixed-group $`L^2`$ argument does not pay (41). |
| Sifted Möbius convolution | Same source, Proposition 2.2 | Its smooth-divisor convolution and Rankin choice motivate Lemma 3. That lemma needs no new zero-free theorem. |
| Marked determinant bound | Same source, Sections 4--5; [Cofactor averaging](cofactor-dispersion.md) | The analytic transfer remains conditional. No full independent certification or arbitrary-log bound for the unmarked affine sum is asserted. Formula (11) does not automatically extend the source operator estimates. |
| Actual shift averages | Lichtman, [arXiv:2009.08969v2](https://arxiv.org/html/2009.08969v2), Theorems 1.1 and 1.3 | Allows averages of Möbius shifts, including fixed prime-tuple weights. The locked-intercept residue partition (55) is not that average. |
| Ordinary centered correlations | OpenAI, [Ordinary two-point correlations of multiplicative functions](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026), build/introduction.tex, labels thm:q-affine, thm:elliott, cor:affine; blob da38786f2b27248f49985c1e7f3d8a95fd152f81 | The inspected source claims fixed-form Liouville power-log saving and qualitative bounded-multiplicative Elliott cancellation; it explicitly claims no uniformity in growing affine coefficients. Its statements and described mechanism do not pay (53). This is an interface inspection, not a proof audit. |
| Uniform covering moduli | Hypothesis (43), matching companion manuscript Section 2 | Used only in (45)--(48). Its uniformity and exceptional-zero requirements are explicit. No quasi-RH claim is promoted to an audited unconditional premise here. |

The surviving obligation is signed cancellation on the retained
band-free sector, or a bound such as (53) or (56) that controls it
without the unsigned loss in Theorem 6. The arithmetic estimates above
remove a concrete ambiguity in the transfer and rule out an entire
absolute marking-removal architecture. They do not prove a positive
lower bound for any new specified prime gap.

