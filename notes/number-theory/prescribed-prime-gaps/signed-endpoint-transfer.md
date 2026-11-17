# Signed endpoint mass after a congruence cover

**Mira Cult**

For an endpoint-safe class, the weighted prime-pair count equals an explicitly
calibrated positive term plus a signed Möbius remainder. This note proves that
identity and states exactly what lower bound would force the two endpoints
to be prime. The [interior cover](cover.md) then guarantees consecutivity.
The required signed lower bound is not proved.

The fixed-parameter proof uses classical Bombieri–Vinogradov and classical
Mertens cancellation. A separate section gives a conditional extension to
growing moduli. No historical novelty is claimed for the divisor identity.

## 1. A calibrated endpoint decomposition

Fix an even integer $`g\gt 0`$, an even integer $`Q\ge2`$, and $`a\in\mathbb Z`$
with $`(a(a+g),Q)=1`$. Write

```math
\vartheta(n)=(\log n)\mathbf1_{\mathbb P}(n),\qquad
S_{Q,a,g}(X)=\sum_{\substack{X\lt n\le2X\\n\equiv a\pmod Q}}
                     \vartheta(n)\Lambda(n+g),\qquad X\gt g.
```

Here $`\vartheta`$ is a function on integers; $`\theta(x;q,b)`$ below denotes
the summatory prime weight in a progression. For $`D\ge1`$, define

```math
R_D(X)=\sum_{\substack{X\lt n\le2X\\n\equiv a\pmod Q}}
 \vartheta(n)\sum_{\substack{d\mid n+g\\d\gt D}}
                  \mu(d)\log\frac{n+g}{d}.
\qquad\text{(1)}
```

Put $`r=Qg`$ and

```math
K(r)=\prod_{p\mid r}\frac p{p-1}
      \prod_{p\nmid r}\frac{p(p-2)}{(p-1)^2},
\qquad \kappa(Q,g)=\frac{K(Qg)}{\varphi(Q)}\gt 0.
\qquad\text{(2)}
```

The second product converges absolutely and is positive since $`2\mid r`$.

**Theorem 1 (unconditional, fixed parameters).** For every fixed $`A\gt 0`$
there is a sufficiently large $`B=B(A)`$ such that, with
$`D=\lfloor\sqrt X/(Q(\log X)^B)\rfloor`$,

```math
S_{Q,a,g}(X)=\kappa(Q,g)X+R_D(X)
                      +O_{Q,g,A}\bigl(X(\log X)^{-A}\bigr).
\qquad\text{(3)}
```

**Proof.** The identity
$`\Lambda(v)=\sum_{d\mid v}\mu(d)\log(v/d)`$ is exact. On the support
of $`\vartheta(n)`$, a divisor $`d\mid n+g`$ must satisfy $`(d,g)=1`$:
otherwise some prime dividing both $`d`$ and $`g`$ divides the prime $`n`$,
forcing $`n\le g`$, contrary to $`n\gt X\gt g`$. Also $`(d,Q)=1`$ because $`n+g`$
is a unit modulo $`Q`$. Thus no contributing divisor is lost by restricting
to $`(d,Qg)=1`$.

For such $`d`$, the conditions $`n\equiv a\pmod Q`$ and
$`n\equiv-g\pmod d`$ specify one reduced residue $`b_d\pmod{Qd}`$.
Consequently the complementary small-divisor term is exactly

```math
T_D(X)=\sum_{\substack{d\le D\\(d,Qg)=1}}\mu(d)
 \sum_{\substack{X\lt n\le2X\\n\equiv b_d\pmod{Qd}}}
              \vartheta(n)\log\frac{n+g}{d}.
\qquad\text{(4)}
```

Bombieri–Vinogradov applies to the subset of moduli $`Qd\le QD`$.
Partial summation against $`\log((t+g)/d)`$ costs $`O(\log X)`$:
its supremum has that size and its variation on $`[X,2X]`$ is at most
$`\log2`$. One may use maximal Bombieri–Vinogradov, or apply the
nonmaximal form at the endpoints and under the partial-summation
integral. Passing from $`\psi`$ to prime-only $`\theta`$ costs
$`O(\sqrt X(\log X)^2)`$ per modulus. The sum of these costs, including
the weight, is absorbed by increasing $`B`$. Since
$`\varphi(Qd)=\varphi(Q)\varphi(d)`$ here,

```math
T_D(X)=\frac1{\varphi(Q)}\int_X^{2X}
 \sum_{\substack{d\le D\\(d,r)=1}}
       \frac{\mu(d)}{\varphi(d)}\log\frac{t+g}{d}\,dt
       +O_{Q,A}\bigl(X(\log X)^{-A}\bigr).
\qquad\text{(5)}
```

To calibrate the coefficient without assuming a prime-pair conjecture,
let

```math
A_r(y)=\sum_{\substack{d\le y\\(d,r)=1}}\frac{\mu(d)}{\varphi(d)},
\qquad
B_r(y)=\sum_{\substack{d\le y\\(d,r)=1}}
                \frac{\mu(d)}{\varphi(d)}\log\frac yd.
```

Their Dirichlet series factors as

```math
F_r(s)=\prod_{p\nmid r}\left(1-\frac{p^{-s}}{p-1}\right)
      =\frac{H_r(s)}{\zeta(1+s)}.
\qquad\text{(6)}
```

The coefficients $`h_r(n)`$ of $`H_r(s)`$ are multiplicative, with

```math
h_r(p^j)=
\begin{cases}
 -1/(p^j(p-1)),&p\nmid r,\\
 p^{-j},&p\mid r,
\end{cases}
\qquad j\ge1.
```

Therefore $`\sum_n|h_r(n)|n^\eta\lt \infty`$ for every fixed
$`0\lt \eta\lt 1`$. Convolution with the classical estimate
$`\sum_{n\le y}\mu(n)/n=O_C((\log y)^{-C})`$, splitting the
$`h_r`$-sum at $`\sqrt y`$, gives
$`A_r(y)=O_{r,C}((\log y)^{-C})`$ for every $`C\gt 0`$.

The identity $`B_r(y)=\int_1^y A_r(t)\,dt/t`$ now proves convergence
with any prescribed logarithmic saving. For real $`s\gt 0`$,
$`F_r(s)/s=\int_1^\infty A_r(t)t^{-s-1}\,dt`$; dominated convergence
and $`\zeta(1+s)\sim1/s`$ identify the limit as $`H_r(0)=K(r)`$.
Hence

```math
\begin{aligned}
\sum_{\substack{d\le D\\(d,r)=1}}
 \frac{\mu(d)}{\varphi(d)}\log\frac{t+g}{d}
 &=\log\frac{t+g}{D}\,A_r(D)+B_r(D)\\
 &=K(r)+O_{r,A}((\log X)^{-A})
\end{aligned}
\qquad\text{(7)}
```

uniformly for $`X\le t\le2X`$, since $`D=X^{1/2+o(1)}`$ and $`g,Q`$
are fixed. Equations (1), (4), (5) and (7) prove (3). $`\square`$

The normalization can alternatively be written

```math
\kappa(Q,g)=\frac{Q}{\varphi(Q)^2}
 \prod_{\substack{p\mid g\\p\nmid Q}}\frac p{p-1}
 \prod_{p\nmid Qg}\frac{p(p-2)}{(p-1)^2}.
\qquad\text{(8)}
```

This is the coefficient per unit interval in $`n`$, not in
$`(n-a)/Q`$.

**Corollary 2 (the remaining lower-bound obligation).** Suppose an
interior covering forces every $`n+j`$, $`0\lt j\lt g`$, composite on
$`n\equiv a\pmod Q`$ once $`n\gt N_0`$. If for some $`\epsilon\gt 0`$ and
arbitrarily large $`X`$ one has

```math
R_D(X)\ge-(1-\epsilon)\kappa(Q,g)X,
\qquad\text{(9)}
```

then gap $`g`$ occurs infinitely often, with
$`\gg_{Q,g,\epsilon}X/(\log X)^2`$ occurrences in each sufficiently
large successful dyad.

Indeed, (3) gives a positive main mass. Terms for which $`n+g`$ is a
proper prime power contribute $`O(\sqrt X(\log X)^3)=o(X)`$.
Every remaining term is a prime pair, each of weight at most
$`(\log(3X))^2`$, and the proper interior covering proves consecutivity.
One sufficiently large successful dyad would instead prove one occurrence.
No estimate establishing (9) is supplied here.

## 2. Uniform calibration under a common zero-free half-plane

This section is conditional. For a fixed $`1/2\le\beta\lt 1`$, assume
the uniform progression estimate

```math
\theta(t;q,b)=\frac t{\varphi(q)}
       +O_\beta\bigl(t^\beta\log^2(3qt)\bigr),\qquad (b,q)=1,
\qquad\text{(10)}
```

and, for every fixed $`0\lt \eta\lt 1-\beta`$,
$`M(y)=\sum_{n\le y}\mu(n)=O_\eta(y^{1-\eta})`$.
These are the precise analytic inputs used below.

A valid common zero exclusion $`\Re\rho\le\beta`$ for all Dirichlet
$`L`$-functions gives (10) by the uniform explicit formula and zero count;
its zeta instance gives the stated Mertens consequence. Nontrivial zeros
on the boundary are included. The character sum over zeros is bounded by
$`t^\beta O(\log^2(qt))`$, and imprimitive-character corrections are
smaller. Common zero exclusion rules out any exceptional real zero above
$`\beta`$. A merely fixed-character estimate does not justify this step.
No proof of a new common zero-free boundary is assumed in the unconditional
results. This section states the progression and Mertens inputs explicitly.

**Lemma 3 (uniform arithmetic coefficient).** Under the Mertens input,
for every fixed $`0\lt \eta\lt 1-\beta`$ and $`\varepsilon\gt 0`$,

```math
|A_r(D)|+|B_r(D)-K(r)|
       \ll_{\eta,\varepsilon}r^\varepsilon D^{-\eta}
\qquad\text{(11)}
```

uniformly in even $`r`$ and $`D\ge2`$.

**Proof.** Partial summation gives
$`\sum_{n\le y}\mu(n)/n=O_\eta(y^{-\eta})`$, with limiting sum zero.
The coefficients in (6) satisfy

```math
\sum_{n\ge1}|h_r(n)|n^\eta
\le C_\eta\prod_{p\mid r}(1-p^{-(1-\eta)})^{-1}
\ll_{\eta,\varepsilon}r^\varepsilon.
```

For the last bound, separate finitely many small primes and use
$`(1-p^{-(1-\eta)})^{-1}\le p^\varepsilon`$ at every other prime.
Convolution bounds $`A_r(D)`$; integrating its tail bounds
$`B_r(D)-K(r)`$. $`\square`$

**Proposition 4 (conditional, growing parameters).** Under (10) and
Lemma 3, for $`g,Q`$ positive even, $`(a(a+g),Q)=1`$, $`g\lt X`$ and
$`2\le D\le X`$,

```math
T_D(X)=\kappa(Q,g)X+
 O_{\beta,\eta,\varepsilon}\!\left(
  \frac X{\varphi(Q)}(Qg)^\varepsilon D^{-\eta}\log(3X)
  +DX^\beta\log^3(3QDX)\right).
\qquad\text{(12)}
```

This follows by partial summation in (4), then (7) and (11). In particular,
for fixed positive $`C,\delta,\epsilon_0`$,

```math
Qg\le X^C,\qquad D\ge X^\delta,\qquad
QD\le X^{1-\beta-\epsilon_0}
\quad\Longrightarrow\quad
T_D(X)=\kappa(Q,g)X+o(\kappa(Q,g)X)
\qquad\text{(13)}
```

uniformly over these data. To check the relative error, observe
$`K(r)\ge K(2)\gt 0`$: adjoining a prime $`p\gt 2`$ multiplies $`K`$ by
$`(p-1)/(p-2)\gt 1`$. Choose $`\varepsilon\lt \delta\eta/(2C)`$.
The first relative error in (12) is then a negative power of $`X`$
times $`\log X`$; the second is
$`O(X^{-\epsilon_0}(\log X)^3)`$ since
$`\kappa(Q,g)\ge K(2)/Q`$.

For example, $`\beta=7/8`$ permits $`Q\le X^{1/16}`$ and
$`D=X^{1/32}`$, with an exponent margin $`1/32`$ in the final inequality.
This makes the Type I calibration uniform at a growing CRT modulus.
The remainder (1) is unchanged: (12) proves no prime-pair lower bound
and no first-occurrence estimate.

## 3. The exact cofactor form

Changing variables $`m=(n+g)/d`$ in (1) gives the exact switched form

```math
R_D(X)=\sum_{m\le(2X+g)/D}\log m
 \sum_{\substack{d\gt D\\X\lt dm-g\le2X\\dm\equiv a+g\pmod Q}}
                          \mu(d)\vartheta(dm-g).
\qquad\text{(14)}
```

The moving lower boundary and the product constraint are part of the
identity. Replacing these sums by unrestricted progression prefixes
would change the problem.

The other notes denote this cofactor by $`c`$. Its first column has
weight $`\log1=0`$. Both the product window and the moving lower divisor
cutoff belong to the identity.

## 4. What the subsequent arguments accomplish

- [Cofactor averaging](cofactor-dispersion.md) transfers one phase-uniform
  base-energy bound to every cofactor and all moving cutoffs. The base-energy
  bound itself remains an explicit unproved hypothesis.
- [Primitive-root counting](root-counting-moduli.md) proves the required
  modular equidistribution and fixed-gap densities, including prime powers
  in the modulus. It does not prove the complete signed operator bound.
- [Rough endpoints](rough-endpoint-marking.md) localizes the calibrated main
  term to the sector avoiding the auxiliary primes, and proves that a broad
  class of absolute marking-removal estimates cannot hold.
- [Endpoint parity](endpoint-repair.md) supplies an explicit comparison
  sequence and parity companion, and identifies the localized sign estimate
  a Chen-type repair would need.

The universal prime-gap target and the signed lower bound (9) remain open.

## 5. A fixed-gap coordinate change

In the determinant application below, $`A,B`$ are auxiliary products
and $`D_{\rm aux}`$ is a shared auxiliary product. The notation keeps
it distinct from the small-divisor cutoff $`D`$.

**Lemma 7 (algebraic conjugacy).** Suppose primitive endpoints
$`P=(u,v)`$ and $`P'`$ have coordinates coprime to $`g`$, and their
determinant is divisible by $`g`$. They have the same unit ratio
$`r=v/u\pmod g`$. On that ratio component define

```math
T_{g,r}(u,v)=\left(u,\frac{ru-v}{g}\right).
\qquad\text{(19)}
```

This is an integral bijection onto primitive $`(x,y)`$ with $`(x,g)=1`$.
It multiplies determinants by $`-1/g`$.

**Proof.** The congruence makes the second coordinate integral.
The inverse is $`(x,y)\mapsto(x,rx-gy)`$, and
$`\gcd(x,rx-gy)=\gcd(x,y)`$ when $`(x,g)=1`$.
The determinant of the displayed linear map is $`-1/g`$. $`\square`$

Hence the equation
$`\det(P,P')/D_{\rm aux}=-g(B-A)`$ becomes the unit-shift equation $`B-A`$.
If $`G=\left(\begin{smallmatrix}u&c_0\\v&d_0\end{smallmatrix}\right)
\in\mathrm{SL}_2(\mathbb Z)`$ completes $`P`$, then

```math
G'=T_{g,r}G\begin{pmatrix}1&0\\0&-g\end{pmatrix}
 =\begin{pmatrix}u&-gc_0\\(ru-v)/g&d_0-rc_0\end{pmatrix}
 \in\mathrm{SL}_2(\mathbb Z).
\qquad\text{(20)}
```

The root coordinate $`c_0/u`$ changes to $`-gc_0/u`$ modulo $`1`$.
The degree-$`g`$ circle map preserves Haar measure; its inverse branches
compensate its Jacobian. The relative position $`G'z`$ corresponds to the original position
$`G\operatorname{diag}(1,-g)z`$. A primitive relative vector $`z`$ represents
an original primitive position exactly when $`(z_1,g)=1`$. This is a
coordinate projection independent of the auxiliary-list ordering.
At auxiliary primes not dividing $`g`$, the induced coordinate changes
permute the projective lines bijectively, preserving uniform line averaging.
The transformed real support is a parallelogram and must be retained.

The required root counts and component densities are proved in
[Primitive-root counting](root-counting-moduli.md). This coordinate
calculation does not by itself establish the complete signed base estimate.

## Classical inputs and evidence

Bombieri–Vinogradov is used in its maximal, all-moduli averaged form below
the square-root threshold; see Maynard,
[*Small gaps between primes*, arXiv:1311.4600](https://arxiv.org/abs/1311.4600),
Section 2. The required Mertens estimate follows from the classical zeta
zero-free region; see Koukoulopoulos,
[*The Distribution of Prime Numbers*](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf),
Chapters 7–8. The coefficient calculation and all conditional parameter
losses are proved above. [Verification](VERIFICATION.md) records source
identity and the scope of mathematical review.
