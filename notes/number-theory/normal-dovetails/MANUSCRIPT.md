# Normal dovetails from analytic functions
## A common framework for analytic, singular, and flat sources

Mira-Cult research notes. Public exposition prepared 11 November 2026 from the corrected 20 October 2026 source.

**Review scope.** Sections 1–4 and Appendices A–B give the reviewed core: coefficient-window admission, D-finite and rational-derivative consequences, and exact regular-power exceptions. Sections 5–7 retain the singular, flat, and near-polynomial producer proofs; their principal estimates have received targeted checks, not the same complete core review. All arguments appear together here, with their hypotheses and review limits stated where used. See [verification and review](VERIFICATION.md). No formal proof, external referee acceptance, or historical priority is claimed.

### Abstract

We concatenate the complete first $A_rD_r$ fractional radix digits of an analytic function at all affine inputs $(bj+1)b^{-A_r}$ in each stage $b^{r-1}\le j<b^r$. An exponential upper bound and a finite-window, factorial-scale lower bound on Taylor coefficients suffice for normality through every output prefix. A single computable schedule works pointwise for all nonpolynomial real D-finite germs on a common positive-radius disk. The schedule can meet any specified computable, nondecreasing, divergent overhead budgets above logarithmic input precision and copied length. Uniformity of the discrepancy estimate requires uniform coefficient-window data; uniformity of the schedule alone does not provide it.

The construction admits rational, algebraic and transcendental analytic source functions. For $(1+x)^\alpha$ the exact exceptional parameters are the nonnegative integers; for $(1-x)^{-\theta}$ they are the nonpositive integers. These are results about newly constructed digit streams, not a claim that normality implies transcendence or a normality theorem for the sampled function values or their limit.

The coefficient-window theorem is the broadest analytic admission result in this account, so we state it first. Singular and flat functions need different derivative estimates and schedules; they are treated afterward rather than being silently included in its hypotheses.

## 1. Construction and the coefficient-window theorem

Fix an integer $b\ge2$. Stage $r\ge1$ contains every row index $b^{r-1}\le j<b^r$. Choose positive integers $A_r,D_r$ and put $K_r=A_rD_r$. For a row $j$ in stage $r$, use the aliases $A_j=A_r$, $D_j=D_r$, and $K_j=K_r$. The source input is

```math
x_j=(bj+1)b^{-A_r},\qquad b^{r-1}\le j<b^r.
```

For each fixed parameter $u$ in a set $U$, reduce the real source value $h_u(x_j)$ modulo 1 and copy its complete first $K_r$ fractional digits. Use the terminating expansion at ambiguous endpoints. Concatenating these blocks in increasing $j$ gives a number $Y_u$. For a word $w$ of length $W$, let $C_w(N;u)$ count occurrences starting at the first $N$ positions of this infinite output, including words that end beyond position $N$. Counting only words completed by $N$ changes the count by at most $W-1$. The parameter is fixed within each output; it never varies from row to row.

An **admissible schedule** retains all rows in their original order, uses positive integers $A_r,D_r$, copies each full $K_r$-digit prefix, and satisfies $x_j\to0$ and $D_r\to\infty$. Every sampled value must lie in the stated real domain of the source. Additional budget or regularity conditions are imposed only where explicitly stated.

A **common schedule** does not depend on $u$. **Pointwise normality** means that every fixed parameter gives a normal output. **Uniform normality on $U$** means that the normalized word-count error tends to zero uniformly over $u\in U$; compact-uniform normality requires this on each specified compact parameter set. A common schedule need not give uniform error near exceptional parameters. A computable schedule also does not by itself make the copied digits computable from arbitrary real input data.

In applications, a parameterized source may be written as $h_\theta(x)=\mathcal B(\theta,g(x))$. The operation $\mathcal B$ acts before digits are copied; it is not applied to an already normal output.

### Coefficient-window hypotheses and conclusion


A family of real analytic germs $h_u$ on a common complex disk $|x|<\rho$ around zero is **window admissible on a parameter set U** if, writing

$h_u'(x)=\sum_{n\ge 0} c_n(u) x^n$, it admits a specified positive rational lower bound $\rho$ for the common analytic radius, numbers $M\ge 1$, $C\ge 1$, integers $d\ge 1$, $n_0\ge 0$, independent of $u \in U$, such that, with the shared exponential scale $S=\max(2,2/\rho)$:

(W1) $|c_n(u)| \le  M S^n$ for all $n\ge 0$ and all $u \in U$;

(W2) for every $n\ge n_0$,

```math
\max_{0\le i<d} |c_{n+i}(u)| \ge  \exp(-C(n+d+1) \log(n+d+2))
```

The coefficients and the germs are real, and their Taylor series represent the actual source functions on this disk. Cauchy's estimate on the one interior disk $|x|\le \rho/2$ gives this shared exponential scale S; a uniform bound there supplies M in (W1). Pointwise, M may depend on the germ. The other window constants may be merely existential for qualitative statements, or computably supplied for an effective explicit onset and compact-uniform bound. No rationality hypothesis is imposed on coefficients or parameters.

**Theorem A (window admission, strong all-prefix version).** Let $h_u$ satisfy (W1)-(W2) on  $U$ with the specified common analytic-radius lower bound $\rho$. Let $F,G:\mathbb N_{>0}\longrightarrow\mathbb N_{>0}$ be computable nondecreasing functions tending to infinity. There is one computable schedule, depending only on $b,F,G,\rho$ and **not on $u$ or the remaining window data**, with:

```math
x_j\longrightarrow0,\qquad D_j\longrightarrow\infty,\qquad \frac{A_j}{\log_bj}\longrightarrow1,
```

and, eventually,

```math
A_j-\log_bj\le G(j),\qquad K_j\le F(j)\log_bj.
```

such that, for every fixed word $w$, uniformly in $u \in U$,

```math
\left|C_w(N;u)-Nb^{-W}\right|\le C_{U,b,W}N\frac{B_{r(N)}}{r(N)D_{r(N)}}
```

for all sufficiently large $N$.  Here $r(N)$ is the stage containing the last observed output digit and $B_r=A_r-r$, as defined precisely below. In particular the concatenation is normal uniformly on $U$. For any shared positive domain radius, the same schedule works *pointwise* for every germ having some finite data satisfying (W1)-(W2) on that common domain, even when the coefficient-window constants cannot be chosen uniformly across the germs. Without a fixed positive radius lower bound, a domain-dependent finite initial adjustment is required for each germ: a fixed early sample may be outside its domain. This adjustment leaves all eventual budgets and discrepancy bounds unchanged.

The theorem holds equally for $h_u(x)$ with an additive integration constant or an additional additive center, because these only rotate each harmonic sum at a common digit offset. That observation is a proof convenience, not a replacement of $\mathcal B(u,g(x))$ by an additive center.

## 2. Proof of the coefficient-window theorem


The arithmetic of a rational Taylor series can support fresh-prime grids, but it is not the only way to obtain cancellation. Here the phase is differentiated without truncating the source. The order of differentiation grows, so a derivative estimate with constants uniform in that order is essential.

A lower bound on every coefficient would exclude functions such as cosine. A lower bound on the largest coefficient in each fixed-width window allows zeros and cancellations. An invertible polynomial-coefficient recurrence supplies precisely this weaker condition by running the recurrence backwards. This is the mechanism behind the D-finite corollary.

Here “rational”, “algebraic” and “transcendental” describe source functions, not their output numbers. Whether any algebraic irrational is normal remains open, and no implication from normality to transcendence is used.

### Explicit schedule (no quantitative convergence modulus for F or G)

Set

```math
S=\max\left(2,\frac2\rho\right),\qquad B_0=3+\left\lceil\log_b(4S)\right\rceil.
```

For $r\ge2$, define

```math
B_r=\max\left\lbrace B_0,\,
\min\left(\left\lfloor\sqrt r\right\rfloor,
\left\lfloor\frac{G(b^{r-1})}{4}\right\rfloor\right)\right\rbrace,
```

```math
\begin{aligned}
D_1&=1,\\
D_r&=\min\left\lbrace D_{r-1}+1,
\max\left(1,\left\lfloor\frac{\log_2B_r}{8}\right\rfloor\right),
\max\left(1,\left\lfloor\frac{F(b^{r-1})}{4}\right\rfloor\right)
\right\rbrace,\\
A_r&=r+B_r,\qquad K_r=A_rD_r.
\end{aligned}
```

All floors, ceilings and thresholds can be evaluated by integer or rational comparisons. No rate of divergence for $F$ or $G$ is needed.

For stage 1 take $B_1=B_0, A_1=1+B_0, D_1=1$ (only a finite adjustment). This ensures $x_j\le b^{2-B_0}<1/(2S)$ from the first row. These are nondecreasing, divergent B and D profiles, $B_r\le \sqrt{r}$ for all sufficiently large r, $D_r\le 1+(\log_2 B_r)/8$, and $2^D=O(B^{1/8})$. The min-with-previous-plus-one guarantees $D_r\le D_{r-1}+1$ and no downward jumps. For $j$ in stage $r$, $\log_b j$ lies in $[r-1,r)$, so the two eventual budgets follow from the caps. Since $x_j\le b^{2-B_r}$, the source lies in the domain and tends to zero. Since $K_r=(r+B_r)D_r$, both $A_r/\log_b j \longrightarrow  1$ and $K_r/\log_b j \longrightarrow  \infty$ hold, and $B_r/(rD_r)\longrightarrow 0$.

### Uniform analytic derivative lemma

For $k\ge 1$, let $c_{k-1}$ be a usable coefficient furnished by (W2). For $0\le x<1/S$, the Taylor remainder identity gives

```math
\frac{h_u^{(k)}(x)}{(k-1)!}=c_{k-1}+\sum_{\ell\ge1}\binom{k+\ell-1}{\ell}c_{k+\ell-1}x^\ell
```

Therefore, if $2k S x\le 1$,

```math
\left|\frac{h_u^{(k)}(x)}{(k-1)!}-c_{k-1}\right|\le4MkS^kx \tag{2.1}
```

This follows from the majorant $M S^{k-1}[(1-Sx)^{-k}-1]$, $-\log(1-z)\le 2z$, and $e^v-1\le 2v$ for $0\le v\le 1$. Condition (W2) converts the absolute error to a relative error at most $1/2$ whenever

```math
B_r\ge B_*(M,S,C,d,n_0,b)+4Ck\log(k+2)
```

Only $k\le D_r+n_0+2d+12=O(\log B_r)$ is needed, so this inequality holds for all sufficiently large r, uniformly on $U$. Consequently $h_u^{(k)}$ has one fixed sign throughout every required real row interval, and lies between one half and three halves of $(k-1)! c_{k-1}$ in signed magnitude. Furthermore, for every selected order,

```math
\left|\log_b\bigl((k-1)!\,|c_{k-1}|\bigr)\right|\le\frac{B_r}{16} \tag{2.2}
```

for all sufficiently large r. When effective upper and nonzero lower bounds for the window data are supplied, these thresholds can be found by finite integer/rational bounds. With merely existential data the thresholds are existential; the common schedule is still computable from $b,F,G,\rho$. No hidden order-dependent van der Corput constant is used.

### Actual-phase Fourier calculation

Fix a late stage, abbreviate $B=B_r$, $A=r+B$, $D=D_r$, $K=AD$, $m_{\mathrm{full}}=(b-1)b^{r-1}$; include a real interval containing $b^{r-1}-1 \le  y \le  b^r$. For the word length $W$, discard the first $T B$ offsets of each copied row and the final $W-1$ crossing offsets, with

$L_0=n_0+d+10$, $L_1=L_0+d+1$, $T=8(L_1+1)$.

For each retained integer offset $TB\le t\le K-W$, set $z=\left\lfloor t/(A-1)\right\rfloor$. Condition (W2) supplies some index $n$ in $[z+L_0,z+L_0+d-1]$ with $c_n \ne  0$ and the stated lower bound; take $k=n+1$. Then

$3\le k\le D+L_1$, $t-k(A-1)\le -L_0(A-1)$,

$t-kB \ge  t(1-B/r)-L_1 B \ge  5t/8$ for $B/r\le 1/4$.     (2.3)

For harmonic $h\ge 1$, define the **untruncated actual phase**

```math
f_{t,h}(y)=h b^t h_u((by+1)b^{-A})
```

(The letter h in the subscript is a harmonic integer, not the source germ.) The chain rule and (2.1)-(2.3) give derivatives of one sign and $\lambda_h \le  |f^{(k)}| \le  \Lambda_h$ with $\Lambda_h/\lambda_h=3$. For $h=1$ and all sufficiently large stages,

$\lambda_1 m_{\mathrm{full}}^k \ge  b^{t/2}$, $\Lambda_1 \le  b^{-8r}$.     (2.4)

The first inequality uses $(k-1)!|c_{k-1}| \ge  b^{-B/16}$ and $m_{\mathrm{full}}\ge b^{r-1}$. The second uses $k\ge z+L_0+1$, $L_0\ge 11$, and the upper side of (2.2). No value of $u$ enters (2.3)-(2.4) except through constants already uniform in (W1)-(W2).

Put $Q_r=2^{D+L_1}$ and $s_t=\min(t,r)$. Choose a **separate integer Fejér cutoff at every actual offset**:

```math
H_t=\max(1,\left\lfloor b^{s_t/(8 Q_r)}\right\rfloor)
```

For $1\le h\le H_t$, $\Lambda_h\le b^{-7r}$, $\lambda_h m_{\mathrm{full}}^k\ge b^{t/2}$, and $\Lambda_h/\lambda_h=3$. Applying the growing-order derivative estimate in Appendix A to any consecutive row subinterval with more than k terms, and evaluating its absolute upper bound at $m_{\mathrm{full}}$, yields

```math
|\sum_{j \in I} \exp(2 \pi i h b^t h_u(x_j))| \le  12 m_{\mathrm{full}} b^{-s_t/Q_r} \tag{2.5}
```

Indeed the three derivative expressions are bounded by $b^{-r/2^k}$, $b^{-6r/2^k}$, and $b^{-t/2^k}$. The bound holds also for intervals with at most $k$ terms by the trivial estimate $k\le 12 m_{\mathrm{full}} b^{-s_t/Q_r}$, valid uniformly after another effective finite stage threshold. Importantly, (2.5) applies at each **actual** offset, to the **complete untruncated phase**, for all required harmonics and every incomplete consecutive row interval. No selected-row reindexing or independent digit approximation is made.

### Offset-dependent Fourier-to-words and summation

Use the endpoint-safe Fejér transfer proved in Appendix B: for $m$ circle phases $z_1,\ldots,z_m$ and any interval of length $b^{-W}$, the word error is at most

```math
\frac{2m}{\sqrt{H+1}}+\frac2\pi\sum_{h=1}^H\frac{\left|\sum_j e(hz_j)\right|}{h}
```

A word beginning at offset $t$ within a row is exactly membership of $\lbrace b^t h_u(x_j)\rbrace$ in its radix cylinder in base $b$; no digit-near-boundary implication is used. From (2.5) and the chosen $H_t$, the retained-offset word bill is

```math
\le  2m b^{-s_t/(16 Q_r)} + 8 m_{\mathrm{full}} b^{-s_t/Q_r}(1+(\log b)s_t/(8Q_r)) \tag{2.6}
```

For fixed $b\ge 2$, geometric summation over *all* offsets $TB\le t\le K-W$ gives

```math
\sum_t b^{-s_t/(16Q_r)} \le  C_b Q_r + K b^{-r/(16Q_r)}
```

```math
\sum_t b^{-s_t/Q_r}(1+s_t/Q_r) \le  C_b Q_r + K(1+r/Q_r)b^{-r/Q_r}
```

Because $Q_r=O(B_r^{1/8})=O(r^{1/16})$ and $K_r=O(r \log r)$, each final tail is $O(Q_r)$ after an effective stage threshold. Thus the total bound on any **nonempty** consecutive subbatch of $m$ rows (in particular the original initial segment of that stage) is

```math
\text{error}\le m(TB_r+W+C_bQ_r)+m_{\mathrm{full}}C_bQ_r \tag{2.7}
```

An empty subbatch contributes zero. A single incomplete final copied row is charged its actual number $z\le K_r$ of observed starts. All crossing starts are charged inside the $W$ term. Equation (2.7), rather than a batch-endpoint-only assertion, is the source of the all-prefix theorem.

### Every output prefix

For $N$ whose last digit lies in stage $r$, sum (2.7) over all completed stages and the completed portion of stage r, with only trivial $m_s K_s$ charges for the finitely many early stages preceding the analytic onset. Because $B_s$ and $D_s$ are nondecreasing, $Q_s\le Q_r$, and the full row counts grow geometrically, this gives

```math
\left|C_w(N;u)-Nb^{-W}\right|=O_{U,b,W}\!\left(b^r(B_r+Q_r+W)+K_r\right) \tag{2.8}
```

For $r\ge 3$, the preceding full stage is already part of the prefix and gives

```math
N \ge  (b-1)b^{r-2} K_{r-1} \ge  c_b b^r r D_r
```

using $D_r\le D_{r-1}+1\le 2 D_{r-1}$ and $K_{r-1}\ge (r-1)D_{r-1}$. Since $K_r=O(rD_r)$ and $Q_r=O(B_r^{1/8})=O(B_r)$, dividing (2.8) by N proves Theorem A with $O(N B_r/(rD_r))$. This argument includes all original source rows, all word lengths fixed in advance, any incomplete last stage, and any incomplete last row. The early-stage contribution is finite and uniform on $U$ when its admission constants are uniform.

For example, let $L_r$ be the least integer with $2^{L_r} \ge  r+2$ and use the unbudgeted exact-integer choice $B_r=\max(B_0,\min\lbrace m\ge 1: m^3\ge L_r\rbrace )$ and the **maximal bounded-increment** depth recurrence

$D_1=1$, $D_r=\min(D_{r-1}+1,\max(1,\left\lfloor (\log_2 B_r)/8\right\rfloor))$,

with no additional smaller F cap. This gives $D_r=\Theta(\log B_r)$ eventually and therefore the quantitative uniform rate

```math
O_{U,b,W}\!\left(\frac{N(\log\log N)^{1/3}}{\log N\,\log\log\log N}\right)
```

here all iterated logarithms are used only in the sufficiently large regime. An unspecified increasing depth merely lying below that cap need not have this rate. Using $B_r=\max(B_0,\min\lbrace m\ge 1: m^2\ge L_r\rbrace )$ with the same maximal recurrence gives the weaker but cleaner $O\!\left(\frac{N\sqrt{\log\log N}}{\log N}\right)$. The arbitrary-budget rule above can make B diverge even more slowly, with an exact profile-dependent envelope.

**Scope caution.** This theorem is proved for functions meeting (W1)-(W2). It is not a blanket theorem for all analytic functions: deliberately sparse or super-small coefficient sequences can violate the window estimate.

## 3. D-finite functions and the rational-derivative classification


**Lemma B (quantitative recurrence window).** Suppose, for every $n\ge n_0$, the sequence of Taylor coefficients satisfies

```math
q_d(n,u)c_{n+d}(u)+ \ldots + q_0(n,u)c_n(u)=0
```

where both endpoint coefficients $q_0(n,u)$ and $q_d(n,u)$ are nonzero for every indicated $n$ and $u$. Suppose $d,n_0$ are fixed on $U$, and for constants $P\ge 1$, $s\ge 0$ shared on $U$,

```math
\sum_{i=1}^d |q_i(n,u)/q_0(n,u)| \le  P(n+2)^s
```

and the initial window vector $V_{n_0}(u)=(c_{n_0}(u),\ldots,c_{n_0+d-1}(u))$ has supremum norm at least $\nu>0$ uniformly on $U$. Then for $n\ge n_0$,

```math
\max_{0\le i<d}|c_{n+i}(u)| \ge  \nu P^{-(n-n_0)} ((n+1)!)^{-s} \tag{3.1}
```

and hence (W2) holds with a uniform constant C depending on $\nu,P,s,n_0,d$, computable when effective upper bounds for P,s and a positive lower bound for nu are supplied.

**Proof.** Let $V_n=(c_n,\ldots,c_{n+d-1})$. The companion step $V_{n+1}=T_n V_n$ is invertible because both endpoint recurrence coefficients are nonzero. Its inverse shifts all but the recovered first coordinate; the first coordinate is $-\sum_{i=1}^d(q_i/q_0)c_{n+i}$. Hence $\lVert T_n^{-1}\rVert_\infty\le\max\left(1,\sum_{i=1}^d|q_i/q_0|\right)\le P(n+2)^s$. Iterating **backwards** from $V_n$,

```math
\nu\le\lVert V_{n_0}\rVert_\infty\le\left(\prod_{t=n_0}^{n-1}P(t+2)^s\right)\lVert V_n\rVert_\infty
```

which gives (3.1) by bounding the product by $((n+1)!)^s$. The factorial logarithm is at most $(n+1)\log(n+1)$, giving (W2). This proof bounds the window norm, not each coefficient; cancellations in individual coefficients are allowed. ∎

**Corollary C (real analytic D-finite derivatives).** Let $h$ be real analytic on a neighborhood of zero and suppose its derivative $h'$ is D-finite over $\mathbb R(x)$ (equivalently $h$ itself is D-finite), and $h'$ is not a polynomial. Then $h$ meets (W1)-(W2) for some finite constants. In particular Theorem A gives a computable schedule for every such $h$ once a positive rational analytic-radius lower bound is fixed; that schedule needs no recurrence computation. On a class with fixed positive common analytic radius, a single schedule can be selected **without knowing its D-finite recurrence** and works pointwise for that entire class.

**Proof.** A linear differential equation with polynomial coefficients for $h'$ induces a finite-width recurrence with polynomial coefficients in n, valid for all sufficiently large n. Remove identically zero outer coefficient polynomials and shift the recurrence so that its first and last coefficients are not identically zero. Each has only finitely many integer roots, so past a finite $n_0$ both are nonzero. For arbitrary real recurrence coefficients this cutoff is existential. Computing it requires effective coefficient bounds and certified nonzero lower bounds for the leading nonzero coefficients (or equivalent effective root-bound data); a symbolic real recurrence alone does not supply those. Effective window constants also require effective initial-vector nondegeneracy and analytic upper bounds. Ratios $q_i/q_0$ are at most a constant times $(n+2)^s$, because these are real polynomials in n, and the initial window cannot be identically zero: otherwise the nonzero leading $q_d$ forces all later coefficients to vanish and $h'$ would be polynomial. An analytic radius provides (W1) by Cauchy's estimate. For compact parameter families whose recurrence coefficients, radius and initial vector obey shared nondegeneracy and bound conditions, this argument supplies the same constants uniformly. On any class with a specified common analytic disk, the theorem's schedule uses only $b,F,G,\rho$, through $S=\max(2,2/\rho)$, so it applies pointwise even if the remaining coefficient-window constants vary arbitrarily between individual sources. Without a common disk, individual schedules may be chosen; a single fixed finite first input need not lie in every germ's domain. ∎

The D-finite hypothesis alone does **not** provide uniformity across a degenerating parameter family: the first/last recurrence coefficients or the initial window may tend to zero, and a common coefficient lower bound can fail. Composition of arbitrary D-finite functions is not asserted to be D-finite. Products of D-finite germs and algebraic substitutions in suitable analytic domains furnish standard structured examples; explicit recurrences should be checked rather than assumed.

Examples covered by Corollary C include analytic primitives of $e^x$, $\cos x$, $\log^2(1+x)$ and their nonpolynomial real linear combinations (if a combination becomes polynomial, it leaves the admitted class). For $\cos x$, every other Taylor coefficient vanishes, but the recurrence $c_{n+2}=-c_n/((n+1)(n+2))$ has an invertible two-dimensional window.

### Exact rational-derivative admission


**Corollary D (rational-derivative admission).** Let $R\in\mathbb Q(x)$ be regular at zero, and let $g(0)=0$, $g'=R$. In the complete-prefix affine-input model, some schedule normalizes $\theta+g(x_j)$ uniformly over all additive centers $\theta$ if and only if $R$ is not a polynomial. In the positive case the schedule in Theorem A meets any chosen budgets $F,G$ there.

**Proof.** A nonpolynomial rational function is D-finite and analytic on a disk about zero; so is its primitive. Corollary C and Theorem A apply. Additive centers do not change the derivative coefficients and multiply each harmonic sum at a common offset by a complex number of modulus one. Thus the discrepancy estimate is uniform in the center. A positive rational radius bound is effective from the rational numerator and denominator after cancellation: if $Q(x)=q_0+\sum_{i\ge1}q_ix^i$ with $q_0\ne0$, choose rational $0<\rho\le1$ with $\rho\sum_{i\ge1}|q_i|<|q_0|$. Then $Q$ has no zero on $|x|\le\rho$.

Conversely, if $R$ is polynomial, $g$ is a rational-coefficient polynomial of some degree $m$ (including the zero polynomial). Choose a positive integer $q$ clearing its coefficients and set the center to zero. For every row in stage $r$ and integer offset $t\ge mA_r$, the number $q b^t g(x_j)$ is an integer. Every deep source phase therefore belongs to the fixed grid $q^{-1}\mathbb Z/\mathbb Z$. Choose a fixed word length $W$ with $b^W>q$. Some canonical radix cylinder of length $W$ misses that grid, and that word never starts at any deep within-row position. The fraction of remaining positions at completed-stage endpoints tends to zero: each row loses at most $mA_r+W$ starts out of $A_rD_r$, and $D_r\to\infty$. The finitely many early rows are negligible. The omitted word has frequency zero rather than $b^{-W}$, contradicting normality. Thus center-uniform normality is impossible. $\square$

This is a function-class classification for existence of a schedule, not a classification of all schedules. The primitive $g(x)=x/(1-x)$ is admitted, despite being rational. At the same time, the inverse operation $g/(1+g)=x$ destroys admission at center zero. Arbitrary nonlinear composition therefore does not preserve the property.

## 4. Parameterized operations and exact power exceptions


For a specified parameter set U, call $\mathcal B$ **normalization-surviving for g** if some admissible common schedule makes every $Y_u$, $u \in U$, normal; call it **compact-uniformly surviving** if each prescribed compact subset has a uniform $o(N)$ bound under that same schedule. A parameter is a **structural exception** if no admissible schedule normalizes its source. **Schedule suppression** means a particular schedule produces a nonnormal output at the parameter, without asserting structural failure. **Exact cancellation** means an algebraic/functional identity eliminates high derivatives, while **near-cancellation** refers to a quantitative, observation-scale loss; the last three notions are not interchangeable.



**Theorem E (two regular powers).** In the observation model of Section 1 the following classifications hold, each with a single computable schedule independent of its parameter, normal pointwise for every listed nonexceptional real parameter and uniform on compact sets disjoint from the listed exceptions:

(i) $\mathcal B(\theta,y)=\theta^y$, $\theta>0$, $g(x)=\log(1+x)$: write $\alpha=\log \theta$, take the positive real branch; $h_\theta(x)=(1+x)^\alpha$. The exact exception set is $\theta=e^m$, $m=0,1,2,\ldots$.

(ii) $\mathcal B(\theta,y)=(1+y)^\theta$, $g(x)=x/(1-x)$ on $0<x<1$: $h_\theta(x)=(1-x)^{-\theta}$. The exact exception set is $\theta=0,-1,-2,\ldots$.

**Proof.** For (i), $h'(x)=\sum c_n x^n$ with

$c_0=\alpha$, $c_{n+1}/c_n=(\alpha-1-n)/(n+1)$.

For $\alpha$ not a nonnegative integer, $c_0\ne 0$ and no recurrence factor vanishes. The one-dimensional backward recurrence on any compact parameter set avoiding these integers supplies (W2); a common disk $|x|<1/2$ supplies (W1). For $\alpha=m\ge 0$, $(1+x)^m$ is an integer-coefficient polynomial. In every row, at offsets $t\ge m A_r$, $b^t h(x_j)$ is an integer; therefore all but $m A_r+O(W)$ of its $K_r=A_rD_r$ digit starts are strings of zeros. Since $D_r\longrightarrow \infty$, a fixed all-zero word has frequency tending to 1 at completed-stage endpoints rather than $b^{-W}$.

For (ii), $h'(x)=\theta(1-x)^{-\theta-1}$, with

$c_0=\theta$, $c_{n+1}/c_n=(\theta+n+1)/(n+1)$.

The same argument applies; at $\theta=-m$ the value $(1-x)^m$ is an integer-coefficient polynomial, with exactly the same fixed-center obstruction. The classification is exact in the sense of existence of a schedule in this model: these polynomial endpoints fail for **every** admissible schedule, not just the theorem's one. ∎

The classification concerns these explicit compositions, not an arbitrary complex or negative-base real power. Parameter $\theta$ is held fixed along each output.

## 5. Singular powers on positive inputs

**Review qualification.** The following producer proof has received targeted checks of its principal estimates. Compact-uniform control through positive integer parameters is not established.


Consider $\mathcal B(\theta,y)=y^\theta$, $g(x)=x/(1-x)$ and $x>0$. Choose the positive real branch $y^\theta=\exp(\theta \log y)$ for every real $\theta$. Then

```math
h_\theta(x)=x^\theta (1-x)^{-\theta}.
```

**Theorem F (singular powers).** There is one computable stage schedule of the form in Theorem A for which every fixed **$\theta\ne 0$** produces a normal concatenation, all original rows and cutoffs included. For compact $J$ avoiding the nonnegative integers, the discrepancy estimate of Theorem A is uniform on $J$. The positive integer parameters are also admitted by the analytic rational-derivative theorem, using the **same source schedule**, but a bound uniform while crossing those integers is not established here. At $\theta=0$ the source equals 1 and every fractional digit is zero.

**Proof on compact $J$ disjoint from nonnegative integers.** Set $u_\theta(x)=(1-x)^{-\theta}$ and $p_k(\theta)=\theta(\theta-1)\cdots(\theta-k+1)$. The quantity

```math
\delta=\min_{\substack{\theta\in J\\ \ell\in\mathbb Z_{\ge 0}}}|\theta-\ell|
```

is strictly positive. Leibniz's formula gives, for $k\ge 1$,

```math
h_\theta^{(k)}(x)=p_k(\theta) x^{\theta-k} u_\theta(x) [1+E_{k,\theta,x}],
```

where

```math
|E_{k,\theta,x}| \le  \exp(C_J k^2 x/\delta)-1.\tag{5.1}
```

To check (5.1), divide the $\ell$th Leibniz term by the $\ell=0$ term: the ratio of falling factorials contributes at most $\delta^{-\ell}$, while $u_\theta^{(\ell)}/u_\theta=(\theta)^{\overline{\ell}}(1-x)^{-\ell}$ contributes at most $(\ell+C_J)^\ell(1-x)^{-\ell}$. Together with $\binom{k}{\ell}\le k^\ell/\ell!$ the sum is bounded by an exponential in $C_J k^2 x/\delta$. Since $x\le b^{2-B_r}$ and $k\le D_r+L_1=O(\log B_r)$, it is at most 1/2 for large $r$, uniformly on $J$. Thus the derivative has one sign. The lower product satisfies $|p_k(\theta)|\ge \min(1,\delta)^k$; the upper satisfies $|p_k(\theta)|\le (k+C_J)^k$.

On the real source interval $b^{r-1}-1\le y\le b^r$, the input $x=(by+1)b^{-A_r}$ lies between $b^{-B_r-1}$ and $b^{2-B_r}$ for large $r$. Consequently the variation ratio of the $k$th derivative is at most $6 b^{3(k+C_J)}$. This is **not** a constant 3, but $\log_b$ of it is $O_J(k)=o(r)$. Taking $k=\left\lfloor t/(A_r-1)\right\rfloor+L_1$ with a sufficiently large fixed $L_1=L_1(J)$ gives $3\le k\le D_r+L_1$ for all sufficiently large $r$ and all retained $t\ge T_J B_r$. The floor gives precisely

```math
t-k r \le  -(L_1-1)r+O(D_r B_r),
```

because $\left\lfloor t/(A_r-1)\right\rfloor\ge t/(A_r-1)-1$; the stronger $-L_1 r$ is not justified. The existing large fixed $L_1$ absorbs this one-unit loss, and $D_r B_r=o(r)$. First apply the derivative estimates to harmonic 1:

```math
\lambda_1 m_{\mathrm{full}}^k \ge  b^{t/2},\qquad \Lambda_1\le b^{-8r},\qquad
\frac{\Lambda_1}{\lambda_1} \le  6b^{3(k+C_J)}.\tag{5.2}
```

The lower estimate reflects cancellation of $x^{-k}$ against the $b^{-k B}$ factor: $\log_b(\lambda_1 m_{\mathrm{full}}^k) = t - \theta B_r + O_J(k \log(k+2))$, uniformly on the interval. The upper follows from the corrected floor inequality and a sufficiently large $L_1$. Choose $0<c_J\le 1$ small enough for the derivative saving, and put

```math
H_t=\max(1,\left\lfloor b^{c_J \min(t,r)/(8\cdot 2^{D_r+L_1})}\right\rfloor)
```

Then $H_t\le b^{r/8}$, so **only for $1\le h\le H_t$** one has $\Lambda_h\le b^{-7r}$, $\lambda_h m_{\mathrm{full}}^k\ge b^{t/2}$, and the same variation ratio as in (5.2). The three terms of Appendix A are bounded by $b^{-c_J \min(t,r)/2^k}$ after decreasing $c_J$ if needed; the first ratio's polynomial in $B$ factor is paid by $m_{\mathrm{full}}\asymp b^r$. Repeating the geometric offset summation and exact all-prefix assembly in Section 2 gives $O_J(N B_r/(rD_r))$ for every fixed word.

For $\theta=m$ positive integer, $h_m(x)=x^m/(1-x)^m$ is analytic at zero and has nonpolynomial rational derivative, so its Taylor coefficients satisfy (W1)-(W2). The universal schedule from Section 2 applies without alteration, proving pointwise normality at these isolated parameters. For $\theta=0$, $h_0=1$. Hence one schedule works for the full punctured real axis; claimed compact uniformity is restricted as stated. ∎

**Important distinction.** For negative $\theta$ the input function diverges as $x\to 0$, but its **fractional part** still obeys the phase derivative argument; singularity is not a proof of failure. At a positive integer, the fractional function itself is rational and admitted, whereas its leading singular-power derivative approximation vanishes and the separate analytic proof is needed. No claim that mere nonpolynomiality of an arbitrary nonsmooth germ suffices is made.

## 6. Flat sources: suppression and rescue

**Review qualification.** These two flat-function examples retain producer-proof status, with targeted checks of the Bell estimates and derivative bounds. They are not a theorem for arbitrary smooth flat functions.


For $g(x)=x/(1-x)$, the compositions

```math
\mathcal B_1(g(x))=\frac{g(x)}{1+g(x)}=x,\qquad \mathcal B_2(g(x))=\frac1{1+g(x)}=1-x
```

are exact polynomial identities. Likewise $\exp(\log(1+x))=1+x$. For an integer-coefficient polynomial $P$, the source values have at most $\deg(P)A_r+O(W)$ potentially nonconstant starts per copied row. All these examples therefore fail in this observation model at the stated fixed center for **every** admissible schedule with $D_r\to \infty$. Invertibility and a nonzero first derivative are plainly insufficient.

**Theorem G (flat, schedule-dependent survival).** Fix $g(x)=x/(1-x)>0$ for $0<x<1$ and $\mathcal B(\theta,y)=\exp(-\theta/y)$, with real $\theta\ne 0$. There exists one computable schedule independent of $\theta$, satisfying all source limits, for which every fixed nonzero $\theta$ produces a normal output. Convergence is uniform on each compact interval avoiding zero. By contrast, under the earlier *balanced* schedule, which has $K_r=O(r \log r)$ and precision gap $B_r^{\mathrm{old}}\ge c r/\log r$ for some fixed $c>0$, the output for each fixed $\theta>0$ eventually consists entirely of zero copied rows. Thus suppression by one schedule is not impossibility for the operation.

**Proof.** The exact composite is $h_\theta(x)=\exp(\theta-\theta/x)$. Choose the following exact integer schedule, for sufficiently large $r$,

```math
B_r=3+\min\lbrace m\ge 1: b^{b^m}\ge r+4\rbrace ,\qquad A_r=r+B_r,
```

```math
D_r=\max(1,\left\lfloor (\log_2 B_r)/8\right\rfloor).
```

Use a bounded-increment smoothing of $D$ and copy $K_r=A_rD_r$ digits. The threshold comparisons involve integers only, so this schedule is computable without deciding equality of transcendental real expressions. Then $b^{B_r}=\Theta_b(\log r)$ and $D_r\to \infty$.

Write the logarithm of the source as $q(y)=\theta-\theta b^A/(by+1)$. Its first derivative is $q'(y)=\theta b^{A+1}/(by+1)^2$, of sign $\theta$, and its normalized higher derivatives satisfy

```math
\frac{|q^{(\ell)}(y)|}{|q'(y)|^\ell} \le  \ell! (C_b/(|\theta| b^{B_r}))^{\ell-1},\qquad \ell\ge 2,
```

throughout the stage, with a fixed $b$-dependent constant. Expanding $\frac{d^k}{dy^k}\exp(q)$ by the elementary Bell partition formula, the sum of terms containing an $\ell\ge 2$ block has relative magnitude at most

```math
\exp(C_b k^2/(|\theta|b^{B_r}))-1.\tag{6.1}
```

For $k\le D_r+12=O(\log B_r)$ this is below 1/2 eventually, uniformly on $\delta\le |\theta|\le M$. Hence its $k$th derivative has the sign of $\theta^k$, and is comparable to $\exp(q)|q'|^k$ by factors between 1/2 and 3/2. Since $|q|=O_{\theta,b}(b^{B_r})=O_\theta(\log r)$ and $\log_b |q'|=-r+B_r+O_{\theta,b}(1)$, with stage variation bounded by $\exp(O_\theta(b^{B_r}))=r^{O_\theta(1)}$, the explicit choice $L=10$ in

```math
k=\left\lfloor t/(A_r-1)\right\rfloor+10
```

supplies $3\le k\le D_r+10\le D_r+12$ and, for $t\ge T_\theta b^{B_r}$, the harmonic-one bounds

```math
\lambda_1 m_{\mathrm{full}}^k \ge  b^{t/2},\qquad \Lambda_1\le b^{-8r},\qquad
\log_b(\frac{\Lambda_1}{\lambda_1})=O_\theta(\log r)
```

Indeed $t-k r\le -9r+O(D_r B_r)$ and the remaining logarithmic derivative terms are $O_\theta(D_r B_r+\log r)=o(r)$, leaving the claimed $-8r$ margin. Choose $0<c\le 1$ small enough and

```math
H_t=\max(1,\left\lfloor b^{c \min(t,r)/(8\cdot 2^{D_r+12})}\right\rfloor)
```

Since $H_t\le b^{r/8}$, the upper bound $\Lambda_h\le b^{-7r}$ is asserted **only for $1\le h\le H_t$**; in that range the same variation ratio and the lower bound $\lambda_h m_{\mathrm{full}}^k\ge b^{t/2}$ hold.

The order is at most $D+12$, the growing-order estimate in Appendix A applies, and its three terms are bounded by $b^{-c \min(t,r)/2^k}$ for a fixed positive $c$ once $r$ is large. Offset-dependent Fejér cutoffs and summation as in Section 2, with $T_\theta b^{B_r}=O_\theta(\log r)$ early offsets, give the all-prefix estimate

```math
|C_w(N;\theta)-Nb^{-W}| = O_{\theta,b,W}\left(\frac{N\log r(N)}{r(N)D_{r(N)}}\right).\tag{6.2}
```

The constants and onset are uniform on compact subsets of $\mathbb R\setminus\lbrace 0\rbrace$. On the earlier balanced schedule, $x_j\le b^{2-B_r^{\mathrm{old}}}$, so $0<h_\theta(x_j)\le \exp(\theta-\theta b^{B_r^{\mathrm{old}}-2})$ for $\theta>0$. Under the two comparison bounds stated above, $K_r=O(r \log r)$ and $B_r^{\mathrm{old}}\ge c r/\log r$, so $b^{B_r^{\mathrm{old}}}/K_r\to \infty$. Hence this is eventually smaller than $b^{-K_r}$ for every row, forcing its full $K$-digit block to zero. This suppression statement is restricted to that schedule; it does not cover arbitrary copied lengths allowed to grow faster than this exponential shrinkage. At $\theta=0$ the source is the integer 1. ∎

**Reciprocal-square kernel, with the Bell estimate expanded.** For $\mathcal B(\theta,y)=\exp(-\theta/y^2)$, set

```math
z=by+1,\qquad a=b^A,\qquad v=a/z=1/x,\qquad q(y)=-\theta(v-1)^2
```

Direct differentiation of $-\theta(a^2 z^{-2}-2a z^{-1}+1)$ gives, for every $\ell\ge 1$,

```math
q^{(\ell)}=(-1)^{\ell+1} \theta \ell! b^\ell z^{-\ell} [(\ell+1)v^2-2v]
```

In particular $q'=2\theta(b/z)v(v-1)$ has sign $\theta$ when $v\ge 2$. For $\ell\ge 2$, using $2v(v-1)\ge v^2$ and $\ell+1\le 4^{\ell-1}$,

```math
\frac{|q^{(\ell)}|}{|q'|^\ell} \le  \ell! [4/(|\theta|v^2)]^{\ell-1}
\le  \ell! [C_b/(|\theta|b^{2B_r})]^{\ell-1}
```

To justify the summed Bell remainder, write $\eta=C_b/(|\theta|b^{2B_r})$. In the complete Bell partition formula the leading term is $(q')^k$. Group all other terms by their number $j$ of blocks. The normalized absolute sum is bounded by

```math
\sum_{j=1}^{k-1} \frac{k!}{j!} \binom{k-1}{j-1} \eta^{k-j}
\le  \sum_{s=1}^{k-1} \frac{(k^2\eta)^s}{s!} \le  \exp(k^2 \eta)-1
```

The coefficient in the first sum is the unsigned Lah number: it follows by taking $k!$ times the coefficient of degree $k$ in $\exp(\sum_{\ell\ge 1} \eta^{\ell-1} u^\ell)$ in a formal variable $u$. Thus the relative remainder is at most

```math
\exp(C_b k^2/(|\theta|b^{2B_r}))-1,
```

uniformly on compact parameter sets avoiding zero. This also justifies (6.1) with $\eta=C_b/(|\theta|b^{B_r})$ for the reciprocal kernel.

Choose

```math
B_r=3+\min\lbrace m\ge 1: b^{b^{2m}}\ge r+4\rbrace ,\qquad A_r=r+B_r,
```

and the same bounded-increment depth with $k\le D_r+12$. This threshold again uses integer comparisons only. Then $b^{2B_r}=\Theta_b(\log r)$, the Bell remainder tends to zero, $|q|=O_\theta(\log r)$, and $\log_b|q'|=-r+2B_r+O_\theta(1)$. The same $k=\left\lfloor t/(A_r-1)\right\rfloor+10$ gives $\Lambda_1\le b^{-8r}$ and $\lambda_1 m_{\mathrm{full}}^k\ge b^{t/2}$ after discarding $O_\theta(\log r)$ offsets; $D_r B_r=o(r)$ pays the extra $2k B_r$. With the preceding $H_t$, $\Lambda_h\le b^{-7r}$ for $1\le h\le H_t$, and the variation logarithm is $O_\theta(\log r)$. The derivative estimate, offset sum and all-prefix assembly therefore give (6.2) for this kernel as well. **This is a second flat-kernel instance, not a blanket theorem for arbitrary $C^\infty$ flat operations.**

## 7. The near-polynomial parameter scale

**Review qualification.** This producer argument has received targeted checks of its epsilon dependence, long-word obstruction and borrow convention. The parameter is fixed within each infinite output.


Here $\theta$ remains fixed along each output, but in a **triangular comparison** we may choose a different parameter for a different output cutoff $N$; these are distinct infinite outputs, not row-varying $\theta_j$. Fix a nonnegative integer $m$, a regular stage schedule in Section 2 with $K_{r-1}/K_r \to  1$, and $\alpha=m+\epsilon$ where $0<|\epsilon|\le 1/2$. Let $E(\epsilon)=\max(0,\log_b(1/|\epsilon|))$. Offsets are zero-based: offset $t$ starts at digit $t+1$, and a within-row word must satisfy $t\le K_r-W$. The sign of $\epsilon$ is held fixed when taking a sign-specific subsequence.

**Proposition H (sharp scale for this schedule).** For any family $\epsilon_N$ with $0<|\epsilon_N|\le 1/2$, the triangular word frequencies of the outputs generated from $h_{m+\epsilon_N}(x)=(1+x)^{m+\epsilon_N}$ satisfy

```math
\frac{C_w(N;m+\epsilon_N)}{N} \to  b^{-|w|}\qquad\text{for every fixed }w
```

**if and only if** $E(\epsilon_N)/K_{r(N)} \to  0$. The analogous statement holds in family (ii) with $\theta=-m+\epsilon_N$, so the actual exponent is $m-\epsilon_N$ and the source is $(1-x)^{m-\epsilon_N}$. In this convention positive $\epsilon$ again gives a positive perturbation and zero words, and negative $\epsilon$ gives borrowed $(b-1)$ words. The parameters are not allowed to vary within one output.

**Sufficient direction.** For derivatives of order $k>m$, the exact identity

```math
\frac{d^k}{dx^k} (1+x)^{m+\epsilon} = (m+\epsilon)_{\underline{k}}(1+x)^{m+\epsilon-k}
```

has magnitude bounded above and below, on $0\le x\le b^{2-B_r}$, by $|\epsilon| \exp(\pm C_m k \log(k+2))$, with the ratio of the maximum to minimum bounded uniformly when $|\epsilon|\le 1/2$ and $k$ exceeds $m+2$. Choose explicitly $L_m\ge \max(m+3,12)$ and $k=\left\lfloor t/(A_r-1)\right\rfloor+L_m$, so **every chosen derivative order exceeds $m$**, and $k\le D_r+L_m$ at all sufficiently large stages. The whole high-derivative Taylor remainder retains the $\epsilon$ factor: define

```math
R_\epsilon(x)=\frac{(1+x)^{m+\epsilon}-(1+x)^m}{\epsilon}
```

This has a uniformly bounded analytic derivative on a fixed interior disk for $|\epsilon|\le 1/2$, extending continuously at $\epsilon=0$. For every coefficient index $n\ge m$, $c_n(\epsilon)=\epsilon a_n(\epsilon)$ with $|a_n(\epsilon)|\le M_m S_m^n$. Since $k>m$, all coefficients in the derivative remainder have that form, and (2.1) becomes

```math
\left|\frac{h^{(k)}(x)}{(k-1)!}-c_{k-1}(\epsilon)\right| \le  |\epsilon| 4 M_m k S_m^k x
```

Thus the relative remainder estimate has no spurious factor $1/|\epsilon|$. Equivalently the exact derivative identity above supplies the same uniform sign and variation bounds. The growing derivative calculation in Section 2 works after discarding $O_m(B_r+E(\epsilon))$ actual offsets: take $t\ge T_m B_r+2 E(\epsilon)$ with a sufficiently large fixed $T_m$. The lower bound needed is the safe one

```math
\lambda_1 m_{\mathrm{full}}^k\ge b^{t/16}
```

The harmonic-one upper bound is $\Lambda_1\le b^{-8r}$; with an offset-dependent cutoff as in Section 2 (and a sufficiently small fixed saving constant), $\Lambda_h\le b^{-7r}$ only for $1\le h\le H_t$. Fourier and harmonic summation pay $O_m(B_r+E+2^D)$ starts per row and the same ambient-row bill. This bound is harmless even if the retained range is empty: charge the row trivially, at most the discarded-offset bill. Summing with geometric row counts gives, for all prefixes with $r$ large and $E=o(K_r)$,

```math
\frac{|C_w(N;m+\epsilon_N)-Nb^{-W}|}{N} \le  O_{m,b,W}\left(\frac{B_r}{rD_r}+\frac{E(\epsilon_N)}{K_r}\right)+o(1).\tag{7.1}
```

For family (ii), replace the numerator defining $R_\epsilon$ by $(1-x)^{m-\epsilon}-(1-x)^m$; the same analytic $\epsilon$ factor and derivative argument apply.

This uses exact phases and Fejér intervals, so **no** numerical digit-stability assumption is made near a carry boundary.

**Necessary direction and the borrow.** Let $P_m(x)=(1+x)^m$ and $\Delta=(1+x)^{m+\epsilon}-P_m(x)$. For $0<x\le 1/2$ and $|\epsilon|\le 1/2$,

```math
0<|\Delta|\le C_m |\epsilon| x,\qquad \operatorname{sgn} \Delta=\operatorname{sgn} \epsilon
```

For row $j$ in a late stage, $P_m(x_j)$ is a rational polynomial with denominator dividing $b^{m A_r}$ and $x_j\le b^{2-B_r}$. At offsets $t\ge m A_r$, $b^t P_m(x_j)$ is an integer. Fix $C_{\ast}>2+\log_b C_m$. For any actual within-row offset satisfying

```math
m A_r\le t\le K_r-W,\qquad t+W\le E(\epsilon)+B_r-C_{\ast},
```

one has $b^t P_m(x_j)$ integer and the strict bound

```math
0<b^t|\Delta|\le C_m b^{t-E+2-B_r}<b^{-W}
```

For $\epsilon>0$ the fractional part of $b^t(P_m+\Delta)$ lies in the cylinder of $W$ zeros. For $\epsilon<0$ it is $1-b^t|\Delta|$ and lies strictly inside the cylinder of $W$ digits $b-1$: this is the **borrow**, with strict endpoint slack. This proves a digit statement at a terminating rational endpoint, not a general inference from closeness of two reals. The number of forced constant-word starts per row is at least

```math
\max(0, \min(K_r,E+B_r-C_{\ast}-W)-m A_r-O(W)).\tag{7.2}
```

If $\limsup E(\epsilon_N)/K_{r(N)}>0$, pass to a sign-constant subsequence with $E\ge \rho K_r$. The regular schedule gives $N\le C_b b^r K_r$. Because $D_r\to \infty$, $m A_r=o(K_r)$, $B_r=o(K_r)$, $K_{r-1}/K_r\to 1$, and the **entire previous stage** is present at every such cutoff, (7.2) forces a positive fraction $\eta(\rho,b)>0$ of its starts to be the same constant word of any fixed length $W$. The preceding-stage proportion is bounded below independently of each fixed $W$; using $K_{r-1}/K_r\to 1$, its forced length is at least $\min(1,\rho)K_{r-1}/2$ eventually. Choosing one fixed $W$ with $b^{-W}<\eta/2$ contradicts normality. Thus $E/K_r\to 0$ is necessary. In family (ii), $\Delta=(1-x)^{m-\epsilon}-(1-x)^m$ also has sign $\epsilon$ and $0<|\Delta|\le C_m|\epsilon|x$, so the same integer-endpoint and borrow proof applies with this stated parameter convention. The proof uses a *long constant word*, not merely an excess of single zeros that might in principle be compensated elsewhere. ∎

For a **fixed** $\epsilon\ne 0$, $E$ is constant and the criterion gives survival. For $\epsilon_N$ exponentially small in $K$, a positive density of long constant blocks survives. This is a scale threshold for these specified outputs, **not** a classification of all imaginable schedules or a theorem about parameter sequences $\theta_j$ varying from row to row.

## Appendix A. Imported growing-order derivative estimate

Write $e(t)=\exp(2\pi i t)$.

Juan Arias de Reyna, *Explicit van der Corput's d-th derivative estimate*,
arXiv:2407.02094v1, 2 July 2024, Theorem 11, equation (15), and Remark 14,
equation (19):

<https://arxiv.org/html/2407.02094v1#S5.Thmtheorem11>

In the following weaker formulation all three constants are replaced by
12. If $k\ge3$ and $m>k$, and a real $C^k$ phase satisfies

```math
 0<\lambda\le f^{(k)}(x)\le\Lambda,
```

on an interval containing m consecutive integer sampling points and the
unit intervals immediately preceding them, then, putting $v=2^k$,

```math
 \left|\sum e(f(j))\right|
 \le12m\max\left\lbrace 
  (\Lambda/(\lambda m))^{2/v},\quad
  (\Lambda^2/\lambda)^{1/(v-2)},\quad
  (\lambda m^k)^{-2/v}\right\rbrace .                 \tag{V1}
```

The paper's actual constants are all below 11, uniformly in k. The
uniformity in k is essential here. A fixed-order derivative theorem
would not justify the construction. A derivative of constant negative
sign is handled by replacing f by -f.

The absolute right side of (V1) is nondecreasing as a function of m:
the three powers of m are respectively $1-2/v$, $1$, and $1-2k/v$,
all nonnegative for $k\ge3$. Thus replacing m by a larger ambient M is
valid. Short intervals $m\le k$ are handled separately by the trivial bound.
This resolves the incomplete-stage issue without a lower bound on the
sampled row count.

## Appendix B. Endpoint-safe Fourier-to-words lemma

For any $n\ge1$ circle points $z_1,\ldots,z_n$, any interval $I$, and $H\ge1$, write $F_h=\sum_{i=1}^n e(hz_i)$. Then
```math
\left|\frac{\#\lbrace i:z_i\in I\rbrace }n-|I|\right|
 \le\frac2{\sqrt{H+1}}+\frac2\pi\sum_{h=1}^H\frac{|F_h|}{hn}.
\tag{B.1}
```
This intentionally elementary version is sufficient; no sharp Erdős–Turán theorem is imported.

To prove it, use the Fejér kernel
```math
\mathcal F_H(t)=\frac1{H+1}\left|\sum_{a=0}^He(at)\right|^2.
```
It is nonnegative, has mass one, and has Fourier coefficients $1-|h|/(H+1)$ for $|h|\le H$. Since $\sin(\pi t)\ge2t$ for $0\le t\le1/2$, its mass $\alpha$ outside circle distance $\delta$ obeys
```math
\alpha\le[2(H+1)\delta]^{-1}.
```
Convolve the closed $\delta$-expansion of $I$ with $\mathcal F_H$, then add $\alpha$; convolve the open contraction, then subtract $\alpha$. These are pointwise majorant and minorant, including all endpoint conventions. Their constant terms differ from $|I|$ by at most $2\delta+\alpha$; every nonzero Fourier coefficient is at most $1/(\pi|h|)$. Integrating against the empirical measure and pairing the positive and negative frequencies gives (B.1) after taking $\delta=1/[2\sqrt{H+1}]$.

