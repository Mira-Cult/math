# Normal dovetails from analytic functions
## Coefficient windows, common schedules, and exact power exceptions

Mira-Cult research notes. Public exposition prepared 11 November 2026 from the corrected 20 October 2026 source.

**Proof manuscript.** This file gives the full producer argument for the coefficient-window theorem, its real D-finite corollary, and the exact regular-power exceptions. Its analytic dependency is stated explicitly in Appendix A. See [verification and review](VERIFICATION.md) for the precise scope of the fresh nonauthor review. This is not a formal proof or external referee acceptance, and historical priority is not claimed.

### Abstract

We concatenate the complete first $A_rD_r$ fractional radix digits of an analytic function at all affine inputs $(bj+1)b^{-A_r}$ in each stage $b^{r-1}\le j<b^r$. An exponential upper bound and a finite-window, factorial-scale lower bound on Taylor coefficients suffice for normality through every output prefix. A single computable schedule works pointwise for all nonpolynomial real D-finite germs on a common positive-radius disk. The schedule can meet any specified computable, nondecreasing, divergent overhead budgets above logarithmic input precision and copied length. Uniformity of the discrepancy estimate requires uniform coefficient-window data; uniformity of the schedule alone does not provide it.

The construction admits rational, algebraic and transcendental analytic source functions. For $(1+x)^\alpha$ the exact exceptional parameters are the nonnegative integers; for $(1-x)^{-\theta}$ they are the nonpositive integers. These are results about newly constructed digit streams, not a claim that normality implies transcendence or a normality theorem for the sampled function values or their limit.

## 1. Construction and quantifiers

Fix `b>=2`. Stage `r>=1` consists of **all** original indices `b^(r-1) <= j < b^r`. Stage parameters `A_r,D_r` are positive integers and `K_r=A_r D_r`. The source input is **exactly**

`x_j=(b j+1)b^(-A_r)`, `j` in stage `r`.

A real source value `h_theta(x_j)=B(theta,g(x_j))` is reduced modulo 1 and its first `K_r` **canonical fractional** radix digits, with terminating expansions used at ambiguous endpoints, constitute one block. Their full ordered concatenation is `Y_theta`. For a word `w` of length `W`, `C_w(N;theta)` counts the `N` starts in the *infinite* concatenation, including starts whose last `W-1` digits lie beyond `N`. Counting only starts completed by `N` differs by at most `W-1`.

A **common schedule** does not depend on `theta`; pointwise means for each fixed parameter the output is normal, while compact-uniform means a single `o(N)` error estimate with constants independent of theta in that compact set. A common schedule does NOT imply a uniform estimate over an unrestricted set containing arbitrarily near exceptional parameters. The schedule's computability does not guarantee digit computability for an arbitrary input real.

The operation acts on the parameter *inside the composition*. None of the results below transforms an already normal output to another real number.

## 2. Why a coefficient window is the right hypothesis

The arithmetic of a rational Taylor series can support fresh-prime grids, but it is not the only way to obtain cancellation. Here the phase is differentiated without truncating the source. The order of differentiation grows, so a derivative estimate with constants uniform in that order is essential.

A lower bound on every coefficient would exclude functions such as cosine. A lower bound on the largest coefficient in each fixed-width window allows zeros and cancellations. An invertible polynomial-coefficient recurrence supplies precisely this weaker condition by running the recurrence backwards. This is the mechanism behind the D-finite corollary.

Rational, algebraic and transcendental refer below to functions, not to the arithmetic type of a particular output number. Normality is not known to imply transcendence; no such implication is used here: whether any algebraic irrational is normal remains an open question.

## 3. The coefficient-window theorem

A family of real analytic germs `h_u` on a common complex disk `|x|<rho` around zero is **window admissible on a parameter set U** if, writing

`h_u'(x)=sum_(n>=0) c_n(u) x^n`, it admits a specified positive rational lower bound `rho` for the common analytic radius, numbers `M>=1`, `C>=1`, integers `d>=1`, `n0>=0`, independent of `u in U`, such that, with the shared exponential scale `S=max(2,2/rho)`:

(W1) `|c_n(u)| <= M S^n` for all `n>=0` and all `u in U`;

(W2) for every `n>=n0`,

`max_(0<=i<d) |c_(n+i)(u)| >= exp(-C(n+d+1) log(n+d+2))`.

The coefficients and the germs are real, and the Taylor expansion on the disk is the actual real source. Cauchy's estimate on the one interior disk `|x|<=rho/2` gives this shared exponential scale S; a uniform bound there supplies M in (W1). Pointwise, M may depend on the germ. The other window constants may be merely existential for qualitative statements, or computably supplied for an effective explicit onset and compact-uniform bound. No rationality hypothesis is imposed on coefficients or parameters.

**Theorem A (window admission, strong all-prefix version).** Let `h_u` satisfy (W1)-(W2) on U with the specified common analytic-radius lower bound rho. Let `F,G:positive integers -> positive integers` be computable nondecreasing functions tending to infinity. There is one computable schedule, depending only on `b,F,G,rho` and **not on u or the remaining window data**, with:

`x_j -> 0`, `D_j -> infinity`, `A_j/log_b j -> 1`,

`A_j - log_b j <= G(j)` eventually, and `K_j <= F(j) log_b j` eventually,

such that, for every fixed word `w`, uniformly in `u in U`,

`|C_w(N;u)-N b^(-W)| <= C_(U,b,W) N * B_(r(N))/(r(N) D_(r(N)))` for all sufficiently large N.  Here `r(N)` is the stage containing the last observed output digit and `B_r=A_r-r`, as defined precisely below. In particular the concatenation is normal uniformly on U. For any shared positive domain radius, the same schedule works *pointwise* for every germ having some finite data satisfying (W1)-(W2) on that common domain, even when the coefficient-window constants cannot be chosen uniformly across the germs. Without a fixed positive radius lower bound, a domain-dependent finite initial adjustment is required for each germ: a fixed early sample may be outside its domain. This adjustment leaves all eventual budgets and discrepancy bounds unchanged.

The theorem holds equally for `h_u(x)` with an additive integration constant or an additional additive center, because these only rotate each harmonic sum at a common digit offset. That observation is a proof convenience, not a replacement of `B(u,g(x))` by an additive center.

### Survival versus suppression

For a specified parameter set U, call `B` **normalization-surviving for g** if some admissible common schedule makes every `Y_u`, `u in U`, normal; call it **compact-uniformly surviving** if each prescribed compact subset has a uniform `o(N)` bound under that same schedule. A parameter is a **structural exception** if no admissible schedule normalizes its source. **Schedule suppression** means a particular schedule produces a nonnormal output at the parameter, without asserting structural failure. **Exact cancellation** means an algebraic/functional identity eliminates high derivatives, while **near-cancellation** refers to a quantitative, observation-scale loss; the last three notions are not interchangeable.

### Explicit schedule (no quantitative convergence modulus for F or G)

For `r>=2`, set (floors and maxima are exact integer operations)

`B_r=max(B0,min(floor(sqrt(r)), floor(G(b^(r-1))/4)))`, where `B0=3+ceil(log_b(4S))` and `S=max(2,2/rho)` is fixed from the common radius;

`D_1=1`,

`D_r=min(D_(r-1)+1, max(1,floor((log_2 B_r)/8)), max(1,floor(F(b^(r-1))/4)))`;

`A_r=r+B_r`, `K_r=A_r D_r`.

For stage 1 take `B_1=B0, A_1=1+B0, D_1=1` (only a finite adjustment). This ensures `x_j<=b^(2-B0)<1/(2S)` from the first row. These are nondecreasing, divergent B and D profiles, `B_r<=sqrt(r)` for all sufficiently large r, `D_r<=1+(log_2 B_r)/8`, and `2^D <= O(B^(1/8))`. The min-with-previous-plus-one guarantees `D_r<=D_(r-1)+1` and no downward jumps. For `j` in stage `r`, `log_b j` lies in `[r-1,r)`, so the two eventual budgets follow from the caps. Since `x_j<=b^(2-B_r)`, the source lies in the domain and tends to zero. Since `K_r=(r+B_r)D_r`, both `A_r/log_b j -> 1` and `K_r/log_b j -> infinity` hold, and `B_r/(rD_r)->0`.

### Uniform analytic derivative lemma

For `k>=1`, let `c_(k-1)` be a usable coefficient furnished by (W2). For `0<=x<1/S`, the Taylor remainder identity gives

`h_u^(k)(x)/(k-1)! = c_(k-1) + sum_(ell>=1) binom(k+ell-1,ell) c_(k+ell-1) x^ell`.

Therefore, if `2k S x<=1`,

`|h_u^(k)(x)/(k-1)! - c_(k-1)| <= 4 M k S^k x`.     (3.1)

This follows from the majorant `M S^(k-1)[(1-Sx)^(-k)-1]`, `-log(1-z)<=2z`, and `e^v-1<=2v` for `0<=v<=1`. Condition (W2) converts the absolute error to a relative error at most `1/2` whenever

`B_r >= B0(M,S,C,d,n0,b) + 4 C k log(k+2)`.

Only `k<=D_r+n0+2d+12=O(log B_r)` is needed, so this inequality holds for all sufficiently large r, uniformly on U. Consequently `h_u^(k)` has one fixed sign throughout every required real row interval, and lies between one half and three halves of `(k-1)! c_(k-1)` in signed magnitude. Furthermore, for every selected order,

`|log_b((k-1)! |c_(k-1)|)| <= B_r/16`      (3.2)

for all sufficiently large r. When effective upper and nonzero lower bounds for the window data are supplied, these thresholds can be found by finite integer/rational bounds. With merely existential data the thresholds are existential; the common schedule is still computable from `b,F,G,rho`. No hidden order-dependent van der Corput constant is used.

### Actual-phase Fourier calculation

Fix a late stage, abbreviate `B=B_r`, `A=r+B`, `D=D_r`, `K=AD`, `m_full=(b-1)b^(r-1)`; include a real interval containing `b^(r-1)-1 <= y <= b^r`. For the word length `W`, discard the first `T B` offsets of each copied row and the final `W-1` crossing offsets, with

`L0=n0+d+10`, `L1=L0+d+1`, `T=8(L1+1)`.

For each retained integer offset `TB<=t<=K-W`, set `z=floor(t/(A-1))`. Condition (W2) supplies some index `n` in `[z+L0,z+L0+d-1]` with `c_n != 0` and the stated lower bound; take `k=n+1`. Then

`3<=k<=D+L1`, `t-k(A-1)<=-L0(A-1)`,

`t-kB >= t(1-B/r)-L1 B >= 5t/8` for `B/r<=1/4`.     (3.3)

For harmonic `h>=1`, define the **untruncated actual phase**

`f_(t,h)(y)=h b^t h_u((by+1)b^(-A))`.

(The letter h in the subscript is a harmonic integer, not the source germ.) The chain rule and (3.1)-(3.3) give derivatives of one sign and `lambda_h <= |f^(k)| <= Lambda_h` with `Lambda_h/lambda_h=3`. For `h=1` and all sufficiently large stages,

`lambda_1 m_full^k >= b^(t/2)`, `Lambda_1 <= b^(-8r)`.     (3.4)

The first inequality uses `(k-1)!|c_(k-1)| >= b^(-B/16)` and `m_full>=b^(r-1)`. The second uses `k>=z+L0+1`, `L0>=11`, and the upper side of (3.2). No value of `u` enters (3.3)-(3.4) except through constants already uniform in (W1)-(W2).

Put `Q_r=2^(D+L1)` and `s_t=min(t,r)`. Choose a **separate integer Fejer cutoff at every actual offset**:

`H_t=max(1,floor(b^(s_t/(8 Q_r))))`.

For `1<=h<=H_t`, `Lambda_h<=b^(-7r)`, `lambda_h m_full^k>=b^(t/2)`, and `Lambda_h/lambda_h=3`. Applying the growing-order derivative estimate in Appendix A to any consecutive row subinterval with more than k terms, and evaluating its absolute upper bound at `m_full`, yields

`|sum_(j in I) exp(2 pi i h b^t h_u(x_j))| <= 12 m_full b^(-s_t/Q_r)`.     (3.5)

Indeed the three derivative expressions are bounded by `b^(-r/2^k)`, `b^(-6r/2^k)`, and `b^(-t/2^k)`. The bound holds also for intervals with `<=k` terms by the trivial estimate `k<=12 m_full b^(-s_t/Q_r)`, valid uniformly after another effective finite stage threshold. Importantly, (3.5) applies at each **actual** offset, to the **complete untruncated phase**, for all required harmonics and every incomplete consecutive row interval. No selected-row reindexing or independent digit approximation is made.

### Offset-dependent Fourier-to-words and summation

Use the endpoint-safe Fejer transfer proved in Appendix B: for `m` circle phases and any interval of length `b^(-W)`, the word error is at most

`2m/sqrt(H+1) + (2/pi) sum_(1<=h<=H) |sum e(h phase)|/h`.

A word beginning at offset `t` within a row is exactly membership of `{b^t h_u(x_j)}` in its base-`b` cylinder; no digit-near-boundary implication is used. From (3.5) and the chosen `H_t`, the retained-offset word bill is

`<= 2m b^(-s_t/(16 Q_r)) + 8 m_full b^(-s_t/Q_r)(1+(log b)s_t/(8Q_r))`.     (3.6)

For fixed `b>=2`, geometric summation over *all* offsets `TB<=t<=K-W` gives

`sum_t b^(-s_t/(16Q_r)) <= C_b Q_r + K b^(-r/(16Q_r))`,

`sum_t b^(-s_t/Q_r)(1+s_t/Q_r) <= C_b Q_r + K(1+r/Q_r)b^(-r/Q_r)`.

Because `Q_r=O(B_r^(1/8))=O(r^(1/16))` and `K_r=O(r log r)`, each final tail is `O(Q_r)` after an effective stage threshold. Thus the total bound on any **nonempty** consecutive subbatch of `m` rows (in particular the original initial segment of that stage) is

`error <= m*(T B_r+W+C_b Q_r) + m_full*C_b Q_r`.     (3.7)

An empty subbatch contributes zero. A single incomplete final copied row is charged its actual number `z<=K_r` of observed starts. All crossing starts are charged inside the `W` term. Equation (3.7), rather than a batch-endpoint-only assertion, is the source of the all-prefix theorem.

### Every output prefix

For `N` whose last digit lies in stage `r`, sum (3.7) over all completed stages and the completed portion of stage r, with only trivial `m_s K_s` charges for the finitely many early stages preceding the analytic onset. Because `B_s` and `D_s` are nondecreasing, `Q_s<=Q_r`, and the full row counts grow geometrically, this gives

`|C_w(N;u)-Nb^(-W)| <= O_(U,b,W)( b^r (B_r+Q_r+W) + K_r )`.     (3.8)

For `r>=3`, the preceding full stage is already part of the prefix and gives

`N >= (b-1)b^(r-2) K_(r-1) >= c_b b^r r D_r`,

using `D_r<=D_(r-1)+1<=2 D_(r-1)` and `K_(r-1)>=(r-1)D_(r-1)`. Since `K_r=O(rD_r)` and `Q_r=O(B_r^(1/8))=O(B_r)`, dividing (3.8) by N proves Theorem A with `O(N B_r/(rD_r))`. This argument includes all original source rows, all word lengths fixed in advance, any incomplete last stage, and any incomplete last row. The early-stage contribution is finite and uniform on U when its admission constants are uniform.

For example, let `L_r` be the least integer with `2^L_r >= r+2` and use the unbudgeted exact-integer choice `B_r=max(B0,min{m>=1: m^3>=L_r})` and the **maximal bounded-increment** depth recurrence

`D_1=1`, `D_r=min(D_(r-1)+1,max(1,floor((log_2 B_r)/8)))`,

with no additional smaller F cap. This gives `D_r=Theta(log B_r)` eventually and hence a quantitative **uniform** rate

`O_(U,b,W)(N (log log N)^(1/3)/(log N * log log log N))`;

here all iterated logarithms are used only in the sufficiently large regime. An unspecified increasing depth merely lying below that cap need not have this rate. Using `B_r=max(B0,min{m>=1: m^2>=L_r})` with the same maximal recurrence gives the weaker but cleaner `O(N sqrt(log log N)/log N)`. The arbitrary-budget rule above can make B diverge even more slowly, with an exact profile-dependent envelope.

**Scope caution.** This theorem is proved for functions meeting (W1)-(W2). It is not a blanket theorem for all analytic functions: deliberately sparse or super-small coefficient sequences can violate the window estimate.

## 4. Why invertible recurrences give the window: a complete lemma

**Lemma B (quantitative recurrence window).** Suppose, for every `n>=n0`, the sequence of Taylor coefficients satisfies

`q_d(n,u)c_(n+d)(u)+ ... + q_0(n,u)c_n(u)=0`,

where both `q_0` and `q_d` are nonzero. Suppose `d,n0` are fixed on U, and for constants `P>=1`, `s>=0` shared on U,

`sum_(i=1)^d |q_i(n,u)/q_0(n,u)| <= P(n+2)^s`,

and the initial window vector `V_(n0)(u)=(c_n0,...,c_(n0+d-1))` has supremum norm at least `nu>0` uniformly on U. Then for `n>=n0`,

`max_(0<=i<d)|c_(n+i)(u)| >= nu P^(-(n-n0)) ((n+1)!)^(-s)`,     (4.1)

and hence (W2) holds with a uniform constant C depending on `nu,P,s,n0,d`, computable when effective upper bounds for P,s and a positive lower bound for nu are supplied.

**Proof.** Let `V_n=(c_n,...,c_(n+d-1))`. The companion step `V_(n+1)=T_n V_n` is invertible because both endpoint recurrence coefficients are nonzero. Its inverse shifts all but the recovered first coordinate; the first coordinate is `-sum_(i=1)^d(q_i/q_0)c_(n+i)`. Hence `||T_n^(-1)||_infinity <= max(1,sum |q_i/q_0|) <= P(n+2)^s`. Iterating **backwards** from V_n,

`nu <= ||V_(n0)|| <= (prod_(t=n0)^(n-1) P(t+2)^s)||V_n||`,

which gives (4.1) by bounding the product by `((n+1)!)^s`. The factorial logarithm is at most `(n+1)log(n+1)`, giving (W2). This proof bounds the window norm, not each coefficient; cancellations in individual coefficients are allowed. QED.

**Corollary C (real analytic D-finite derivatives).** Let `h` be real analytic on a neighborhood of zero and suppose its derivative `h'` is D-finite over `R(x)` (equivalently `h` itself is D-finite), and `h'` is not a polynomial. Then `h` meets (W1)-(W2) for some finite constants. In particular Theorem A gives a computable schedule for every such `h` once a positive rational analytic-radius lower bound is fixed; that schedule needs no recurrence computation. On a class with fixed positive common analytic radius, a single schedule can be selected **without knowing its D-finite recurrence** and works pointwise for that entire class.

**Proof.** A linear differential equation with polynomial coefficients for `h'` induces a finite-width recurrence with polynomial coefficients in n, valid for all sufficiently large n. Remove identically zero outer coefficient polynomials and shift the recurrence so that its first and last coefficients are not identically zero. Each has only finitely many integer roots, so past a finite n0 both are nonzero. For arbitrary real recurrence coefficients this cutoff is existential. Computing it requires effective coefficient bounds and certified nonzero lower bounds for the leading nonzero coefficients (or equivalent effective root-bound data); a symbolic real recurrence alone does not supply those. Effective window constants also require effective initial-vector nondegeneracy and analytic upper bounds. Ratios `q_i/q_0` are at most a constant times `(n+2)^s`, because these are real polynomials in n, and the initial window cannot be identically zero: otherwise the nonzero leading `q_d` forces all later coefficients to vanish and `h'` would be polynomial. An analytic radius provides (W1) by Cauchy's estimate. For compact parameter families whose recurrence coefficients, radius and initial vector obey shared nondegeneracy and bound conditions, this argument supplies the same constants uniformly. On any class with a specified common analytic disk, the theorem's schedule uses only `b,F,G,rho`, through `S=max(2,2/rho)`, so it applies pointwise even if the remaining coefficient-window constants vary arbitrarily between individual sources. Without a common disk, individual schedules may be chosen; a single fixed finite first input need not lie in every germ's domain. QED.

The D-finite hypothesis alone does **not** provide uniformity across a degenerating parameter family: the first/last recurrence coefficients or the initial window may tend to zero, and a common coefficient lower bound can fail. Composition of arbitrary D-finite functions is not asserted to be D-finite. Products of D-finite germs and algebraic substitutions in suitable analytic domains furnish standard structured examples; explicit recurrences should be checked rather than assumed.

Examples covered by Corollary C include analytic primitives of `e^x`, `cos x`, `log^2(1+x)` and their nonpolynomial real linear combinations (if a combination becomes polynomial, it leaves the admitted class). For `cos x`, every other Taylor coefficient vanishes, but the recurrence `c_(n+2)=-c_n/((n+1)(n+2))` has an invertible two-dimensional window.

## 5. Exact classifications for the regular power centers

**Theorem D (two regular powers).** In the observation model of Section 1 the following classifications hold, each with a single computable schedule independent of its parameter, normal pointwise for every listed nonexceptional real parameter and uniform on compact sets disjoint from the listed exceptions:

(i) `B(theta,y)=theta^y`, `theta>0`, `g(x)=log(1+x)`: write `alpha=log theta`, take the positive real branch; `h_theta(x)=(1+x)^alpha`. The exact exception set is `theta=e^m`, `m=0,1,2,...`.

(ii) `B(theta,y)=(1+y)^theta`, `g(x)=x/(1-x)` on `0<x<1`: `h_theta(x)=(1-x)^(-theta)`. The exact exception set is `theta=0,-1,-2,...`.

**Proof.** For (i), `h'(x)=sum c_n x^n` with

`c_0=alpha`, `c_(n+1)/c_n=(alpha-1-n)/(n+1)`.

For `alpha` not a nonnegative integer, `c_0!=0` and no recurrence factor vanishes. The one-dimensional backward recurrence on any compact parameter set avoiding these integers supplies (W2); a common disk `|x|<1/2` supplies (W1). For `alpha=m>=0`, `(1+x)^m` is an integer-coefficient polynomial. In every row, at offsets `t>=m A_r`, `b^t h(x_j)` is an integer; therefore all but `m A_r+O(W)` of its `K_r=A_rD_r` digit starts are strings of zeros. Since `D_r->infinity`, a fixed all-zero word has frequency tending to 1 at completed-stage endpoints rather than `b^(-W)`.

For (ii), `h'(x)=theta(1-x)^(-theta-1)`, with

`c_0=theta`, `c_(n+1)/c_n=(theta+n+1)/(n+1)`.

The same argument applies; at `theta=-m` the value `(1-x)^m` is an integer-coefficient polynomial, with exactly the same fixed-center obstruction. The classification is exact in the sense of existence of a schedule in this model: these polynomial endpoints fail for **every** admissible schedule, not just the theorem's one. QED.

The classification concerns these explicit compositions, not an arbitrary complex or negative-base real power. Parameter `theta` is held fixed along each output.

## 6. Exact admission in the rational-derivative class

**Corollary H.** Let $R\in\mathbb Q(x)$ be regular at zero, and let $g(0)=0$, $g'=R$. In the complete-prefix affine-input model, some schedule normalizes $\theta+g(x_j)$ uniformly over all additive centers $\theta$ if and only if $R$ is not a polynomial. In the positive case the schedule in Theorem A meets any chosen budgets $F,G$ there.

**Proof.** A nonpolynomial rational function is D-finite and analytic on a disk about zero; so is its primitive. Corollary C and Theorem A apply. Additive centers do not change the derivative coefficients and multiply each harmonic sum at a common offset by a complex number of modulus one. Thus the discrepancy estimate is uniform in the center. A positive rational radius bound is effective from the rational numerator and denominator after cancellation: if $Q(x)=q_0+\sum_{i\ge1}q_ix^i$ with $q_0\ne0$, choose rational $0<\rho\le1$ with $\rho\sum_{i\ge1}|q_i|<|q_0|$. Then $Q$ has no zero on $|x|\le\rho$.

Conversely, if $R$ is polynomial, $g$ is a rational-coefficient polynomial of some degree $m$ (including the zero polynomial). Choose a positive integer $q$ clearing its coefficients and set the center to zero. For every row in stage $r$ and integer offset $t\ge mA_r$, the number $q b^t g(x_j)$ is an integer. Every deep source phase therefore belongs to the fixed grid $q^{-1}\mathbb Z/\mathbb Z$. Choose a fixed word length $W$ with $b^W>q$. Some canonical radix cylinder of length $W$ misses that grid, and that word never starts at any deep within-row position. The fraction of remaining positions at completed-stage endpoints tends to zero: each row loses at most $mA_r+W$ starts out of $A_rD_r$, and $D_r\to\infty$. The finitely many early rows are negligible. The omitted word has frequency zero rather than $b^{-W}$, contradicting normality. Thus center-uniform normality is impossible. $\square$

This is a function-class classification for existence of a schedule, not a classification of all schedules. The primitive $g(x)=x/(1-x)$ is admitted, despite being rational. At the same time, the inverse operation $g/(1+g)=x$ destroys admission at center zero. Arbitrary nonlinear composition therefore does not preserve the property.

## Appendix A. Imported growing-order derivative estimate

Write $e(t)=\exp(2\pi i t)$.

Juan Arias de Reyna, *Explicit van der Corput's d-th derivative estimate*,
arXiv:2407.02094v1, 2 July 2024, Theorem 11, equation (15), and Remark 14,
equation (19):

<https://arxiv.org/html/2407.02094v1#S5.Thmtheorem11>

In the following weaker formulation all three constants are replaced by
12. If k>=3, m>k, and a real C^k phase satisfies

\[
 0<\lambda\le f^{(k)}(x)\le\Lambda,
\]

on an interval containing m consecutive integer sampling points and the
unit intervals immediately preceding them, then, putting v=2^k,

\[
 \left|\sum e(f(j))\right|
 \le12m\max\left\{
  (\Lambda/(\lambda m))^{2/v},\quad
  (\Lambda^2/\lambda)^{1/(v-2)},\quad
  (\lambda m^k)^{-2/v}\right\}.                 \tag{V1}
\]

The paper's actual constants are all below 11, uniformly in k. The
uniformity in k is essential here. A fixed-order derivative theorem
would not justify the construction. A derivative of constant negative
sign is handled by replacing f by -f.

The absolute right side of (V1) is nondecreasing as a function of m:
the three powers of m are respectively `1-2/v`, `1`, and `1-2k/v`,
all nonnegative for k>=3. Thus replacing m by a larger ambient M is
valid. Short intervals m<=k are handled separately by the trivial bound.
This resolves the incomplete-stage issue without a lower bound on the
sampled row count.

## Appendix B. Endpoint-safe Fourier-to-words lemma

For any \(n\ge1\) circle points \(z_1,\ldots,z_n\), any interval \(I\), and \(H\ge1\), write \(F_h=\sum_{i=1}^n e(hz_i)\). Then
\[
\left|\frac{\#\{i:z_i\in I\}}n-|I|\right|
 \le\frac2{\sqrt{H+1}}+\frac2\pi\sum_{h=1}^H\frac{|F_h|}{hn}.
\tag{B.1}
\]
This intentionally elementary version is sufficient; no sharp Erdős–Turán theorem is imported.

To prove it, use the Fejér kernel
\[
\mathcal F_H(t)=\frac1{H+1}\left|\sum_{a=0}^He(at)\right|^2.
\]
It is nonnegative, has mass one, and has Fourier coefficients \(1-|h|/(H+1)\) for \(|h|\le H\). Since \(\sin(\pi t)\ge2t\) for \(0\le t\le1/2\), its mass \(\alpha\) outside circle distance \(\delta\) obeys
\[
\alpha\le[2(H+1)\delta]^{-1}.
\]
Convolve the closed \(\delta\)-expansion of \(I\) with \(\mathcal F_H\), then add \(\alpha\); convolve the open contraction, then subtract \(\alpha\). These are pointwise majorant and minorant, including all endpoint conventions. Their constant terms differ from \(|I|\) by at most \(2\delta+\alpha\); every nonzero Fourier coefficient is at most \(1/(\pi|h|)\). Integrating against the empirical measure and pairing the positive and negative frequencies gives (B.1) after taking \(\delta=1/[2\sqrt{H+1}]\).

