# Nearby prime targets with an exact total

This is the full analytic component of the [eventual-existence proof](proof.md).
It constructs prime row and column targets with an exact total and prescribed
residues, and individual diagonal targets near the same center. The
[controller theorem](controller.md#u-the-centered-universal-controller)
realizes these targets using the prescribed entries. The main note states
[the result and its status](README.md#what-is-proved).

For the final specialization, $`p_j`$ denotes the $`j`$-th prime with $`p_1=2`$,
$`P_n=\{p_2,\ldots,p_{n^2+1}\}`$, and $`T_n=\sum_{p\in P_n}p`$.
Labels A1–A4 refer to the statements below.

## Source used and the fixed-system boundary

**MMS.** Kaisa Matomäki, James Maynard and Xuancheng Shao, *Vinogradov's theorem
with almost equal summands*, arXiv:1610.02017v2, 13 March 2017,
[versioned PDF](https://arxiv.org/pdf/1610.02017v2),
published in Proceedings of the London Mathematical Society (3) 115 (2017),
323–347, DOI [10.1112/plms.12040](https://doi.org/10.1112/plms.12040).
The exact locators used are Theorem 2.1 and its proof on printed pages 5–6,
Proposition 3.1, and the verification of Theorem 2.1's hypotheses in Section 5.

The published headline theorem concerns three primes with no prescribed
individual residues. We derive the fixed-modulus variant A1 from its proof;
we do not silently read extra conclusions into that headline statement.
All analytic applications still have exactly three variables. The growing
number of targets in A3 is handled by an elementary balancing argument.

Here is the analytic contract from MMS in the notation needed below. Fix an
exponent $`\vartheta>11/20`$, sufficiently small $`\epsilon>0`$, and any fixed
$`\eta_0>0`$. Put



```math
h=x^\vartheta,\quad I=[x-h/3,x+h],\quad
 W=\prod_{p\le 0.1\log\log x}p.
```



MMS supplies a nonnegative prime majorant $`\rho^+\ge1_{\mathbb P}`$, constants
$`\alpha^+<2.9`$, $`\alpha^-=0.99`$, and the following facts for all sufficiently
large $`x`$:



```math
\left|\sum_{\substack{m\in I\\m\equiv c\pmod W}}
 \left(\rho^+(m)-\frac{\alpha^+W}{\varphi(W)\log x}\right)e(m\gamma)
 \right|\le\frac{\eta_0h}{\varphi(W)\log x}
 \qquad ((c,W)=1,\ \gamma\in\mathbb R).                 \qquad\text{(A.1)}
```



For every subinterval $`J\subseteq I`$ of length at least
$`x^{\vartheta-\epsilon}`$ and every reduced class $`a\pmod d`$ with
$`d\le\log x`$,



```math
\#\{p\in J:p\equiv a\pmod d\}
 \ge\frac{\alpha^-|J|}{\varphi(d)\log x}.               \qquad\text{(A.2)}
```



The normalized prime functions in its $`W`$-progressions satisfy an
$`L^{5/2}`$ Fourier restriction bound with constant $`O(1)`$, as used explicitly
in the proof of Theorem 2.1 (including its footnote concerning coefficients
up to the square of the progression length). Proposition 3.1 then gives
positive triple convolution when each normalized function has density
greater than $`1/3`$ on every progression of a fixed positive relative length,
its majorant has arbitrarily small relative Fourier error, and that
restriction bound holds. The margin
$`\alpha^-/\alpha^+>0.99/2.9>1/3`$ is fixed.

The quantifiers in these imports are essential: $`\vartheta,\epsilon,\eta_0`$
are fixed before $`x\to\infty`$. We only add a modulus bounded independently
of $`x`$. We make no assertion of uniformity for arbitrary growing moduli or
for a growing number of simultaneous prime forms.

## A1. Almost-equal ternary primes in prescribed fixed classes

**Statement.** Fix an even integer $`q\ge2`$ and an exponent
$`\vartheta>11/20`$. There is $`M_0(q,\vartheta)`$ such that, whenever $`M\ge M_0`$
is an odd integer and $`a_1,a_2,a_3\in(\mathbb Z/q\mathbb Z)^\times`$ satisfy



```math
a_1+a_2+a_3\equiv M\pmod q,
```



there are primes $`p_1,p_2,p_3`$ such that



```math
p_i\equiv a_i\pmod q,\qquad p_1+p_2+p_3=M,\qquad
 |p_i-M/3|\le M^\vartheta.
```



The modulus need not be squarefree. For $`q`$ in a fixed finite set, one may
take a common threshold. Repeated primes are permitted.

**Proof.** It suffices to treat $`11/20<\vartheta<1`$; larger exponents follow
from any smaller one in that interval. In the analytic contract set $`x=M/3`$.
Define



```math
V=\mathrm{lcm}(q,W),\qquad d_0=V/W.
```



For sufficiently large $`x`$, every prime divisor of $`q`$ divides $`W`$, so



```math
d_0\mid q,\qquad \frac{\varphi(V)}V=\frac{\varphi(W)}W,
 \qquad \varphi(V)=d_0\varphi(W).                       \qquad\text{(A.3)}
```



In particular $`d_0`$ is bounded. We check the three parts of the MMS
transference proof after replacing $`W`$ by $`V`$.

**Fourier error after imposing prime powers.** For any reduced class
$`b\pmod V`$, let $`c=b\pmod W`$. Within that $`W`$-class, the identity



```math
1_{m\equiv b\ (V)}
 =\frac1{d_0}\sum_{j=0}^{d_0-1}e\!\left(\frac{j(m-b)}V\right)           \qquad\text{(A.4)}
```



restricts to the requested $`V`$-class. Apply (A.1) at each shifted frequency
$`\gamma+j/V`$ and average. The error stays at most
$`\eta_0h/(\varphi(W)\log x)`$, which by (A.3) is



```math
\frac{d_0\eta_0h}{\varphi(V)\log x}.                  \qquad\text{(A.5)}
```



The main term has the correct normalization, since $`W/\varphi(W)=V/\varphi(V)`$.
The cost is the displayed bounded factor $`d_0`$ when measured relative to one
$`V`$-progression. We choose $`\eta_0`$ smaller by a factor depending on $`q`$;
we do not insert a congruence mask for free.

**Lower density on progressions.** Let $`P`$ be an arithmetic progression
in the normalized interval $`[L]`$ with $`|P|\ge\eta L`$, where $`\eta>0`$ is
the fixed transference parameter. Its step $`s`$ is at most $`2/\eta`$ for
large $`L`$. Its image in the integers is a progression of modulus $`Vs`$.
Every prime divisor of $`s`$ divides $`W`$ once $`x`$ is sufficiently large.
Moreover $`V\le q(\log x)^{1/5}`$ eventually, so $`Vs\le\log x`$.
The image is reduced, since the chosen $`b`$ is reduced modulo $`V`$ and all
prime divisors of $`s`$ already divide $`V`$. Its span has length
$`Vs(|P|-1)\gg_\eta h`$, hence is at least $`x^{\vartheta-\epsilon}`$.
Applying (A.2) and using



```math
\varphi(Vs)=s\varphi(V)
```



shows that the normalized prime function has average at least
$`\alpha^-/\alpha^+-o(1)>1/3`$ on $`P`$. This pays both the prime-power issue
and the extra small progression step.

**Restriction norm.** One may use the same linear-form restriction estimate
as MMS: its coefficient size condition remains valid because
$`L\asymp h/V`$ and $`x=o(L^2)`$ when $`\vartheta>1/2`$.
There is also a direct bounded-cost deduction from the original
$`W`$-progression estimate. A $`V`$-progression is a residue subsequence of a
$`W`$-progression of length $`L_0=d_0L+O(1)`$. If $`f(j)=F(d_0j+a)`$, additive
orthogonality gives



```math
\widehat f(\gamma)=\frac1{d_0}\sum_{r=0}^{d_0-1}
 e\!\left(\frac{a(\gamma+r)}{d_0}\right)
 \widehat F\!\left(\frac{\gamma+r}{d_0}\right).          \qquad\text{(A.6)}
```



With the convention $`\widehat F(\xi)=\sum_mF(m)e(-m\xi)`$, this identity
is exact. Jensen's inequality and a change of variables yield



```math
\|\widehat f\|_{5/2}\le\|\widehat F\|_{5/2}
 \ll L_0^{3/5}\ll_q L^{3/5}.                           \qquad\text{(A.7)}
```



The normalizing factors for $`F`$ and $`f`$ are identical by (A.3).
Discarding a bounded number of endpoints adds only $`O(\log x)`$ to these
norms. This is $`o(L^{3/5})`$. The majorant's endpoint errors are also
negligible: its explicit formula (5.1) involves three prime divisors
larger than $`x^{1/10}`$, so it is bounded by an absolute constant on $`I`$.
The restriction constant may depend on the fixed $`q`$, as allowed when
choosing the transference error tolerance.

**Compatible lifted residues and the target.** We choose
$`b_i\in(\mathbb Z/V\mathbb Z)^\times`$ lifting $`a_i\pmod q`$ and satisfying
$`b_1+b_2+b_3\equiv M\pmod V`$. At prime powers dividing $`q`$ the prescribed
classes already satisfy the condition. At every prime $`\ell\mid W`$ with
$`\ell\nmid q`$, choose three nonzero residues with sum $`M\pmod\ell`$.
Such a triple exists for every odd $`\ell`$: choose a nonzero first residue,
then a second residue different from zero and from the value that would
force the third to vanish. There are at most two excluded choices, and
for $`\ell=3`$ the same argument still leaves a choice among the three
residues. The prime 2 already divides $`q`$. The Chinese remainder theorem
combines these choices, including all prime powers in $`q`$.

For a precise endpoint convention put



```math
m=\left\lfloor\frac{x-h/3}{V}\right\rfloor,\qquad
 L=\left\lfloor\frac{x+h}{V}\right\rfloor-m-1,
```



and take representatives $`0\le b_i<V`$. All integers
$`V(m+j)+b_i`$, $`1\le j\le L`$, lie in $`I`$. Define



```math
f_i(j)=\frac{\log x}{\alpha^+}\frac{\varphi(V)}V
           1_{\mathbb P}(V(m+j)+b_i),
```



with analogous majorants using $`\rho^+`$. The checks above are precisely
the hypotheses of MMS Proposition 3.1. The required normalized target is



```math
\ell_0=\frac{M-b_1-b_2-b_3}{V}-3m
       =\frac hV+O(1),\qquad L=\frac{4h}{3V}+O(1).
```



Thus $`\ell_0\in[L/2,L]`$ for sufficiently large $`x`$. Positive triple
convolution gives indices summing to $`\ell_0`$, hence primes summing
exactly to $`M`$. They lie in $`I`$, so
$`|p_i-M/3|\le(M/3)^\vartheta\le M^\vartheta`$.
Only bounded residue filtering and one fixed triple convolution were used.
This proves A1. ∎

## A2. Bracketing primes in every requested class

**Statement.** Fix even $`q\ge2`$ and $`\theta>11/20`$. For every sufficiently
large real $`\mu`$ and every reduced residue $`a\pmod q`$, there are primes
$`p_a^-<\mu<p_a^+`$ in that class with



```math
|p_a^\pm-\mu|\le\mu^\theta.
```



**Proof.** Choose $`11/20<\vartheta<\min(\theta,1)`$. Set
$`D=\mu^\theta`$ if $`\theta<1`$; it is enough to prove this case, since it
implies larger exponents. Choose integers $`M^\pm\equiv a+2\pmod q`$
within $`q`$ of $`3(\mu\pm D/2)`$. They are odd. Apply A1 to the prescribed
classes $`(a,1,1)`$ and totals $`M^\pm`$. The first prime satisfies



```math
p_a^\pm=\mu\pm D/2+O(q)+O(\mu^\vartheta).
```



As $`\vartheta<\theta`$, the last two terms have magnitude below $`D/4`$
for large $`\mu`$. These primes therefore lie strictly on the requested
sides and within distance $`D`$. The finitely many classes are uniform. ∎

## A3. Prime vectors with exact total, uniformly in their length

**Statement.** Fix an even modulus $`q\ge2`$ and
$`11/20<\theta<1`$. There is $`\mu_0(q,\theta)`$ such that the following holds
for **every** integer $`k\ge3`$. Let $`T`$ be an integer with $`\mu=T/k\ge\mu_0`$,
and let $`a_1,\ldots,a_k`$ be reduced classes modulo $`q`$ with



```math
\sum_{i=1}^k a_i\equiv T\pmod q.
```



Then there are primes $`t_1,\ldots,t_k`$, not necessarily distinct, with



```math
t_i\equiv a_i\pmod q,\qquad
 \sum_{i=1}^k t_i=T,\qquad
 |t_i-\mu|\le\mu^\theta\quad(1\le i\le k).             \qquad\text{(A.8)}
```



The threshold is independent of $`k`$. It can also be made uniform for all
even $`q\le Q`$, with $`Q`$ fixed.

**Proof.** Put $`D=\mu^\theta`$. For each requested class obtain the two
bracketing primes from A2. For the first $`k-3`$ indices, choose the lower
prime if the cumulative discrepancy



```math
E_j=\sum_{i\le j}(t_i-\mu)
```



is nonnegative before the choice; otherwise choose the upper prime.
Starting at $`E_0=0`$, induction gives $`-D\le E_j\le D`$ at every step.
Indeed the new increment lies in $`[-D,0]`$ when the previous discrepancy
is nonnegative, and in $`[0,D]`$ when it is negative. This is a deterministic
one-dimensional rule; its error does not grow with the number of indices.

The remaining integer is



```math
M=T-\sum_{i\le k-3}t_i=3\mu-E_{k-3}.
```



It satisfies $`|M-3\mu|\le D`$ and the congruence for the last three classes.
Since all reduced classes modulo the even $`q`$ are odd, the original
congruence implies $`T\equiv k\pmod2`$. Subtracting $`k-3`$ odd primes makes
$`M`$ odd. For large $`\mu`$, $`M\asymp\mu`$ and exceeds the threshold in A1.

Choose $`11/20<\vartheta<\theta`$ and apply A1 to this residual total and
the last three classes. Each final prime differs from $`\mu`$ by at most



```math
\frac D3+M^\vartheta\le D
```



for all sufficiently large $`\mu`$. Together with the first choices this
proves (A.8). Every threshold depends only on $`q,\theta`$, not on $`k`$.
Taking a maximum over the finite set of moduli gives the last assertion. ∎

This lemma does not ask that the primes $`t_i`$ belong to the entry pool.
They are prospective **line totals**, for which the original problem permits
repetition and permits equality with an entry. The exact entry pool remains
unchanged by this analytic lemma.

## A4. Consequence at the initial-prime-pool scale

Write $`X_n=p_{n^2+1}`$ and $`\mu_n=T_n/n`$. For any fixed $`Q`$ and any fixed
$`11/20<\theta<2/3`$, all sufficiently large odd $`n`$ have the following
property: for every even $`q\le Q`$ and every reduced residue vector
$`(a_1,\ldots,a_n)`$ with sum $`T_n\pmod q`$, there is a vector of prime
totals with exact sum $`T_n`$ and maximum distance from $`\mu_n`$ at most
$`\mu_n^\theta=o(X_n)`$.

**Proof.** The prime number theorem gives
$`X_n\sim2n^2\log n`$ and, by partial summation,
$`T_n\sim n^4\log n`$. Hence $`\mu_n\sim n^3\log n`$ and



```math
\frac{\mu_n^\theta}{X_n}
 \asymp n^{3\theta-2}(\log n)^{\theta-1}\longrightarrow0.
                                                                  \qquad\text{(A.9)}
```



Apply A3 with $`k=n`$. For example $`\theta=3/5`$ is sufficient. ∎

The same fixed-modulus bracketing result supplies an individual diagonal
prime in any reduced class modulo $`2q`$ within $`o(X_n)`$ of a desired center
of order $`\mu_n`$. Row and column target vectors can each be chosen by A3
because each has the same required total $`T_n`$. Array realization is supplied
separately by [Theorem U](controller.md#u-the-centered-universal-controller).
