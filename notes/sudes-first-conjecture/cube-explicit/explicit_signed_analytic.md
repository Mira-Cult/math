# Explicit logarithmic prime windows for the signed cube

Public proof manuscript. See [provenance](../PROVENANCE.md#explicit-prime-cube) for the pinned sources, internal review and verification limits.

## 1. Frozen sources and the obstruction being replaced

The qualitative source is `a2445962ec6e06b2a893980fb7a183057eb9bcee`,
delivered at `cdb7879e358f93afa54b685027a27692d22635a9`. Its literal
short-window use is Thorner--Zaman, *Refinements to the prime number theorem
for arithmetic progressions*, [arXiv:2108.10878v2](https://arxiv.org/pdf/2108.10878v2),
Section 1.2, together with Remark 1.2 and (1.6). The polylogarithmic-modulus
improvement to exponent `7/12` uses Siegel's ineffective bound. Increasing
a number does not turn a long-interval error `exp(-c sqrt(log X))` into an
error smaller than `X^-epsilon` for a fixed positive epsilon. The original
power windows are therefore not retained by this analytic replacement.

The effective inputs below are the frozen square derivations at scientific
revision `f519b7fd796393cd6ab202f6790fe1824e6fc22f`, with independent-review
delivery `b776784e3cffc3aeeb3c3c6886516c3337a16bd1`. Their complete public proof counterparts are linked below; raw source
hashes are recorded in the provenance of Manuscript III.
In dependency order the relevant manuscripts are:

1. [effective_pair_supply](../classical-primes.md), E1 and the **corrected primitive-character**
   E2 proof, including its historical normalization correction;
2. [cutoff_analytic_optimization](../optimized/cutoff_analytic_optimization.md), the retained totient normalization;
3. [cutoff_analytic_refinement](../optimized/cutoff_analytic_refinement.md) and [cutoff_linear_window_analytic](../optimized/cutoff_linear_window_analytic.md),
   intermediate signed errors and endpoint envelopes;
4. [cutoff_relaxed_height_analytic](../optimized/cutoff_relaxed_height_analytic.md), the parameterized zero-sum proof;
5. [cutoff_constant_window_analytic](../optimized/cutoff_constant_window_analytic.md), Sections 2.1--2.2, retaining the
   integral factors `1/pi` and the different exceptional signs.

The present proof reuses those finite analytic formulas, not their square
cutoff or their constant target radius. All specialized inequalities below
are re-evaluated for inverse powers of logarithms.

Primary sources inspected in this continuation are:

- Bennett--Martin--O'Bryant--Rechnitzer (BMOR), *Explicit bounds for primes
  in arithmetic progressions*, Illinois J. Math. 62 (2018), 427--532,
  [author-hosted journal text](https://personal.math.ubc.ca/~gerg/papers/downloads/EBPAP.pdf):
  Proposition 1.11, printed p.436; Definition 6.1; the parameter definitions
  (6.20), Lemmas 6.8--6.9 and their proofs, pp.499--501; Lemma 6.11, p.503.
- McCurley, *Explicit estimates for the error term in the prime number
  theorem for arithmetic progressions*, Math. Comp. 42 (1984), 265--285,
  [publisher text](https://www.ams.org/mcom/1984-42-165/S0025-5718-1984-0726004-6/S0025-5718-1984-0726004-6.pdf),
  (3.24), (3.31)--(3.36), and (3.39)--(3.40), pp.276--280. Direct PDF
  retrieval initially failed; the indexed publisher text subsequently
  supplied these displayed formulas and their surrounding proofs.
- Rosser--Schoenfeld (RS62), *Approximate formulas for some functions of
  prime numbers*, Illinois J. Math. 6 (1962), 64--94,
  [scanned original](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf),
  printed p.69, Theorem 2, Corollary 1, and the corollary to Theorem 3.

No downloaded-byte hash or new computational verification of these
published papers is asserted. Their stated computational inputs remain
analytic imports. The exact repository sources, by contrast, have raw
SHA-256 bindings in the certificate.

## 2. A finite family of analytic interfaces

Let `b` be an integer with `0<=b<=100` and let `d` be a positive integer
at most `10^12`. These are a logarithmic exponent and a length denominator,
not a cube order or the target-list radius. Write


```math
u=\log Y,\qquad \ell=\lceil\log_2Y\rceil,\qquad
 H=c-a\ge\frac{Y}{d u^b},\qquad (a,c]\subset[Y/2,2Y].       \qquad\text{(A1)}
```


For a specified integer `U>=10000`, choose a rational number


```math
0\lt \alpha\lt \sqrt{\frac{U-1}{R_1U}},\qquad R_1=9.645908801.
                                                                    \qquad\text{(A2)}
```


The certificate chooses a downward square-root bracket on a `10^-12`
grid and subtracts one further grid unit. Define the continuous envelopes


```math
\begin{split}
 Q_w(u)&=1024u^2,& B_w(u)&=\log(1024u^2),\\
 Q_s(u)&=128u,& B_s(u)&=\log(128u),\\
 f_j(u)&=2Q_j(u)(0.32181\alpha\sqrt u+4)e^{-\alpha\sqrt u},\\
 r(u)&=2^{21}u^5e^{-u}+2^{12}u^2e^{-u/2}.                 \qquad\text{(A3)}
\end{split}
```


**Finite weak interface AW.** Suppose the weak checks in Section 6 hold
at `U`, including


```math
2d B_w(U)^2 U^b\,[f_w(U)+r(U)]\lt 1.                       \qquad\text{(A4)}
```


Then for every real `u>=U`, every integer `1<=q<=512u^2`, every reduced
class modulo `q`, and every interval (A1), the number of primes is at least


```math
\boxed{\frac{H}{4q\ell^9}}.                             \qquad\text{(AW)}
```


**Finite strong interface AS.** Suppose the strong checks in Section 6
hold at `U`, including


```math
4d U^b\,[f_s(U)+r(U)]\lt 1.                               \qquad\text{(A5)}
```


Then for every real `u>=U`, every integer `1<=q<=64u`, every reduced
class modulo `q`, and every interval (A1), the number of primes is at least


```math
\boxed{\frac{H}{2\varphi(q)\log(2Y)}}.                  \qquad\text{(AS)}
```


The conclusions are uniform over the interval endpoints, the modulus and
class, all target-dependent centers satisfying the displayed hypotheses,
and the entire real scale tail. A closed interval inherits the half-open
count. A different endpoint convention must pay its endpoint loss; neither
subtraction of theta values nor the certificate silently drops that cost.

These interfaces imply the literal FL counts: `q<=128ell^2` implies
`q<=512u^2` because `ell<=2u` here. AS implies `H/(4g ell)` for the
original even `g` whenever `g<=64u`, since `phi(g)<=g` and
`log(2Y)<=2ell`. The controller and target manuscript establish these
inequalities at their actual, possibly shifted centers.

## 3. Signed errors and reduced-class lifting

For an even `Q>=100000`, put `nu=sqrt(log x/R1)`. Retain the possible
exceptional zero and its real character in


```math
M_{Q,A}(x)=\frac{x-\chi_\beta(A)x^\beta/\beta}{\varphi(Q)}.
                                                                    \qquad\text{(A6)}
```


Omit the exceptional term when there is no such zero. The frozen square
source CW5 proves, on `exp(nu)/Q>=100000`,


```math
|\theta(x;Q,A)-M_{Q,A}(x)|\le
 0.32181x\nu e^{-\nu}
 +\frac{sQxe^{-\nu}}{\varphi(Q)}
 +2\log Q\log x+Q\log Q+2\sqrt x,                       \qquad\text{(A7)}
```


where `s=2` if the exceptional term is absent or `chi_beta(A)=1`,
and `s=4` if `chi_beta(A)=-1`. In particular the favorable-sign error is
at most twice the adverse-sign error. There is no claim that coefficient
2 works for both signs.

The proof's normalization matters. If `chi*` is the primitive inducing
character, it uses


```math
\psi(t,\chi)=\psi(t,\chi^*)-
 \sum_{p\mid Q,\ p\nmid\mathrm{cond}\,(\chi^*)}
       \sum_{p^j\le t}\chi^*(p)^j\log p.                 \qquad\text{(A8)}
```


The removed prime powers and the nonspectral primitive remainder are
paid in (A7). The zero-counting integral keeps the primitive conductor
inside its two-sided counting estimate until integration by parts has
finished. Only the resulting one-sided bounds are majorized using `Q`.
The coefficient `0.32181` follows by retaining `1/pi` in the low and high
zero integrals, with the explicit epsilon allowances in the frozen proof;
it is not obtained by dividing an already combined error by pi. The
reflected exceptional zero is included among the paid ordinary terms.

For this application we impose the stronger original-domain condition


```math
\log x\ge4R_1(\log Q)^2.                               \qquad\text{(A9)}
```


It implies `nu>=2logQ`, hence `exp(nu)/Q>=Q>=100000`.
The certificate also checks `log x>500log10`, retaining the literal
BMOR proper-prime-power domain. Thus the expanded height domain of the
square campaign is not needed to obtain a lower numerical cube floor.

Given any original `q>=1`, multiply by the smallest power of 2 making
`Q` both even and at least 100000. If `q` is already even and large,
take `Q=q`; if `q` is odd and large, take `Q=2q`. Otherwise `Q<200000`.
It follows pointwise that `Q<=Q_w(u)` in AW and `Q<=Q_s(u)` in AS.

The map from units modulo `Q` to units modulo `q` is onto and every
fiber has size `phi(Q)/phi(q)`. The only additional prime divisor is 2,
below the interval. Hence the primes in an original reduced class
partition exactly into those lifted reduced classes. Multiplying their
summed error by `phi(q)` yields the factor `phi(Q)`, with
`phi(Q)<=Q/2`. This handles odd FL moduli as well as the even seed gap.

For every endpoint `x` in (A1), `log x>u-1`; (A2) yields
`nu>alpha sqrt(u)` throughout the tail. The function `nu exp(-nu)`
decreases here. Since `a+c<=4Y`, the adverse exponential error at both
endpoints, multiplied by `phi(Q)` and divided by `Y`, is bounded by
`f_j(u)`. For the nonspectral terms the same normalization gives at most


```math
2QB_j(u)(u+1)+Q^2B_j(u)+3Q\sqrt Y.
```


Using `Q<=1024u^2`, `B_j(u)<u`, and `u>=1` bounds this by
`2^21u^5+2^12u^2 sqrt(Y)`. After division by `Y` it is (A3)'s
`r(u)`. All endpoints and the full weak modulus are charged before
specialization to any concrete request.

## 4. The exceptional zero leaves enough main term

BMOR Proposition 1.11, valid for every quadratic character modulo `Q`,
gives


```math
1-\beta\ge\frac{40}{\sqrt Q\log^2Q}.                  \qquad\text{(A10)}
```


For AW, use `sqrt(Q)<=32u`, `log Q<=B_w(u)`, and `u>=25`. Thus at
every `t` in the interval,


```math
(1-\beta)\log t\ge\frac{6/5}{B_w(u)^2}.
```


The inequality `1-exp(-z)>=z-z^2/2`, applied to that lower bound,
and `B_w(u)^2>4` imply


```math
1-t^{\beta-1}\ge\frac{1}{B_w(u)^2}.                  \qquad\text{(A11)}
```


Indeed `6/5-(36/25)/8>1`. Thus the adverse main increment is at least
`H/[phi(Q) B_w(u)^2]`. Condition (A4) pays an adverse error less than
half this amount. In the favorable case the main derivative is at least
`1/phi(Q)` and the error is at most doubled. The same remaining
`H/[2phi(Q)B_w(u)^2]` follows because `B_w(u)^2>4`. The absent case is
also stronger. These comparisons are made separately in each lifted
class before summing them.

After summation and division by `log(2Y)`, the retained count is


```math
\frac{H}{2\varphi(q)B_w(u)^2\log(2Y)}.
```


It dominates AW: `B_w(u)<u`, `log(2Y)<2u`, `ell>=u`, and
`phi(q)<=q` show that its denominator is at most `4q u^3`, whereas
`4q ell^9>=4q u^9`.

For AS, `sqrt(Q)<12sqrt(u)` and `log Q<=B_s(u)`. The exact base
comparison


```math
40(U-1)\gt 24\sqrt U\,B_s(U)^2                           \qquad\text{(A12)}
```


persists because `(1-1/u)sqrt(u)/B_s(u)^2` increases when `B_s(u)>4`.
It makes the exceptional exponent exceed 2. Since `exp(2)>4`, the
adverse main derivative is greater than `3/[4phi(Q)]`. Condition (A5)
pays less than `H/[4phi(Q)]`, leaving the desired half main term. For
the favorable sign, the main is at least `H/phi(Q)` and the error is
less than `H/[2phi(Q)]`. Summing lifted classes and dividing by the
maximum prime weight proves AS.

## 5. Exact-pool location and a sharper mean

Let `N` be any positive integer, `X=p_(N+1)`, and let `T` be the sum
of exactly the first `N` odd primes. Set `m=T/N` and `L=log X`.
These definitions include the cube case `N=n^3` without a new pool.

**Mean lemma AM.** If `L>=1000`, then


```math
\boxed{\frac{12}{25}X\lt m\lt \frac{501}{1000}X}.             \qquad\text{(A13)}
```


In particular `|m-X/2|<X/24`. The upper bound is the frozen square
mean lemma MR, whose proof uses only `N=pi(X)-1`, and therefore transfers
literally to this pool. Here is the exact partial-summation formula:


```math
I=\int_2^X\pi(t)\,dt,\qquad T=X(N+1)-I-2.              \qquad\text{(A14)}
```


Using RS62 `pi(t)>t/log t` from `sqrt X` to `X` gives
`I>(X^2-X)/(2L)`. The term `I-X+2` is positive here. Combined with
`N<X/(L-3/2)`, it gives


```math
\frac mX\lt \frac12+\frac{3}{4L}+(L+1/2)e^{-L}
 \lt \frac{501}{1000}.                                    \qquad\text{(A15)}
```


The last comparison is checked at 1000 and persists termwise.

For a lower bound, split (A14)'s integral at `z=X/L^2`.
The bound `pi(t)<=t` below `z` and RS62
`pi(t)<t/(log t-3/2)` above `z` yield


```math
I\le\frac{X^2}{2L^4}
       +\frac{X^2}{2(L-2\log L-3/2)}.                   \qquad\text{(A16)}
```


Here `z>exp(3/2)`, as required by the literal RS62 domain. Since
`log L/L<=1/100` for `L>=1000`, the second denominator is at least
`97L/100`. Also `X>=1000L`, and the lower pi bound gives
`N>X/L-1>=999X/(1000L)`. Because `X-2>0`, (A14) now implies


```math
\frac mX\gt 1-\frac{1000}{999}
             \left(\frac1{2L^3}+\frac{50}{97}\right)
 \gt \frac{12}{25}.                                       \qquad\text{(A17)}
```


The rational comparison at `L=1000` proves the last inequality, which
then improves as `L` increases. In the cube case (A13) also gives
`12nX/25<mu<501nX/1000` and the corresponding bounds for `T=n^3m`.
The final composition supplies its explicit `X` versus `n` envelopes.

For midpoint windows
`I_±=[m±X/6-delta X,m±X/6+delta X]`, (A13) and `delta<=1/48`
place both intervals inside `[X/4,3X/4]`. Their centers are greater
than `X/4`, not equal to `X`. Thus their local logarithms are at least
`L-log4`; this loss is included when AS is consumed. The central
growth interval `[X/4,3X/4]` has local center `X/2` and log `L-log2`.
All controller primes are odd and no larger than `X`, so these
supplies preserve the exact prescribed input pool.

## 6. Certification and all larger real scales

In addition to (A4) or (A5), the program checks:

- the original source domain `U-1>4R1 B_j(U)^2`, proper-prime-power
  domain, and `B_j(U)>4`, so `(u-1)/B_j(u)^2` increases;
- (A2), `alpha sqrt(U)>1`, and the pointwise modulus-lift envelopes;
- (A11) or (A12), including the increasing strong exceptional envelope;
- the derivatives controlling the entire tail.

For AW, the logarithmic derivative of its exponential comparison,
multiplied by `u`, is at most


```math
b+\frac52+\frac4{B_w(u)}-\frac{\alpha\sqrt u}{2}.
                                                                    \qquad\text{(A18)}
```


For AS the corresponding expression is at most
`b+3/2-alpha sqrt(u)/2`. The program verifies that each is negative
at `U`; the displayed upper bounds decrease thereafter. The two weak
remainder comparisons decrease when
`u>b+5+4/B_w(u)` and `u/2>b+2+4/B_w(u)`; the strong ones need only
`u>b+5` and `u/2>b+2`. These too are checked at `U` and persist.
Thus the proof differentiates continuous majorants only. Every actual
integer modulus, power-of-two lift, and dyadic ceiling obeys those
majorants pointwise; no derivative is taken across an integer jump.

All certification uses standard-library integers and fractions. Logarithms
use range reduction and the positive atanh series with an explicit
geometric remainder. Square roots use integer-square-root bracketing.
Exponentials use positive Taylor sums after reduction to `[0,1]`, an
explicit tail, and outward dyadic rounding after each squaring. The two
tiny normalized remainders are each bounded by `2^-128`, using exact
integer bit-length inequalities and `exp(u)>2^u` at the integer base.
The derivative proof concerns the actual exponential functions, not these
auxiliary base-point integer bounds.

The arithmetic verification searches the sufficient integer floors and
checks the immediately preceding integer separately. This is a limit of the displayed sufficient estimates, not a counterexample
to prime supply and not a lower bound for the prime-cube conjecture.
The complete cutoff certificate binds its chosen profile and all local
requests separately; an attractive component floor is not a cube cutoff.

