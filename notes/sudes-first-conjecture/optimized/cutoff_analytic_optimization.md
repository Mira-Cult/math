# Signed progression increments at the scales actually used

## Scope, status, and sources

These are manuscript-local results for the cutoff
campaign. They preserve the public proof and the scientific source
`c2118dfad1aeb660d66308dc6a94d6c959f5010c`. Independent review must name the
exact new scientific revision; successful arithmetic is not that review.

This note uses the **corrected primitive-character** proof E2 in
[effective_pair_supply.md](../classical-primes.md), whose SHA-256 is
`70b1e235b91885882afedd2e206df8f59e0064bf8923a6d9d3937ebe1a2a7c4d`.
Its imports remain BMOR and MCC84 as pinned in [REFERENCES.md](../REFERENCES.md).
In particular, the identity is
`psi(t,chi)=psi(t,chi*)-J_chi(t)`: the deleted Euler-factor prime powers are
explicitly paid. The imprimitive-zero substitution rejected in the recovery
record is not used.

The BMOR journal PDF was inspected for Proposition 1.11 (printed p.436),
Lemma 6.10 (p.501), Lemma 6.11 and Lemma 6.12 (pp.503–504), and Proposition
6.16 with all of (6.23) (p.506); the last page was also visually checked.
The exact source is [the author-hosted journal PDF](https://personal.math.ubc.ca/~gerg/papers/downloads/EBPAP.pdf).
The MCC84 primary PDF returned HTTP 403 in this run; the primitive derivation
and prior source inspection are the preserved E2 dependency, not a newly
claimed independent reconstruction of McCurley's paper. BMOR's stated
computational inputs remain imported.

All logarithms in this note are natural, except explicit `log_2`. Put


```math
u=\log Y,\qquad \ell=\lceil\log_2Y\rceil,
\qquad R_1=9.645908801,\qquad \alpha=8/25.
```


The two scales below are deliberately different. The small macro scale is
used for entry reservoirs. The larger target scale is used only at
`y=T/n`, whose logarithm grows about three times `log n`.

## 1. Recover the normalization before discarding it

**N2.** For even `Q>=100000` and `x>=exp(4 R_1(log Q)^2)`, write
`v=sqrt(log x/R_1)` and retain the signed exceptional main term `M_{Q,a}`
defined in E2. Then


```math
|\theta(x;Q,a)-M_{Q,a}(x)|\le
 2xv e^{-v}+\frac{10Qx e^{-v}}{\varphi(Q)}
 +2\log Q\log x+Q\log Q+2\sqrt x.                 \qquad\text{(N2)}
```


**Proof.** E2's proof, immediately after (E2.3), pays the principal and
exceptional smoothing shifts by `5h/phi(Q)`, with
`h=2Qx exp(-v)`. It then replaces `10Qx exp(-v)/phi(Q)` by the larger
`10Qx exp(-v)`. Retaining the former term gives (N2), with every other
normalization, zero sum, nonspectral remainder, and prime-power bound
unchanged. The signed exceptional term is retained through the two positive
averages exactly as in the corrected proof. This is a strengthening of its
conclusion by recovering an already proved intermediate bound, not a claim
that BMOR itself states N2. The factor `phi(Q)` is essential below.

For an even modulus `q<100000`, multiply by a power of two to obtain
`100000<=Q<200000`; otherwise take `Q=q`. A reduced class modulo `q`
partitions into `d=phi(Q)/phi(q)` reduced classes modulo `Q` throughout
`[Y/2,2Y]`. The only possible excluded prime is 2, which is below this
interval. In particular, after multiplying the summed errors by `phi(q)`,
the factor is **phi(Q)**, not an independent product of worst-case bounds
for `d` and `phi(q)`. Since `Q` is even, `phi(Q)<=Q/2`.

The logarithm series used by the verifier gives
`69/100<log 2<7/10`. For `u>=10000` it follows, with strict room for the
ceiling, that


```math
\ell\le\frac32(u-1),\qquad \log(2Y)\le\ell,
 \qquad \log x\gt u-1,\quad \log x\lt u+1\lt 2u.              \qquad\text{(N3)}
```


Also `R_1 alpha^2<1-1/10000`, so every endpoint has
`v>=alpha sqrt(u)`. The function `v exp(-v)` decreases for `v>1`.

## 2. Weak target windows with a much denser supply

**AW.** Suppose `u>=80000`, `q` is even,
`2<=q<=128ell^2`, and `(a,q)=1`. Every real interval `(b,c]` inside
`[Y/2,2Y]` of length


```math
H\ge\frac{Y}{2\ell^4}
```


contains at least


```math
\boxed{\frac{H}{qF}},\qquad
 F=\ell\bigl(7+2\lceil\log_2\ell\rceil\bigr)^2          \qquad\text{(AW)}
```


primes congruent to `a mod q`. This is uniform in every larger real `Y`,
all listed moduli and residues, and all such intervals.

**Source domain.** The lifted modulus satisfies `Q<=128ell^2<=288u^2`.
Set `L=6+2log u`. Since `log 288<6`, `log Q<L`. The exact base
comparison `79999>40 L(80000)^2` and the positive derivative of
`(u-1)/L^2` prove


```math
\log x\gt u-1\ge40L^2\gt 4R_1(\log Q)^2                   \qquad\text{(AW1)}
```


on the entire tail. Thus N2 is in its original domain.

**Signed main increment.** Write `B=log(128ell^2)`, so
`log Q<=B<L`, and use `sqrt Q<12ell`. If an exceptional zero exists,
BMOR Proposition 1.11 and (N3) give, for every point `t` in the interval,


```math
(1-\beta)\log t\ge\frac{40(u-1)}{\sqrt Q(\log Q)^2}
 \gt \frac{20}{9B^2}\gt \frac2{B^2}.                         \qquad\text{(AW2)}
```


Since `B^2>=2` and `1-exp(-z)>=min(z/2,1/2)`, the unfavorable
exceptional sign still leaves


```math
M'_{Q,a}(t)\ge\frac1{\varphi(Q)B^2}.                 \qquad\text{(AW3)}
```


No exceptional zero, or the other sign, only increases this lower bound.
Summing the lifted classes produces main increment at least
`H/[phi(q)B^2]`.

**All normalized errors.** Multiplying the two endpoint errors, summed
over lifted classes, by `phi(q)`, bounds the exponential part by


```math
4QY\bigl(\alpha\sqrt u+10\bigr)e^{-\alpha\sqrt u}
 \le576Yu^{5/2}e^{-\alpha\sqrt u}.                     \qquad\text{(AW4)}
```


Here `b+c<=4Y`, `phi(Q)<=Q/2`, and
`alpha sqrt u+10<=sqrt u/2`. This is where retaining the denominator in
N2 avoids the old quadratic modulus cost. The two polynomial remainders
are at most `85000u^5`: use
`4Q L u+Q^2 L<=1152u^4+82944u^5<=85000u^5`, with `L<=u`.
The square-root remainders total less than `3Q sqrt Y<=864u^2 sqrt Y`.
Thus the full normalized error divided by `Y` is bounded by


```math
A(u)=576u^{5/2}e^{-\alpha\sqrt u}
       +85000u^5e^{-u}+864u^2e^{-u/2}.                  \qquad\text{(AW5)}
```


It is enough to prove `4ell^4 L^2 A(u)<1`. The ceiling-free majorant is


```math
11664u^{13/2}L^2e^{-\alpha\sqrt u}
 +1721250u^9L^2e^{-u}
 +17496u^6L^2e^{-u/2}\lt 1.                               \qquad\text{(AW6)}
```


The exact rational certificate bounds the left side at `u=80000` by
`0.347691642416` (this decimal is an upward enclosure).
The logarithmic derivative of the first term is
`[(13/2)+4/L-alpha sqrt(u)/2]/u`, which is negative already at the
base. The other derivatives are negative when `u>9+4/L` and
`u/2>6+4/L`; both conditions hold throughout the tail. This proves
(AW6) for every larger `u`, without differentiating `ell` across its jumps.

The total error is less than `H/[2phi(q)L^2]`, hence at most
`H/[2phi(q)B^2]`. Subtraction from (AW3) and division by `log(2Y)`
leave at least `H/[2phi(q)B^2 log(2Y)]` primes.
If `j=ceil(log_2 ell)`, then
`B=(7+2log_2ell)log2<(7/10)(7+2j)` and `log(2Y)<=ell`.
Since `2(7/10)^2<1`, the count is at least the quantity (AW).
This last comparison could also use `phi(q)<=q/2`; the weaker displayed
integer `F` is convenient and sufficient.

## 3. Strong entry-reservoir and target windows

**AS-macro.** If `u>=10000`, `q` is even, `2<=q<=32ell`,
and `(a,q)=1`, then every `(b,c]` inside `[Y/2,2Y]` of length
`H>=Y/50000` contains at least


```math
\frac{H}{2\varphi(q)\log(2Y)}                         \qquad\text{(AS)}
```


primes in that reduced class.

**AS-target.** The same conclusion holds for `u>=80000` and the smaller
window requirement `H>=Y/(2ell^4)`.

**Proof.** After the same power-of-two lift, `Q<=48u` (including
`Q<200000` when needed). Put `L_1=4+log u`; then `log Q<L_1`.
The certificate checks


```math
u-1\gt 40L_1^2,\qquad
 \frac{40(u-1)}{7\sqrt u\,L_1^2}\gt 2                    \qquad\text{(AS1)}
```


at `u=10000`. The first persists because `(u-1)/L_1^2` increases.
For the second, write its variable part as
`(1-1/u)sqrt(u)/L_1^2`. Both factors increase: the second has positive
logarithmic derivative when `L_1>4`. Since `sqrt48<7`, the exceptional
exponent is greater than 2. The signed main derivative therefore exceeds
`3/[4phi(Q)]`, using `exp(2)>4`.

The normalized exponential error improves (AW4) to
`96Yu^(3/2) exp(-alpha sqrt u)`. The same two harmless remainder bounds
in (AW5) remain valid. For AS-macro, multiply these by `200000`: the
exact certificate gives total less than `0.243151978543` at `u=10000`.
Every term decreases thereafter; for the first this requires only
`alpha sqrt u/2>3/2`. Thus the normalized error is less than `H/4`.
Subtracting it from the signed main increment gives at least
`H/[2phi(q)]` in theta weight, proving (AS).

For AS-target, multiply the error by `8ell^4`, bounded using
`ell<=3u/2`. The three terms are


```math
3888u^{11/2}e^{-\alpha\sqrt u}
 +3442500u^9e^{-u}+34992u^6e^{-u/2}.                    \qquad\text{(AS2)}
```


Their sum is less than 1 at `u=80000` by the certificate, and each
decreases thereafter. This again leaves the required half main term.

## 4. A useful optimization inside Proposition 6.16

Before changing the analytic architecture, the old parameter choice itself
can be improved. For the same `Z=8`, take


```math
\kappa_1=1/5,\quad\kappa_2=2^{17},\quad\kappa_3=128.
```


The verifier encloses every logarithm and square root in the three original
conditions (6.23) by rational intervals and checks them directly. For
`t=log x>=2^29` and `100000<=Q<=64t`, the source-scale condition follows from


```math
\sqrt t\ge\frac85(\log64+\log t)^3.
```


It holds at `2^29` and persists because
`sqrt(t)/(log64+log t)^3` increases once `log64+log t>6`.
The remaining thresholds `kappa_2,kappa_3` are smaller. Thus Proposition
6.16 gives its original error `x/[4(log x)^8]` on this endpoint domain.
This removes roughly ten binary orders from the previous endpoint-log
floor, but remains much weaker than the signed-increment route above.
It is a proved parameter experiment, not the active input to AW or AS.

The reason is structural: suppressing the exceptional contribution at each
endpoint separately pays a `sqrt(Q)(log Q)^3` threshold. Keeping its sign
through the interval instead pays only its still-positive derivative.
Retaining the original smoothing normalization independently removes another
factor of the modulus in the error comparison. Neither operation assumes the
absence of an exceptional zero.

## 5. Reproduction, exact arithmetic, and composition boundary

Executable replay details are recorded in [Provenance](../PROVENANCE.md#optimized-bound).

The implementation uses only integers and fractions. Natural logarithms use
range reduction and an atanh series with a positive rational tail; square
roots use integer-square-root bracketing; exponentials need only positive
Taylor lower sums. The exponentially small remainders are bounded using
`exp(u)>2^u` at integer base points. The continuous majorants above handle
all ceiling jumps, modulus changes, interval endpoints and larger real scales.

The code checks the exact corrected E2 source hashes and finite inequalities.
It does not reprove BMOR/MCC84, kernel-check E2 or this analysis, verify actual
prime counts by enumeration, or assert a complete square theorem. The
controller must separately supply its gap bound, full reservation accounting,
centering, routing and diagonal independence. The target construction must
consume the exact density `F` and check its finite integer hypotheses.
The full composition must translate `log(m-X/4)>=10000` and
`log y>=80000` separately back to `n`; an analytic scale cutoff is not an
order cutoff.

[Manuscript index](../README.md) · [Optimized theorem](../optimized-bound.md) · [Source and review record](../PROVENANCE.md#optimized-bound)
