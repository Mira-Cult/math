# Constant target windows with the original integral factors retained

This is additive to the frozen
[height-domain extension](cutoff_relaxed_height_analytic.md), denoted ZH0.
It preserves all earlier analytic profiles. Its
[rational certificate](../PROVENANCE.md#optimized-bound) binds
ten required source files and calls ZH0's finite checks. The statements
here supply primes and an upper bound for their mean; the complete square
theorem, exact permutation, diagonals, and order conversion are separately
composed with the finite controller and target construction.

## 1. The selected analytic profile

All logarithms are natural unless a base is displayed. Set


```math
u=\log Y,\qquad \ell=\lceil\log_2Y\rceil,\qquad
 F=\ell\bigl(7+2\lceil\log_2\ell\rceil\bigr)^2.
```


**CW-target.** For every real `Y` with


```math
\boxed{\log Y\ge8990},\qquad D=Y/1370,
```


every even `2<=q<=(369/1000)ell^2`, every reduced class modulo `q`,
and every half-open real interval `(b,c]` inside `[Y-D,Y+D]` of length
`H>=D/2`, there are at least


```math
\boxed{H/(qF)}                                      \qquad\text{(CW1)}
```


primes in that class. For even `2<=q<=ell`, the same interval has the
stronger count


```math
\boxed{H/[2\varphi(q)\log(2Y)]}.                     \qquad\text{(CW2)}
```


**CW-macro.** For every real `Y` with


```math
\boxed{\log Y\ge5982},
```


every even `2<=q<=ell`, every reduced class modulo `q`, and every
half-open interval `(b,c]` inside `[Y/2,2Y]` satisfying


```math
b+c=2Y,\qquad H=c-b\ge\frac{500}{6241273}Y,
```


the count is at least the quantity in CW2. These statements cover their
entire real scale tails, including every ceiling, modulus, and lift change.

The macro length is the exact ratio needed by the selected bin parameters:
with `A_bin=29092` and `eta=6007/7000`, it is `2Y/(eta A_bin)`.
The controller must establish that each actual bin has this length and that
its own center lies above the macro scale floor.

## 2. The source factors and signed smoothing

The primary sources, with their inherited imports and status, are those
listed in ZH0. Two specific locators are essential for this further change:
[McCurley, printed pp.278–280](https://www.ams.org/mcom/1984-42-165/S0025-5718-1984-0726004-6/S0025-5718-1984-0726004-6.pdf),
(3.34) and (3.36), and the corresponding unsimplified Stieltjes integrals
in his proofs of Lemmas 3.7–3.8. The later displayed BMOR integrals had
already replaced `1/pi` by a larger constant. We return to the
parameterized calculation, with the conductor normalization and
exceptional-pair treatment checked in ZH0, to retain those factors.

Write `nu=sqrt(log x/R)`, `R=9.645908801`, and
`mathcal H=exp(nu)/Q`, where `Q>=100000` and `mathcal H>=100000`.
Thus `nu>23`. Every nonintegral epsilon term has the same bound already
proved in ZH0.

### 2.1. Retain `1/pi` in both integrals

The low-zero integral is at most


```math
\frac1{2\pi}\int_1^{\mathcal H}
     t^{-1}e^{-\nu^2/\log(Qt)}\log(Qt)\,dt
 <\frac{\nu e^{-\nu}}{2\pi}.                         \qquad\text{(CW3)}
```


For high zeros, the actual two integrals before combination are


```math
\frac{C_1}{2}\int_{\mathcal H}^\infty
      t^{-4}e^{-\nu^2/\log(Qt)}dt
 +\frac1{2\pi}\int_{\mathcal H}^\infty
      t^{-3}e^{-\nu^2/\log(Qt)}\log(Qt/(2\pi))dt.
```


Since `C_1 pi/t<log(2pi)` for `t>=100000`, their sum is less than
the integral in ZH6 divided by `pi`. ZH0's elementary integration by
parts therefore bounds its normalized contribution by
`(1+1/(2nu))/(2pi)`. This step retains the original factor while
absorbing the `C_1` integral explicitly; it does not divide an already
combined error bound by `pi`.

For an exact elementary enclosure of the circular constant, use


```math
\pi=4\arctan(1/2)+4\arctan(1/3).
```


The tangent addition identity and the angles' ranges prove the identity.
Sixteen terms of each alternating arctangent series, with the next term
as remainder bound, prove `3.14159<pi<4`. Also `log(2pi)>1`, using
`exp(1)<3<2pi`. With ZH0's other epsilon allowances, the complete
low- and high-zero coefficients are consequently less than, respectively,


```math
\frac1{2(3.14159)}+12\cdot10^{-6}<0.159168,
 \qquad
 \frac{1+1/46}{2(3.14159)}+11\cdot10^{-6}<0.162628.
```


The smoothing factors at `mathcal H>=100000` give


```math
\begin{split}
 &0.159168(1+2/\mathcal H)\\
 &\quad+0.162628(1+6/\mathcal H+18/\mathcal H^2+20/\mathcal H^3)
 <\boxed{0.32181}.                                   \qquad\text{(CW4)}
 \end{split}
```


Each positive height correction decreases, and the base inequality is
rationally certified. The primitive-character remainder and omitted prime
powers are unchanged. In particular the identity remains
`psi(t,chi)=psi(t,chi*)-J_chi(t)` with its explicit allowance.

### 2.2. Distinguish the two exceptional signs

If an exceptional zero exists, let `epsilon=chi_beta(a)` and write
`M(t)=[t-epsilon t^beta/beta]/phi(Q)`. For a reduced class,
`epsilon` is either 1 or -1. If `epsilon=1`, then


```math
0<M'(t)=\frac{1-t^{\beta-1}}{\varphi(Q)}<\frac1{\varphi(Q)}.
```


The positive double average displaces `M` by at most `h/phi(Q)`,
because its mean displacement is `h`. This also holds if there is no
exceptional zero. As `h=2Qx exp(-nu)`, the smoothing contribution in
these cases is `2Qx exp(-nu)/phi(Q)`.

For the favorable sign `epsilon=-1`, the derivative lies between
`1/phi(Q)` and `2/phi(Q)`. Its smoothing allowance remains
`4Qx exp(-nu)/phi(Q)`, and its main increment is at least
`H/phi(Q)`. Thus there is no universal error bound with coefficient 2.
The two valid error bounds are


```math
E_s(x)=0.32181x\nu e^{-\nu}
 +\frac{sQxe^{-\nu}}{\varphi(Q)}
 +2\log Q\log x+Q\log Q+2\sqrt x,                    \qquad\text{(CW5)}
```


with `s=2` for the adverse or absent exceptional zero and `s=4` for
the favorable sign. We have `E_4<=2E_2`.

For weak supply, let `A/B^2` be the lower adverse main derivative used
below. The certificate checks `2A<B_0^2<=B^2`. If the adverse error
is below `(A-1/2)H/[phi(Q)B^2]`, the favorable error is below twice
that amount; subtracting it from `H/phi(Q)` still leaves more than
`H/[2phi(Q)B^2]`. The no-exceptional-zero case is also stronger than
the adverse one. For strong supply, the adverse main is at least
`3H/[4phi(Q)]`. An adverse error below `H/[4phi(Q)]` leaves half
the main, whereas the favorable error is below `H/[2phi(Q)]` and
its main is at least `H/phi(Q)`. The desired half main therefore
survives in every class. These comparisons are made per lifted class
before the classes are summed, so differing exceptional signs cause no
independence assumption.

## 3. A closer lift for small moduli

For every even `q>=2`, set


```math
Q=q\left\lceil\frac{100000}{q}\right\rceil.           \qquad\text{(CW6)}
```


Then `Q>=100000`, `Q<100000+q`, and the multiplier is at most 50000.
The reduction homomorphism from units modulo `Q` to units modulo `q`
is onto. For completeness, a unit modulo `q` can be made nonzero modulo
every additional prime dividing `Q` by the Chinese remainder theorem;
prime powers already dividing `q` preserve its nonzero residue. Every
fiber therefore has the same cardinality `phi(Q)/phi(q)`.

A prime in a reduced class modulo `q` which fails to be a unit modulo
`Q` must divide the multiplier. It is at most 50000 and is below all
intervals used here. Consequently the prime classes partition exactly
into those `phi(Q)/phi(q)` reduced classes. After normalization, the
summed errors still carry exactly `phi(Q)`, not separately maximized
class and totient factors. Since `Q` is even, `phi(Q)<=Q/2`.

For `q<=ell<=a u`, where `a=1443/1000`, this supplies the pointwise
continuous envelope


```math
Q<Q_s(u)=100000+au.                                  \qquad\text{(CW7)}
```


For the larger selected target modulus, `Q<200000` when it is lifted
and is unchanged otherwise. It still fits `Q<=C ell^2`, with
`C=369/1000`, as checked in the certificate.

## 4. Exact target specialization and its entire tail

Fix `U=8990`, `d=1370`, and `C=369/1000`. The certificate encloses
`log 2`, proving pointwise


```math
10u/7<\ell\le au,\qquad \log(2Y)\le\ell.
```


For each fixed profile, choose an exact rational `alpha` strictly below
`sqrt((U-1)/(R U))`: the code takes the downward square-root bracket
on a `10^-12` grid and subtracts one more grid unit. For the target
profile it is


```math
\alpha_t=160980871033/500000000000.
```


Then every endpoint satisfies `nu>=alpha_t sqrt u` for all `u>=U`,
because `log x>u-1`. No smoothness of an integer parameter is assumed.
Put


```math
B=\log(C\ell^2),\qquad L(u)=\log(Ca^2)+2\log u,
 \qquad c_y=2(1+1/d).
```


We have `b+c<=c_yY` and `log Q<=B<=L(u)`. The new source domain is


```math
U-1>R[L(U)+\log100000]^2.                             \qquad\text{(CW8)}
```


It persists because `(u-1)/(L(u)+log100000)^2` increases when the
logarithm term exceeds 4. The exact check includes this condition.

As in AL7 and ZH8, choose outward `s_C>=sqrt C` and
`B_0<=log(C(10U/7)^2)`, and set


```math
z_0=\frac{40(1-1/U)}{a s_C},\qquad
 A=10^{-6}\left\lfloor10^6\left(z_0-\frac{z_0^2}{2B_0^2}\right)\right\rfloor
 =\frac{42387977}{1000000}.                            \qquad\text{(CW9)}
```


BMOR's real-zero bound and `1-exp(-z)>=z-z^2/2` give the adverse
main derivative at least `A/[phi(Q)B^2]` on every later scale.
The favorable-sign comparison from §2.2 applies because `2A<B_0^2`.

Using CW5 with `s=2`, the normalized endpoint error divided by `Y`
is at most


```math
\begin{split}
 f(u)+r(u),\qquad
 f(u)&=c_yCa^2u^2\left(\frac{0.32181\alpha_t\sqrt u}{2}+2\right)
                         e^{-\alpha_t\sqrt u},\\
 r(u)&=85000u^5e^{-u}+864u^2e^{-u/2}.                  \qquad\text{(CW10)}
 \end{split}
```


The nonspectral envelope follows from the same original remainders,
`Q<=288u^2`, and `log Q<=u`. At the exact base the certificate proves


```math
\frac{2dL(U)^2}{A-1/2}\,[f(U)+r(U)]
 <\boxed{0.999606454099}<1.                            \qquad\text{(CW11)}
```


The logarithmic derivative of the exponential summand, multiplied by
`u`, is at most `5/2+4/L(u)-alpha_t sqrt u/2`, negative at the
base and thereafter. The other terms decrease when
`u>5+4/L(u)` and `u/2>2+4/L(u)`; these inequalities also hold
throughout the tail. Hence the required half inverse-log-squared main
term remains on every larger scale. Summing lifted classes, dividing by
`log(2Y)`, and using `2phi(q)<=q` and
`B<=log2*(7+2ceil(log_2ell))` proves CW1.

For CW2, use `Q_s(u)` from CW7. At the base, its endpoints already
satisfy the original E2 source domain and


```math
\frac{40(u-1)}{\sqrt{Q_s(u)}\log^2Q_s(u)}>2.
```


The latter persists: its logarithmic derivative multiplied by `u`
exceeds `1/2-2/log Q_s(u)>0`. Thus the adverse main derivative
exceeds `3/[4phi(Q)]`. Replace `Ca^2u^2` in CW10 by `Q_s(u)`
and multiply the resulting normalized error by `8d`. The exact ratio
is less than `0.000946288488`; every summand decreases, since the
exponential comparison now needs only `alpha_t sqrt u/2>3/2`.
Section 2.2 treats the favorable sign, proving CW2.

## 5. Centered macro specialization

Fix `U_s=5982`, `A_bin=29092`, `eta=6007/7000`, and


```math
\alpha_s=321952736721/1000000000000.
```


Use the same `Q_s(u)` and the same original-source and adverse-main
comparisons as for CW2. They hold at `U_s` and persist by the
continuous derivatives just given. Because `b+c=2Y`, the adverse
exponential error is bounded by


```math
f_s(u)=2Q_s(u)\left(\frac{0.32181\alpha_s\sqrt u}{2}+2\right)
                     e^{-\alpha_s\sqrt u}.
```


The macro length is at least `2Y/(eta A_bin)`. It is therefore enough
that `2eta A_bin[f_s(u)+r(u)]<1`. Its exact upper bound at the base is


```math
\boxed{0.999206400830}<1.                             \qquad\text{(CW12)}
```


The exponential envelope has logarithmic derivative at most
`[3/2-alpha_s sqrt u/2]/u<0`; the remaining terms decrease as well.
Thus the adverse error is below `H/[4phi(q)]` on the whole tail,
and §2.2 again covers the favorable sign. This proves CW-macro.

## 6. A sharper mean for the exact odd-prime pool

**MR.** Let `X=p_(n^2+1)`, let `T` be the sum of the first `n^2`
odd primes, and put `m=T/n^2`. If `log X>=1000`, then


```math
\boxed{m<\frac{501}{1000}X}.                         \qquad\text{(MR1)}
```


This uses only [Rosser–Schoenfeld 1962, printed p.69](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf),
Corollary 1, inequalities (3.4) and (3.5):
`pi(X)<X/(log X-3/2)` in its stated domain and `pi(t)>t/log t`
for `t>=17`. These are imported analytic inequalities; the certificate
checks their specialization, not the theorems themselves.

Write `N=n^2=pi(X)-1`, `u=log X`, and
`I=integral_2^X pi(t)dt`. Exact partial summation, including the largest
prime and removing the input prime 2, gives


```math
T=X(N+1)-I-2.
```


The lower bound for `pi`, integrated from `sqrt X` to `X`, yields
`I>(X^2-X)/(2u)`. In particular `I-X+2>0` on the stated domain.
The sign is essential when using `N<X/(u-3/2)`. Consequently


```math
\begin{split}
 \frac mX
 &=1-\frac{I-X+2}{NX}\\
 &<\frac12+\frac3{4u}+(u+1/2)e^{-u}.                  \qquad\text{(MR2)}
 \end{split}
```


Both error terms decrease for `u>=1000`. At 1000 the second is less
than `1/4000`, since `2^1000>4002000`, while the first is `3/4000`.
This proves MR1 strictly. The source-domain and positivity comparisons
are included in the exact certificate. No different input pool has been
introduced, and the earlier lower bound `m>2X/5` remains available
separately for the order-to-target-scale conversion.

## 7. Reproduction and certification boundary

Executable replay details are recorded in [Provenance](../PROVENANCE.md#optimized-bound).

The program performs 16 inherited height checks, seven new source-factor
checks, five mean checks, 21 target checks, 14 macro checks, four
counterinvoice comparisons, and ten rejection controls. It uses only
integers and fractions for certification. The required source map must
match all ten files exactly; missing, extra, empty, malformed, nonregular,
or mismatched inputs fail. The campaign's complete manifest additionally
binds this manuscript, its code, and the finite composition.

All full-tail assertions use continuous envelopes checked pointwise for
every rounded parameter. The scalar derivatives apply only to those
envelopes; no derivative is transferred across a ceiling or floor jump.
The imported zero-counting and prime theorems, the primitive explicit
formula, the source-fidelity derivation, and the written calculus remain
mathematical inputs to ordinary review. Arithmetic success is not an
end-to-end kernel-checked proof or a certificate for an explicitly listed
prime square. All earlier classical profiles remain separately reproducible.

[Manuscript index](../README.md) · [Optimized theorem](../optimized-bound.md) · [Source and review record](../PROVENANCE.md#optimized-bound)
