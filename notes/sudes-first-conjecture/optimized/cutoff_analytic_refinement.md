# Local target intervals and the small selected modulus

This is an additive successor to
[the first signed-interface optimization](cutoff_analytic_optimization.md).
It preserves that frozen source and its `log Y>=80000` result. Its exact
source bindings and the corrected primitive E2 dependency are enforced by
[the accompanying rational checker](../PROVENANCE.md#optimized-bound).
This is a conventional proof; see the public provenance record for its review scope.

The primary BMOR/MCC84 imports and inspected page locators are recorded in
the preceding note. This refinement makes no different zero-set
identification, does not remove any Euler-factor prime-power allowance, and
does not assume that an exceptional zero is absent.

## 1. Refined statement

Write


```math
u=\log Y,\qquad \ell=\lceil\log_2Y\rceil,\qquad
 D=Y/\ell^3,\qquad
 F=\ell\bigl(7+2\lceil\log_2\ell\rceil\bigr)^2.
```


**AL.** For every real `Y` with


```math
\boxed{\log Y\ge35896},                               \qquad\text{(AL0)}
```


every even integer `2<=q<=ell^2/2`, every reduced class `a mod q`,
and every real interval `(b,c]` inside `[Y-D,Y+D]` of length `H>=D/2`,
there are at least


```math
\boxed{H/(qF)}                                         \qquad\text{(AL1)}
```


primes in that class. For even `q<=32ell` there are also at least


```math
\boxed{H/[2\varphi(q)\log(2Y)]}.                       \qquad\text{(AL2)}
```


The two conclusions have different uses: (AL2) selects a short repeatable
target-prime gap, and (AL1) supplies that selected gap's lifted residue
classes. The square composition must prove that its chosen modulus is
indeed at most `ell^2/2`. Merely replacing an analytic input by that smaller
range would not prove the needed modulus bound.

All inequalities below cover the full tail (AL0). The cutoff concerns an
analytic scale, not the order of a square. The code also implements the
same proof for explicitly supplied `p in {3,4}` and `0<C<=128`, with
`D=Y/ell^p` and `q<=C ell^2`; it accepts parameters only when all its
arithmetic and persistence checks pass. The displayed theorem uses exactly
`p=3,C=1/2,U=35896`.

## 2. Sharpen the already normalized error, preserving its proof

For the modulus `Q>=100000` and variable `v=sqrt(log x/R_1)` in N2,
its proof gives the sharper estimate


```math
|\theta(x;Q,a)-M_{Q,a}(x)|\le
 \frac{253}{250}xv e^{-v}
 +\frac{4Qx e^{-v}}{\varphi(Q)}
 +2\log Q\log x+Q\log Q+2\sqrt x.                     \qquad\text{(AL3)}
```


There are two elementary changes to the original proof. First, if its
smoothing-height variable is denoted `H_0` to avoid confusion with interval
length, then `H_0>=Q>=100000`. The exact spectral coefficient in E2.3 is


```math
0.5001(1+2/H_0)
 +0.511(1+6/H_0+18/H_0^2+20/H_0^3)<1.012=253/250.
```


Each positive term decreases in `H_0`, so the rational check at 100000
proves the whole assertion. Second, write the positive average as an
average over independent `r,s in [0,h]`. The principal part changes by
exactly `h/phi(Q)`. The exceptional function `f(t)=t^beta/beta` has
`0<f'(t)<=1` on the averaging domain. Consequently


```math
|A_h^\pm f(x)-f(x)|\le A_h(r+s)=h,
```


not merely `4h`. The two changes together are at most `2h/phi(Q)`.
Since `h=2Qx exp(-v)`, their cost is `4Qx exp(-v)/phi(Q)`.
All averaging domains, primitive-character terms, zero sums and prime-power
remainders are exactly those in the corrected E2 proof. Thus (AL3) follows
without a fresh explicit-formula substitution.

## 3. Fixed rational envelopes

Fix


```math
U=35896,\quad C=1/2,\quad p=3,\quad
 a=1443/1000,\quad \alpha=32197/100000,\quad
 c_y=200001/100000,\quad c_s=253/250.
```


The rational log enclosure proves `log2>6931/10000`. For every `u>=U`,
including all ceiling jumps,


```math
\ell\le au,\quad \ell>10u/7,\quad
 \log(2Y)\le\ell,\quad
 v\ge\alpha\sqrt u.                                  \qquad\text{(AL4)}
```


For the last inequality, `log x>u-1` on the entire target interval and
the certificate verifies `R_1 alpha^2<1-1/U`.
The two local endpoints obey


```math
b+c\le2Y(1+\ell^{-p})\le c_yY.                       \qquad\text{(AL5)}
```


Lift small even `q` by a power of two as in N2. The lifted modulus satisfies
`100000<=Q<=C ell^2<=C a^2u^2`: the small-modulus bound `Q<200000`
also fits this envelope. Set


```math
B=\log(C\ell^2),\qquad
 L(u)=\log(Ca^2)+2\log u.
```


Then `log Q<=B<=L(u)`. The source-domain check at the actual endpoint is


```math
U-1>4R_1 L(U)^2.                                     \qquad\text{(AL6)}
```


It persists because `(u-1)/L(u)^2` increases when `L(u)>4`.
In particular (AL3) is used only where its original analytic hypotheses
hold; the smaller final cutoff is not obtained by ignoring the source range.

## 4. Spend the actual exceptional derivative

The possible unfavorable exceptional contribution still has a positive
derivative. Choose rational enclosures `s_C>=sqrt C` and
`B_0<=log(C(10U/7)^2)`. Define


```math
z_0=\frac{40(1-1/U)}{a s_C},\qquad
 A=10^{-6}\left\lfloor10^6\left(z_0-
                    \frac{z_0^2}{2B_0^2}\right)\right\rfloor.
                                                               \qquad\text{(AL7)}
```


The enclosures and their series lengths are specified in the code. They
give exactly


```math
A=\frac{4682267}{125000}=37.458136,\qquad
 A-\frac12=\frac{4619767}{125000}=36.958136.             \qquad\text{(AL8)}
```


For every larger `u`, BMOR Proposition 1.11 implies


```math
z=(1-\beta)\log t\ge\frac{z_0}{B^2}.
```


The inequality `1-exp(-r)>=r-r^2/2` for `r>=0`, monotonicity in `z`,
and `B>=B_0` therefore show


```math
1-\exp(-z)\ge\frac{A}{B^2},\qquad
 M'_{Q,a}(t)\ge\frac{A}{\varphi(Q)B^2}.                \qquad\text{(AL9)}
```


The no-exceptional-zero case and the favorable sign also dominate this
quantity; the code checks `A<B_0^2`. After the lift is summed, the weighted
main increment is at least `AH/[phi(q)B^2]`.

The gain over the first optimization is not a new zero-free theorem. The
smaller actual modulus makes the known real-zero bound stronger, and the
finite target density allows most of that signed main increment to be used
as an error budget instead of discarding it.

## 5. Certify the complete error and its persistence

Multiplying the lifted endpoint error by `phi(q)` introduces `phi(Q)`,
which is at most `Q/2`. Put `w=alpha sqrt u`. From (AL3)–(AL5), the
exponential part of this normalized error divided by `Y` is bounded by


```math
f(u)=c_y C a^2u^2\left(\frac{c_s w}{2}+4\right)e^{-w}.
                                                               \qquad\text{(AL10)}
```


The old conservative remainder bounds `85000u^5 exp(-u)` and
`864u^2 exp(-u/2)` remain valid, since `Q<=288u^2` and `log Q<=u`.
It suffices that


```math
\frac{2a^p u^p L(u)^2}{A-1/2}
 \left(f(u)+85000u^5e^{-u}+864u^2e^{-u/2}\right)<1.      \qquad\text{(AL11)}
```


The exact verifier encloses the left side at `U=35896` strictly below
`0.999884447128`. Its finite rational Taylor sums and integer powers are
part of the reproducible input; the displayed decimal is an outward
enclosure, not a floating-point test.

For the first summand, `u` times its logarithmic derivative is bounded by


```math
p+\frac52+\frac4{L(u)}-\frac{\alpha\sqrt u}{2}<0.
```


The two other summands decrease when `u>p+5+4/L(u)` and
`u/2>p+2+4/L(u)`. The certificate checks these domains at the base.
They persist because `L` and `sqrt u` increase. Thus (AL11) holds for
every larger real `u`, with no assumption that a ceiling or a selected
modulus varies smoothly.

Subtracting errors leaves at least `H/[2phi(q)B^2]` in theta weight.
Since `q` is even, `2phi(q)<=q`. Also `C<=128` and
`B<log2*(7+2ceil(log_2ell))`, while `log(2Y)<=ell`.
Dividing by the maximum prime weight therefore gives (AL1).

For the strong conclusion (AL2), the first note's AS-macro proof supplies
the lower main derivative `3/[4phi(q)]` for all `u>=10000` and even
`q<=32ell`. Use `Q<=48u` in (AL10), retaining the same local endpoint and
spectral constants. Multiplication of its normalized error by `8a^p u^p`
gives, at `U`, an outward upper bound `0.000429801868<1`. Each summand
again decreases; the exponential comparison requires only
`alpha sqrt u/2>p+3/2`. Thus the error is below `H/[4phi(q)]`, leaving
the half main term asserted in (AL2).

## 6. Exact scope of the numerical optimization

The final verifier defaults to the exact tuple
`(U,p,C)=(35896,3,1/2)` and runs four negative controls. One rejects
`U=35895` under this particular sufficient envelope. That rejection is a
limitation of this estimate, not a counterexample to the analytic statement
or the square problem at any smaller order. Other controls reject an
unsupported radius power and zero or out-of-range modulus caps.

The arithmetic check does not certify the imported theorems, the source E2
normalization or its mathematical derivation, a finite square, or the full
all-odd-order conclusion. The seed, target and controller components must
prove their own hypotheses, especially the small selected modulus and the
larger target radius. The composition must translate this target-scale floor
and the unchanged macro floor `log Y>=10000` separately to the square order.

[Manuscript index](../README.md) · [Optimized theorem](../optimized-bound.md) · [Source and review record](../PROVENANCE.md#optimized-bound)
