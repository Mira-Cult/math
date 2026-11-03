# Faster common-gap prefixes using a short-progression upper bound

*Presentation copy: mathematical delimiters and equation labels are adapted for GitHub rendering. The unchanged, hash-bound source is in the [complete replay packet](../../../../packet/README.md).*


Author: `/root`. This additive lemma improves the prefix growth rate after
an explicit radius threshold. It changes no frozen AP, BN or controller
source. It needs independent nonauthor review at its exact scientific
revision. It is not a complete square cutoff or a formal proof.

## BT1. Exact primary import

Montgomery and Vaughan, *The large sieve*, Mathematika20(1973),119--134,
DOI10.1112/S0025579300004708, Theorem2, printedp121, equation(1.10):
for positive real x,y and relatively prime positive integers k,a,


```math
\pi(x+y;k,a)-\pi(x;k,a)
                 \lt \frac{2y}{\varphi(k)\log(y/k)}
                 \qquad(y\gt k).                              \qquad\text{(BT1)}
```


The statement was inspected in the original author-hosted paper at
https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf,
PDFpage3. In particular, (1.10) has no unspecified constant or
additional scale threshold. The subsequent (1.11) is not used.
This is an imported unconditional analytic theorem, not a theorem proved
by the finite checker or a new zero computation.

Only upper bounds for nearby class primes are used here. The lower
progression supplies needed by a full controller remain separate.

## BT2. One common-gap stage

Retain AP's notation and hypotheses. An interval of width cX contains
N distinct unused primes in r fixed reduced classes modulo the positive
even integer g, where 1<=r<=phi(g). The cases r=1 and r=phi(g)
are both allowed. Let N>=M>0, let the current g-grid radius satisfy
0<R<X/L, and put


```math
c_0=\frac1{2(c+1/L)},\qquad
 0\lt \eta\lt c_0,\qquad \epsilon=c_0-\eta.
```


All counts refer to the same current unused set, after every previous
selection or deletion. Partition its containing interval into half-open
bins of length at most R, using at most cX/R+1 bins. Cauchy--Schwarz
gives at least


```math
c_0N^2R/(rX)-N/2                       \qquad\text{(BT2)}
```


unordered within-bin, same-class pairs. Subdivide every spatial bin
by its r classes before applying Cauchy--Schwarz; there are at most
r(cX/R+1) such cells. Each counted pair has positive gap at most R, divisible
by g. This is the same finite pair count as in AP.

Choose a positive real lambda and set


```math
\zeta=\frac{\lambda\varphi(g)}{2g},\qquad
 D=\zeta g(\eta MR/(rX)-1/2).
```


Assume D/g>=exp(lambda). This implies D>g and makes BT1 applicable
to the interval (p,p+D] for every lower prime p in the unused set.
The number of its upper same-class neighbours at gap strictly less
than D is bounded by the count in that closed upper interval, hence is
strictly less than


```math
\frac{2D}{\varphi(g)\log(D/g)}
 \le\frac{2D}{\varphi(g)\lambda}
 =\eta MR/(rX)-1/2.                                           \qquad\text{(BT3)}
```


Subtracting at most N times this bound from BT2 leaves strictly more
than


```math
(c_0N^2-\eta MN)R/(rX)\ge\epsilon M^2R/(rX)         \qquad\text{(BT4)}
```


eligible pairs with gaps in [D,R]. The same minus N/2 occurs in both
counts and cancels; it is not dropped with the wrong sign.

There are at most floor(R/g)<=R/g possible positive gaps. For one gap h,
the graph connecting p to p+h has degree at most2 and is a union of
paths. One alternating matching has at least half its edges. Therefore
the original common-batch condition


```math
\epsilon M^2g\ge2zQrX                 \qquad\text{(BT5)}
```


still supplies zQ vertex-disjoint pairs with a single common difference
h in [D,R]. BN's narrowing may keep Q of them and leave all other
candidates unused. Only2Q entries are reserved. All original gap-grid
and diagonal equal-gap requirements are preserved.

This argument does not replace the common-batch condition by a
two-pair assertion. It also does not use probabilistic independence
of primes, windows or deletion sets. The prime upper bound applies
to the full class and therefore to every adversarially depleted subset.

## BT3. The terminal shift is unchanged

As in AP let M_j=M_start-2Qj, with M_j>=M_f>0 throughout all stages.
Set


```math
R_* =rX/(2\eta M_f),\qquad S=R-R_* .
```


At any stage with S>0,


```math
D=\zeta\eta g M_j S/(rX)
           +\frac{\zeta g}{2}(M_j/M_f-1)
       \ge\zeta\eta gM_jS/(rX).                              \qquad\text{(BT6)}
```


In particular the sufficient phase-start condition


```math
S\ge\frac{rX\exp(\lambda)}{\zeta\eta M_f}
                                                                    \qquad\text{(BT7)}
```


gives D/g>=exp(lambda) at every later stage of that phase. The radius
increases and stock stays above M_f. Each chosen h then gives


```math
S_{\rm new}\ge(1+\zeta\eta gM_j/(rX))S.  \qquad\text{(BT8)}
```


The shift R_* is the same for every lambda. Switching to a faster
phase therefore incurs no new origin loss and needs no new seed pairs.
An initial ordinary phase, with multiplier1 and no BT threshold,
can first reach BT7. For that phase use the same spatial/class pair count
and discard gaps below g(eta M_jR/(rX)-1/2): each lower endpoint has
strictly fewer than eta M_jR/(rX)-1/2 possible positive g-multiple
neighbours, so the same cancellation and BT5 apply elementarily.
Higher lambda phases can be entered successively.
If X/L is crossed sooner, selection stops; no later phase is necessary.
The actual gap h<=R ensures the usual overshoot bound R_new<=2R.

## BT4. Exact finite phase caps

Consider a phase beginning at global stage a and containing at most J
further stages. Write M_a=M_start-2Qa. Use multiplier zeta as above
or multiplier1 for the initial ordinary AP phase. Provided the
terminal stock remains at least M_f, summing
log(1+t)>=t/(1+t_max) gives the explicit lower logarithmic growth


```math
\Lambda=
 \frac{\zeta\eta g\{JM_a-QJ(J-1)\}}
      {rX(1+\zeta\eta gM_a/(rX))}.                             \qquad\text{(BT9)}
```


Thus Lambda>=log(S_target/S_start) certifies that the desired shifted
radius is reached in at most J stages. A controller may use smaller
stock numerators and a larger valid denominator bound, provided both
directions are stated and paid. It may also replace every M_j in the
numerator by the global lower stock M_f, which is weaker but simpler.

At a phase transition an actual earlier stop causes fewer deletions,
so the same worst-case global stage indices and terminal-stock floor
remain valid. The stored rational S_start for a later phase is a lower
bound, not the actual possibly larger radius. All prefix entries are
charged using the complete sum of phase caps. The final target may be
S_target=X/L-R_*, or the stronger X/L. A nonpositive final target
means the desired original radius has already been reached.

The checker uses exact rational phase data, upward Taylor enclosures
of exp(lambda), and outward logarithm bounds. Its negative controls
include an unpaid phase-entry threshold, a missing -1/2 intercept,
insufficient stock, omitted candidate multiplicity and shortened phase
caps. A separate actual-prime fixture constructs a valid common-gap
batch and verifies distinct labels, grid extension and the short-pair
invoice directly. No floating-point discovery value certifies a phase.

## BT5. Infinite-tail use and limits

A complete controller still needs every lower progression supply,
weighted seed demand, modulus domain, reservation budget, placement,
target list and flow inequality. It must certify BT5 and every BT7--BT9
comparison uniformly on each entire order band, including stock and
rounding changes. Applying BT at one numerical order does not establish
the tail. A controller's exact interval envelopes and fixed integer
phase counts can discharge these obligations, just as in AP.

The finite checker supports the arithmetic and reproducibility of
BT2--BT9. The universal matching/phase argument, the imported BT1 and
the complete square composition require ordinary mathematical review.
None is claimed to be kernel checked.
