# Prime-pool spread and variance-sensitive completion

Author: `/root`. This additive research component requires independent
nonauthor review. It preserves the accepted sources and proves no final
square cutoff by itself. The numerical verifier checks finite rational
inequalities and source bindings, not the imported analytic theorems or
the universal mathematical arguments.

Use the exact original pool: `N=n^2=pi(X)-1`, `X=p_(n^2+1)`,
`T=sum_(2<=j<=n^2+1) p_j`, `m=T/N`, and `E=ceil(log_2 X)`.
All unmarked logarithms are natural. Write `u=log X`.

## PS1. A mean-square bound for the full input pool

For every such pool with `u>=32`,

\[
 \frac1N\sum_{p\text{ in the pool}}(p-X/2)^2<\frac{X^2}{10}.
                                                        \tag{PS1}
\]

The only analytic imports in this calculation are Rosser--Schoenfeld
(1962), Theorem 2, (3.3)--(3.4), printed p.69:
`pi(t)>t/(log t-1/2)` for `t>=67`, and
`pi(t)<t/(log t-3/2)` for `t>exp(3/2)`.
The [original scan](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf)
and DOI `10.1215/ijm/1255631807` locate these imports.

Put `I(x)=integral_2^x pi(t)dt` and
`J(x)=integral_2^x t pi(t)dt`. Partial summation, subtracting the prime 2
exactly, gives

\[
 T=X\pi(X)-I(X)-2,\qquad
 \sum p^2=X^2\pi(X)-2J(X)-4.
\]

Consequently the mean square in (PS1), divided by `X^2`, equals

\[
 \frac14+\frac1{NX}\int_2^X(1-2t/X)\pi(t)\,dt
               +\frac{2X-4}{NX^2}.              \tag{PS2}
\]

Bounding this signed integral together retains a cancellation that is
lost by separately bounding the first and second moments.

Let `a=1/64`, `c=21/5`, and `b=65/32`. The previously proved
antiderivative calculation in [MM](cutoff2_moderate_mean.md) gives

\[
 I(x)<x/2+\frac{x^2}{2(\log x-b)}               \tag{PS3}
\]

whenever `log x>=337/16`. This is its numerical hypothesis, rechecked
here, not an invocation of MM's final literal `log X>=41` statement.
Indeed, split at `sqrt(x)`, bound the lower integral by `x/2`, and use
`F(t)=t^2/[2(log t-b)]`. The derivative inequality
`F'(t)>=t/(log t-3/2)` is equivalent to
`log t>=337/32`. The source domains and positive denominators follow.
At `x=aX`, `log x>=32-log64>32-c=139/5>337/16`.

Split the signed integral in (PS2) at `aX` and `X/2`. On its first
piece discard the negative part of the weight and use (PS3). On the
second piece use `pi(t)<t/(u-c-3/2)` and

`integral_0^(1/2) (s-2s^2)ds=1/24`.

On the negative piece use `pi(t)>t/(u-1/2)` and

`integral_(1/2)^1 (2s^2-s)ds=5/24`.

The source threshold `t>=67` holds there. Thus the signed integral is
strictly less than `X^2 R(u)+aX/2`, where

\[
 R(u)=\frac{a^2}{2(u-c-b)}
      +\frac1{24(u-c-3/2)}-\frac5{24(u-1/2)}.    \tag{PS4}
\]

The source upper count gives `X/N>u-3/2`. Also the lower count and
`X>2(u-1/2)` give `1/N<2u/X`. The finite certificate checks
`32>46 log2`, so `X>2^46` at the endpoint. In particular the required
count inequalities have positive denominators.

The function `(u-3/2)R(u)` decreases for `u>=32`: each positive term
is a positive constant times `(u-3/2)/(u-A)` with `A>3/2`, and the
negative term equals `-5/24+5/[24(u-1/2)]`. Its endpoint is negative,
so `R(u)<0` on the entire tail. Using that sign before replacing `X/N`
is essential. Equations (PS2)--(PS4) yield

\[
 \frac1{NX^2}\sum(p-X/2)^2
 <\frac14+(u-3/2)R(u)+aue^{-u}+4ue^{-2u}.        \tag{PS5}
\]

Every nonconstant term on this right side decreases on the stated
domain. At `u=32`, replace `exp(32)` from below by `2^46`; the resulting
exact rational is less than `1/10`. This proves (PS1) for every larger
real scale, without rounding any logarithm.

## PS2. Sampling without replacement and Bernstein's bound

Let `X>0` and let a finite population have values in `[0,X]`, mean `mu`, and variance
`sigma^2`. For a uniformly sampled subset of size `r`, write `S` for
the sum of the centered values. For `0<=t<3/X`,

\[
 \mathbb E e^{tS}
 \le\exp\left\{\frac{r\sigma^2t^2}{2(1-tX/3)}\right\}.
                                                        \tag{PS6}
\]

Here is a proof of the required comparison, so no probabilistic
independence of draws is assumed. For positive numbers `z_1,...,z_M`,
the elementary symmetric mean of degree `r` is at most the `r`th
power of their arithmetic mean. For `r=0,1` this is immediate. For
`2<=r<=M`, maximize the elementary symmetric sum on the compact simplex
with fixed nonnegative sum. Its maximum is positive, so at least `r`
coordinates are positive. If two coordinates are unequal, averaging
them preserves their sum and strictly increases their product; the
coefficient of that product is the positive degree-`r-2` symmetric sum
of the other coordinates. A maximum therefore has every coordinate
equal. This proves the comparison, including the boundary cases.

Apply it to `z_j=exp(t(x_j-mu))`. The moment generating function of
the subset sum is at most that for `r` independent uniform draws from
the population. For one centered draw `Z`, `|Z|<=X`, `E Z=0`, and
`E|Z|^k<=sigma^2 X^(k-2)` for every `k>=2`. The elementary induction
`k!>=2*3^(k-2)` gives

`E exp(tZ)<=1+sigma^2 t^2/[2(1-tX/3)]`.

Taking the logarithm and using `log(1+s)<=s` proves (PS6).
For a deviation `x>0`, apply the same reasoning to `-Z`. If
`r sigma^2=0`, the sum is deterministically zero and the concentration
claim is immediate. Otherwise exponential Markov inequality with
`t=x/(r sigma^2+Xx/3)` yields

\[
 \Pr(|S|\ge x)\le
  2\exp\left\{-\frac{x^2}{2(r\sigma^2+Xx/3)}\right\}. \tag{PS7}
\]

This choice is in the permitted domain. In particular, for any `L>0`,
`x=sqrt(2r sigma^2 L)+(2/3)XL` makes the exponent at least `L`.
Squaring proves this last algebraic comparison directly; no numerical
square-root approximation is used in the proof.

## PS3. Balanced cell counts remove depletion from the leading variance

Use [PB](cutoff2_prefix_balance_experiment.md)'s exact balanced counts.
If `r_0=2d(P_0+J_b+7K)`, the actual number of reserved primes is

`B_actual=r_0(n+8)+B_r`,

and every line has `r_0+q` occupied cells for some `q>=0`. Let
`N_0=n^2-B_actual>0` and suppose the certified upper invoice is
`B_actual<=B<n^2`. Then `r_0<n`. The number `r` of remaining cells
on that line is `n-r_0-q`. For a uniform completion its entries form
a uniformly sampled subset of the unused pool.

Removing primes can only decrease their sum of squared distances from
the fixed center `X/2`. The variance about the unused pool's own mean
is no larger. By (PS1), `sigma_unused^2<n^2 X^2/(10N_0)`. Moreover,

\[
 \frac{rn^2}{N_0}
 =n\left(1+\frac{8r_0+B_r-nq}{N_0}\right)
 \le n\left(1+\frac{8n+B_r}{n^2-B}\right).       \tag{PS8}
\]

Thus one uniform bound for all required lines is

\[
 V=\frac n{10}\left(1+\frac{8n+B_r}{n^2-B}\right),\qquad
 u_c=\sqrt{2V\log(8n+8)}+\frac23\log(8n+8).     \tag{PS9}
\]

By (PS7) and the union bound over `2n+2` lines, a completion exists
whose every line differs from its expected sum by at most `u_c X`.
The union bound is at most one half. The successful prefix allocation
is chosen first and fixes the unused population; no independence
between that allocation and completion is required. This replaces only
`u_c` in PB14. All residue, prefix, bridge, wide, flow and diagonal
obligations remain separate.

All expressions in (PS8) use actual counts before upper bounding them.
The balanced count identity, rather than an assumption about randomly
distributed deletions, is why the leading variance does not acquire a
factor `1/(1-B/n^2)`.

## PS4. Two additional finite estimates for the smaller profiles

The MM integral proof also applies at `u>=35`: its displayed derivative
domains already hold. With `exp(35)>2^50`, its exact rational endpoints
give

\[
               .476X<m<.522X.                   \tag{PS10}
\]

Both envelopes persist by the MM monotonicity proof. The literal final
MM threshold 41 is not used outside its domain.
The upper-mean proof also uses RS (3.5), `pi(t)>t/log t` for `t>=17`,
at its stated domain; this import is included in the input manifest.

For `u>=32` and integer `E>=44`, a disjoint seed matching of at least

\[
                 \left\lfloor\frac{4X}{5E^3}\right\rfloor
                                                        \tag{PS11}
\]

exists in `(X/4,3X/4]` with a common even gap `2<=g<=E` and a common
reduced lower residue. The proof is an evaluated version of the old
elementary seed argument. Since `log(4/3)>1/4` and `log4<7/5`, the
number of primes in that half-pool exceeds

`X[3/(4(u-3/4))-1/(4(u-29/10))] > (123/250)X/u`.

The last inequality, after multiplication by positive denominators,
has numerator

`(1/125)u^2-(1917/10000)u-10701/10000`,

which is positive at 32 and increasing thereafter. Put
`rho=(123/250)/(693148/10^6)`. Because `u<=E log2`, the count is
greater than `rho X/E`. Remove consecutive-prime edges with gaps
greater than `E`; there are fewer than `X/(2E)` of them. Alternating
edges in each remaining path leaves more than

`(rho-1/2)X/(2E)-1/2`

disjoint pairs. Every label is reduced since each prime is larger than
`g`, and there are at most `E(E+2)/8` possible even-gap/reduced-residue
labels. The exact certificate verifies

`[(rho-1/2)/2-(E+2)/(10E)]*2^26>1/2`

at `E=44`. This coefficient increases for larger integer `E`; also
`X/E>2^(E-1)/E>=2^26`. Pigeonholing the already disjoint matching
proves (PS11), including its integer floor.

## PS5. A coupled ceiling envelope starting at order 2^23

For every real `v=log_2 n>=23`,

\[
                  2v\le E<\frac{5213}{2300}v.    \tag{PS12}
\]

The lower bound follows from `X>=n^2`. For the upper bound, import
RS Theorem 3, (3.11), printed p.69:
`p_j<j(log j+log log j-1/2)` for integers `j>=20`.
With `eta=2^-46`, `b_2=693148/10^6`, and `j=n^2+1`, put

`z(v)=2 b_2 v+eta`, `W(v)=z(v)+log z(v)-1/2`.

The inequalities `j<=n^2(1+eta)` and `log j<z(v)` give
`X<n^2(1+eta)W(v)`. Thus, pointwise through every ceiling jump,

\[
 E<2v+1+\frac{\eta+\log W(v)}{\log2}.           \tag{PS13}
\]

At `v=23`, the exact logarithm enclosures in the certificate put the
right side below `52.13=(5213/2300)23`. This comparison includes the
full unit for the ceiling, rather than treating `E` as a smooth function.
Furthermore `z(v)>2`, `log z(v)>1/2`, and

`(log W(v))'=2 b_2(1+1/z(v))/W(v)<(1+1/z(v))/v`.

The latter divided by `log2` is already less than `5213/2300-2` at
23 and decreases in this upper bound thereafter. Subtracting the smooth
right side of (PS13) from `(5213/2300)v` therefore gives an increasing
positive function. This proves the entire real-order envelope without
differentiating a ceiling. Its application to integer prime indices uses
`j>=2^46+1>20`, as required by the imported theorem.

## Reproduction and scope

Run `python3 -B problems/prime-line-sums/code/cutoff2_pool_statistics.py`.
The exact manifest fixes the required public sources, parameters and
analytic imports. Missing, empty, malformed, altered and symlinked
sources are rejected. Finite mechanism controls check the symmetric-mean
comparison and balanced-count variance identity in small exhaustive
cases. Those controls do not replace the mathematical proofs above.
No RH assumption, finite zero computation, private artifact or new
prime pool is introduced by this component.
