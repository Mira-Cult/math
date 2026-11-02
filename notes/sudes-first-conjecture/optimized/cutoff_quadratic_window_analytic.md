# Analytic supply for quadratic target windows

This is a separate corollary of the signed
primitive-character argument in [AL](cutoff_analytic_refinement.md).
It preserves the cubic-window manuscript and checker. Independent review
must bind the exact new scientific revision before this corollary is used
in an established complete cutoff.

## Statement AQ

Let `Y` be real, write `u=log Y`, `ell=ceil(log_2 Y)`, and suppose


```math
\boxed{u\ge22027}.                                   \qquad\text{(AQ0)}
```


Put


```math
D=Y/\ell^2,\qquad
 F=\ell\bigl(7+2\lceil\log_2\ell\rceil\bigr)^2.
```


For every even `2<=q<=(117/250)ell^2`, every reduced class `a mod q`, and every
real interval `(b,c]` inside `[Y-D,Y+D]` of length `H>=D/2`, the
number of primes congruent to a is at least


```math
H/(qF).                                               \qquad\text{(AQ1)}
```


For even `2<=q<=32ell`, the same intervals also have the stronger count


```math
H/[2\varphi(q)\log(2Y)].                              \qquad\text{(AQ2)}
```


The same two conclusions hold for the retained, wider modulus range
`q<=ell^2/2` if `u>=22146`. Both exact profiles are checked; the smaller
default threshold uses the narrower, explicitly stated cap. The square
composition must prove its selected modulus fits that cap.

This is an analytic statement. The existing cubic controller does **not**
thereby gain a quadratic correction radius. A new controller or allocation
lemma must independently justify that radius, preserve all entries and
diagonals, and pay the complete reservation and centering costs.

## Proof: re-evaluate the larger windows in their original domains

Use the corrected normalized explicit-formula consequence (AL3), including
the `1.012` spectral coefficient and `4Q/phi(Q)` smoothing term. Its proof
and primitive-character normalization are unchanged. The square-root
prime-power correction and all nonspectral remainders are retained.

In AL's notation set


```math
U=22027,\quad p=2,\quad C=117/250,\quad
 a=1443/1000,\quad\alpha=32197/100000,\quad
 c_y=200001/100000,\quad c_s=253/250.
```


The exact certificate verifies anew, at this smaller base, all of


```math
\ell\le au,\quad \ell>10u/7,\quad
 R_1\alpha^2<1-1/U,\quad
 2(1+U^{-2})<c_y,
```


and the power-of-two lift `100000<=Q<=C ell^2`, including all originally
small even q. For


```math
B=\log(C\ell^2),\qquad L(u)=\log(Ca^2)+2\log u,
```


one has `log Q<=B<=L(u)`. The original analytic source-domain comparison
`U-1>4R_1 L(U)^2` passes, and `(u-1)/L(u)^2` increases throughout
the tail because `L(u)>4`. Thus the improved cutoff respects the source
domain for every actual endpoint; it is not obtained by substituting a
smaller value in a theorem with an unchanged larger premise.

Compute the fixed rational derivative coefficient by (AL7), using this U.
The downward rounding now gives exactly


```math
A=\frac{38456667}{1000000}=38.456667,\qquad
 A-\frac12=\frac{37956667}{1000000}=37.956667.           \qquad\text{(AQ3)}
```


The same signed exceptional-zero argument proves
`M'_{Q,a}(t)>=A/[phi(Q)B^2]` on the entire interval, for every larger
scale. It pays an exceptional zero if present; no zero-exclusion computation
or RH assumption enters this corollary.

With `w=alpha sqrt u`, the normalized endpoint error divided by Y remains


```math
f(u)+85000u^5e^{-u}+864u^2e^{-u/2},\qquad
 f(u)=c_y C a^2u^2(c_s w/2+4)e^{-w}.
```


The necessary comparison is exactly the larger-window version of AL11:


```math
\frac{2a^2u^2L(u)^2}{A-1/2}
 \left(f(u)+85000u^5e^{-u}+864u^2e^{-u/2}\right)<1.      \qquad\text{(AQ4)}
```


At `u=22027`, rational interval arithmetic bounds its left side by
`0.999868372791`. Its exponential term decreases because
`alpha sqrt u/2>9/2+4/L(u)`; the remaining terms decrease because
`u>7+4/L(u)` and `u/2>4+4/L(u)`. All conditions hold at U and persist.
These continuous majorants dominate every change in the integer ceilings,
lifted modulus, residue class or interval endpoint.

After subtracting the errors, the remaining theta weight is at least
`H/[2phi(q)B^2]`. The unchanged even-modulus and logarithm comparison
from AL gives (AQ1). The stronger assertion (AQ2) uses AS-macro's
three-quarters signed derivative, valid already for `u>=10000`, and the
stronger `Q<=48u` error. Its normalized quarter-main error ratio at the
new base is at most `0.000850861820`; its tail derivative conditions also
pass. This proves (AQ2).

For the preserved half-cap profile, substitute `C=1/2,U=22146` in the
same formulas. The coefficient is `A=9321347/250000=37.285388`, the
error budget is `9196347/250000=36.785388`, the weak error ratio is below
`0.999998147154`, and the strong ratio is below `0.000761904052`.
Its domain and derivative checks pass independently. This is a second
complete analytic profile, not an inference from a test at a nearby value.

## Exact verifier and limits

Executable replay details are recorded in [Provenance](../PROVENANCE.md#optimized-bound).

The checker uses integer/rational logarithm, square-root and exponential
enclosures. It checks 18 finite comparisons for each profile and nine
negative controls, including the just-insufficient `U=22026` for the
selected error envelope, an
unpaid larger modulus cap, and empty, missing, extra, malformed, nonstring
and mismatched source-map records. Its dependency set is exact and pinned;
missing or empty files and changed bytes are rejected.

The primary analytic imports are the same BMOR and MCC84 inputs used in
the corrected E2 proof. Their status remains imported conventional
mathematics; this checker does not reprove them, kernel-check the argument,
verify any particular square, or establish a complete cutoff by itself.
The comparison failure below U is not a mathematical lower bound.

The principal remaining obligation for using AQ is a complete controller
with `D=y/e^2`. The larger window may reduce the final analytic floor,
but the additional required correction capacity and entry consumption
must be paid in an independent, reviewed finite construction.

[Manuscript index](../README.md) · [Optimized theorem](../optimized-bound.md) · [Source and review record](../PROVENANCE.md#optimized-bound)
