# Coupled scales, rounding, and the actual order cutoff

This is the common composition calculation for the cutoff
campaign. It preserves all earlier scientific sources. Its numerical
specializations are stated separately in the final campaign theorem; no
isolated scale estimate in this document is itself a square theorem.

All analytic logarithms are natural. The integer `e` below is a ceiling,
not Euler's number. Write


```math
X=p_{n^2+1},\quad T=\sum_{j=2}^{n^2+1}p_j,\quad
 m=T/n^2,\quad y=T/n,\quad
 E=\lceil\log_2X\rceil,\quad e=\lceil\log_2y\rceil,
 \quad v=\log_2n.
```


The baseline uses `K=floor(n/E^3)` and `D=y/e^4`. Later profiles explicitly
change these two design parameters. The meanings of X,T,m,y,E,e and the
input pool do not change. Prime targets are values of line sums and may
repeat. Each input prime still occurs in exactly one cell.

## 1. Imported estimates and elementary consequences

The preserved mean calculation M0 in
[effective_pair_supply.md](../classical-primes.md), using RS62
(3.2), (3.5), and (3.6), proves


```math
n^2\le X<n^3\quad(n\ge64),\qquad
 \frac25X<m<\frac35X\quad(X\ge2^{256}).                 \qquad\text{(CM1)}
```


It uses `pi(X)-1=n^2`; the prime 2 is not inserted into the pool. The
additional RS62 Theorem 2 inequality (3.4), valid for `x>exp(3/2)`, gives


```math
n^2+1=\pi(X)<\frac X{\log X-3/2},\qquad
 \frac X{n^2}>\log X-\frac32
 >Q(E):=\frac{693E-2193}{1000}.                         \qquad\text{(CM2)}
```


The last comparison uses `log X>(E-1)log 2` and `log 2>693/1000`.
Thus a reservation proportional to n squared must be compared with
`n^2 log n`, rather than with the weaker `X>=n^2`. This gain is genuine
in the sufficient invoice, and is not a lower bound for the square problem.

The upper-index estimate C1 in
[cutoff_seed_optimization.md](cutoff_seed_optimization.md) proves


```math
X<4n^2\log n\quad(n\ge64),\qquad
 E<2v+\log_2v+3.                                      \qquad\text{(CM3)}
```


It follows from `pi(z)>z/log z` at `z=4n^2 log n`, with
`4log n<n`, and treats the actual index `n^2+1`.

## 2. Ceiling envelopes and their persistence

For every real `v>=4096`, (CM1)--(CM3) imply


```math
2v\le E\le4v,\qquad
 \frac54 E\le e\le2E,\qquad
 e>3v-2,\qquad E<\frac{167}{250}e.                    \qquad\text{(CM4)}
```


For `e<=2E`, use `y<nX<=X^(3/2)` and round its logarithm upward.
For the lower comparison, `n>X^(1/3)` and `m>2X/5` give
`e>4(E-1)/3-2=(4E-10)/3`; this is at least `5E/4` for `E>=40`.
The sharper comparison follows from `e>3v-2` and


```math
\frac v{250}-\log_2v-\frac{542}{125}>0.               \qquad\text{(CM5)}
```


At `v=4096`, its value is exactly `6/125`. Its derivative is greater
than `1/250-3/(2v)>0`, using `log 2>2/3`. It therefore holds for every
larger real v. These are pointwise envelopes for the integer ceilings;
no derivative of E or e is used.

For `n>=2^v0`, the sufficient order-growth condition `n>=E^32` follows
from


```math
2^{v_0}\ge(4v_0)^{32},\qquad v_0\log2>32.            \qquad\text{(CM6)}
```


The logarithmic derivative of `2^v/(4v)^32` is `log2-32/v`, positive
throughout that tail. Its first integer endpoint above the derivative
domain is 333. The final theorem uses a much larger v0. Any controller
floor is consequently translated through `E>=2v`, and its independent
growth restriction is checked rather than inferred from that floor alone.

For every floor K, the proofs use inequalities valid at each point:
`floor z<=z` and `floor z>=z-1`. In particular, if `n/E^2>=50`,


```math
\left\lfloor\frac n{E^2}\right\rfloor
 \ge\frac{49}{50}\frac n{E^2};                        \qquad\text{(CM7)}
```


and if `n/E>=1000`,


```math
\left\lfloor\frac{101n}{100E}\right\rfloor
 \ge\frac{1009}{1000}\frac nE.                       \qquad\text{(CM8)}
```


These bounds remain valid when K jumps; monotonicity of a smooth surrogate
is never transferred to the floor itself.

## 3. The selected target modulus

The additive seed-density refinement SD in
[cutoff_seed_density_refinement.md](cutoff_seed_density_refinement.md)
gives an even common gap


```math
2\le g\le\frac{159}{200}E\quad(E\ge4096),             \qquad\text{(CM9)}
```


with the same required disjoint seed supply `floor(X/(2048E^3))`.
Its target refinement TD reapplies the exact-total proof using


```math
b=\frac{173287}{250000}=0.693148>\log2,\qquad
 L_t=\lceil b(e+1)\rceil,\qquad h\le gL_t.            \qquad\text{(CM10)}
```


The strict predecessor argument producing h is part of TD. A gcd identity
is not being substituted for a finite positive-gap construction.
Since `L_t<=be+b+1`, (CM4) and (CM9) show


```math
h<\frac{4601289711}{12500000000}e^2
     +\frac{11239539711}{12500000000}e
   <\frac{369}{1000}e^2\quad(e\ge1024).                \qquad\text{(CM11)}
```


Both coefficients are exact rationals. The last comparison is checked at
1024, after which the linear term divided by e squared decreases. This
couples the entry-scale seed and the target-scale progression requirement.

## 4. Translate every analytic scale separately

Put `a=log2`. For a positive constant c and an order exponent v define


```math
G_c(v)=2va+\log\{c(2va-3/2)\},\qquad
 F(v)=3va+\log\{(2/5)(2va-3/2)\}.                    \qquad\text{(CM12)}
```


These functions are defined in the entire domain here and strictly increase:
their derivatives are respectively `2a+2a/(2va-3/2)` and
`3a+2a/(2va-3/2)`. By (CM1)--(CM2), every actual scale satisfies

| Actual scale | Separate logarithmic lower envelope |
|---|---|
| Global seed-class supply, centered at `X/2` | `log(X/2)>G_(1/2)(v)` |
| Lower original macro interval, `m-X/4` | `log(m-X/4)>G_(3/20)(v)` |
| Upper original macro interval, `m+X/4` | `log(m+X/4)>G_(13/20)(v)` |
| Any reflected wide-bin center, extent w | `log Y>G_(3/20-w)(v)` |
| Prime targets, `y=T/n` | `log y>F(v)` |

The last line grows with coefficient three in v; the macro lines grow
with coefficient two. The final cutoff is the maximum of their separately
translated floors and the controller, target-size, and rounding floors.
Lowering a progression theorem's scale floor does not automatically lower
the order floor by the same operation.

For a reflected band with `w=19/200`, its smallest center is strictly
greater than `11X/200>X/32`. Thus, with `ell_Y=ceil(log_2Y)`,
`E<=ell_Y+5`. The seed cap then implies `g<=ell_Y` once `ell_Y>=20`.
Every bin has length `X/32000>=Y/32000`; all bin centers are below X.
Its halfwidth `X/64000` is below `Y/2`. The global interval
`(X/4,3X/4]` is centered at `Y=X/2`, has length Y, and lies in
`[Y/2,2Y]`. The two original narrow residue intervals also satisfy all
these length, modulus, and containment conditions. Their endpoint
conventions are covered by the real-interval analytic statements.

## 5. Exact-total sizes and final displacement

For every integer `e>=256`, put


```math
F_e=e\{7+2\lceil\log_2e\rceil\}^2\le4e^2.           \qquad\text{(CM13)}
```


The bound is proved by integer dyadic-bin induction in TQ; its endpoint
and jump inequalities are reproduced by the finite checker. The target
lemma's exact hypotheses are


```math
D\le y/4,\quad D\ge512F_e e^2,\quad
 n\ge8e\{3F_e(4e+6)+7\}.                            \qquad\text{(CM14)}
```


It is enough to have `D>=2048e^4` and `n>=680e^4`. For `D=y/e^p`,
with p equal to 1, 2, 3, or 4, these follow from


```math
E^{28}\ge680\cdot16,\qquad
 \frac25E^{96-(p+4)}\ge2048\,2^{p+4},                \qquad\text{(CM15)}
```


using `n>=E^32`, `e<=2E`, and `y>(2/5)n^3`. These are increasing
positive-power comparisons on the entire integer E tail. Centrality is
`e^p>=4`. They are far below the analytic floors in the completed profiles.

For the quadratic controller (CM7), the ratio satisfies
`D/(KX)<96/245<2/5`. For the linear controller (CM8), the sharper
ceiling ratio in (CM4) gives


```math
\frac{D}{KX}
 <\frac{3/5}{1009/1000}\frac{167}{250}
 =\frac{2004}{5045}<\frac25.                         \qquad\text{(CM16)}
```


The baseline lies strictly within `KX/10` of y, so its distance to any
target supplied within D of y is strictly below `KX/2`. Apply the exact-
total target lemma twice, once to the row classes and once to the column
classes, each with total the actual T. For each diagonal use any prime
in its reduced class in a central interval of length at least D/2.
Its analytic lower count is positive, hence the integer count is at least
one. The diagonals have no additional total constraint. The finite
controller realizes all these targets by disjoint permutations of the
original entries. This is the final logical step, not a numerical test of
a randomly chosen array.

## 6. Scope of the certificate

The campaign verifier checks exact rational inequalities and outward
transcendental enclosures, binds the complete required source set, and
checks the sufficient derivative and integer-bin conditions used above.
The prime-distribution imports, finite graph argument, integral-flow
theorem, martingale argument, constructive grid proofs, and their
composition remain conventional mathematics. No successful arithmetic
script, hash check, or finite mechanism test independently proves those
claims or converts them into an end-to-end kernel-checked theorem.

[Manuscript index](../README.md) · [Optimized theorem](../optimized-bound.md) · [Source and review record](../PROVENANCE.md#optimized-bound)
