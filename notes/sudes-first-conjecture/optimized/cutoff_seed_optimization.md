# Match after screening the gaps

## S1: smaller gap, larger guaranteed supply

For every integer `X>=2^32`, put `E=ceil(log_2 X)`. There are an even
`2<=g<=E`, a reduced class `a mod g`, and at least


```math
\left\lfloor\frac{X}{20E^3}\right\rfloor
```


vertex-disjoint prime pairs `(p,p+g)` in `[X/4,3X/4]`, with all lower
endpoints congruent to `a mod g`. In particular this supplies the unchanged
controller requirement `floor(X/(2048E^3))`.

### Proof and primary dependence

The already-proved RS62 calculation E1.1 gives


```math
M:=\pi(3X/4)-\pi(X/4)
 \gt \frac{68497}{175000}\frac{X}{\log X}
 \gt \frac{68497}{122500}\frac XE.                    \qquad\text{(S1.1)}
```


The last inequality uses `log X<=E log 2` and `log 2<7/10`.
For completeness, the positive series
`log 2=2 sum_{j>=0} 1/((2j+1)3^(2j+1))` is at most
`2/3+1/36=25/36<7/10`, with a strict inequality in the tail bound.
The first inequality is RS62 (3.5)--(3.6), exactly as expanded in E1.1;
its domain `X>=2^32` is unchanged. It is an imported prime-density
consequence, not established by the arithmetic program.

List all M primes in `(X/4,3X/4]`. Consider **all** consecutive-prime
edges. Their gap sum is less than `X/2`. Consequently fewer than
`X/(2E)` edges have gap greater than E. The number s of edges with gap
at most E therefore satisfies


```math
s\gt \frac{7247}{122500}\frac XE-1.                  \qquad\text{(S1.2)}
```


These short edges form a disjoint union of paths. In each path choose
alternate edges, starting with its first edge. A component with r edges
contributes `ceil(r/2)`, so the resulting vertex-disjoint matching has
at least s/2 edges. Thus its size is greater than


```math
\frac{7247}{245000}\frac XE-\frac12
 \gt \frac{X}{40E}.                                    \qquad\text{(S1.3)}
```


For the last comparison the exact difference of coefficients is
`1122/245000`. Throughout the domain,
`X/E>2^(E-1)/E>=2^31/32=2^26`; indeed E is an integer at least 32,
and the ratio of consecutive envelopes is `2E/(E+1)>1`. At the base
`(1122/245000)2^26>1/2`. This explicitly handles every dyadic ceiling
jump, including `X=2^32`.

Every selected gap is even, since all listed primes are odd. Every lower
endpoint exceeds `X/4>E`, so it is coprime to its gap. The number of labels
`(g,a mod g)` is at most


```math
\sum_{j=1}^{\lfloor E/2\rfloor}2j
 =\lfloor E/2\rfloor(\lfloor E/2\rfloor+1)
 \le E(E+2)/4\le E^2/2.                              \qquad\text{(S1.4)}
```


Pigeonholing **after** forming the matching therefore leaves more than
`X/(20E^3)` pairs of one label, still vertex-disjoint. This proves S1.
When `X=p_(n^2+1)`, every endpoint belongs to the exact prescribed odd-prime
pool. The selection does not consume any prime outside it.

## Why the order of operations matters

Pairing the primes first guarantees disjointness but discards half of the
consecutive edges before the gap screen. A first repair retained the natural
logarithm in E1.1 and proved `g<=2E` with matching supply `X/(80E^3)`.
Screening all consecutive edges first, then matching their path components,
improves both conclusions to S1. No statistical assumption about gaps is used.
The matching is formed before pigeonholing, so no later matching loss is
silently omitted. The gap may vary with X and the selected class may vary
with the gap; the later progression estimates must remain uniform.

Smaller actual g and its actual totient may be preferred during the finite
search, but the theorem only claims the above worst-case guarantee. It does
not assume a fixed bounded gap or count a shared endpoint twice. Multiple-gap
gadgets and unproved bounded nonnegative Bezout representations are unused.

## Interface consequences

If `e=ceil(log_2 y)>=E`, and the refined target selection supplies
`h<=g e`, then its lifted modulus satisfies `h<=e^2`, rather than the
old `128e^2`. This implication requires the target lemma separately.

For the controller's macro scale `Y=m +/- X/4<X`, its interval length
is `2delta X`. Since g is even, `phi(g)<=g/2<=E/2`, and for E>=3,
`log(2Y)<=log(2X)<E`. A strong count
`H/(2phi(g)log(2Y))` therefore supplies at least
`2delta X/E^2` primes per required class. The global half-pool interval
supplies at least `X/(2E^2)`. These are raw counts; the controller must
still charge all reservations before claiming remaining supply.

## C1: a sharper coupling of the two ceilings

For every `n>=64`, the same RS62 lower bound for pi gives


```math
X\lt 4n^2\log n.                                      \qquad\text{(C1.1)}
```


Indeed, `4log n<n` at64 (use `log64<6`) and thereafter, by the derivative
`1-4/n>0`. Put `z=4n^2 log n`. Then `log z<3log n`, so
`pi(z)>z/log z>(4/3)n^2>n^2+1`. This proves (C1.1) for the actual
index `n^2+1`, not merely for `p_(n^2)`.

Set `v=log_2 n`. For `v>=128`, (C1.1) and `log2<1` imply


```math
E\le2v+\log_2v+3,
 \qquad e\gt 3v-2,
 \qquad E\lt \frac7{10}e.                              \qquad\text{(C1.2)}
```


The middle inequality follows from `y>(2/5)n^3>n^3/4`.
For the last, `v/10-log_2v-22/5` is positive at128 and increasing for
`v>=128`, because its derivative exceeds `1/10-3/(2v)>0`.
Consequently `2v+log_2v+3<(7/10)(3v-2)<(7/10)e`.
These continuous envelopes hold pointwise across both integer-ceiling jumps.

If the refined target lemma gives `h<=gL` for
`L=ceil(7(e+1)/10)`, then S1 and (C1.2) imply


```math
h\le EL\lt \frac{49}{100}e^2+\frac{119}{100}e
 \le\frac12 e^2\qquad(e\ge119).                     \qquad\text{(C1.3)}
```


Here `L<=7e/10+17/10`. The target lemma must establish its integer gap
selection; (C1.3) does not replace that step with a gcd assertion.
The ordinary square tail with `v>=128` already has `e>382`, so this
additional condition is automatic.

## Verification boundary

[cutoff_seed_optimization.py](../PROVENANCE.md#optimized-bound) verifies
all rational coefficients, base inequalities, the integer-bin persistence
factor, and the matching loss on every edge mask of paths up to length 14.
It independently checks disjointness and a dynamic-programming optimum.
The exhaustive finite path checks support the implementation; the path proof
above handles arbitrary lengths. RS62 and its E1 density derivation remain
mathematical inputs, not consequences of those finite experiments.

[Manuscript index](../README.md) · [Optimized theorem](../optimized-bound.md) · [Source and review record](../PROVENANCE.md#optimized-bound)
