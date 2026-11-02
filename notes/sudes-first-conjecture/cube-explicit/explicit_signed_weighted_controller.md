# Weighted logarithmic scales for the unchanged finite signed-cube controller

Public proof manuscript. See [provenance](../PROVENANCE.md#explicit-prime-cube) for the pinned sources, internal review and verification limits.

## 1. The coefficient region is nonempty

FSC permits arbitrary ordered positive integers `K0<=K1<=K2<=K3` and an
actual midpoint half-width `delta X`, provided its stated finite inequalities
hold. It does not require strict gaps between powers of `log X`. Let


```math
K_i=\left\lceil\frac{\alpha_i n}{L^{a_i}}\right\rceil,
 \qquad \delta=\frac{\eta}{L^d},\qquad L=\log X,
 \quad(a_0,a_1,a_2,a_3;d)=(5,5,3,3;2).                 \qquad\text{(W1)}
```


All coefficients here are positive rational numbers. Take the same constants
as FSC: `c=2^16`, graph degree 64, cut expansion 8, graph-plus-path degree
66, and `H=2^20*67=70254592`. No graph, packing, cut-flow, tensor-routing,
reservoir or centering argument is changed.

The centering, tensor and deletion exponent margins now equal zero. Their
constant ratios therefore matter. The relevant limiting inequalities include


```math
(2c+1/8)\frac{\alpha_0}{\alpha_1}\lt 1,\qquad
 \frac{25\alpha_0+800c\alpha_1}{9\alpha_2}\lt 1,\qquad
 2c\frac{\alpha_2}{\alpha_3}\lt 1,                         \qquad\text{(W2)}
```



```math
96\eta\frac{H\alpha_3+c\alpha_2}{\alpha_0}\lt 1,
 \qquad 24\,2^{23}\frac{\alpha_2}{\eta}\lt 1.             \qquad\text{(W3)}
```


Every lower-order term and every ceiling must still be paid. These formulas
only identify a feasible coefficient region before exact evaluation.

A simple explicit point is


```math
(\alpha_0,\alpha_1,\alpha_2,\alpha_3)
   =(2^{-161},2^{-143},2^{-120},2^{-102}),
 \qquad \eta=2^{-92}.                                  \qquad\text{(W4)}
```


The exact limiting horizontal ratio is `1048577/2097152`; the tensor ratio
is `1527099483025/2199023255552`; the face ratio is `1/2`; the centering
ratio is `843055107/1073741824`; and the midpoint deletion ratio is `3/4`.
The small `K0` terms in the first two ratios and the old `K2` term in
centering have not been discarded.

## 2. Rational balancing and preserved profiles

For a rational `q>1`, put


```math
A=C=2c,\qquad B=\frac{800c}{9},\qquad E=24\,2^{23},
 \qquad
 \eta=\frac{1}{q^3AB\,96(HqC+c)},                       \qquad\text{(W5)}
```



```math
\alpha_2=\frac{\eta}{qE},\quad
 \alpha_1=\frac{\alpha_2}{qB},\quad
 \alpha_0=\frac{\alpha_1}{qA},\quad
 \alpha_3=qC\alpha_2.                                  \qquad\text{(W6)}
```


The leading face, centering and midpoint deletion ratios are exactly `1/q`.
The horizontal ratio is `(1+1/(16c))/q`; the tensor ratio is
`1/q+25alpha0/(9alpha2)`. Thus those last two are slightly larger than
`1/q`. The full finite check below, rather than an equality of approximate
leading ratios, determines the required domain.

All these profiles have `0<alpha0<=alpha1<=alpha2<=alpha3<=1`. Since the
exponents are nonincreasing, `alpha_i/L^ai` is pointwise nondecreasing in
`i` for `L>=1`; taking ceilings preserves the actual scale order. The
companion module retains (W4) and the balanced choices
`q=1001/1000`, `10001/10000`, and `100003/100000` separately. It also
exposes (W5)–(W6) for other exact rational choices, which must pass the same
finite rows. An unsuccessful parameter choice is a failure of sufficient
inequalities, not a counterexample to prime cubes.

## 3. Exact all-tail envelopes

Assume the separate exact-pool estimates give `n^3<=X<=n^4` and
`L>=2^16`. As in FSC, `L/4<=log n<=L/3` and `n>=L^201` throughout
this real tail. Set `t=L^-201` and use the pointwise bounds


```math
\frac{\alpha_i}{L^{a_i}}\le\frac{K_i}{n}
 \le k_i:=\frac{\alpha_i}{L^{a_i}}+t,\qquad
 F\le f:=100L+1,\quad g\le G:=24L+16,\quad R\le r:=12L+7,
                                                               \qquad\text{(W7)}
```



```math
P\le p:=256f^2+32f(3L/2+1),\qquad \lambda:=5L/3+5.
                                                               \qquad\text{(W8)}
```


Here `F=ceil(100L)`, `R=g/2-1`, and the native prefix length and all
floor conventions remain exactly those of FSC. Lower bounds on `Ki/n`
are used in every denominator. Define the normalized upper bounds


```math
j=pt+32k_3+rt,\qquad
 s=4pt+32k_0+64k_1+32k_2+4rt,\qquad M_*=Hj+cs,
                                                               \qquad\text{(W9)}
```



```math
b_p=(4c+H)pt,\quad b_r=(4c+H)rt,\quad
 b_m=32c(k_0+2k_1+k_2)+32Hk_3,
                                                               \qquad\text{(W10)}
```



```math
Q_*=4288pt+2048k_0+4096k_1+131072k_2
       +8(192+4t)t(pt+32k_3)+(8+38t)rt.               \qquad\text{(W11)}
```


In this section only, `Q_*` is a normalized outward bound for the actual
entry invoice divided by `n^3`; it is not the deletion allowance called
`2^21 n^2 K2` in FSC. The two meanings are kept separate by the formula.

The following principal ratios must be at most one:

| Finite condition | Outward ratio |
|---|---|
| Joint packing | `100(M_*+(H+c+100)t)` |
| New cuboid packing | `100H(j+t)` |
| Rectangular free choices | `12*64^2/c+4M_*+j+8t` |
| Slice free choices | `10*64/c+2M_*+j+6t` |
| Plane free choices | `10*64/c+2M_*+2j+10t` |
| Reserved pool below one half | `2Q_*` |
| Complete invoice versus joint deletions | `Q_* L^a2/(2^21 alpha2)` |
| Centering, changed mean, both concentration steps and residues | `(3b_p+4b_r+3 eta L^-d b_m+16L^-100)L^a0/alpha0` |
| Horizontal correction | `(2k0+c(pt+32k0))L^a1/(16alpha1)` |
| Tensor correction | `{lambda^2(2k0+2c(pt+32k1))+Gt^4/2+512Gt^2}L^a2/(2alpha2)` |
| Face correction after all four bodies | `(2k0+c(3pt+64k1+32k2)+4t)L^a3/(16alpha3)` |

The remaining six controller rows are the unchanged graph union bound;
`48eta L^-d` for the midpoint width; `256Gf^2t^3` for prefix growth;
`Gt^4 L^a0/alpha0` for native floor capacity; and `8t^6` for each of
the two concentration union bounds. Thus all seventeen hypotheses are
covered, including the original axis controls and the new diagonals.

Every displayed ratio expands as a Laurent polynomial in `L` with
nonnegative rational coefficients and no positive exponent. The code
checks those two facts for every generated polynomial. Each ratio is
therefore nonincreasing on the entire positive real line, including all
larger values of `L`; every actual ceiling is bounded pointwise by (W7).
The proof never differentiates a ceiling or infers a whole tail from a
finite sampling. Constant terms are retained and must be strictly below
one before a finite sufficient domain is sought.

## 4. Prime-supply algebra and its literal analytic requests

The common-gap seed construction and exact complete invoice are unchanged.
The complete seed-pair demand remains
`256F^2(2144n^2+768n+16)`, including four distinct pairs for each new
cuboid seed stage. Under the uniform strong prime-count hypothesis on
`[X/4,3X/4]`, the same elementary seed proof yields
`floor(X/(1024L^3))` pairs in one reduced class, with `2<=g<=8L`.

Use the separate exact-pool estimate


```math
\frac{X}{n^3}\gt L-\frac32\ge\frac L2.                  \qquad\text{(W12)}
```


Besides the harmless interval-containment and modulus rows, the supply
ratios are as follows:

| Supply condition | Outward ratio |
|---|---|
| Seed demand and its floor loss | `2048L^2{256f^2(2144t+768t^2+16t^3)+t^3}` |
| Midpoint deletions at most half a class supply | `2^23 G(L+1)k2 L^(d-1)/eta` |
| Global growth deletions at most half a class supply | `2^25 G k2` |
| Four disjoint equal-gap pairs after deletions | `32G(L+1)^2 t^3 L^(2d)/eta^2` |
| Seed integer and reduced-class losses, each | `32L t^3` |
| Remaining global density relative to `X/(gF)` | `8/100` |

The factor `2^25` in the direct global-growth ratio pays the factor 2
from (W12). Independently, the midpoint deletion condition implies the
global-growth condition whenever `delta<=1/4`; the direct row is retained
so its claimed numerical meaning is exact.

For the lower and upper midpoint bands let `Y=m±X/6`, `u=log Y`.
The mean bounds `12X/25<m<501X/1000` give `X/4<Y<X` and `u>L-2`.
If the analytic strong theorem is proved for intervals of length at least


```math
\frac{Y}{(1/\eta)u^d},                    \qquad\text{(W13)}
```


then it applies to the actual band of length `2eta X/L^d`: for `u>=4d`,
`(L/u)^d<=(1+2/u)^d<=2`. The sufficient finite row `(4d+2)/L<=1`
pays the passage from `L` to `u`. The original moduli obey
`g<=24L+16<=64(L-2)<64u` when `L>=18/5`, also separately recorded.
In (W4), (W13)'s denominator is `2^92`; the balanced profiles use the
exact rational denominator `1/eta`.

These large fixed denominators exceed the original analytic component's
stated parameter range. They require a separately proved extension; this
component does not call that theorem outside its domain. The source
must still preserve its exceptional signs, conductor normalization,
endpoint conventions and whole-tail error comparisons.

After the worst preceding deletion of `2^21 n^2 K2` entries, the two
actual class stocks are at least `delta X/[2g(L+1)]`. The fourth row
above proves `delta^2 X>=32g(L+1)^2`. Together with `X>=g` it makes
their product at least `4(floor(X/g)+1)`, so there are four disjoint
equal-difference pairs. The bands are disjoint; equality of a positive
difference already yields a matching. This pays actual cuboid requests,
not a putative one-pair substitute. The residue classes `-1,+1` remain
units for every even gap, and `g=2` still needs no residue stages.

## 5. Exact finite results and scope

The standard-library checker is
`explicit_signed_weighted_controller.py` (see [verification scope](../PROVENANCE.md#explicit-prime-cube)).
All decisions use integer and `Fraction` arithmetic. Decimal intervals
below are outward renderings only.

| Profile | First sufficient `L` in the proved envelope domain | Centering ratio there | Tensor ratio there | Midpoint deletion ratio there |
|---|---:|---|---|---|
| (W4), powers of two | 65536 | `[.785156252793,.785156252794]` | `[.694508024188,.694508024189]` | `[.750019073602,.750019073603]` |
| (W5), `q=1001/1000` | 65536 | `[.999000999000,.999000999001]` | `[.999092462371,.999092462372]` | `[.999026405065,.999026405066]` |
| (W5), `q=10001/10000` | 65536 | `[.999900009999,.999900010000]` | `[.999991555677,.999991555678]` | `[.999925438926,.999925438927]` |
| (W5), `q=100003/100000` | 200002 | `[.999970000899,.999970000900]` | `[.999999999928,.999999999929]` | `[.999978333916,.999978333917]` |

For every row and every profile the finite ratio is at most one at the
listed domain, and the Laurent proof establishes all larger real `L`.
The first three floors are the common auxiliary-domain floor, not an
assertion that a condition fails at 65535. The last floor is set by
the tensor ratio, including its constant `+5`, all prefix terms and its
native rounding losses. These are component domains, not cube cutoffs.

The recorded arithmetic checks cover these profiles.

See the [verification record](../PROVENANCE.md#explicit-prime-cube) for the checks on these profiles.

Nine negative controls reject doubled centering load, halved midpoint
supply, doubled tensor input, doubled final-level load, an unproved old cap,
a growing exponent margin, unordered scales, an unsupported envelope
domain, and the invalid reuse of the old total-deletion supply envelope at
the constant scales below. Their rejection establishes arithmetic and parameter discipline;
it is not a substitute for independent mathematical review. FSC's exact
support construction, full correction order, body spill, target
compatibility and exact-pool permutation conclusion remain the same
parameterized theorem consumed by the new composition.

## 6. Constant final scales: geometric result with a separate supply obligation

The same finite geometric and correction inequalities permit


```math
(a_0,a_1,a_2,a_3;d)=(2,2,0,0;2).                    \qquad\text{(W14)}
```


In particular `K2` and `K3` may be fixed small fractions of `n`, with
ceilings. This statement uses FSC's proved finite exclusions, not its
qualitative predecessor's `o(n)` assertions. Every occupied-cell and
distinct-coordinate term remains in (W9) and the full seventeen ratios;
the constant terms of joint packing and old free choices are now positive
and are evaluated.

A simple profile is


```math
(\alpha_0,\alpha_1,\alpha_2,\alpha_3)
 =(2^{-101},2^{-83},2^{-60},2^{-42}),\qquad \eta=2^{-92}.
                                                               \qquad\text{(W15)}
```


For a more tightly balanced profile, use `A,B,C` from (W5), choose rational
`q>1`, and set


```math
\eta=\frac1{q^3AB\,96(HqC+c)},\qquad
 \alpha_2=\frac1{q\,3200(HqC+c)},\qquad
 \alpha_1=\frac{\alpha_2}{qB},\quad
 \alpha_0=\frac{\alpha_1}{qA},\quad
 \alpha_3=qC\alpha_2.                                  \qquad\text{(W16)}
```


The identity `alpha0=(3/100)eta` is exact. The limiting joint-packing,
centering and final-face ratios equal `1/q`. The horizontal and tensor
ratios include the same small positive `K0` terms as in Section 2.
The remaining geometric ratios have their actual constant contributions;
none is declared negligible merely because its coefficient is small.

All seventeen finite rows pass for every real `L>=65536` both for (W15)
and for (W16) with `q=10001/10000`. The exact base-point enclosures include:

| Finite condition | (W15) upper ratio at `L=65536` | (W16), `q=10001/10000`, upper ratio |
|---|---:|---:|
| Joint packing | `.051116943542` | `.999900010000` |
| New cuboid packing | `.051116943360` | `.999900002884` |
| Rectangular free choices | `.752044677749` | `.789996000543` |
| Centering with residues | `.785156252794` | `.999900010000` |
| Horizontal stage | `.500000476838` | `.999900963578` |
| Tensor stage | `.694508024189` | `.999991555678` |
| Face stage after bodies | `.500000000001` | `.999900010000` |

The code allows zero exponents, uses the same pointwise ceiling bounds,
and proves persistence by nonnegative Laurent coefficients with no positive
powers. The constant reserved fraction is paid before using the changed
unused-pool mean. The finite packing inequality is verified with its full
factor 100; the construction does not merely assume that an arbitrarily
small fixed fraction behaves like a vanishing one.

**The supply distinction is essential.** The old PS2/PS3 proof charged
the entire invoice against every one of the two narrow midpoint classes.
At (W14), its midpoint-deletion envelope has a positive power of `L`, so
that old sufficient proof has no complete tail. The companion module
therefore rejects these profiles in its default full-supply mode. They
are available only with `include_supply=False` or `--controller-only`.
The theorem supplied by this section is a finite geometry and correction
result conditional on the required physical reservoir data. A new prime
allocation proof must furnish that data and pay its own preceding deletions.

For precision, the data consumed after prime allocation are exactly the
disjoint input pairs defining each reservoir: the complete prefix grid;
the stated number of macro stages with differences in `[X/4,X/2]`
divisible by `g` and pair midpoints within `delta X` of `m`; and the
residue stages with their specified differences congruent to 2 modulo
`g`. Every cuboid stage requires four actual disjoint pairs of its common
difference. The pairs for all reservoirs must be disjoint from one another.
The geometric embedding and reference-state proofs use these differences,
midpoints and counts, not a common endpoint residue for all macro stages
or the temporal order in which primes were allocated. Each macro pair
may therefore be in any reduced class, provided its two endpoints have
the same class and the required common difference. Arbitrary new supply
claims are not inferred from this observation.

Once such data have been constructed within the exact first `n^3` odd
primes, FSC's finite proof from support embedding through concentration,
residues, triangular axis corrections, bodies and face flows applies
unchanged under the seventeen checked inequalities. An allocation that
constructs all prefixes and residue reservoirs before the macros is
compatible with this use, but its supply and depletion argument belongs
to the separate complete composition. In particular this section does
not assert PS2 after the full invoice when only a smaller phase-specific
deletion budget has been proved.

The two controller-only profiles have separate recorded checks.

See the [verification record](../PROVENANCE.md#explicit-prime-cube) for the checks on these profiles.

These successes establish the complete finite physical allowances for the
new scale choices. They supply no numerical cube cutoff until the new
prime allocation, actual analytic domains and exact target construction
are all composed and independently reviewed.
