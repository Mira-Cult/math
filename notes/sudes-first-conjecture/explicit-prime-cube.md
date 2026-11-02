# An explicit full signed-line prime cube for every odd order above 2^61750

Public proof manuscript. See [provenance](PROVENANCE.md#explicit-prime-cube) for the pinned sources, internal review and verification limits.

## The theorem

**Theorem ESC3-R.** Set the specified integer


```math
\boxed{N_0=2^{61750}}.
```


For every odd integer $`n\ge N_0`$, precisely the first $`n^3`$ odd primes
admit a bijective placement in an $`n`$-by-$`n`$-by-$`n`$ cube such that
every full signed-coordinate line has prime sum. Each coordinate of such a
line is fixed, $`t`$, or $`n+1-t`$, for $`1\le t\le n`$, and at least
one coordinate varies. Identical cell sets are counted once. For $`n\ge3`$
there are exactly $`3n^2+6n+4`$ such lines: all axes, both diagonals in every
coordinate-parallel square slice, and the four body diagonals. Prime sums
may repeat. Every input prime occurs exactly once. For $`n=1`$, the separate
singleton cube contains 3.

This is an unconditional conventional proof using the explicitly stated
classical analytic imports. The certificate uses exact integer and rational
arithmetic to check their domains and every displayed composition inequality.
It is not a kernel verification of those imports or of the geometric proofs.
An explicit cube at the cutoff is unnecessary and is not enumerated.

The first successful research checkpoint had cutoff $`2^{250226}`$. The present
manuscript gives the improved complete proof; the source and review history
are recorded in [provenance](PROVENANCE.md#explicit-prime-cube). The earlier
[qualitative cube proof](prime-cube.md) remains a separate Manuscript IV.
Neither this theorem nor its cutoff changes the square bound $`2^{4320}`$.

## 1. Parameters, exact prime pool and local scales

Let


```math
X=p_{n^3+1},\quad T=\sum_{j=2}^{n^3+1}p_j,\quad
 m=T/n^3,\quad\mu=T/n^2=nm,\quad L=\log X,\quad v=\log_2n.
```


Analytic logarithms are natural. Set $`c=65536`$, $`H=70254592`$,
$`q=10001/10000`$, $`A=C=2c`$, and $`B_c=800c/9`$. Define the following
fixed positive rational numbers (the symbol $`B_c`$ is not a prime-scale
ceiling or a number of reflected bins):


```math
\begin{aligned}
 k_2&=\{3200q(HqC+c)\}^{-1},& k_1&=k_2/(qB_c),\\
 k_0&=k_1/(qA),&k_3&=qCk_2,\\
 \eta&=\{96q^3AB_c(HqC+c)\}^{-1}. &&
\end{aligned}                                                    \qquad\text{(1)}
```


In particular $`k_0=3\eta/100`$ exactly. Their evaluated values are:

| Constant | Exact rational value |
|---|---|
| $`k_0`$ | $`2197265625/49457052345572100623155796370771673088`$ |
| $`k_1`$ | $`3515625/603663417173567074727534526464`$ |
| $`k_2`$ | $`15625/460512586111358861312`$ |
| $`k_3`$ | $`25/5620929436736`$ |
| $`\eta`$ | $`18310546875/12364263086393025155788949092692918272`$ |

Use precisely


```math
\begin{gathered}
K_0=\lceil k_0n/L^2\rceil,\quad K_1=\lceil k_1n/L^2\rceil,\\
 \quad K_2=\lceil k_2n\rceil,\quad K_3=\lceil k_3n\rceil,
 \qquad\delta=\eta/L^2.                                      \qquad\text{(2)}
\end{gathered}
```


Thus the last two scales are fixed small fractions of $`n`$. Their packing
is proved by finite inequalities below; an old $`o(n)`$ exclusion is not
being used at these scales. Set


```math
F=\lceil100L\rceil,\quad B=\lceil\log_2X\rceil,
 \quad s=256F^2,\quad P=s+32FB.                              \qquad\text{(3)}
```


A common even gap $`g\le8L`$ is selected from actual input-prime pairs;
put $`R=g/2-1`$. Each level uses exactly $`32K_i`$ macro stages. The
target radius and the analytic length denominators are


```math
d_t=\frac{\mu}{\rho L^2},\quad \rho=\frac{101}{100k_0},\qquad
 D_m=\lceil1/\eta\rceil=675253621358211080508153807,
```


```math
D_t=\left\lceil\frac{203}{100k_0}\right\rceil
       =45692161711905616447718407570.                       \qquad\text{(4)}
```


The exact-pool bounds, including the excluded prime 2, are rederived in
[the analytic source](cube-explicit/explicit_signed_analytic.md). RS62 Theorem 2 gives,
for the present range,


```math
n^3\le X\lt n^4,\quad X/n^3\gt L-3/2,\qquad
             12X/25\lt m\lt 501X/1000.                          \qquad\text{(5)}
```


The first two inequalities hold for $`n\ge64`$, and the mean box for
$`L\ge1000`$. The identity used for the mean is
$`T=X(\pi(X)-1)+X-\int_2^X\pi(t)\,dt-2`$. The finite RS62 integral
bounds, rather than an asymptotic mean, are replayed by the certificate.
These also give explicit bounds for $`T=n^3m`$ and $`\mu=nm`$.

For $`L\ge65536`$, $`n\gt e^{L/4}\ge L^{201}`$. At the endpoint,
$`65536/4\gt 201\cdot16\gt 201\log65536`$, and the derivative
$`1/4-201/L`$ is positive. This bound pays every polynomial prefix and
rounding term throughout the tail. With $`t=v\log2`$, define


```math
G_a(v)=3t+\log\{a(3t-3/2)\},\qquad
 H_a(v)=4t+\log\{a(3t-3/2)\}.                           \qquad\text{(6)}
```


Both functions increase. Equations (5) imply $`\log(aX)\gt G_a(v)`$ and
$`\log(anX)\gt H_a(v)`$. These are lower bounds for every real $`v`$ in
the tail, not just endpoint approximations.

## 2. Effective analytic input, including arbitrarily large fixed denominators

The former power-window Thorner--Zaman input is not consumed here. A
relative error of the form $`\exp(-c\sqrt{\log X})`$ does not eventually
fit a fixed negative power of $`X`$. The new windows in (2) and (4) have
inverse-logarithmic relative size and are supplied by the finite analytic
interfaces AW/AS, proved from explicit BMOR and McCurley bounds in
[their dedicated source](cube-explicit/explicit_signed_analytic.md).

Write $`u=\log Y`$, and let $`I\subset[Y/2,2Y]`$ be half-open, of length
at least $`Y/(D u^b)`$. AS provides


```math
\#\{p\in I:p\equiv a\pmod h\}
        \ge |I|/(2\varphi(h)\log(2Y))\quad(h\le64u),          \qquad\text{(7)}
```


and AW provides


```math
\#\{p\in I:p\equiv a\pmod h\}
        \ge |I|/(4h\lceil\log_2Y\rceil^9)
                      \quad(h\le512u^2),                    \qquad\text{(8)}
```


uniformly in reduced classes. No ineffective threshold remains in the
instances used below. The original analytic code stated $`D\le10^{12}`$.
Since (4) exceeds that domain, the following extension is part of this
proof, and its arithmetic verification is recorded in [provenance](PROVENANCE.md#explicit-prime-cube).

**Fixed-denominator extension.** AW/AS remain valid for any fixed exact
rational $`D\ge1`$ when their displayed normalized endpoint inequality
and both scaled remainder inequalities are verified. Their domain and
tail-derivative conditions are unchanged.

To prove this, put $`R_1=9.645908801`$ and choose a rational
$`\alpha\lt \sqrt{(U-1)/(R_1U)}`$. The even lifted modulus is bounded by
$`Q=128u`$ in AS and $`Q=1024u^2`$ in AW; small lifts are also required
to be at least 100000. With $`B_Q=\log Q`$, the source's endpoint terms are


```math
f=2Q(0.32181\alpha\sqrt u+4)e^{-\alpha\sqrt u},\qquad
 r=2^{21}u^5e^{-u}+2^{12}u^2e^{-u/2}.                       \qquad\text{(9)}
```


The normalized sufficient bounds are $`4D u^b(f+r)\lt 1`$ for AS and
$`2D B_Q^2u^b(f+r)\lt 1`$ for AW. The unfavorable exceptional term is
bounded with its sign; the favorable term has the corresponding stronger
main increment. Neither is dropped. Primitive conductor normalization,
omitted Euler factors, the reflected exceptional zero, both endpoints,
and prime-power removal are retained in the underlying derivation.

The factor $`D`$ multiplies only the required error budget. It changes
neither zero-free and zero-counting domains nor any logarithmic derivative.
The extension computes the spectral enclosure at $`D=1`$, removes the
explicitly added $`2^{-127}`$ remainder allowance, and multiplies the
spectral part by $`D`$. It then proves afresh that each scaled nonspectral
term is below $`2^{-128}`$, before restoring their sum. For example the
weak polynomial and root coefficients are bounded by
$`2D2^{21}U^{b+7}`$ and $`2D2^{12}U^{b+4}`$, using $`B_Q\lt U`$.
Their integer ceiling bit lengths are checked against $`U-128`$ and
$`\lfloor U/2\rfloor-128`$, respectively; $`e\gt 2`$ makes these
sufficient. The source derivative inequalities make these comparisons
persist for all real $`u\ge U`$. This proves the extension without an
out-of-domain call to the old theorem and without scaling an unpaid
truncation error.

Here are the evaluated thresholds, including rejection of the immediately
preceding integer $`U`$ by an actual analytic comparison. For the global
request it is the strong exceptional-main guard; for the other three rows
it is the endpoint error budget:

| Request | $`b,D`$ | Analytic floor $`U`$ |
|---|---|---:|
| Global seeds and prefix growth, AS | $`0,1`$ | 16081 |
| Every reflected bin and residue window, AS | $`2,D_m`$ | 110866 |
| All strong target requests, AS | $`2,D_t`$ | 120365 |
| All weak target requests, AW | $`2,D_t`$ | 171218 |

The quoted first sufficient floors belong to this proved sufficient model;
their failure one step below is not a lower bound for any prime statement.

## 3. Prime supplies: seeds, early phases and a new reflected-bin allocation

The finite phased supply theorem FSR is fully proved in
[the reflected allocation source](cube-explicit/explicit_signed_reflected_supplies.md).
Here are its requests, invoices and proof, so the change of architecture is
explicit in the composition.

AS on $`(X/4,3X/4]`$, centered at $`X/2`$, supplies at least $`X/(4L)`$
primes. Pair consecutive elements. Their gaps sum to at most $`X/2`$, so
at most $`X/(16L)`$ exceed $`8L`$. After the initial floor loss, at least
$`X/(32L)`$ pairs have one of at most $`4L`$ even gaps. Pigeonholing
also over at most $`8L`$ lower endpoint classes supplies
$`\lfloor X/(1024L^3)\rfloor`$ disjoint pairs with one common gap and
one reduced class. Reducedness follows because every prime exceeds the gap.
The full seed-pair demand is $`256F^2(2144n^2+768n+16)`$; the extra unit
for the floor and every cuboid's four actual pairs are explicitly paid.

Allocate **all seeds, then all prefixes, then all residues, then all
macros**. This is an allocation order, distinct from the eventual correction
order. The maximum entry invoice before macros is


```math
Q_0=4288n^2P+8(192n+4)P+(8n^2+38n-14)R.                \qquad\text{(10)}
```


The full invoice, including all old and new controls, is


```math
\begin{aligned}
 Q={}&n^2(4288P+2048K_0+4096K_1+131072K_2)\\
 &+8(192n+4)(P+32K_3)+(8n^2+38n-14)R\\
 &\le Q_*:=2^{21}n^2K_2.                               \qquad\text{(11)}
\end{aligned}
```


The exact $`32K_3`$ convention fits the previous $`33K_3`$ allowance;
the new residue invoice fits the previous $`24ng`$ allowance. The
complete old invoice is retained, not hidden in an asymptotic term.

The seed, growth and residue supply rows prove


```math
Q_0\le X/(8gL),\quad Q_0\le\delta X/[2g(L+1)],\quad
 \delta^2X\ge32g(L+1)^2,\quad 256gF^2\le X.            \qquad\text{(12)}
```


The fresh global reduced class retains more than $`X/(gF)`$ elements.
The finite repeated-difference lemma grows each complete subset-sum prefix
to length at least $`X`$ within $`P`$ stages. Each cuboid takes four
actual disjoint equal-gap pairs at each request. The residue windows
centered at $`m\pm X/6`$ retain their classes $`-1,+1`$; the product
of their stocks exceeds $`4(\lfloor X/g\rfloor+1)`$, yielding four
disjoint pairs of gap $`2\pmod g`$. If $`g=2`$, this phase is empty.
All removed endpoints are included in (10).

For macros, a single pair of narrow bands cannot supply the constant
$`K_2/n`$ profile. Set $`w=1/48`$, $`B_r=\lfloor w/\delta\rfloor`$,
$`h=2\delta X`$, $`a=m-X/6-wX`$. Use the disjoint reflected bins


```math
I_i=(a+ih,a+(i+1)h],\quad
 J_i=(2m-a-(i+1)h,2m-a-ih],\quad0\le i\lt B_r.             \qquad\text{(13)}
```


All bins lie in $`[X/4,3X/4]`$; their lower and upper whole bands are
disjoint. In each reduced class modulo $`g`$, each bin initially contains
at least $`W=\delta X/(\varphi(g)(L+1))`$ primes. Let $`A_{i,r}`$ and
$`C_{i,r}`$ denote their remaining stocks. The aggregate
$`S=\sum_{i,r}\min(|A_{i,r}|,|C_{i,r}|)`$ decreases by at most one per
deleted prime. This deterministic fact holds for adaptive and concentrated
deletions. Since $`B_r\delta\ge w/2`$, the checked conditions


```math
Q_*\le\frac{wX}{4(L+1)},\qquad
                    \delta wX\ge128(L+1)^2             \qquad\text{(14)}
```


give $`S\ge wX/[4(L+1)]`$. Cauchy's inequality gives at least
$`S^2/(B_r\varphi(g))`$ available lower/upper pairs within matching
bin/classes. There are at most $`2X/g`$ differences. Some difference
therefore has at least $`S^2/(2B_rX)\ge4`$ occurrences. For a fixed
positive difference the occurrences form a matching, because each endpoint
determines its partner and the two whole bands are disjoint. Thus every
macro request has four fresh equal-gap pairs. Their midpoints are within
$`\delta X`$ of $`m`$, and their shared gap lies in
$`[7X/24,3X/8]\subset[X/4,X/2]`$ and is divisible by $`g`$.

Different macros may use different reduced classes. The physical controller
needs the gap, midpoint and disjointness properties, not a common macro
class. The matching invariant holds after every earlier request using the
full invoice (11). This proves the revised supply hypothesis; it does not
assert that the older all-deletions-in-one-class hypothesis holds.

The actual bin centers satisfy
$`Y_-\gt 117X/400`$, $`Y_+\gt 751X/1200`$. The residue centers have lower
bounds $`47X/150`$, $`97X/150`$. With $`u=\log Y`$, $`L\lt u+2`$,
$`(L/u)^2\le2`$, and $`2\delta X\ge Y/(D_m u^2)`$.
Also $`g\le24L+16\le64u`$. Thus AS applies at every local center,
uniformly in the chosen gap and in every adaptive request. No lower center
has been replaced by $`X`$.

## 4. Exact-total prime targets using the finite TQ lemma

The frozen square source is scientific revision
`f519b7fd796393cd6ab202f6790fe1824e6fc22f`, reviewed delivery
`b776784e3cffc3aeeb3c3c6886516c3337a16bd1`. Only its named finite and
analytic mechanisms are imported. In particular its square cutoff is not
applied to this cube. The new [cube TQ composition](cube-explicit/explicit_signed_targets_tq.md)
proves the target interface used here from the literal frozen TQ lemma.

For $`\ell=\lceil\log_2 y\rceil`$, sufficient finite sizes are


```math
k\ge680\ell^{11},\qquad2048\ell^{11}\le d_t\le y/4.   \qquad\text{(15)}
```


Both progression counts are required down to length $`d_t/2`$. The
TQ proof constructs the needed small-gap pairs by partitioning an already
counted stock; it does not silently ask the analytic theorem for counts
in those smaller bins. Its wide pairs use the extended $`2d_t`$ region,
and its subset-sum interval and two-coordinate unit CRT meet the exact
target residue. The new cube composition checks that these operations fit
every finishing list, including the shifted centers.

Specifically, the symmetric axis-target construction assigns weight-two
off-diagonal orbits with discrepancy at most $`2d_t`$. Exactly $`n`$
diagonal slots remain, centered within $`2d_t/n`$ of $`\mu`$. TQ fills
them with the exact total. The resulting symmetric matrix defines all
three axis-target arrays and all their margins with grand total $`T`$.
For each of six face families its required total is the corresponding
diagonal-square aggregate. Such a total may be composite and a nonunit
modulo $`g`$. The three-unit CRT construction, valid prime-power by
prime-power, supplies prescribed unit residues with that total; TQ then
supplies its length-$`n`$ prime list with the exact integer total. Four
body primes need no further family-total constraint.

Every target differs from $`\mu`$ by at most $`(2+2/n)d_t`$. Hence for
$`n\ge200`$, (4)--(5) give


```math
\frac{\max|\text{target}-\mu|}{K_0X}
    \le\frac{(201/100)(501/1000)}{\rho k_0}
    =\frac{100701}{101000}\lt 1.                          \qquad\text{(16)}
```


This sharp bound matters: replacing it by $`3d_t`$ would fail. Every
local target mean $`y\in[\mu-2d_t,\mu+2d_t]`$ lies in
$`[7\mu/8,9\mu/8]`$. Thus $`u=\log y\ge L`$, $`y\ge X`$, and
$`\log y\ge H_{21/50}(v)`$. The shifted-window inequality


```math
(D_t-2\rho)L^2\ge4                  \qquad\text{(17)}
```


proves $`d_t/2\ge y/(D_tu^2)`$. The explicit choice (4) pays its
positive margin. All intervals stay in $`[y/2,2y]`$. The weak TQ modulus
bound $`128\ell^2\le512u^2`$, the gap bound $`g\le16\ell`$, and the
strong modulus conditions are all checked at the shifted center. Nine
target-algebra comparisons prove (15)--(17) and their real-tail persistence
already for $`v\ge113`$. In particular the finishing length is $`n`$,
never $`n^2`$. Target primes may repeat; none is inserted as an extra
input entry.

## 5. Finite packing, centering and the complete correction

We use the parameterized finite controller FSC, with the supply replacement
FSR proved above. Its full geometric and probabilistic proof is
[here](cube-explicit/explicit_signed_controller.md); the additive
[weighted derivation](cube-explicit/explicit_signed_weighted_controller.md) retains
all coefficients when exponents coincide. The following is the complete
finite interface consumed in this proof.

The routing graph has degree at most 64 and cut expansion at least 8; its
existence follows from the retained finite random-permutation union bound.
The residue path raises the relevant degree to at most 66, so
$`H=2^{20}(66+1)`$. Put


```math
J=P+32K_3+R,\quad S=4P+32K_0+64K_1+32K_2+4R,\quad M=HJ+cS.
```


The checked packing requirement is
$`n\ge100(M+H+c+100)`$. In particular
$`n\ge\max(11,100H(J+1))`$ for all prefix, macro and residue passes.
The old face cap $`c=65536`$ is justified in FSC: the largest old rectangle
saturation fraction is $`12\cdot64^2/c=3/4`$; occupied-cell, exceptional
axis, distinct-coordinate and reflection exclusions leave the displayed
positive free-choice margins. For example the full rectangle ratio is
$`3/4+(4M+J+8)/n\lt 1`$. Its plane and slice counterparts, and the native
old loads, are checked as well. The profile does not use the old
asymptotic $`c=10^{12}`$ argument without re-proving its finite demands.

Old supports avoid the four body diagonals. Fresh reflection orbits across
an entire body bundle limit the later spill on any face to $`4X`$,
including central and reflected coordinates. The four-pair physical cuboid
identities isolate the required face transfers or body correction, preserve
axes as required, and use distinct occupied cells. Prefix lengths, native
reference states and scalar complete-grid ranges include their floor losses.

For centering define


```math
B_p=(4c+H)P,\quad B_r=(4c+H)R,\quad
 B_m=32c(K_0+2K_1+K_2)+32HK_3.
```


The exact centering/residue inequality is


```math
3B_p+4B_r+3\delta B_m+16\sqrt{n\log n}\le K_0. \qquad\text{(18)}
```


Whole complementary reservoir orientations are randomized independently;
dependent cells within a reservoir are never randomized separately. For
each axis, face or body line the range contribution of one fair reservoir
is at most $`2X`$, with at most $`n`$ nonempty contributors. Hoeffding
with deviation $`4X\sqrt{n\log n}`$ gives at most $`2n^{-8}`$ per
line. Union-bounding over exactly $`3n^2+6n+4\le4n^2`$ lines costs at
most $`8n^{-6}`$. The remaining pool is sampled without replacement;
the same finite sampling inequality and union bound apply to its completion.

Before this use of the unused-pool mean, (11) and the separate occupancy
row prove $`Q\lt n^3/2`$. The change in its mean is explicitly bounded by
the total reserved discrepancy divided by the unused cardinality. The
prefix, residue and midpoint terms in (18), and its retained concentration
allowance, pay the resulting drift. Both bad-event unions together are
less than one. Consequently a reference placement exists whose line errors,
after residue repair, require at most the declared $`K_0X`$ centering
allowance. Including (16) makes the first correction demand at most
$`2K_0X`$.

The correction order is residues, plane axes, horizontal axes, vertical
axes, four bodies, then six face-family flows. The successive finite demands
are checked separately:


```math
\begin{aligned}
2K_0+c(P+32K_0)&\le16K_1,\\
(5\log n+5)^2\{2K_0+2c(P+32K_1)\}
       +g/(2X)+512gn^2/X&\le2K_2,\\
2K_0+c(3P+64K_1+32K_2)+4&\le16K_3.                  \qquad\text{(19)}
\end{aligned}
```


These retain the smaller triangular drifts; no stage is prematurely
bounded by $`K_3`$. The tensor estimate is the integer routing bound,
not a rational-rank claim. Once axes and bodies are fixed, the six exact
family identities make each face demand sum zero. Integral graph flows on
the $`g`$-grid, cut expansion 8 and the checked demands fit the scalar
capacity


```math
g\lfloor3K_3X/g\rfloor\ge2K_3X,
```


using $`K_0X\ge g`$, scale ordering, and the native floor conventions.
Every switch permutes the input entries. Compatibility follows from the
integer signed incidence theorem for odd $`n\ge11`$, with its six
additional identities and no additional body relation. The order-five
torsion and order-three diagonal-square obstruction are retained as finite
regressions and are not extrapolated to this tail. The final placement
therefore has exactly the prime targets already constructed, proving the
desired full signed-line coverage.

## 6. Numerical maximum, all-tail proof and bottlenecks

The thirty controller/supply rows are nonnegative Laurent polynomials in
$`L`$ with nonpositive powers, using $`n^{-1}\le L^{-201}`$ and
$`K_i/n\le k_iL^{-a_i}+L^{-201}`$. The code checks this sign structure,
the constant limits, the explicit domain $`L\ge65536`$, and each value.
All thirty rows already pass at that domain endpoint. Thus all subsequent
ceiling and bin-count jumps are handled by pointwise bounds. The analytic
derivative checks prove every real larger $`u`$; the target derivative
checks prove every real larger $`v`$. No sampled sequence of orders is
used to assert persistence.

| Interface | Required natural-log floor | First sufficient integer $`v`$ |
|---|---:|---:|
| Global seeds and growth, center $`X/2`$ | 16081 | 7730 |
| All finite geometry, packing, centering and supply inequalities | 65536 for $`L`$ | 31511 |
| Strong target requests, center at least $`7\mu/8`$ | 120365 | 43409 |
| Upper reflected bins | 110866 | 53310 |
| Lower reflected bins | 110866 | 53311 |
| Both original residue windows | 110866 | at most 53311 |
| Weak target requests, center at least $`7\mu/8`$ | 171218 | **61750** |
| Nine target size/box/shift comparisons | order-domain floor | 113 |

At $`v=61750`$, the rational outward calculation gives


```math
H_{21/50}(v)\gt 171218.249034679552,
```


whereas its upper bound at $`v=61749`$ is below 171218. The largest
required order is therefore the **evaluated** maximum 61750. The limiting
AW endpoint ratio at $`U=171218`$ is less than 0.999883524579. The first
failed preceding comparison is about this sufficient profile, not a
counterexample to the cube theorem.

At the finite envelope domain $`L=65536`$, useful controller upper ratios
are: joint packing 0.999900010000, centering 0.999900010000, horizontal
correction 0.999900963578, tensor correction 0.999991555678, and final face
correction 0.999900010000. These include the small additional constant terms;
dominant-term ratios alone are not substituted for the full rows. The
geometry is tight in its parameters, but its required order is smaller
than the analytic maximum. Enlarging target windows further would require
more $`K_0`$ capacity and a joint controller reoptimization.

The improvement from the first successful profile has three distinct causes.
The finite TQ lemma replaces a $`d_t/500`$ prime-count request by
$`d_t/2`$, with a newly checked cube composition. Rational multipliers
permit equal exponent margins, where the old coefficient-one schedule
required strict gaps. Finally the reflected-bin stock invariant removes
the factor $`\delta`$ from total macro depletion. For the former
single-class supply interface the smallest nonnegative integer corner was
$`(a_0,a_1,a_2,a_3;d)=(5,5,3,3;2)`$; its inequalities require
$`d\ge2`$, $`a_2\ge d+1`$, $`a_1\ge a_2+2`$. FSR changes that
interface and allows $`(2,2,0,0;2)`$. This is an architectural improvement,
not an assertion that the latter corner worked under the former hypotheses.

## 7. Dependency and certification ledger

| Dependency | Effectivity and scope |
|---|---|
| Frozen signed incidence, tensor routing and physical trades | Finite integer proofs; all original geometry, torsion and obstruction fixtures retained |
| FSC and its weighted extension | New finite inequalities, degree-64 graph, packing, occupancy, centering, native floors and triangular correction |
| FSR | New finite allocation proof, early invoice, adaptive reflected stock and four fresh pairs per cuboid |
| Frozen TQ and new cube TQ composition | Finite exact-list hypotheses, weighted orbits, shifted finishing centers, all six exact family totals and four body primes |
| RS62 | Explicit prime-size and exact-pool mean estimates, literal domains checked |
| BMOR and McCurley | Explicit analytic imports; exceptional zero, conductor normalization, all moduli and endpoint losses retained |
| AW/AS plus the fixed-denominator extension | All requested floors numerically evaluated; all real larger local centers covered |
| Qualitative Thorner--Zaman consequence | Preserved fallback only; no premise in ESC3-R |
| Unevaluated asymptotic allowances | None consumed by this composition |

The exact numerical profile was replayed from a self-contained research archive,
including independent analytic and reflected-supply oracles. The public
[verification record](PROVENANCE.md#explicit-prime-cube) gives the exact scope
and distinguishes arithmetic replay from proof of the classical imports.
The proof components linked here contain the finite interfaces, analytic
estimates, allocation argument, target construction and whole-tail reasoning;
no private-repository access is needed to read those proofs. This public
exposition does not claim that its reformatted bytes satisfy the original
research archive's source manifest.

This completes the proof for every odd $`n\ge2^{61750}`$, with the exact
initial odd-prime pool and the entire required signed-line family.
