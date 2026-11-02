# The original controller with a smaller seed gap

This is an additive finite specialization of
the unchanged [FC theorem](../explicit-controller.md). The exact-pool problem
and notation are [canonical](../README.md). This manuscript has explicit
prime-supply hypotheses; the small-gap matching, progression estimates,
and exact-total target construction must be supplied separately by the
complete composition. Its arithmetic program does not prove those imports.
Nonauthor review must name the exact scientific source actually examined.

## SG: the finite controller corollary

Let n be odd and let X, T, m, y, E, and e have their usual exact-pool
meanings. Suppose


```math
n^2\le X\le n^3,\quad 2X/5\lt m\lt 3X/5,
 \qquad E\ge10000,\qquad n\ge E^{32}.              \qquad\text{(SG1)}
```


Set


```math
A=64000,\quad \delta=1/A,\quad K=\lfloor n/E^3\rfloor,
 \quad M=\left\lfloor\frac X{4E^2}\right\rfloor,
 \quad H=\left\lfloor\frac X{AE^2}\right\rfloor,
 \quad D=\frac y{e^3}.                             \qquad\text{(SG2)}
```


The target exponent changes explicitly from four to three. K retains the
original baseline formula. Suppose an even g with 2 at most g at most E
and a reduced class a modulo g have the following supplies in the exact pool:

1. At least floor(X/(2048 E cubed)) vertex-disjoint gap-g pairs with lower
   endpoint in class a.
2. At least X/(2 E squared) pool primes in class a.
3. In each interval
   $`I_\pm=[m\pm X/4-X/A,m\pm X/4+X/A]`$, at least
   $`2X/(AE^2)`$ pool primes in each needed class a, -1, and 1 modulo g.

Repeated classes denote the same condition. Then **the complete conclusion
of FC holds** with the parameters (SG2): a baseline permutation of exactly
the prescribed pool has all required line sums units modulo g and within
KX/10 of y, and FC realizes every compatible target vector within KX/2
of that baseline. Both diagonal targets remain independently specified.

Moreover, every target within D of y is within FC's permitted box, and the
size conditions of the optimized target lemma with density cost at most
4e squared hold. The prime-supply hypotheses of that target lemma and its
exact row/column totals remain separate requirements.

### How the raw supplies arise from the strong analytic interface

If the strong interval estimate is available at X and the two macro centers,
the stated raw counts follow without an extra analytic assertion. Since g
is even, phi(g) at most g/2 is at most E/2. Also


```math
\log(2X)\le(E+1)\log2\le E\quad(E\ge3).
```


For example the positive log series, bounded after its first term, gives
$`\log2\le2/3+1/36\lt 3/4`$; this proves the last comparison. The interval
(X/2,X] has length X/2, so the strong count
$`|I|/(2\varphi(g)\log(2X))`$ is at least X/(2E squared).
The centers Y plus/minus are less than X; the macro interval length is
2X/A, so the same denominator upper bound E squared gives 2X/(A E squared).
Availability at the actual scales and requested interval lengths must still
be proved by the analytic composition.

These are factors 32 and 64 stronger than the earlier global and macro
counts at a fixed width. The improvement pays both the smaller range g at
most E and the actual even-modulus totient bound. It does not select an
unproved favorable gap or add disjointness assumptions to overlapping supplies.

## 1. Prefix, floors, and all seeds

The definitions of s and P are exactly FC's. The floor bounds are


```math
M\ge X/(8E^2),\qquad H\ge X/(2AE^2).
```


They follow from X at least E to the power 64, since E to the power 62
exceeds 8 and 2A. Consequently


```math
s\le16E^2+1\le24E^2,
 \qquad P\le16E^2+128E^3+2\le160E^3.              \qquad\text{(SG3)}
```


Multiplying the original ceiling definition by g gives
$`sg\le4X/M+g\le32E^2+E\le33E^2\le X`$.
Also $`gM/(16X)\le1/(64E)\le1`$, and


```math
M^2g\ge X^2/(32E^4)\ge48X,\qquad
 H^2\ge X^2/(4A^2E^4)\gt X\ge\lceil X/g\rceil.
```


The sufficient comparisons are E to the power 60 at least 1536 and
strictly greater than 4A squared. The seed floor retains half, and


```math
(64n+4)s\le1632nE^2\le X/(4096E^3).
```


For the last comparison it suffices that n is at least
6684672 E to the fifth power, which follows from E to the power 27 at
least 6684672. Every ordinary seed and both physical pairs per diagonal
seed group are charged. The smaller prefix cap is a direct consequence
of the larger retained M, not an assumption about faster reservoir growth.

## 2. The entire reservation still fits every supply

Keep the original degree-64 graphs and the exact FC reservation count:


```math
B=(128n+8)(P+7K)+4(n+1)(g/2-1).
```


Use the prime-index logarithm from [CG1](cutoff_controller_optimization.md):
RS62 Theorem 2 (3.4) gives
$`X/n^2\gt Q(E)=(693E-2193)/1000`$ on this domain. The original
coefficient 128n+8 is retained, and g at most E gives


```math
\begin{split}
 \frac{E^2B}{n^2}&\le U(E):=
 \left(128+\frac8{E^{32}}\right)
 \left(\frac{160}{E^{27}}+\frac7E\right)
 +\frac2{E^{29}}\left(1+\frac1{E^{32}}\right),\\
 \frac{E^2B}{X}&\lt \frac{U(E)}{Q(E)}\le\frac1A.
\end{split}                                             \qquad\text{(SG4)}
```


At E=10000 the middle ratio is below
0.000012933385701997760619, against allowed 1/64000=0.000015625.
All decisions use exact rationals. Separately U(E)/E squared is less than
one half, establishing 2B at most n squared. A B/X estimate alone would
not establish that exact-pool occupancy condition.

After subtracting the **whole** B from every requested raw supply, the
global count leaves M because 1/2 minus 1/A is at least 1/4, and each
macro interval/class leaves H because 2/A minus 1/A equals 1/A.
This includes seeds, all prefixes, all wide pairs, both residue paths,
and both sorts of diagonal rectangles. It applies to adaptive selections
even if every previously used entry lies in the currently needed class.
No allocation-specific independence assumption is used.

## 3. Placement, baseline centering, and transfers

Substituting (SG3) into FC's original L and J gives


```math
\begin{split}
 (4L+8)/n&\le122892/E^{29}+5376/E^3\lt 1,\\
 4J/n&\le1280/E^{29}+56/E^3+4/E^{31}\lt 1.
\end{split}                                             \qquad\text{(SG5)}
```


Thus all six separate pair passes fit, and all main and residue rectangles
on both diagonals are placed jointly with disjoint supports. The smaller
gap and prefix bounds are not used to combine passes or reuse entry positions.

Since n/E cubed is at least five,
$`K\ge(4/5)n/E^3`$. This proves KX at least 2g using only
$`(4/5)E^{92}\ge2`$. Dividing FC's full centering expression by K,
and using log n at most E, yields


```math
\frac{6000}{A}+
 \frac{576\cdot160}{(4/5)E^{26}}+
 \frac{92}{(4/5)E^{28}}+
 \frac3{(4/5)E^{12}}\lt \frac1{10}.                   \qquad\text{(SG6)}
```


At the endpoint this is below 0.093750000000000000000001. The term
92E bounds 10g+82; the square-root term uses
$`\sqrt{n\log n}/K\le E^3\sqrt E/((4/5)\sqrt n)`$.
The increased width therefore pays its full centering cost, leaving a
strict positive margin for prefixes, residue repairs, and completion noise.

The interval endpoints lie in (1,X) since 3/20 minus 1/A exceeds
2 to the negative 32 and 17/20 plus 1/A is less than one. All finite FC
hypotheses have now been established directly, including the changed M and H.
FC's graph, flow, exact-pool completion, and independent diagonal conclusion
apply without any structural change to their proofs.

## 4. A larger target window using the coupled logarithms

The upper index bound X at most n cubed gives
$`\log_2n\ge\tfrac13\log_2X`$. Since m is greater than 2X/5,


```math
\log_2y\gt \tfrac43\log_2X-2
 \gt \tfrac43(E-1)-2,
 \quad\text{and hence}\quad
 e\gt \tfrac43E-\tfrac{10}{3}\ge\tfrac54E.            \qquad\text{(SG7)}
```


The last inequality holds for every E at least 40, across all integer
ceiling jumps. It uses the actual relation y=nm rather than independent
worst-case logarithms. Therefore


```math
\frac{D}{KX}
 \lt \frac{3/5}{4/5}\left(\frac45\right)^3
 =\frac{48}{125}=0.384.
```


The target's displacement plus the strict baseline radius is less than
0.484 KX, within the permitted 0.5 KX. This avoids increasing K while
changing the target exponent to three. Also E at most e at most 2E;
with target density cost F at most 4e squared, the target lemma's sufficient
requirements D at least 2048e to the fourth power and n at least 680e to
the fourth power follow from


```math
(2/5)E^{89}\gt 2^{18},\qquad E^{28}\gt 680\cdot16.
```


They are extremely slack at E=10000. They do not replace the target prime
count or exact-total requirements. Its lifted modulus now satisfies
$`h\le8ge\le8Ee\le8e^2`$; (SG7) would give the smaller convenient
upper bound $`(32/5)e^2`$, if useful to the analytic producer.

## 5. Entire tail and reproducibility

Every positive-power comparison above persists with E. Every nonconstant
term in U, the placement bounds, and the centering bound is a positive
decreasing power of E; Q is positive and increasing. Thus all checks hold
for every integer E at least 10000. Floors and ceilings are handled by
pointwise envelopes reapplied at each n; no smooth monotonicity of K is
assumed. As a separate order conversion, n at least 2 to the power 5000
gives E at least 10000 and n at least E to the power 32, using
E at most 4 log base 2 of n and the increasing logarithmic difference.
This is a combinatorial conditional domain, not an analytic or square cutoff.

Executable replay details are recorded in [Provenance](../PROVENANCE.md#optimized-bound).

The program checks 34 exact finite inequalities and ten negative controls,
including missing, empty, extra, malformed, and mismatched source maps.
It binds the exact FC and prime-index proof dependencies. The full composition
manifest must also bind the new small-gap matching, analytic, target and
composition sources. The first integer E passing the depletion invoice is
9099; the clean corollary uses 10000. Neither number is a lower bound on
Sude's problem, and a higher analytic floor remains independently binding.

Compared with the baseline, retained M is larger by a factor 32, the prefix
cap drops from 5120E cubed to 160E cubed, and the retained macro supply is
larger by a factor 10000. The complete original reservation count is still
paid. The smaller seed gap and stronger counting conversion, together with
the index logarithm and wider target interval, are the proved sources of
the improvement. The separate degree-12 graph experiment is unnecessary
for this corollary and is not one of its dependencies.

[Manuscript index](../README.md) · [Optimized theorem](../optimized-bound.md) · [Source and review record](../PROVENANCE.md#optimized-bound)
