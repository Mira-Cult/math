# A constant relative target window with the actual graph costs

The new finite theorem permits a target radius D=y/R with a fixed integer R,
and K=floor(n/C) with a fixed integer C. All input primes still occur exactly
once, and rows, columns and both main diagonals remain controlled. Three
coupled improvements are material: the smaller graph reduces the entry
invoice, its actual degree reduces placement and centering costs, and the
resulting smaller baseline error leaves more of the transfer box for targets.
The aggregate stock also retains its natural-logarithm denominator instead
of rounding it upward to E. That saving materially enlarges K.
The scale parameter e is still ceil(log2 y), but D no longer shrinks as e
increases.

## 1. A finite theorem with degree-dependent costs

Let n at least three be odd. Choose d=12 with [G1](cutoff_graph_experiment.md), or d=10 with
[the split-cut construction](cutoff_degree10_graph.md). In either case there
is an undirected multigraph on n vertices with degree at most d and cut
boundary at least half its smaller side. Multiplicities are retained and
each graph edge receives a separate reservoir. Two such graphs control
rows and columns. Their total number of ordinary reservoirs is at most dn.

Use the exact input pool, even g, reduced seed class a, integers K,M,H and
the prefix definitions s,P from FC. Use RBC's reflected-bin parameters
delta, integer N, w=N delta, its bins, and the separate narrow intervals
for residue repairs. Put


```math
\begin{split}
 B_0&=(2dn+8)P+4(n+1)(g/2-1),\\
 B&=B_0+(2dn+8)7K,\\
 L_d&=3dP+21dK+3g-4,\\
 J&=2(P+7K+g/2-1).                             \qquad\text{(CW1)}
\end{split}
```


Retain RBC's seed, phase-one global and narrow-class supplies, its reflected
raw bin supply W in every reduced class, and the aggregate stock condition


```math
S_0=N\varphi(g)W-B\gt 0,\qquad S_0^2\gt NX.         \qquad\text{(CW2)}
```


For seeds the original stronger assumption (64n+4)s remains sufficient,
but only the actual (dn+4)s or fewer needed seeds are reserved. The two
diagonal reservoirs and every residue gadget are separate and unchanged.
Assume the bands lie inside (1,X), 0<delta<1/24, w at least delta,
7(1/2-2w) at least two, and 1/2+2w<1. Retain the prefix inequalities
X at least g, sg at most X, gM at most 16X, M squared g at least 48X,
and H squared greater than ceil(X/g). Assume also


```math
2B\le n^2,\qquad n\gt 4J,\qquad n\gt 4L_d+8,
 \qquad KX\ge2g.                               \qquad\text{(CW3)}
```


Let c0 be a positive rational less than one half. The new centering
hypothesis is


```math
63d\delta K+9dP+10g+\frac{3d}{2}-14
       +3\sqrt{n\log n}\lt c_0K.                 \qquad\text{(CW4)}
```


**Theorem CWC.** Under these hypotheses there is a baseline permutation
of exactly the first n squared odd primes whose row, column and both main
diagonal sums are units modulo g and strictly within c0 KX of y. Every
compatible integer target vector within KX/2 of that baseline, with row
and column totals both equal to the actual T, is realized by a permutation
of the same exact pool. Diagonal targets remain independent; target primes
may repeat. This statement is conditional on its explicit prime supplies.

### Selection, disjointness and complete coverage

RBC's reservation proof applies with the actual coefficient 2d. All seeds,
all growth prefixes and all ordinary and diagonal residue gadgets are
selected first; their entry cap is B0. The prefixes leave a complete g-grid
through total difference between X and 2X. Only afterwards are the wide
main stages selected from the reflected bins. With at most B actual deleted
entries, the remaining matched-bin stock is at least S0. The number of
same-bin, same-class pairs is at least S0 squared divided by N phi(g),
greater than X/g. There are at most floor(X/g) possible positive g-multiple
differences below X, so a fresh equal-difference double pair exists.

This step charges one aggregate depletion budget even if a whole bin or
class has been exhausted. The half-open bins are disjoint, so a deleted
prime is charged at most once. A diagonal stage may use different bins
and classes for its two pairs. Each pair has midpoint within delta X of
m and the same difference as its partner; that is sufficient for its
rectangle trade. An ordinary stage uses just one pair. The difference
bounds and the explicit seven-stage inequality ensure at most 7K wide
stages per reservoir. No unused candidate pair is counted as reserved.

### Actual placement invoice

The six ordinary passes now have maximum degrees


```math
dP,\quad dP,\quad7dK,\quad7dK,\quad
 2(g/2-1),\quad2(g/2-1).
```


An ordinary line has at most dP endpoints from its own prefix pass and
2dP entries from the perpendicular pass, with analogous wide counts.
The two residue passes contribute at most 6(g/2-1) entries and the joint
rectangle placement contributes at most two. Their total is exactly the
upper bound Ld in (CW1). The usual greedy pass argument has at most n/2
full transverse lines, at most 2Ld occupied-cell exclusions and at most
four diagonal exclusions. Thus n>4Ld+8 suffices. The diagonal rectangles
still use distinct rows and columns jointly across both diagonal families
under n>4J. All supports are disjoint and all ordinary pairs avoid both
diagonals. This is a new verified load bound, not an invocation of FC with
its original L silently replaced.

### Actual midpoint and completion invoice

Put every main reservoir at its midpoint subset and all residue controls
in their reference orientations. If a line has r reserved cells with sum
Z, then


```math
|Z-rm|\le\mathcal E X,\qquad
 \mathcal E=21d\delta K+3dP+3g+d/2-4.          \qquad\text{(CW5)}
```


For a row or column the full invoice, after division by X, is:

| Source | Upper bound |
|---|---:|
| Own and perpendicular uncontrolled prefixes | 3dP |
| Own and perpendicular wide-pair midpoints | 21d delta K |
| Midpoint rounding in at most d own reservoirs | dg/(2X), at most d/2 |
| Reference residue-path entries | 6(g/2-1)=3g-6 |
| At most one rectangle | 2 |

This sums to (CW5). Each diagonal's smaller bound
P+7 delta K+(g/2-1)+g/(2X) is also at most the displayed expression for
d=10 or 12. The two midpoints in a rectangle need not coincide; both are
within delta X of m, so their fixed row and column sums obey the same bound.

Because at least n squared divided by two entries are unreserved, summing
(CW5) over rows shows that their mean differs from m by at most
2 mathcal E X/n. Uniformly permuting them into the unfilled cells gives
expected line error at most 3 mathcal E X. The same sampling-without-
replacement estimate as FC gives a simultaneous fluctuation at most
3X sqrt(n log n), since (4n+4)n to the power -9/2 is less than one for
every n at least two. This is an existence proof with its explicit union
bound, not a probabilistic heuristic for individual orders.

The residue repairs then add at most (g-2)X to any line. Consequently the
full normalized error is


```math
3\mathcal E+(g-2)+3\sqrt{n\log n}
 =63d\delta K+9dP+10g+3d/2-14+3\sqrt{n\log n},
```


which is strictly less than c0 K by (CW4). In particular, degree 12 has
the exact midpoint coefficient 756; using the looser coefficient 768 is
also valid. Degree 10 has coefficient 630. These are actual count reductions,
not an uncharged enlargement of the midpoint tolerance.

### Integer flows, residues and exact pool

For capacity C_edge=floor(KX/g), every required integral demand divided by
g has absolute value at most floor(KX/(2g))=floor(C_edge/2). Each graph's
half-side cut bound therefore supplies every cut inequality. Integral
max-flow/min-cut realizes the complete zero-sum demand vector. Exact row
and column target totals T give the required zero sums. The diagonal
reservoirs retain their independent signed grids and the unchanged ranges
cover every correction of size KX/2 under KX at least 2g.

The residue paths and rectangles are merely selected early; their choices
of orientation remain free until the actual baseline is known. Main-pair
differences are multiples of g, so their varying endpoint classes do not
invalidate residue preservation. Each final operation permutes entries on
disjoint supports, and completion includes every unreserved pool prime.
This proves CWC with the exact input pool and both diagonals.

## 2. A parameterized constant-window specialization

Retain the exact definitions X,T,m,y,E,e. Assume n squared at most X at
most n cubed, n at least E to the power 32, E at least the stated endpoint,
and


```math
2X/5\lt m\lt \mu X,\qquad 2/5\lt \mu\le3/5.           \qquad\text{(CW6)}
```


Here mu is a rational upper-mean input; it is not the mean itself. The
profiles with mu=501/1000 require the separately proved sharper mean
estimate. They do not follow from the old upper bound 3X/5 by arithmetic
alone. The coordinator must verify that imported estimate's actual domain.

Use 2 at most g at most E and at least floor(X/(2048E cubed)) disjoint
gap-g seed pairs. For positive integers A,N,C,R,F,S set


```math
\begin{gathered}
 \delta=1/A,\quad w=N/A,\quad K=\lfloor n/C\rfloor,
 \quad D=y/R,\quad b=1-1/F,\\
 M=\left\lfloor\frac X{4E^2}\right\rfloor,
 \quad H=\left\lfloor\frac X{AE^2}\right\rfloor,
 \quad W_0=\frac X{A\varphi(g)E},\qquad
 W=\frac X{A\varphi(g)\log(2X)}.               \qquad\text{(CW7)}
\end{gathered}
```


The letter F here is only the floor-loss denominator; it is not the target
module's density-cost parameter. The executable manifest names it
`floor_loss_denominator` to prevent ambiguity. All selected profiles use
F=1000000 and S=100000. Require raw global count X/(2E squared) in the
seed class, count W0 in each required narrow residue interval/class, and
count W in every reduced class of every reflected bin. The strong analytic
count for a bin of length 2X/A centered at Y<X is at least
X/[A phi(g) log(2Y)], which is at least W. Keeping this natural logarithm
is essential. Uniformity across all reduced classes is used materially in
the aggregate argument.

The bin centers satisfy


```math
(3/20-w)X\lt Y\lt (\mu+1/4+w)X=\eta X.
```


Every bin has length 2X/A, thus at least 2Y/(A eta). This sharper endpoint
comparison is available to the analytic interface. The bins lie in their
own [Y/2,2Y] domains if 2/A at most 3/20-w. The narrow residue intervals
satisfy the same conservative scale and length bounds. No arithmetic
checker verifies the required counts; it certifies these interface requests.

### Exact reservations and ceilings

As in RBC's direct calculation at E at least 8192, the floor and ceiling
estimates give M at least X/(8E squared), H at least X/(2AE squared),
s at most 24E squared, P at most 160E cubed and sg at most 33E squared.
The prefix and residue double-pair hypotheses follow from the explicit
power bounds in the program. The old conservative seed invoice is still
at most 1632nE squared. No corollary with the old E at least 10000 premise
is invoked below that premise.

The prime-index input from Rosser--Schoenfeld gives
X/n squared greater than Q(E)=(693E-2193)/1000. Define


```math
\begin{split}
 U_0(E)&=\left(2d+\frac8{E^{32}}\right)\frac{160}{E^{27}}
       +\frac2{E^{29}}\left(1+\frac1{E^{32}}\right),\\
 V(E)&=\left(2d+\frac8{E^{32}}\right)
       \left(\frac{160}{E^{28}}+\frac{7E}{C}\right)
       +\frac2{E^{30}}\left(1+\frac1{E^{32}}\right).
\end{split}                                            \qquad\text{(CW8)}
```


They bound E squared B0/n squared and EB/n squared, respectively. It is
sufficient that


```math
\frac{U_0(E)}{Q(E)}\le\frac1A,\qquad
 \frac{V(E)}E\frac{b_2(E+1)}{Q(E)}\le w-\frac1S,\qquad
 \frac{V(E)}E\lt \frac12.                         \qquad\text{(CW9)}
```


Here b2=693148/1000000 is an exact rational upper bound for log 2, certified
by ten terms of its atanh series plus the geometric tail bound
9/[4 times 21 times 3 to the power 21]. Thus log(2X)<b2(E+1)<E.
The second comparison bounds log(2X)B/X, not EB/X. Since phi(g) at most
E/2, the first budget leaves M globally and H in each required narrow class.
The second leaves aggregate stock at least X/[S log(2X)], hence at least
X/(SE), across all bins and classes. The third separately leaves half the input
pool unreserved. The paired-stock square condition follows from
E to the power 62 greater than NS squared.

When E to the power 32 is at least CF, the floor in K retains K at least
bn/C. The actual placement, rectangle, capacity and centering checks are


```math
\begin{gathered}
 \frac{1920d}{E^{29}}+\frac{84d}{C}+\frac{12}{E^{31}}\lt 1,
 \qquad\frac{1280}{E^{29}}+\frac{56}{C}+\frac4{E^{31}}\lt 1,
 \qquad bE^{95}\ge2C,\\
 \frac{63d}{A}+\frac{9d\cdot160C}{bE^{29}}
 +\frac{(10E+3d/2-14)C}{bE^{32}}
 +\frac{3C}{bE^{15}}\lt c_0.                      \qquad\text{(CW10)}
\end{gathered}
```


For the fluctuation comparison, log n/n decreases beyond exp(1), and
32 log E at most 32E at most E squared at the stated endpoints. This
controls all n at least E to the power 32. The exact floor is not
replaced by its unfloored argument on the capacity side.

The target displacement satisfies


```math
\frac D{KX}\lt \frac{\mu C}{bR}.                  \qquad\text{(CW11)}
```


Thus the exact rational comparison c0+mu C/(bR)<1/2 places every target
inside the transfer box. One need not separately require a target ratio
below 2/5 when the proved baseline radius is smaller than 1/10. This joint
budget is an essential part of the improvement.

The convenient optimized target conditions n at least 680e to the fourth
and D at least 2048e to the fourth follow from e at most 2E and


```math
E^{28}\gt 680\cdot16,\qquad (2/5)E^{92}\gt 32768R.
```


R at least four implies D at most y/4. Prime supplies for the target module
are still separate inputs. Unlike the preceding shrinking-window profile,
its fixed target intervals of length at least y/(2R) remain a fixed
relative length at every larger scale.

## 3. Exact numerical profiles and persistence

The standalone program presently includes the following evaluated profiles.
All have E at least 8192, n at least E to the power 32, S=100000 and
floor-loss denominator F=1000000.

| Profile | d | A | N | C | R | mu | c0 |
|---|---:|---:|---:|---:|---:|---:|---:|
| Degree-12 fallback | 12 | 8192 | 768 | 2688 | 4096 | 3/5 | 3/32 |
| Degree-10, A16380 | 10 | 16380 | 1755 | 1308 | 1420 | 501/1000 | 19231/500000 |
| Degree-10, A24584 | 10 | 24584 | 2634 | 1308 | 1382 | 501/1000 | 25627/1000000 |
| Degree-10 selected | 10 | 29092 | 3117 | 1308 | 1370 | 501/1000 | 2707/125000 |
| Degree-10, A32760 | 10 | 32760 | 3510 | 1308 | 1364 | 501/1000 | 19231/1000000 |
| Degree-10, A40012 | 10 | 40012 | 4287 | 1308 | 1354 | 501/1000 | 7873/500000 |
| Degree-10, A45024 | 10 | 45024 | 4824 | 1308 | 1349 | 501/1000 | 13993/1000000 |

The selected profile has baseline fraction 21656/1000000=2707/125000.
It is selected by the separate coupled analytic comparison; this finite
module alone does not announce its resulting order cutoff.
Its exact degree-10 centering invoice is
630 delta K+90P+10g+1+3 sqrt(n log n). After division by K the endpoint
upper bound is below 0.021655437921077959576516, strictly less than the
chosen 0.021656. Baseline plus target is below
0.499983485626755699748401, strictly less than one half. Using a padded
640 delta K coefficient would not certify this selected profile; the actual
degree count in (CW5) is required.

The degree-10 profiles have w=3/28 exactly, so their seven-stage bound is
an equality at the smallest possible difference. Their scaled reservation
invoice log(2X)B/X is below 0.107110942194074743 at the endpoint, against allowed
3/28-1/100000. The remaining stock lower bound X/(100000E) is small but
its square exceeds NX by the explicitly checked power comparison. There
is no assumption that each separate class retains a positive fraction of
its initial stock.

The arithmetic program evaluates every entry cap with all +8 and n+1
terms present before bounding it. No floating-point value enters a
certificate. Displayed decimal intervals are rounded outward from exact
rationals. Which profile produces the best final cutoff depends on the
analytic threshold for its actual bin width and target interval; a larger
target radius alone is not enough to choose a record.

The tail argument requires care because V itself now increases. It is
**not** asserted to be decreasing. Instead V/E decreases directly from
(CW8), and


```math
\frac{E+1}{Q(E)}=\frac{E+1}{(693E-2193)/1000}
```


also decreases for positive Q: its derivative has negative numerator
-(2193+693)/1000. Thus the product (V/E)b2(E+1)/Q decreases. Also U0/Q,
the placement envelopes and the
nonconstant centering terms decrease. Every power lower bound increases.
Checking each listed endpoint proves every integer E above it. The bounds
on K,M,H,P,s are valid pointwise at their actual rounded values. The proof
does not differentiate through a ceiling or floor jump. The composition
must separately prove n at least E to the power 32 for every order on its
claimed tail.

## 4. Verification boundary

Run from the repository root:

```sh
python problems/prime-line-sums/code/cutoff_degree10_graph.py
python problems/prime-line-sums/code/cutoff_constant_window_controller.py
```

The controller checker verifies the finite comparisons for all displayed
profiles, exact reflected-bin endpoint controls, and negative controls for
an insufficient entry budget, an oversized target window, an unproved
baseline radius, a band too wide for seven stages, an unsupported graph
degree, and malformed source maps. It requires the exact complete embedded
source set; missing, empty, nonregular or mismatched files fail closed.
It explicitly reports that it does not certify the mean hypothesis, raw
prime counts, or the complete square theorem. The graph checker's universal
claim rests on its conventional union-bound proof; its finite cut controls
are supporting evidence, not a substitute for that proof.

Independent review must address these exact source files, the degree-10
cut argument, the new placement and centering invoices, phase ordering,
all-tail envelopes and the complete analytic composition. This is ordinary
mathematical review plus exact finite arithmetic, not formal verification.

[Manuscript index](../README.md) · [Optimized theorem](../optimized-bound.md) · [Source and review record](../PROVENANCE.md#optimized-bound)
