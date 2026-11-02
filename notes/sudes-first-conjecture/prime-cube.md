# The full signed-line prime cube

Public proof manuscript. See [review and provenance](PROVENANCE.md#full-signed-line-cube) for source revisions, review scope, and verification limits.

## 1. Exact statement and dependency order

Use coordinates $`[n]_0=\{0,\ldots,n-1\}`$ and the reflection
$`\bar t=n-1-t`$. Translating all coordinates by one identifies this instance
with $`[n]=\{1,\ldots,n\}`$. A full signed-coordinate line has each
coordinate fixed, $`t`$, or $`\bar t`$, with at least one varying coordinate.
Repeated descriptions are deduplicated as subsets. For $`n\ge3`$ the families
are the $`3n^2`$ axes, six families of $`n`$ face diagonals, and four body
diagonals. Their total is $`3n^2+6n+4`$. No square-section sum is required prime.

Put $`A=\{p_2,\ldots,p_{n^3+1}\}`$, $`X=\max A`$, $`T=\sum A`$,
$`m=T/n^3`$, and $`\mu=nm`$. The exact target compatibility consists of the
axis plane-marginal equations, axis directional total $`T`$, and the six
identities equating a face-family total to the perpendicular axis aggregate
on its diagonal square. The bodies have no further equation for odd
$`n\ge11`$. This full integer-image assertion, including the small-order
exceptions, is proved in [signed_incidence.md](cube/signed_incidence.md).

**Theorem USC3 (universal compatible odd signed targets).** For every
sufficiently large odd $`n`$, every compatible vector of odd integer targets
for the full signed-line family, with every coordinate within $`K_0X`$ of
$`\mu`$, is realized by a permutation of exactly $`A`$, where
$`K_0=\lceil n^{3/5}\rceil`$.

**Theorem SC3 (full signed-line prime cube).** For every sufficiently large
odd $`n`$, the first $`n^3`$ odd primes admit a bijective placement in $`[n]^3`$
whose every full signed-coordinate line has prime sum. Sums may repeat.
The separate case $`n=1`$ is the singleton 3.

The proof first supplies the full compatibility and prime-target interfaces,
then pays prime tuples and support placement, centers an actual bijection,
repairs residues, and consumes physical capacities in a fixed order. The
analytic input is the ineffective short-interval progression consequence of
Thorner--Zaman, arXiv:2108.10878v2, printed Section 1.2, and the
[finite target-list lemma](explicit-targets.md). These hypotheses are checked in
[signed_targets.md](cube/signed_targets.md). No growing-complexity prime-pattern
theorem, numerical cube cutoff, or growing-dimension assertion is used.

## 2. Fixed scales and target supply

Retain the baseline scales and add one new scale:



```math
K_0=\lceil n^{3/5}\rceil,\quad K_1=\lceil n^{2/3}\rceil,
 \quad K_2=\lceil n^{3/4}\rceil,\quad
 K_3=\lceil n^{39/50}\rceil,\quad \delta=n^{-1/5}.          \qquad\text{(1)}
```



All implied constants below are absolute, independent of $`n`$, the selected
gap, targets, and preceding choices. Each is fixed before increasing $`n`$.
The basic prime scale is $`X\sim3n^3\log n`$, $`m\sim X/2`$. In addition to
the baseline inequalities, the new margins are



```math
\delta K_3\asymp n^{29/50}=o(K_0),\qquad K_3=o(n),
 \qquad K_2\log^b n=o(K_3)\quad\text{for every fixed }b,
 \qquad nK_3=o(n^2K_2).                                  \qquad\text{(2)}
```



Let $`F=\lceil100\log X\rceil`$ and
$`P=\lceil256F^2\rceil+32F\lceil\log_2X\rceil`$ as in the baseline.
The common seed gap is even and satisfies $`g\le16\lceil\log_2X\rceil`$.
The signed prime-target theorem SPT gives a prime target at every required
line, all compatibility identities, and radius $`2\mu^{3/5}=o(X)`$.
It uses a symmetric axis matrix, six length-$`n`$ prime lists with their
prescribed section totals, and four free body targets. It never asks that
those section totals themselves be prime. Its unit residues are chosen
compatibly; the residue mechanism below reaches them from an arbitrary
odd reference arrangement.

## 3. Tuples, scalar capacity, and total deletion

The baseline matching in $`[X/4,3X/4]`$ gives
$`\gg X/(\log X)^3`$ disjoint common-$`g`$ pairs in one reduced lower class.
It is selected from the exact initial pool. Reserve the needed seed pairs
before any later allocation. The old demand is $`O(n^2P)`$ pairs, and the new
demand is $`O(nP)`$ pairs, with four disjoint pairs paid per cuboid stage.
Their sum is $`o(X/(\log X)^3)`$.

The fixed-difference matching argument in baseline Section 2.2 already
produces at least sixteen equal-difference edges at the starting scale
$`R\ge256gF^2`$. A graph of a fixed positive difference has degree at most
two, so it has a matching of at least a third of its edges. In particular
**four disjoint equal-gap pairs exist at each growth stage**. Each tuple
is removed before the next request. The interval remains complete on the
$`g`$-grid, grows to at least $`X`$, and uses at most $`P`$ stages. This is the
four-pair extension proved in [signed_trades.md](cube/signed_trades.md).

The low/high intervals remain
$`I_\pm=[m\pm X/6-\delta X,m\pm X/6+\delta X]`$.
After worst-case deletion, each required reduced class has
$`\gg\delta X/(g\log X)`$ available entries in each interval. Pigeonholing
low/high pairs gives an actual common difference supported by
$`\gg\delta^2X/(g\log^2X)`$ pairs. These pairs are already a matching,
since the endpoint intervals are disjoint. This number tends uniformly to
infinity, so four fresh pairs can be used. The same argument in lower
class $`-1`$ and upper class $`+1`$ gives four equal actual differences
congruent to 2 modulo $`g`$ for residue cuboids.

Each new main reservoir has its complete prefix and
$`J_3=\lceil32K_3\rceil\le33K_3`$ macro stages. A macro difference is in
$`[X/4,X/2]`$, and each pair midpoint is within $`\delta X`$ of $`m`$.
The total native gap is at least $`8K_3X`$. A subset at the middle of the
complete grid, or its complement, gives both signs of the native capacity



```math
C_3=g\left\lfloor\frac{3K_3X}{g}\right\rfloor\ge2K_3X
 \quad\text{eventually}.                                \qquad\text{(3)}
```



There are at most $`6|E(G)|+4\le192n+4`$ new main reservoirs, with the
baseline graph $`G`$ of maximum degree 64 and expansion at least 8.
Residue paths and bodies require at most $`(6n-2)(g/2-1)`$ new cuboids.
Thus the additional cell/entry invoice is at most



```math
Q_{\rm new}=8(192n+4)(P+33K_3)+24ng=O(nK_3).             \qquad\text{(4)}
```



The baseline invoice is less than $`2^{20}n^2K_2`$ eventually. Use the single
joint worst-case deletion allowance



```math
Q_*=2^{21}n^2K_2.                                       \qquad\text{(5)}
```



Equation (2) pays (4) inside (5). The smallest progression supply has order
at least a constant times
$`\delta X/(\log X)^2\asymp n^{14/5}/\log n`$, whereas
$`Q_*=O(n^{11/4})`$. Hence every required interval and residue class retains
at least half its supply after **any** preceding deletion of at most $`Q_*`$
entries. The shrinking intervals still have logarithmic length exponent
$`14/15\gt 7/12`$ relative to $`X`$; no analytic scale has been silently changed.
All selected entries lie inside the original pool. Entries not chosen for
controllers remain for the final completion.

## 4. Plan all supports, beginning with the new cuboids

The physical cuboid and packing lemmas in
[signed_trades.md](cube/signed_trades.md) supply the following contracts.

* A face bundle on a graph edge $`u,v`$ affects only its two native face
  lines, by equal and opposite scalar changes. It preserves every axis,
  every body, and every other face line.
* A body bundle affects only its native body among the four bodies and
  preserves every axis. Its face effects may vary from stage to stage.
  Fresh reflection orbits across the whole bundle ensure that any one
  face line meets at most one of its stage vertices. Therefore consuming
  all four body bundles changes any face sum by at most $`4X`$.
* Prefix, macro, and residue passes have respectively $`O(P)`$, $`O(K_3)`$,
  and $`O(g)`$ cells on every axis line. The same bounds hold on every
  signed line, by native degree and the intersection contracts.

For simultaneous residue and main placement one may use the union of the
main graph and a path, with maximum degree $`64+2=66`$. Body stages from all
passes share the fresh-orbit rule. The actual invoice is still (4), not
the larger bound obtained by filling every possible slot in this union.
Plan the upper number of slots for each prefix; unused slots are returned
to the ordinary completion. Prime values are allocated only after supports
are planned, using the fresh supplies of Section 3.

Place these new supports first. They occupy only $`o(n)`$ cells on each
axis line, even on exceptional axes lying entirely in a diagonal section,
and $`o(n^2)`$ cells in each coordinate plane. The old supports can therefore
be packed around them. The next lemma supplies the missing full-line
preservation and drift contract; it does not assume the old controller
already had it.

### Old-support extension lemma

The baseline plane, slice, rectangle and axis-residue supports can be placed
around the new supports so that:

1. all old axis-controller effects and their baseline capacities are unchanged;
2. no old support meets a body diagonal;
3. old plane controls meet no additional signed line;
4. each old prefix/macro/residue pass has respectively $`O(P)`$, $`O(K_2)`$,
   and $`O(g)`$ cells on every full signed line;
5. any extra face line meets at most one stage of a particular old slice or
   rectangle reservoir, and therefore has range at most $`2X`$ between that
   reservoir's complementary reference orientations.

**Proof.** Retain the baseline partial matchings and distinct transverse
coordinates, with the following extra exclusions. For a set $`S`$, write
$`\mathcal O(S)=S\cup\{\bar s:s\in S\}`$.

For a plane pair $`z,z'`$, choose $`(x,y)`$ with
$`x,y\notin\mathcal O(\{z,z'\})`$ and $`x\notin\mathcal O(\{y\})`$.
Both pair endpoints then lie outside every diagonal section, so they meet
no extra signed line. These restrictions remove only $`O(n)`$ out of $`n^2`$
positions. The new supports and previous old passes remove $`o(n^2)`$ more.
The old cap exclusions remove a fixed small fraction, and the reservoir's
partial matching removes $`o(n)`$ rows/columns. A free position remains.

For a slice transfer between $`x,x'`$ at fixed $`z`$, choose its transverse
coordinate $`y`$ outside $`\mathcal O(\{x,x',z\})`$. This avoids the $`xy`$
and $`yz`$ diagonal sections and every body. It may meet an $`xz`$ section
when a native endpoint $`x`$ or $`x'`$ equals $`z`$ or $`\bar z`$; these are
the exceptional axes, which are retained rather than excluded. Impose a
separate cap $`cL`$ on each affected $`xz`$ face line in a pass with at most
$`L`$ stages per reservoir. For each sign, the total planned load on the
whole $`xz`$ diagonal section is at most $`64nL`$: in each slice only graph
edges incident to its specified $`x`$ endpoint can contribute. Thus fewer
than $`128n/c`$ face lines of that sign can be saturated. A face line's
fixed coordinate is precisely the free $`y`$, so these forbid only $`O(n/c)`$
choices. Transpose the argument for the other slice-control direction.

For a vertical rectangle on edges $`(x,x')`$ and $`(y,y')`$, choose $`z`$
outside $`\mathcal O(\{x,x',y,y'\})`$. It avoids every $`xz`$ and $`yz`$
diagonal and every body. Its possible extra intersections are the two
$`xy`$ face lines at level $`z`$. In one pass a vertical line belongs to at
most $`64^2`$ edge-pair types, and so has planned load at most $`64^2L`$.
Summing this over the $`n`$ vertical lines of either $`xy`$ section bounds
that section's planned load by $`64^2nL`$. The cap $`cL`$ therefore forbids
only $`O(n/c)`$ levels $`z`$ for each sign.

The added face caps count only the current old pass, not the new cuboids
or earlier old passes; those enter the separate occupied-cell exclusions.
These cap counts hold for partial placements, because they use complete
planned totals rather than an average-distribution assumption. A stage
adds at most two cells to any face line; a cap-rejected line already has
at least $`cL/2`$ cells. The two face-sign cap exclusions for rectangles are
at most $`4\cdot64^2 n/c`$. Adding the original horizontal-axis cap
exclusions gives at most $`12\cdot64^2 n/c`$. Slice caps similarly add at
most $`4\cdot64 n/c`$ to the original $`6\cdot64 n/c`$. Take, for example,
$`c=10^{12}`$, so each combined leading fraction is below $`1/4`$.

Previously occupied cells exclude $`O(K_3+K_2+P+g)=o(n)`$ positions on
the two native slice lines or four rectangle vertical lines. The new
constant-size forbidden sets and the baseline distinct-coordinate rule
also remove $`o(n)`$ choices. Consequently every required stage has a
free location. Plane stages retain their original $`o(n^2)`$ and fixed
fraction bounds. Induction over separate passes proves the claims.
The path and path-product axis-residue gadgets have smaller graph degrees
and fit exactly the same argument.

Finally, a slice reservoir uses distinct $`y`$ (or distinct $`x`$) values,
so a surviving extra face line meets at most one stage and one vertex.
A rectangle reservoir uses distinct $`z`$ values, so a surviving $`xy`$ face
line meets at most one stage and at most two vertices. Its complementary
range is at most $`2X`$. Plane reservoirs have no extra intersections.
These restrictions also prove body avoidance at central or reflected
coordinates; no generic-position assumption was left unexamined. QED.

## 5. Centering the entire signed-line family

Independently choose one of the two complementary central subsets for each
main reservoir. Keep every residue gadget at its fixed reference choice.
Every macro cell has expectation equal to its pair midpoint, within
$`\delta X`$ of $`m`$. Prefix and residue cells have deviation at most $`X`$.
By the separate pass caps, every signed line $`L`$ has reserved-cell count
$`r_L`$ and expected reserved deviation



```math
|\mathbb E C_L-r_Lm|=O(\delta K_3X+PX+gX).               \qquad\text{(6)}
```



The independent objects here are entire reservoir orientations. On an axis
line, every new cuboid choice has zero effect, and each old reservoir has
the baseline range at most $`X`$. On a face line, an old reservoir has range
at most $`2X`$ by the lemma; a native new face reservoir has range at most
$`g`$; other face reservoirs have zero effect; and each body reservoir has
range at most $`X`$ by fresh orbit labels. On a body line, only its own new
body reservoir can vary, with range at most $`g`$. Hence $`2X`$ is a uniform
range bound for one reservoir's contribution to one signed line.

There are $`O(K_3+P)`$ reservoirs meeting a line, bounded by its reserved
cells. The bounded-independent-variable inequality, followed by a union
bound over $`3n^2+6n+4=O(n^2)`$ lines, therefore gives a choice with



```math
|C_L-r_Lm|\le E,
 \quad E=O(\delta K_3X+PX+gX+X\sqrt{K_3\log n}).          \qquad\text{(7)}
```



Both choices retain all later native capacities. In particular no
independence of individual cells within one cuboid or reservoir is assumed.

Fewer than half the entries are reserved eventually, by (5). Sum (7)
over a partition into $`n^2`$ axis lines. If $`m_0`$ is the unused-entry mean,
the fixed total implies $`|m_0-m|\le2E/n`$. Uniformly permute every unused
prime into the unused cells. The expectation of each completed signed
line differs from $`\mu`$ by at most $`3E`$. The baseline sampling-without-
replacement bound applies to any one set of at most $`n`$ free cells:



```math
\Pr(|S_L-\mathbb E S_L|\gt u)\le2\exp(-u^2/(2nX^2)).       \qquad\text{(8)}
```



Taking $`u=4X\sqrt{n\log n}`$ and union bounding over the full family
gives a completion for which every line error is at most



```math
E_0=O(\delta K_3X+PX+gX+X\sqrt{K_3\log n}
                  +X\sqrt{n\log n})=o(K_0X).             \qquad\text{(9)}
```



The positive exponent margins in (1)--(2), including $`29/50\lt 3/5`$,
justify the last equality. Every pool entry now occurs exactly once.

## 6. Full residue repair, with all integer side effects paid

Fix any odd target vector from USC3. Run the three baseline axis-residue
phases on their adapted old supports: plane paths, slice row/column paths,
then path-product rectangles. Their axis-residue proof is unchanged. They
avoid all bodies, and have $`O(g)`$ cells on every face line by the new lemma.
Thus their actual numerical change on any required line is $`O(gX)`$.

Now use the signed residue-routing lemma SR in
[signed_targets.md](cube/signed_targets.md#4-residue-routing-interface-for-the-physical-controller).
First repair the four body residues using at most $`h-1`$ cuboids each,
where $`h=g/2`$. Then repair each face family's residues on a path, using
at most $`h-1`$ cuboids per edge. Their native differences are actual equal
prime gaps $`2\pmod g`$, so division of even target errors by two gives
unit increments modulo $`h`$.

After the axis repair, each face-family error has total zero modulo $`g`$
by its exact section-total compatibility. After any body cuboids it still
does, since cuboids preserve all axis sums. Prefix-sum path coefficients
therefore set every face residue without disturbing axes, bodies, or other
families. If $`g=2`$ no residue switches are needed. All numerical side effects
are $`O(gX)`$ per line, so (9) remains valid. Main reservoir supports and
their central references are untouched.

## 7. Bounded physical correction and preservation

All line differences are now on the $`g`$-grid and initially at most
$`(1+o(1))K_0X`$. First consume the old three numerical stages exactly as
in baseline U3. The modified geometry has unchanged native effects,
unchanged complete capacities, and unchanged asymptotic orders for old-stage
axis loads. The larger fixed cap changes constants, which the strict gaps
between successive scales absorb. Every main gap is a multiple of $`g`$,
so these numerical stages preserve all signed residues set in Section 6.

**Plane totals.** Demands are at most $`(1+o(1))nK_0X`$, with total zero. The $`n`$
reservoirs on each plane-graph edge and the integral cut-flow lemma pay
them. The remaining horizontal errors are $`O(K_0X)`$.

**Horizontal axis lines.** The two graph flows in each slice have correct
exact totals and use level-1 capacity, since $`K_0=o(K_1)`$. They preserve
one another, leaving vertical errors $`O(K_1X)`$.

**Vertical axis tensor.** Its residual $`D`$ has exact zero row and column
margins and is divisible by $`g`$. The baseline tensor-expander theorem gives
an integer coefficient matrix with scalar demands at most



```math
(5\log n+5)^2\|D\|_\infty+g/2+512gn^2
 =O(K_1X\log^2n)+O(gn^2)=o(K_2X).                        \qquad\text{(10)}
```



The old equal-gap rectangle reservoirs consume it physically. Every axis
target is now exact. No body sum has changed during these three stages.
Each face line has changed by at most $`O(K_2X)`$, by the old full-line
occupancy bound. Accordingly the remaining body errors are $`O(K_0X)`$,
and the remaining face errors are $`O(K_2X)`$.

**Body correction.** The four native body reservoirs have capacity (3),
so $`K_0=o(K_3)`$ pays each body error. They preserve all axes and other
bodies. Their face actions are allowed to vary by stage; no false fixed
full-incidence column is assigned to a body bundle. The fresh-orbit
intersection rule gives at most $`4X`$ total drift on each face line.
Consequently every face error is still $`O(K_2X)`$.

**Six independent face flows.** In each face family, the residual total
is exactly zero: both the current array and the targets partition the same
diagonal square, and its perpendicular axis targets are now exact. Each
coordinate error is a multiple of $`g`$. The graph expansion bound implies
that every zero-total demand with magnitude at most $`8C_3`$ per vertex is
realizable with edge capacities $`C_3`$. Since $`K_2=o(K_3)`$ and
$`C_3\ge2K_3X`$, the actual demands meet that condition eventually, including
all fixed occupancy constants. Integral flows, rescaled by $`g`$, are decoded
by the complete face reservoirs. They preserve every axis, every body,
and the other five face families. All required targets are now exact.

Every operation above swaps distinct original entries on disjoint reserved
supports. No entry is lost, duplicated, or replaced. This proves USC3.
Apply SPT, whose radius $`2\mu^{3/5}=o(X)`$ lies inside $`K_0X`$, to obtain
SC3 for every sufficiently large odd order. QED.

## 8. Joint quantitative invoice

| Quantity | Proven bound | Source and consumer |
|---|---|---|
| Axis target, face target, body target windows | $`2\mu^{3/5}=o(X)`$ | SPT; all final native capacities |
| Common-gap seed supply | $`\gg X/\log^3X`$ disjoint pairs | Baseline matching; old and new prefixes |
| Total seed demand | $`O(n^2P)+O(nP)`$ pairs, four paid per new stage | Tuple lemma; complete grids |
| Fresh smallest class supply | $`\gg\delta X/(g\log X)`$ after arbitrary deletion | TZ and (5); all macros and residue tuples |
| Equal-gap low/high matching | $`\gg\delta^2X/(g\log^2X)\to\infty`$ | Four-pair tuple lemma |
| All deleted/reserved prime entries | $`Q_*\le2^{21}n^2K_2=o(n^3)`$ | (4)--(5); every supply invocation |
| New support invoice | $`O(nK_3)`$, residue addition $`O(ng)`$ | New packing; old support availability |
| Full-line prefix/macro/residue occupancy | $`O(P),O(K_3),O(g)`$ | Separate passes; centering |
| Old macro occupancy on extra lines | $`O(K_2)`$ on faces, zero on bodies | Old-support extension; final errors |
| One-reservoir orientation range | At most $`2X`$ per required line | Intersection contracts; concentration |
| Initial plus residue error | $`E_0+O(gX)=o(K_0X)`$ | (9); first correction stage |
| Old tensor scalar demands | $`O(K_1X\log^2n)+O(gn^2)=o(K_2X)`$ | Tensor-expander bound; old rectangles |
| Body correction demand | $`O(K_0X)=o(K_3X)`$ | Old body avoidance; body reservoirs |
| Body spill on one face | At most $`4X`$ | Fresh orbits across body stages |
| Final face demand and capacity | $`O(K_2X)=o(K_3X)`$ versus $`C_3\ge2K_3X`$ | Integral graph flows; isolated face reservoirs |

The threshold is the maximum of the finitely many fixed analytic, prime-scale,
packing and capacity thresholds displayed in these proofs. Uniformity in the
full odd-order tail follows because every ratio is bounded by a fixed constant
times a power of $`n`$ and a logarithmic factor tending to zero, and the prime
counts are uniform in their stated classes and moduli. The use of TZ/FL here
retains an ineffective analytic threshold; no evaluated integer cutoff is
asserted. Finite verification cannot establish that tail.

[Back to the four-manuscript index](README.md).
