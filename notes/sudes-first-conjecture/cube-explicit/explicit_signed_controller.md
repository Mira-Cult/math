# A finite controller for all full signed cube lines

Public proof manuscript. See [provenance](../PROVENANCE.md#explicit-prime-cube) for the pinned sources, internal review and verification limits.

## 1. Parameters and finite statement

Let `n` be odd, `n>=11`, and let


```math
A=\{p_2,\ldots,p_{n^3+1}\},\quad X=\max A,\quad
 T=\sum A,\quad m=T/n^3,\quad \mu=nm.
```


Coordinates are `0,...,n-1`, with reflection `bar(t)=n-1-t`. The required
family comprises exactly `3n^2+6n+4` distinct full signed-coordinate lines.
Compatibility means all three sets of axis plane-margin equations, common
directional total `T`, and the six diagonal-square family-total identities
in equations (1)--(3) of [signed_incidence.md](../cube/signed_incidence.md). There is
no additional body equation for odd `n>=11`. A square section itself is not
required to have prime sum.

Take integers


```math
1\le K_0\le K_1\le K_2\le K_3,\qquad F\ge4,
 \qquad g\ge2\text{ even},\qquad R=g/2-1,
```


and real `0<delta<=1/48`. Put


```math
s=256F^2,\quad B=\lceil\log_2X\rceil,\quad
 P=s+32FB,\quad J=P+32K_3+R,                              \qquad\text{(1)}
```



```math
H=2^{20}(66+1)=70\,254\,592,\qquad c\ge2^{16}
 \quad(c\text{ integral}),                              \qquad\text{(2)}
```



```math
S=4P+32K_0+64K_1+32K_2+4R,\qquad M=HJ+cS.              \qquad\text{(3)}
```


Here `M` is a bound on reserved cells on **each full signed line**, not a
number of reservoirs or an average over lines. The four old gadget types
are planes, horizontal rows, horizontal columns, and vertical rectangles.
For each type the prefix, macro, and residue stages are separate passes.
Their four prefix passes, four residue passes, and macro lengths explain
all terms in `S`. The new cuboids have three passes of lengths `P,32K3,R`.

The following complete entry invoice is used:


```math
\begin{split}
 Q={}&n^2(4288P+2048K_0+4096K_1+131072K_2)\\
 &+8(192n+4)(P+32K_3)+(8n^2+38n-14)R.                    \qquad\text{(4)}
\end{split}
```


This uses the integer choice `J_i=32Ki`, rather than the looser `33Ki`
rounding allowance in the old source. It includes every old and new prefix,
macro and residue entry. Define `Q*=2^21 n^2 K2` and require


```math
Q\le Q_*.                                               \qquad\text{(5)}
```


### The prime-supply hypotheses

These are ordinary cardinality requirements on the prescribed pool.

**PS1 (initial common-gap seeds).** For some reduced class `r mod g` there
are at least


```math
s(2144n^2+768n+16)                                      \qquad\text{(6)}
```


disjoint pairs `(p,p+g)` in `A`, all with lower endpoint in class `r`.
These pairs are chosen first. Only pairs actually requested are removed.

**PS2 (fresh growth stock).** After deletion of any at most `Q*` pool
entries, the remaining primes in class `r` in `[X/4,3X/4]` number at least
`X/(gF)`. Require also


```math
256gF^2\le X.                                          \qquad\text{(7)}
```


**PS3 (fresh balanced macro and residue stocks).** The two intervals


```math
I_-=[m-X/6-\delta X,m-X/6+\delta X],\qquad
 I_+=[m+X/6-\delta X,m+X/6+\delta X]                     \qquad\text{(8)}
```


are contained in `[X/4,3X/4]`. After any at most `Q*` prior deletions,
the lower and upper counts in classes `(r,r)`, and in classes `(-1,+1)`,
respectively have product at least


```math
4(\lfloor X/g\rfloor+1).                              \qquad\text{(9)}
```


Each of these classes is reduced. When `g=2` the residue request is
unneeded. In applying PS3 one may prove a lower bound separately for each
of the two counts; the product condition is what the finite argument uses.
The convenient mean bound `|m-X/2|<=X/24`, together with `delta<=1/48`,
implies the interval containment: the extreme endpoints lie between
`13X/48` and `35X/48`. No lower progression center is replaced by `X`.

### Geometry and correction inequalities

In addition to (5), (7), and the supply hypotheses, assume


```math
n\ge100\{M+H+c+100\},\qquad K_0X\ge g.                \qquad\text{(10)}
```


Write


```math
B_p=(4c+H)P,\quad B_r=(4c+H)R,\quad
 B_m=32c(K_0+2K_1+K_2)+32HK_3.                          \qquad\text{(11)}
```


The centering and residue condition is


```math
3B_p+4B_r+3\delta B_m+16\sqrt{n\log n}\le K_0.         \qquad\text{(12)}
```


The three subsequent demand inequalities are


```math
2K_0+c(P+32K_0)\le16K_1,                              \qquad\text{(13)}
```



```math
(5\log n+5)^2\{2K_0+2c(P+32K_1)\}
       +\frac g{2X}+\frac{512gn^2}{X}\le2K_2,           \qquad\text{(14)}
```



```math
2K_0+c(3P+64K_1+32K_2)+4\le16K_3.                    \qquad\text{(15)}
```


**Finite signed controller theorem FSC.** Under (1)--(15), every compatible
odd target vector for the full signed-line family, with each target within
`K0 X` of `mu`, is attained by a bijective placement of exactly `A` in the
cube. Repeated target values are permitted. No repetition of an entry,
extra entry, unused entry, alternate slope, wrapped line, or section-primality
assumption occurs in this statement.

The rest of the manuscript proves FSC and its uniform logarithmic envelopes.

## 2. Graph and scalar reservoirs with exact floors

### The degree-64 graph

For every integer `n>=2` there is a loopless undirected multigraph of maximum
degree 64 and cut expansion at least 8. Here is the finite counting argument
used in the frozen source. Take 32 independent uniform permutations, retain
one undirected edge for each directed arrow, with multiplicity, and delete
loops. If `|U|=u<=n/2`, fewer than `4u` directed arrows leaving `U` means
at least `28u` of the `32u` specified images lie in `U`. Its probability
is at most


```math
\binom{32u}{28u}(u/n)^{28u}.
```


Union over `U`, using the elementary binomial entropy bound, is bounded by
`sum_{u>=1} rho^u`, where


```math
\rho=e\,2^{69}/7^{28}\lt 3\,2^{69}/7^{28}\lt 1/2.
```


The stronger exact inequality
`(3*2^69)/(7^28-3*2^69)<1` is checked by the rational program. Thus the
union bound is below one. In every permutation the number of arrows entering
a cut equals the number leaving, so its undirected boundary has at least
`8u` edges. Maximum degree is at most 64, including multiplicities. The
construction applies to odd orders without a divisibility condition.

On this graph, integer capacities `[-C,C]` per edge realize every zero-total
integer demand with coordinate norm at most `8C`, by integral max flow.
Indeed each cut demand is bounded by `8C` times its smaller side and the
cut has at least eight times that many edges. Opposing flows can be canceled
on an edge. The same fact holds on a `g`-grid after division by `g`.

### Complete prefixes, with four actual equal-gap pairs when needed

An ordinary stage uses one pair; a checkerboard rectangle uses two disjoint
pairs with the same actual difference; an axis-neutral cuboid uses four.
The four-pair requirement is not a congruence substitute for equality.

Suppose a fresh set of primes in one class modulo `g` lies in an interval
of length at most `X` and has at least `X/(gF)` members. If
`256gF^2<=D<=X`, binning into at most `2X/D` intervals of length at most
`D` yields one with at least `z>=D/(2gF)` points. At least `z^2/4` pairs
in that bin have separation at least `gz/16`. (There are at most `z^2/16`
closer pairs and `z>=128F>=512`.) There are at most `D/g` positive
`g`-multiple differences. One difference occurs at least
`D/(16gF^2)>=16` times and belongs to


```math
[D/(32F),D].                                          \qquad\text{(16)}
```


The graph of a fixed positive difference has degree at most two. A greedy
matching removes at most three edges at each selection; sixteen edges
therefore contain at least six mutually disjoint pairs, of which four may
be used. Any unused candidates stay in the pool.

Start each reservoir with `s=256F^2` seed stages, using one, two, or four
of the disjoint gap-`g` pairs per stage. The resulting subset sums cover
the complete `g`-grid from zero to `sg`. Whenever its current endpoint
`D<X`, append a difference from (16). Since the appended gap is at most
`D`, the two translated grid intervals overlap. The new endpoint is at
least `(1+1/(32F))D`. In each block of `32F` growth stages the endpoint
at least doubles, by the binomial inequality. At most `32F ceil(log2 X)`
stages suffice, so the prefix length is at most `P`. Its endpoint is in
`[X,2X]`. PS2 pays for every earlier allocation, including all seeds.

For a macro stage, PS3 and pigeonholing among at most
`floor(X/g)+1` possible positive differences give four pairs of a common
actual difference. The lower and upper intervals are disjoint; at a fixed
difference these pairs already form a matching. For `(r,r)` the gap is a
multiple of `g`; for `(-1,+1)` it is `2 mod g`. The gap belongs to
`[X/4,X/2]`, since it is in `[X/3-2delta X,X/3+2delta X]`. Every pair
midpoint is within `delta X` of `m`.

Append exactly `32Ki` macro stages to each level-`i` main reservoir.
The prefix already reaches `X`, so all subsequent gaps preserve complete
grid coverage. Its total gap `D_b` satisfies `D_b>=8Ki X`. Choose a
realizable subset of sum


```math
q_b=g\lfloor D_b/(2g)\rfloor
```


or its complement. Their native sums differ by at most `g`. From either
reference every `g`-multiple of absolute value at most


```math
C_i=g\lfloor3K_iX/g\rfloor                             \qquad\text{(17)}
```


is attainable: the nearer endpoint of the complete grid is at distance
at least `D_b/2-g>=4KiX-g>=3KiX`. The last step uses `K0X>=g` and
`Ki>=K0`. Also


```math
C_i\ge3K_iX-g\ge2K_iX.                                \qquad\text{(18)}
```


These are pointwise floor bounds. They do not ignore jumps or assume that a
formal integer coefficient can be consumed without actual prime swaps.

### Complete invoice

There are at most `32n^2` plane reservoirs, `64n^2` slice reservoirs,
and `1024n^2` rectangle reservoirs. Ordinary stages use two entries and
rectangle stages four. Their invoice is the first line of (4). There are
at most `6|E(G)|+4<=192n+4` new main cuboid reservoirs, each using eight
entries per stage, giving the first term in the second line.

For residues there is one plane path, two horizontal paths in each of
`n` slices, and a product of two paths for the vertical tensor. With `R`
stages per path edge or edge pair, their entry total is


```math
[2(n-1)+4n(n-1)+4(n-1)^2]R=(8n^2-10n+2)R.
```


The six face paths and four bodies require `8(6n-2)R` further entries.
Their sum is the final term of (4), and is at most the previously used
`5n^2g+24ng`. The new entry demand is in particular at most
`8(192n+4)(P+33K3)+24ng`, the retained starting interface.

Seed pairs per stage number at most `2144n^2` for the old controls and
`768n+16` for the new ones, proving (6). The invoice pays for all removed
endpoints, even when a growth request first discovers more pairs than it
uses. Equation (5) makes the uniform preceding-deletion allowance literal.

## 3. Finite placement and the improved old face cap

The cuboid descriptions and exact signed-line images are those of Sections
1--2 of [signed_trades.md](../cube/signed_trades.md): a face cuboid meets precisely
its two native face lines outside the axis family, and a body cuboid meets
its one native body plus six specified face lines. Distinct noncentral
reflection orbits are essential, including when native face levels are
central or reflected. Aligned or central cuboids are not substituted.

### New supports first

Apply the finite packing lemma there to the union of the degree-64 graph
and the residue path, of degree at most 66. Use prefix, macro and residue
passes of lengths `P,32K3,R`, omitting the last if `R=0`. Its explicit
condition is `n>=max(11,100H(J+1))`, implied by (10).

This yields disjoint cuboid supports, at most `H` times the pass length
on each axis, and globally fresh free-coordinate reflection orbits within
**each entire bundle**, across all passes. Every face line meets at most
one cell of a particular body bundle. Across the four bodies the complete
possible spill to a face is therefore at most `4X`, irrespective of the
numbers of prefix or macro stages.

The lemma's face occupancy is at most `66J+4`, and its body occupancy is
at most `J`; these are bounded by `HJ`. For an individual nonempty pass
its face occupancy is at most `66L+4<=HL`. Thus the separate prefix,
macro and residue bounds used in (11) also hold on all signed lines.
Unused planned prefix slots are returned to ordinary completion; they do
not require extra primes.

### Old supports: exact exclusions

Pack each of the four old types in its own prefix, macro and residue pass.
A pass has at most `L` stages per reservoir. Cap every nonnative axis and
every affected face line at `cL` entries from this pass. Native slice lines
have at most `64L` entries and native vertical lines of rectangle passes
at most `64^2L`, already below `cL`. Every stage adds at most two entries
to a line. A cap-rejected line therefore already contains more than
`cL-2>=cL/2` entries. Earlier passes and new cuboids are excluded by their
occupied cells, not charged again to this pass's saturation count.

All occupied axis fibers have at most `M` entries by induction. A coordinate
plane contains at most `nM` occupied cells. The complete planned loads,
not average-placement assumptions, give the following saturation bounds.

| Type | Cap exclusions | Existing-cell exclusions | Distinctness and geometric exclusions |
|---|---:|---:|---:|
| Vertical rectangle, one free `z` | `12*64^2 n/c` | `4M` | `J+8` |
| Slice row or column, one free coordinate | `10*64 n/c` | `2M` | `J+6` |
| Plane pair, free `(x,y)` | `10*64 n^2/c` | `2nM` | `2Jn+10n` |

Here is the derivation, including exceptional axes.

For a vertical rectangle on graph edges `(x,x')` and `(y,y')`, every
vertical fiber belongs to at most `64^2` edge pairs. In a fixed `x` plane
the planned entry total is at most `64^2 n L`; the same is true of a
fixed `y` plane. Saturated horizontal lines therefore forbid at most
`8*64^2 n/c` values of `z`, for the two fixed `x` and two fixed `y`
coordinates. Each of the two `xy` diagonal sections has at most
`64^2 n L` planned entries, so its face cap forbids at most
`2*64^2 n/c` further levels. This gives the first table entry. Require
`z` outside the reflection orbits of `x,x',y,y'`, excluding at most eight
values. It then avoids every `xz` or `yz` diagonal and every body. Its
only possible face intersections are the two `xy` lines at level `z`.
Distinct stages of the reservoir use distinct `z`, across all its passes.

For a row transfer in slice `z` between `x,x'`, the whole slice has at
most `64nL` planned entries. The cap on transverse horizontal lines
forbids at most `2*64n/c` free `y` values. Across all slices, the planned
load in a fixed `x` plane is at most `64nL`; vertical caps at the two
native `x` values forbid at most another `4*64n/c` choices. Choose `y`
outside the reflection orbits of `x,x',z`, excluding at most six values.
This removes all `xy` and `yz` diagonal intersections and all bodies.
An endpoint with `x=z` or `x=bar(z)` remains allowed. For either sign
of the resulting `xz` section, only edges incident to the specified
native endpoint in each slice contribute, so the entire section's planned
load is at most `64nL`. Its face caps forbid at most `2*64n/c` choices
per sign. Total saturation is therefore `10*64n/c`, including these
exceptional axes. The free coordinate is distinct within each reservoir
across passes, so any extra face line meets at most one stage and one cell.
Column transfers are the transposed construction.

For a plane transfer between `z,z'`, each coordinate plane has at most
`64nL` planned entries, while the total across all planes is at most
`64n^2L`. The horizontal caps in two planes exclude at most
`8*64n^2/c` positions, and vertical caps exclude at most `2*64n^2/c`.
Require `x,y` outside the reflection orbits of `z,z'`, and `x` outside
the reflection orbit of `y`. At most `10n` positions are removed. Neither
endpoint then belongs to any extra signed line. The partial matching rule
within a reservoir removes at most `J` old `x` and `J` old `y` values,
hence at most `2Jn` positions.

Residue paths have smaller degree, and their plane stage has only one
reservoir per edge instead of `n`. The same table bounds them. For `R=0`
there is no residue pass and no division by its length.

With `c>=2^16`, the worst saturation fraction is


```math
12\cdot64^2/c\le3/4.                                  \qquad\text{(19)}
```


Condition (10) gives `M<n/100`, `J<=M/H`, and `n>=10000`. Thus the
remaining exclusions in the first row are less than `n/20`. The second
row has the smaller saturation fraction `10*64/c<=5/512` and fewer
occupied exclusions. In the third row, dividing the excluded count by
`n^2` gives at most


```math
10\cdot64/c+2M/n+2J/n+10/n\lt 1.
```


Every greedy choice is possible. This is a new finite load proof; its
smaller `c` does not change graph degree, cut expansion, reservoir counts,
tensor constants or cuboid packing. The original `c=10^12` also satisfies
the theorem and is retained as a comparison profile.

Every old body intersection has been excluded. Old planes meet no extra
signed line. Old slice reservoirs meet a given face in at most one cell
and one stage; old rectangle reservoirs meet a given face in at most two
cells and one stage. This holds at central and reflected coordinates,
by the explicit exclusions just given.

The sum of the separate pass caps is exactly bounded by `M`. In particular
all reserved entries together number at most `n^2M<n^3/100`, by summing
vertical fiber occupancies. The unused pool therefore has more than half
of the original entries before its mean is used.

## 4. Centering, with independence at the correct level

Choose independently, for each **whole main reservoir**, one of its two
complementary midpoint subsets from Section 2, with equal probability.
Keep every residue stage in a fixed reference orientation. A macro cell
has expectation equal to its actual pair midpoint; its difference from
`m` is at most `delta X`. Prefix and residue cells cost at most `X`
each. Hence the expected reserved deviation on any signed line is at most


```math
X(B_p+B_r+\delta B_m).                                 \qquad\text{(20)}
```


The range of one reservoir's contribution to one signed line is at most
`2X`. For old axes the range is at most `X`: either the line meets at
most one stage cell, its pair or rectangle sum is fixed, or it is a native
line whose two reference totals differ by at most `g`. For extra faces,
old slices meet at most one cell and old rectangles at most two cells of
one stage; old planes do not meet them. A native new face reservoir has
range at most `g`, nonnative face reservoirs have zero range, and each
new body reservoir has range at most `X` on any face by its globally
fresh orbits. New cuboids leave every axis unchanged. Only the corresponding
new body reservoir can vary a body sum, with range at most `g`.
Here `g<=X` follows from (7).

The number of varying reservoirs on one line is at most its reserved-cell
count, hence at most `M<n`. For a fair two-point variable of width `a`,
`E exp(t(Z-EZ))=cosh(ta/2)<=exp(t^2 a^2/8)`. Multiplying this inequality
for the independent reservoir choices and applying Markov's inequality
gives


```math
\Pr(|C_L-\mathbb EC_L|\gt u)
       \le2\exp(-u^2/(2nX^2)).                          \qquad\text{(21)}
```


Take `u=4X sqrt(n log n)`. Since `3n^2+6n+4<=4n^2` for `n>=11`,
the union failure probability is at most `8n^-6<1`. Thus simultaneous
reserved deviations satisfy


```math
|C_L-r_Lm|\le E:=X(B_p+B_r+\delta B_m)+u.              \qquad\text{(22)}
```


No independence of lines or of individual cells is asserted.

Let `m0` be the mean of unused entries. Summing (22) over the `n^2`
vertical lines, which partition all reserved cells, and using at least
`n^3/2` unused entries, yields `|m0-m|<=2E/n`. Uniformly permute every
unused entry into the free cells. The expectation of any completed line
then differs from `mu` by at most `3E`.

For completeness, sampling without replacement here needs no imported
asymptotic concentration theorem. Reveal the `k<=n` values on one line.
The Doob martingale for their final sum has increments of absolute value
at most `X`: at reveal `j` the increment is the selected value minus the
old remaining mean, multiplied by `(N-k)/(N-j)<=1`, where `N` is the
unused-pool size. Conditional convexity on `[-X,X]` bounds its moment
by `cosh(tX)<=exp(t^2X^2/2)`. Iteration and Markov give the right-hand
side of (21) again. The same `u` and union bound yield a completion with
all line errors at most `3E+u`. Every prescribed entry is now used once.

## 5. Residue repairs and their numerical cost

Put `h=g/2`. An actual residue-stage gap supplied by PS3 is `2 mod g`.
The old plane path, row and column paths, and path-product rectangles
therefore realize every compatible axis residue correction: divide even
errors by two modulo `h`, use path prefix sums (double prefix sums for
the final zero-margin matrix), and take each coefficient in `0,...,h-1`.
There are exactly `R=h-1` available stages per such edge or edge pair.
All reference and target line sums are odd because `n` is odd, so division
of their differences by two is valid. The plane-total differences are
also even. The compatibility identities imply the required zero totals
and zero margins modulo `h` at each subsequent step.

The old supports avoid every body. After the axes have the desired residues,
correct the four body residues with their own residue cuboids, then the
six face families along their paths. Each face-family difference has total
zero modulo `g` by its exact diagonal-square identity. Body cuboids preserve
all axes, so their face spill does not alter this condition. A face cuboid
changes only its two native face lines outside the axis family, and every
new cuboid is axis-neutral. Prefix-sum path coefficients therefore finish
the face residues without disturbing earlier residues.

When `g=2`, `R=0` and no residue stages or corrections exist. Every odd
line is already congruent to its odd target modulo two.

During the whole residue schedule, at most `Br` entries on a signed line
can change, so its numerical change has magnitude at most `Br X`. The
main supports are disjoint and remain at their reference states. Combining
this with (22) and the completion bound gives the following deviation from
`mu`, after all residues:


```math
X\{3B_p+4B_r+3\delta B_m+16\sqrt{n\log n}\}\le K_0X.
```


Thus each desired target error is a multiple of `g` and has magnitude at
most `2K0X`. No coprimality assumption on the current line sums or on
face-family totals has been made.

## 6. The complete triangular physical correction

All corrections below use main reservoirs; they preserve the residues
already established. Equation (18) gives their actual signed capacities.

**Planes.** A `z`-plane demand is the sum of `n` horizontal target errors,
hence has magnitude at most `2nK0X`. The total of these demands is zero.
A graph edge has `n` level-0 reservoirs, each of capacity `C0`, hence
complete combined grid interval of radius `nC0>=2nK0X`. The degree-64
graph's cut condition realizes the demands with room to spare. A flow
can be split over its `n` reservoirs because a sum of complete integer
grid intervals is a complete interval. All vertical sums are unchanged.
A horizontal line changes by at most `c(P+32K0)X`, its level-0 reserved
load times `X`. Its remaining error is bounded by the left side of (13)
times `X`.

**Horizontal axes.** In every slice the two directional lists now have
correct exact totals. Separate row and column flows preserve one another.
Their demand norms are at most `16K1X<=8C1`, by (13) and (18), so all
horizontal axis targets are attained. A vertical line changes by at most
`2c(P+32K1)X` in this stage. Its demand therefore has norm at most


```math
X\{2K_0+2c(P+32K_1)\}.                                \qquad\text{(23)}
```


The use of the smaller level-1 load in (23) is essential; a `K3` bound
would not meet the tensor interface.

**Vertical tensor.** The residual matrix `D` of vertical demands has zero
row and column sums as integers, by the corrected horizontal axes and
exact target compatibility. All entries are multiples of `g`. The finite
tensor theorem in [incidence.md](../cube/incidence.md) applies to the same graph:
cut expansion 8 and degree 64 give spectral gap at least `1/256`, routing
norm at most `5log n+5`, and integer rounding cost `1/2+512n^2`.
It supplies integral edge-pair coefficients with


```math
gB_GFB_G^t=D,\qquad
 \|gF\|_\infty\le(5\log n+5)^2\|D\|_\infty+g/2+512gn^2.
```


Equations (14), (18), and (23) put every coefficient within the level-2
reservoir capacity. Its actual equal-gap pair swaps realize the checkerboard
coefficient and preserve all horizontal sums. All axis targets are now exact.

**Bodies.** All old supports avoided bodies, so their target errors still
have magnitude at most `2K0X<=2K3X<=C3`. Correct each body with its own
scalar cuboid reservoir. These corrections preserve the axes and all other
bodies. Fresh reflection orbits across each whole body bundle bound their
combined change on any face line by `4X`.

**Faces.** Plane controls never met faces. Slice and rectangle controls
had at most `c[2(P+32K1)+(P+32K2)]` cells on any face. Consequently its
remaining demand after the four bodies is at most the left side of (15)
times `X`, and thus at most `16K3X<=8C3`. Each face family has exact
zero total: its desired total and current total both equal the same
perpendicular-axis aggregate on the relevant diagonal square. The six
independent degree-64 graph flows therefore realize these demands on the
`g`-grid. Their supports preserve every axis, every body and the other five
face families.

The final cube attains every prescribed target by disjoint permutations of
original entries. This proves FSC. Every numerical, geometric, randomization
and residue inequality used above is one of the finite hypotheses; there
is no residual `O`, `o`, or unquantified eventual assertion.

## 7. Logarithmic schedules, floor jumps and persistence

For explicit applications set `L=log X`,


```math
F=\lceil100L\rceil,\quad g\le16\lceil\log_2X\rceil,
 \quad K_i=\lceil n/L^{a_i}\rceil,\quad\delta=L^{-d}.
                                                               \qquad\text{(24)}
```


Assume the separately certified elementary scale bounds


```math
n^3\le X\le n^4,\qquad L\ge2^{16}.                     \qquad\text{(25)}
```


Then `L/4<=log n<=L/3`. Also `n>=L^201`: the function
`L/4-201log L` is increasing for `L>=2^16` and is positive there
using `log2<1`. These comparisons hold on the entire real tail.

The rational program explicit_signed_controller.py (see [verification scope](../PROVENANCE.md#explicit-prime-cube))
uses the following pointwise outward envelopes, with `t=L^-201`:


```math
\begin{aligned}
 n^{-1}&\le t,& K_i/n&\le L^{-a_i}+t,& K_i/n&\ge L^{-a_i},\\
 F&\le100L+1,&g&\le24L+16,&R&\le12L+7,\\
 P&\le256(100L+1)^2+32(100L+1)(3L/2+1),
\end{aligned}                                                   \qquad\text{(26)}
```


where `log2>=2/3` suffices for the bound on `ceil(log2 X)`.
The concentration term divided by `n` is at most `16L^-100`, since
`sqrt(log n/n)<=sqrt((L/3)L^-201)<=L^-100`. The tensor's two rounding
terms, after division by `n`, are at most `(g/2)t^4+512g t^2`, by
`X>=n^3`. No floating-point logarithm, root, or exponential is used in
these controller acceptance decisions.

Every hypothesis ratio is expanded into a Laurent polynomial in `L` with
nonnegative rational coefficients. The checker requires every exponent to
be nonpositive. Such a ratio is nonincreasing for **every real** `L`
above the endpoint. Ceilings in `Ki,F,P` and the gap bound are paid by
(26) for every integer order; no monotonicity of the rounded parameters
is presumed. Native capacity floors were already paid pointwise in (18).

The strict exponent conditions for these controller envelopes include


```math
100\gt a_0\gt a_1\gt a_2\gt a_3\gt 0,\qquad d+a_3\gt a_0,
 \qquad a_1\gt a_2+2.                                     \qquad\text{(27)}
```


The depletion interface adds a separate restriction, typically
`a2>d+1`, when a midpoint class contains a constant multiple of
`delta X/(g log X)`. All tested profiles below satisfy this. These
inequalities exhibit a nonempty feasible region before numerical search.
The targets and analytic counts must still be certified at the chosen
profile; this table alone is not a cube cutoff.

### Measured physical-controller bottlenecks

The following are the first sufficient **integer values of `L`** for the
entire controller envelope, whose common domain starts at `65536`.
They are computed by exact rational comparison and monotonic bisection.

| Profile `(a0,a1,a2,a3;d;c)` | First sufficient `L` | Limiting physical condition |
|---|---:|---|
| `(20,18,15,12;9;10^12)` | 88,888,888,888,895 | Vertical tensor |
| `(35,30,25,20;20;10^12)` | 65,536 | Common envelope domain |
| `(22,19,15,12;12;2^20)` | 82,125 | Centering and residue allowance |
| `(19,17,13,11;10;2^20)` | 82,125 | Centering and residue allowance |
| `(16,15,11,10;8;2^16)` | 131,073 | Horizontal and final face stages |

The original logarithmic experiment suffers from one-power separations
against large geometric constants. Wider separations remove that physical
bottleneck. The rigorously smaller old cap then permits narrower exponents,
which may improve the separate analytic windows enough to reduce the complete
cutoff further. None of these component numbers is a lower bound for the
prime-cube problem.

The seventeen executable controller rows cover the graph, interval width,
initial gap range, native floor, joint and new packing, all three placement
choice counts, half-pool occupancy, joint invoice, centering and residues,
all three subsequent stage demands, and both probability union bounds.
The last two use the exact family count bound, not only the axis lines.
Seven retained rejection controls alter a strict exponent margin, cap,
scale order, monotonicity, or the preceding insufficient controller endpoint.
They test arithmetic/source discipline, not mathematical truth of imports.

## 8. Replay and exact scope

The research arithmetic checks are described in the [verification record](../PROVENANCE.md#explicit-prime-cube).

The output records every ratio as an exact nonnegative Laurent polynomial,
its limiting value, outward decimal display bounds, and first sufficient
integer `L`. Decisions and bisection use only `Fraction` and integers.
A changed profile must pass all rows; an individual improved component
cannot establish a smaller complete cutoff.

The original small-order array certificates, four-pair physical trades,
geometry fixtures, order-five torsion controls, and order-three section
obstruction are unchanged. They remain finite diagnostics with their original
scope. This finite controller continues to exclude even orders and supplies
no statement about the exceptional orders below its certified domain.
An explicit cube at the final cutoff is not required by the existence proof.
