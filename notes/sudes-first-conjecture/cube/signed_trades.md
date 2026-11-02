# Axis-neutral cuboids for all signed cube lines

Public proof manuscript. See [review and provenance](../PROVENANCE.md#full-signed-line-cube) for source revisions, review scope, and verification limits.

## 1. All signed-line effects of an elementary cuboid

Use coordinates in $`[n]=\{1,\ldots,n\}`$, with $`n`$ odd, reflection
$`R(t)=n+1-t`$, and center $`c=(n+1)/2`$. A noncentral reflection orbit is
$`\{t,R(t)\}`$ with $`t\ne c`$. Two values in different such orbits are
neither equal nor complementary.

Write $`F_{xy}^+(z)`$ for the line $`(t,t,z)`$ and $`F_{xy}^-(z)`$ for
$`(t,R(t),z)`$. Define the analogous $`xz`$ and $`yz`$ families by permuting
coordinates. These are six families, each containing $`n`$ lines.
The four body lines are



```math
B_{\sigma,\tau}=\{(t,R^\sigma(t),R^\tau(t)):t\in[n]\},
\qquad \sigma,\tau\in\{0,1\}.
```



Together with the $`3n^2`$ axis lines these are precisely family B.

Choose distinct endpoints in each of three ordered pairs, and put



```math
\alpha=e_{x_0}-e_{x_1},\quad
\beta=e_{y_0}-e_{y_1},\quad
\gamma=e_{z_0}-e_{z_1}.
```



An elementary cuboid correction is $`d\,\alpha\otimes\beta\otimes\gamma`$.
Every axis-line sum is zero because each factor has zero total.
Its complete nonaxis image is



```math
\begin{aligned}
\Delta F_{xy}^{\epsilon}(k)
 &=d\,\gamma_k\sum_t\alpha_t\beta_{R^\epsilon(t)},\\
\Delta F_{xz}^{\epsilon}(k)
 &=d\,\beta_k\sum_t\alpha_t\gamma_{R^\epsilon(t)},\\
\Delta F_{yz}^{\epsilon}(k)
 &=d\,\alpha_k\sum_t\beta_t\gamma_{R^\epsilon(t)},\\
\Delta B_{\sigma,\tau}
 &=d\sum_t\alpha_t\beta_{R^\sigma(t)}\gamma_{R^\tau(t)}.
\end{aligned}                                                     \qquad\text{(1)}
```



Here a superscript zero denotes the plus family and a superscript one
the minus family. These formulas follow by evaluating the correction
on every point of the defining line. They include central coincidences
and repeated intersections; no generic-position assumption is hidden
in (1).

### Physical four-pair lemma

Suppose four mutually disjoint pairs of prescribed entries have the
same actual positive difference $`d`$. Place one pair on the two
$`z`$-endpoints for each of the four $`(x_i,y_j)`$ corners. When $`i+j`$ is
even, put the lower entry at $`z_0`$ and the upper entry at $`z_1`$;
reverse this order when $`i+j`$ is odd. Swapping the endpoints in all
four pairs changes the eight entries by



```math
\Delta a_{x_i,y_j,z_k}=d(-1)^{i+j+k}.
```



Thus four actual pair swaps realize the cuboid correction. The entries
remain distinct, and the move is an exact permutation of its eight
entries. The four-pair hypothesis cannot be replaced by a numerical
gcd or by one repeated entry pair. Coordinate reflections and
permutations preserve the assertion.

## 2. Isolated unit transfers and their exceptions

### Face transfer lemma

Fix distinct levels $`u,v`$. Choose $`a,b,c`$ in three different
noncentral reflection orbits, none of which contains $`u`$ or $`v`$.
The cuboid



```math
\{a,b\}\times\{a,c\}\times\{u,v\}
```



with the displayed endpoint order has nonaxis image exactly



```math
d\bigl(e_{F_{xy}^+(u)}-e_{F_{xy}^+(v)}\bigr).                      \qquad\text{(2)}
```



Indeed, the first two coordinate pairs meet only at $`a`$, and do not
meet after reflection. Neither meets the third pair, even after
reflection. Formula (1) now gives (2), zero on the other five face
families, and zero on every body line.

The support itself meets no other nonaxis signed line: its only
nonaxis incidences are the two points $`(a,a,u)`$ and $`(a,a,v)`$.
This stronger support statement will control occupancy and centering.
It follows directly from the same orbit exclusions.

Permuting coordinates and reflecting one varying coordinate gives
the corresponding unit transfer in any of the six face families.
The coefficient is $`d`$, not $`2d`$. The fixed levels may be central or
reflections of each other. They exclude at most two noncentral
reflection orbits. Consequently the choice is available for every
$`u\ne v`$ when $`n\ge11`$, before additional packing restrictions.

### Body control lemma

Choose $`a,b,c,d`$ in four different noncentral reflection orbits.
For a positive scalar $`h`$, the cuboid



```math
\{a,b\}\times\{a,c\}\times\{a,d\}
```



has body image $`h\,e_{B_{0,0}}`$. Its remaining nonaxis image is



```math
h\bigl(
e_{F_{xy}^+(a)}-e_{F_{xy}^+(d)}
+e_{F_{xz}^+(a)}-e_{F_{xz}^+(c)}
+e_{F_{yz}^+(a)}-e_{F_{yz}^+(b)}
\bigr).                                                         \qquad\text{(3)}
```



The common intersection of all three coordinate pairs is exactly
$`a`$. Each pairwise intersection is also exactly $`a`$, and all
reflected intersections are empty. Formula (1) proves the statement.
The only body point in the support is $`(a,a,a)`$; the support meets
precisely the six face lines appearing in (3), in one cell each.
Reflecting coordinates two and three produces the other three body
controls. Their face images are the corresponding reflected images
of (3). Four noncentral orbits exist when $`n\ge9`$.

### Why generic and central cases must be separated

Taking the same pair $`\{a,b\}`$ in all three directions, with $`a,b`$
in different noncentral reflection orbits, gives zero body change:
the two body vertices have opposite cuboid signs. Its three plus
face families instead receive transfers with coefficient $`2h`$.
That tempting symmetric cuboid does not control a body target.

If the common value $`a`$ in the body construction is the center, and
$`b,c,d`$ belong to three distinct noncentral reflection orbits, the
central vertex lies on all four body lines. The correction changes
all four body sums by $`h`$. Each pairwise reflected face intersection
also acquires the central point. The central construction therefore
does not isolate one body. These are exact failures of those
geometries, not impossibility theorems for prime arrangements.
Using noncentral, distinct reflection orbits repairs both failures.

The six face-family totals are already determined by the axis sums.
For example,



```math
\sum_z F_{xy}^+(z)=\sum_t C_{t,t},\qquad
\sum_z F_{xy}^-(z)=\sum_t C_{t,R(t)},
```



where $`C_{x,y}`$ is the vertical axis-line sum. Thus a final
axis-neutral face correction necessarily has zero total in each
family. The unit transfers above realize that requirement without
an extra factor-two obstruction. The complete integer-image theorem
and its modulo-$`g`$ version are proved in the linked incidence source.

## 3. Four equal prime gaps after earlier allocations

Let the prescribed pool be the first $`n^3`$ odd primes, let $`X`$ be its
largest entry, and put $`m`$ equal to its mean. Use the axis-controller
parameters



```math
F=\lceil100\log X\rceil,\qquad
P=\lceil256F^2\rceil+32F\lceil\log_2X\rceil,\qquad
\delta=n^{-1/5}.
```



All asymptotic assertions in this section use the actual analytic
supply established in Sections 2.1--2.3 of the preserved
[cube controller](cube_controller.md), with the enlarged common
deletion budget verified in the full signed-cube proof. They are not
an independent assumption that arbitrary prime pools have the supply.

### Four-pair version of the growth lemma

The axis-controller growth argument already proves the following
stronger conclusion with its unchanged constants. If a fresh set
$`S`$ in one class modulo $`g`$ lies in an interval of length at most $`X`$,



```math
|S|\ge X/(gF),\qquad F\ge4,\qquad 256gF^2\le R\le X,
```



then **four** mutually disjoint pairs from $`S`$ have the same positive
difference $`h`$, with $`h`$ a multiple of $`g`$ and



```math
R/(32F)\le h\le R.                                                \qquad\text{(4)}
```



For completeness, binning produces at least 16 pairs of one such
difference. The graph of pairs of a fixed positive difference has
maximum degree two. A greedy edge matching discards at most three
edges per selection, and hence has at least
$`\lceil16/3\rceil=6`$ edges. Four can be used; all unused entries
remain available. No change to the finite numerical hypothesis is
needed.

The common-gap matching in the prescribed central interval supplies
$`\gg X/\log^3X`$ disjoint pairs of one even gap
$`g\le16\lceil\log_2X\rceil`$, all with lower endpoint in one reduced
class. Grouping four pairs per cuboid seed is therefore valid. There
are only $`O(n)`$ new scalar bundles, so their total seed demand is
$`O(nP)`$ pairs, a lower order addition to the old $`O(n^2P)`$ demand.

Start each new scalar bundle with $`\lceil256F^2\rceil`$ gap-$`g`$
stages, using four pairs at each stage. Iterating (4) gives a prefix
of at most $`P`$ stages whose subset sums contain every multiple of
$`g`$ from zero to a value at least $`X`$. The completeness follows
from the overlap of $`[0,R]`$ and $`[h,h+R]`$ on the $`g`$-grid whenever
$`h\le R`$. The old bound on the number of growth stages applies
unchanged.

### Four balanced macro pairs and residue pairs

Use the midpoint intervals



```math
I_-=[m-X/6-\delta X,m-X/6+\delta X],\qquad
I_+=[m+X/6-\delta X,m+X/6+\delta X].
```



After the full deletion allowance, each relevant reduced class still
has $`\gg\delta X/(g\log X)`$ entries in each interval. Pigeonholing
low/high differences gives a common difference on



```math
\gg \delta^2X/(g\log^2X)
```



pairs. This quantity tends to infinity uniformly in the allowed
modulus range. A fixed low/high difference gives a matching, since
the endpoint intervals are disjoint and each lower endpoint has a
unique upper partner. Four pairs can therefore be selected fresh.
Their common difference is in $`[X/4,X/2]`$, is a multiple of $`g`$,
and every pair midpoint differs from $`m`$ by at most $`\delta X`$.

For residue stages, take the lower endpoints in class $`-1`$ and
upper endpoints in class $`+1`$ modulo $`g`$. The same matching
argument gives four equal actual gaps congruent to 2 modulo $`g`$.
All endpoints are again fresh. The case $`g=2`$ needs no residue
stages.

Only macro pairs have the shrinking midpoint guarantee used in
centering. Prefix and residue entries are charged their full
$`O(X)`$ error where necessary; they are not silently declared
balanced.

### Signed scalar capacity

Set



```math
K_3=\lceil n^{39/50}\rceil,\qquad J_3=\lceil32K_3\rceil .
```



Append $`J_3`$ macro stages to each prefix. The subset sums still
contain a complete $`g`$-grid because every appended gap is at most
$`X`$ and the prefix already reaches $`X`$. If the total gap is $`R_b`$,
then



```math
R_b\ge8K_3X,\qquad R_b=O(K_3X).
```



Choose a realizable subset of gap sum
$`q_b=g\lfloor R_b/(2g)\rfloor`$, or its complement. From either
reference state, every signed multiple of $`g`$ of magnitude at most
$`3K_3X`$ is attainable eventually. This follows from complete
grid coverage and
$`\min(q_b,R_b-q_b)\ge R_b/2-g\ge3K_3X`$.
The two reference native sums differ by at most $`g`$. A fair choice
between them gives each macro cell its actual pair midpoint as
expectation.

For a body bundle this scalar interval concerns its native body
sum only. The face side effects vary with the stage geometry;
there is no asserted fixed full-incidence column for that bundle.
The packing lemma bounds those side effects directly instead.

## 4. Disjoint packing with separate axis-line load bounds

The following finite geometric lemma permits the new reserves to
be placed before the old axis controller.

Fix a loopless multigraph on $`[n]`$ for each of the six face families,
each of maximum degree at most $`\Delta\ge1`$. Each labeled edge
specifies one scalar face bundle whose two native lines are its
endpoints. There are at most $`3\Delta n`$ face bundles. Also specify
one body bundle for each of the four body lines.

Partition stages into finitely many passes. In pass $`p`$, each bundle
has at most $`L_p`$ stages, where $`L_p`$ is a nonnegative integer.
Zero passes may be omitted. Put



```math
J=\sum_p L_p,\qquad H_0=2^{20}(\Delta+1).
```



**Packing lemma.** If



```math
n\ge \max\{11,\;100H_0(J+1)\},                                   \qquad\text{(5)}
```



all stages can be placed as the generic cuboids of Section 2 with
the following simultaneous properties.

1. All eight-cell supports are pairwise disjoint.
2. In pass $`p`$, every axis line contains at most $`H_0L_p`$ reserved
   cells.
3. Within each bundle, every free-coordinate reflection orbit used
   at one stage is different from every such orbit used at every
   other stage of that bundle. For a face bundle, these are the
   three orbits of $`a,b,c`$; its fixed endpoint levels are excluded
   at every stage. For a body bundle these are all four orbits.
4. Each face line contains at most $`\Delta L_p+4`$ pass-$`p`$ cells;
   each body line contains at most $`L_p`$ pass-$`p`$ cells. Across all
   passes, a given face line meets at most one cell from each body
   bundle.

The last bound is a support statement, not just a zero-sum
cancellation. In particular, arbitrary orientation changes of all
stages in all four body bundles change any one face sum by at most
$`4X`$ when all entries lie in $`[1,X]`$.

**Proof.** Place passes and stages sequentially. There are at most
$`(3\Delta n+4)L_p`$ stages in pass $`p`$, so at most
$`8(3\Delta+4)nL_p`$ cells will be placed in that pass. Maintain the
claimed pass-specific cap. Declare an axis line saturated if its
current pass-$`p`$ load exceeds $`H_0L_p-2`$. Every cuboid uses either
zero or two cells of an axis line. Avoiding saturated lines
therefore preserves the cap.

The total incidence of pass-$`p`$ cells with all axis lines is at most
$`24(3\Delta+4)nL_p`$. Since a saturated line has load at least
$`H_0L_p/2`$, the number $`s`$ of saturated lines satisfies



```math
s\le \frac{48(3\Delta+4)}{H_0}n
\le\frac{168}{2^{20}}n.
```



At any one free-coordinate choice, at most 12 newly determined
axis lines need be checked. Each such line, if it depends on that
coordinate, depends injectively on it. Thus the total forbidden
values arising from saturation are at most



```math
12s \lt  n/128.                                                     \qquad\text{(6)}
```



Previously completed passes cause occupied cells but do not enter
the current-pass saturation count. The combined axis-line load
from all passes is at most $`M=H_0J`$. Orbit exclusions within a
bundle forbid at most $`8J+10`$ values, including current roles,
the central value, and the fixed face levels and their reflections.

For a plus $`xy`$ face bundle with fixed levels $`u,v`$, choose its
free coordinates in order $`a,c,b`$.

- The first choice must make $`(a,a,u)`$ and $`(a,a,v)`$ free. A face
  line can meet only the face bundles native to it, at most
  $`\Delta`$ bundles with at most $`J`$ stages each, and at most one
  cell from each of the four body bundles. Consequently at most
  $`2(\Delta J+4)`$ values are excluded by occupied native cells.
  Check the four horizontal axis lines through these points and
  the vertical line with fixed coordinates $`(a,a)`$ for saturation.
- For $`c`$, make $`(a,c,u)`$ and $`(a,c,v)`$ free. These are two fibers
  of the $`y`$-axis family, excluding at most $`2M`$ values. Check
  the two newly determined $`x`$-axis lines and the vertical line
  with fixed coordinates $`(a,c)`$.
- For $`b`$, make $`(b,a,u),(b,a,v),(b,c,u),(b,c,v)`$ free. These lie
  on four fixed $`x`$-axis fibers, excluding at most $`4M`$ values.
  Check the two new $`y`$-axis lines and the two new vertical lines.

The stated native-face occupancy bound is preserved inductively:
generic face stages meet only their two native nonaxis lines.
For a body bundle, its globally fresh reflection orbits ensure
that a fixed face level can be either a common coordinate or one
of the three other roles at at most one stage, even after
reflection. Thus a face line contains at most one cell from that
body bundle across every pass. Reflections and coordinate
permutations give the same construction for the other five
face families.

For a body stage choose $`a,b,c,d`$ in that order. The primary point
$`(a,a,a)`$ has at most $`J`$ occupied candidates, since other body
bundles and every face bundle avoid this body line. Check its
three determined axis lines. Next make $`(b,a,a)`$ free on one
fixed axis fiber and check its two new lines. Then make
$`(a,c,a),(b,c,a)`$ free on two fixed fibers and check their three
new lines. Finally make the four points with third coordinate
$`d`$ free on four fixed vertical fibers and check the four new
horizontal lines. The reflected body constructions are identical
after a coordinate bijection.

At every choice, occupied-cell exclusions are at most $`4M`$,
since $`2(\Delta J+4)\le M`$ when a nonempty pass is being placed.
The orbit exclusions are at most $`M`$ under the same condition.
Together with (6) they exclude fewer than $`5M+n/128\lt n`$ values
by (5). Every choice is therefore possible. All determined
axis lines are checked before their load increases, so their
caps hold. The generic support descriptions give the
pass-specific face and body bounds. This proves the lemma.

The lemma is a finite sufficient condition with explicit constants.
For the application, $`J=O(P+K_3+g)=o(n)`$; hence (5) holds for every
sufficiently large odd $`n`$. For residue repair the six family
graphs may include an additional path. Their union with the
capacity graphs has maximum degree at most $`64+2`$. Prefix, macro,
and residue passes then have respective axis-line load
$`O(P)`$, $`O(K_3)`$, and $`O(g)`$. The choice of a large absolute cap
only changes the eventual threshold.

## 5. Random references, body drift, and the final correction interface

### What the new orientation choices can change

Every stage is axis neutral. Thus changing any subset of stages,
including switching a whole bundle to its complementary midpoint
reference, changes no axis sum at all. This is stronger than a
bound on the variance of the new orientation choices.

For a face bundle, its only nonaxis changes are opposite changes
on its two native face lines. Complementary midpoint references
differ by at most $`g`$ on each of those lines. A body bundle has the
same width bound on its native body line. On every face line it
has at most one cell, so the difference between arbitrary states
is at most $`X`$, including the prefix and residue stages when
those are present. Other body lines are unchanged.

The fair complementary choice gives each macro cell the midpoint
of its own actual pair as expectation, within $`\delta X`$ of $`m`$.
It makes no such assertion about the prefix or residue pairs.
With the packing bounds, the macro contribution to mean
displacement of any full signed line is $`O(\delta K_3X)`$, and
prefix/residue contributions cost $`O((P+g)X)`$. In the chosen scale,



```math
\delta K_3=n^{29/50}+O(n^{-1/5})=o(n^{3/5}).
```



The exact constants, remaining-pool mean, random completion, and
old-controller drift are obligations of the full composition,
where the new reserves are included before balancing the pool.

### Correction after the axis sums have been fixed

Assume the new bundles have been embedded and filled as above,
and a current exact-pool array has the desired axis sums. Each
main bundle is still in one of its two midpoint reference states;
all intervening corrections have disjoint support from its cells.
Assume every current signed sum is congruent to its target
modulo the common even gap $`g`$. Assume each of the four body
errors is within $`3K_3X`$, each face error is $`o(K_3X)`$ uniformly,
and the desired face-family totals agree with the fixed axis
sums.

First correct each body error with its own signed scalar bundle.
These moves preserve all axes and the other bodies. They change
any face sum by at most $`4X`$ in total, so each remaining face
error is still $`o(K_3X)`$. It is still divisible by $`g`$, and its
total in each family is zero.

For each family use the bounded-degree capacity graph with cut
expansion at least $`8\min(|S|,n-|S|)`$. Every edge bundle supplies
all multiples of $`g`$ in $`[-3K_3X,3K_3X]`$. Integral max flow
therefore realizes the family demand once its largest coordinate
is at most $`16K_3X`$. Indeed use the attainable edge capacity
$`C_*=g\lfloor3K_3X/g\rfloor\ge2K_3X`$ eventually. Every cut
demand is at most $`16K_3X`$ times the smaller side, while the
available cut capacity is at least that amount. The actual
errors are smaller eventually. Dividing both demand and
capacity by $`g`$ gives an ordinary integral max-flow problem;
the displayed floor handles the grid boundary explicitly.

Use the attained edge coefficients to select stage subsets in
the corresponding face bundles. Their disjoint supports preserve
all axes, every body, and the other five face families. At the
end all signed targets have been attained using exactly the
prescribed entries.

This is a physical consumption of bounded integer corrections.
The full target compatibility, residue schedule, and old-stage
error bounds are not hypotheses that the desired prime
arrangement already exists; they are separately checkable
interfaces, proved in the incidence and full-composition
manuscripts. In particular this interface alone is not the
eventual prime theorem.

[Back to the four-manuscript index](../README.md).
