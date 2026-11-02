# Reserve the delicate gadgets first, then use all reduced classes

The improvement removes the assumption that every wide pair must use the
same lower-endpoint class as the seed pairs. All small-prefix and residue
gadgets are reserved first. Later wide pairs may use any reduced class,
with the same class at both endpoints of an individual pair. A single
aggregate budget charges every used entry exactly once. Classes are not
assumed to have independent supplies after adaptive deletions.

## 1. The aggregate stock lemma

Let g be even, and let two disjoint intervals inside (1,X) have at least
W available pool primes in every reduced class modulo g before reservations.
After at most B total pool entries have been reserved, let L_r and H_r be
the numbers of still-unused primes in the lower and upper intervals in class r.
Put


```math
S=\sum_{r\in(\mathbb Z/g\mathbb Z)^\times}\min(L_r,H_r).
```


If l_r and h_r count the deleted primes in the two stocks, then
$`\min(L_r,H_r)\ge W-l_r-h_r`$, including when the right side is
negative. Since the intervals are disjoint and the classes partition their
reduced primes, $`\sum_r(l_r+h_r)\le B`$. Hence


```math
S\ge\varphi(g)W-B.                               \qquad\text{(AC1)}
```


This bound remains valid when deletions are adversarial, concentrated in a
single class, or chosen adaptively from earlier selections.
The number of same-class lower--upper pairs is


```math
\sum_r L_rH_r\ge\sum_r\min(L_r,H_r)^2
 \ge S^2/\varphi(g).                              \qquad\text{(AC2)}
```


If S squared exceeds X, this is greater than X/g. Every such pair has a
positive difference divisible by g and less than X. There are at most
floor(X/g) possible differences. Consequently two distinct pairs have the
same difference. They are vertex-disjoint: a fixed lower endpoint and
difference determine the upper endpoint, and a lower endpoint cannot equal
an upper endpoint because the intervals are disjoint.

The bound by floor(X/g) is explicit. Merely claiming more than X/g pairs
while bounding the number of differences by ceil(X/g) would leave a
rounding gap. One could instead use phi(g) at most g/2, but this proof
does not need that extra factor for the pigeonhole step.

## 2. A phase-aware finite controller theorem

Use FC's exact pool, even g, reduced seed class a, positive integers K,M,H,
and rational 0 less than delta less than 1/24. Use its exact definitions of
s, P, L, J, I minus and I plus. Define


```math
\begin{split}
 B_0&=(128n+8)P+4(n+1)(g/2-1),\\
 B&=B_0+(128n+8)7K.
 \end{split}                                      \qquad\text{(AC3)}
```


B0 counts every seed, every growth-prefix entry, and every ordinary and
diagonal residue gadget. B is the original total reservation cap.
Assume:

1. The exact pool has at least (64n+4)s disjoint gap-g seed pairs, with
   lower endpoint in class a.
2. It has at least B0+M primes in class a.
3. Each macro interval has at least W primes in **every** reduced class
   modulo g, where $`W\ge B_0+H`$.
4. $`S_0:=\varphi(g)W-B\gt 0`$` and `$`S_0^2\gt X`$.

Keep FC's finite inequalities, including


```math
\begin{gathered}
 X\ge g,\quad I_-\cup I_+\subset(1,X),\quad sg\le X,
 \quad gM\le16X,\\
 M^2g\ge48X,\quad H^2\gt \lceil X/g\rceil,\quad 2B\le n^2,\\
 n\gt 4J,\quad n\gt 4L+8,\quad KX\ge2g,\\
 6000\delta K+576P+10g+82+3\sqrt{n\log n}\lt K/10.
\end{gathered}                                      \qquad\text{(AC4)}
```


**Theorem AFC.** Under these assumptions, FC's entire conclusion holds:
there is a baseline permutation of exactly the prescribed pool, all required
line sums are units modulo g and within KX/10 of y, and every compatible
integer target vector within KX/2 of that baseline is realized. Row and
column target totals both equal the actual T. Both diagonal targets remain
independent. No input entry is repeated or omitted.

### Phase one: finish every class-specific gadget

First reserve all seed pairs, exactly as in FC. Complete the growth prefix
of **every** ordinary and diagonal main reservoir, stopping when its total
difference first reaches X. Only the global seed class a is used in these
prefixes. At every selection at most B0 entries have been reserved, so the
raw global assumption leaves at least M unreserved primes in that class.
FC's prefix counting proof and all its double-pair requirements apply.
Every completed prefix has total difference between X and 2X, and uses at
most P stages, including its seeds.

Next reserve every residue-path pair and every residue rectangle on both
diagonals. They use lower class -1 and upper class +1, with difference
2 modulo g. At least H primes remain in each needed interval/class,
because all reservations in this phase fit B0 and W is at least B0+H.
The unchanged H-squared pigeonhole proof supplies the diagonal residue
double pairs. When g=2 those residue families are empty.

No wide main-reservoir stage has yet occurred. All class-specific gadgets
are now fully reserved; their later orientations remain free. In particular,
the residue choices need not be determined before the final baseline is
known. The phase order concerns selection of prime entries, not premature
fixing of any line sum.

### Phase two: extend every main reservoir from the aggregate stocks

Each current reservoir radius R is at least X. Throughout this phase the
total number of entries reserved is at most B, including phase one and
every already completed wide stage. Apply (AC1)--(AC2) to the current
stocks. Since S is at least S0 and S0 squared exceeds X, a fresh double
pair of some positive common difference divisible by g always exists.
An ordinary stage needs only one of those pairs; a diagonal stage uses both.
Unused candidate pairs are not charged as reservations.

For any chosen pair from the two macro intervals,


```math
X/3\le d\le2X/3,\qquad
 |(p+(p+d))/2-m|\le\delta X.
```


Its lower class may differ from the seed class and from the lower class
of the next selected pair. The two pairs of a diagonal stage may also
have different lower classes. Their differences are equal and divisible
by g, which is all that the complete-grid and rectangle identities require.
Since d is at most R+g, each extension preserves every covered g-grid
increment. At most 7K stages per reservoir reach total difference 2KX,
as in FC. This gives exactly the total cap B in (AC3).

This proves the adaptive supply invariant without subtracting B separately
from every individual residue class. A whole class may be exhausted; the
aggregate stock still suffices. Prefixes and residue gadgets cannot be
damaged by later depletion because they were already reserved with disjoint
entries in phase one.

### Geometry, centering, and exact transfers

All reservoir and residue families have the same numbers of stages and
entries as in FC. Its degree-64 graphs, separate embedding passes, and
joint placement of all diagonal rectangles apply unchanged under (AC4).
All supports are disjoint; ordinary pairs avoid both diagonals.

The algebra only uses the fact that each main-pair difference is a multiple
of g. Orienting such a pair or a whole reservoir preserves its coordinate
residues. Changing the common lower class of different pairs changes the
reference sums, which are allowed to be arbitrary before the residue repair.
The path and rectangle residue gadgets realize the needed even corrections
for those actual reference sums, exactly as in FC. The zero-total row and
column constraints are still the actual pool total T.

FC's centering invoice uses uncontrolled-prefix entry counts, wide-pair
midpoints, midpoint rounding, residue counts, and disjoint supports. It
does not use a common lower class across different wide pairs. Every one of
those bounds remains valid, so its concentration argument supplies the
baseline radius in (AC4). Its integral flows and both diagonal trades then
realize the stated target box. Every operation permutes reserved entries,
and the completion places every unreserved pool entry. This proves AFC.

## 3. An evaluated quadratic-window specialization

Suppose the exact pool has


```math
n^2\le X\le n^3,\quad 2X/5\lt m\lt 3X/5,
 \qquad E\ge16384,\qquad n\ge E^{32}.
```


Use a gap 2 at most g at most E supplied by the smaller-gap theorem, and
take its unchanged weaker matching requirement floor(X/(2048 E cubed)).
Set


```math
A=64000,\quad\delta=1/A,\quad K=\lfloor n/E^2\rfloor,
 \quad D=y/e^2,\quad
 M=\left\lfloor\frac X{4E^2}\right\rfloor,
 \quad H=\left\lfloor\frac X{AE^2}\right\rfloor,
 \quad W=\frac X{A\varphi(g)E}.                   \qquad\text{(AC5)}
```


Require raw global count X/(2E squared) in the seed class and raw count W
in each macro interval in **every** reduced class. The strong analytic
interface gives the latter from length 2X/A and log(2Y) at most E.
Uniformity in every reduced class is now used materially. Analytic
availability at the actual scales remains an external composition obligation.

The [small-gap controller proof](cutoff_small_gap_controller.md) gives
M at least X/(8E squared), H at least X/(2A E squared),
s at most 24E squared, and P at most 160E cubed. Its seed and prefix
conditions are independent of K. The residue H-squared condition also
remains unchanged, since it is paid in phase one.

With $`Q(E)=(693E-2193)/1000`$, define


```math
\begin{split}
 U_0(E)&=\left(128+\frac8{E^{32}}\right)\frac{160}{E^{27}}
       +\frac2{E^{29}}\left(1+\frac1{E^{32}}\right),\\
 V(E)&=\left(128+\frac8{E^{32}}\right)
          \left(\frac{160}{E^{28}}+\frac7E\right)
       +\frac2{E^{30}}\left(1+\frac1{E^{32}}\right).
\end{split}
```


The prime-index logarithm gives the two different phase invoices


```math
\frac{E^2B_0}{X}\lt \frac{U_0(E)}{Q(E)}\le\frac1A,
 \qquad
 \frac{EB}{X}\lt \frac{V(E)}{Q(E)}\le\frac1{2A}.       \qquad\text{(AC6)}
```


Because phi(g) is at most E/2, W is at least 2X/(A E squared).
The first invoice leaves M globally and H in every phase-one residue
stock. The second gives


```math
S_0=\varphi(g)W-B\ge X/(2AE),\qquad S_0^2\gt X,
```


where the last inequality follows from X greater than 4A squared E squared,
itself implied by E to the power 62 greater than 4A squared. At E=16384,
V/Q is below 0.000004817467425551574144, against allowed
1/128000=0.0000078125. Separately B/n squared is at most V/E, less
than one half; no inference about occupancy is made from B/X alone.

For the enlarged K, the original placement comparisons become


```math
(4L+8)/n\le122892/E^{29}+5376/E^2\lt 1,
 \qquad4J/n\le1280/E^{29}+56/E^2+4/E^{31}\lt 1.
```


Since n/E squared is at least fifty,
$`K\ge(49/50)n/E^2`$. The full centering invoice divided by K is


```math
\frac{6000}{A}+
 \frac{576\cdot160}{(49/50)E^{27}}+
 \frac{92}{(49/50)E^{29}}+
 \frac3{(49/50)E^{13}}\lt \frac1{10}.                 \qquad\text{(AC7)}
```


It is below 0.093750000000000000000001 at the endpoint. The reservoir
range condition KX at least 2g follows from
$`(49/50)E^{93}\ge2`$. All remaining interval, floor, seed, and
double-pair conditions are included in the accompanying exact checker.

The already-proved pointwise ceiling coupling e greater than or equal to
5E/4, together with m less than 3X/5, yields


```math
\frac D{KX}
 \lt \frac{3/5}{49/50}\left(\frac45\right)^2
 =\frac{96}{245}\lt \frac25.
```


The strict baseline radius adds less than KX/10, so every target remains
inside AFC's KX/2 box. The optimized target size conditions for density
cost at most 4e squared follow from
$`(2/5)E^{90}\gt 2^{17}`$` and `$`E^{28}\gt 680\cdot16`$.
The target supply and exact-total lemmas are still required independently.

## 4. Infinite tail, controls, and limits

Every positive-power comparison persists with E. Every nonconstant term in
U0, V, the placement expressions, and the centering expression decreases,
and Q is positive and increasing. Floors are covered by pointwise lower
and upper bounds; every integer ceiling E above the endpoint is checked
through these envelopes. No differentiability of K is assumed.

[cutoff_all_class_controller.py](../PROVENANCE.md#optimized-bound)
passes 32 exact finite inequalities and five negative controls. The first
integer E passing the aggregate-depletion invoice is 12867; the clean
specialization uses 16384. These are sufficient proof thresholds, not
lower bounds on square existence. They must be composed with the actual
analytic and target scales to obtain an order cutoff.

The program exhausts 256 two-class deletion patterns and checks the
min-stock and Cauchy inequalities. Its separate actual-prime fixture uses
g=6, intervals [11000,19000] and [61000,69000], and X=100000. It first
deletes **all 411 lower primes in class 1 modulo 6**, so a per-class
remaining-supply assertion would fail. It then performs ten fresh
equal-difference double-pair stages using 40 distinct primes. The aggregate
paired stock decreases from 361 to 343, and remains above square root X
throughout. Every selected prime is independently trial-divided, both
pairs have the same g-multiple difference, and all midpoint and width
bounds are checked. This is a selection-lemma control, not a square
certificate or verification of this specialization's analytic hypotheses.

Executable replay details are recorded in [Provenance](../PROVENANCE.md#optimized-bound).

The exact required-source map binds FC, the prime-index improvement, and
the preserved small-gap prefix calculation. The full composition verifier
must additionally bind this new argument, the seed and target refinements,
the analytic sources, and the final theorem. No private uncommitted input
is needed for the stated finite checks. This conventional proof and its
finite controls are not a kernel verification of AFC or the analytic imports.

[Manuscript index](../README.md) · [Optimized theorem](../optimized-bound.md) · [Source and review record](../PROVENANCE.md#optimized-bound)
