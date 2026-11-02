# A degree-12 controller network and a cubic target window

This additive argument is separate from the
frozen four-file source at `4a117bf257a07f035af52fb6726dc0c9d52981b3`.
Its proposed conclusions need nonauthor review at their own exact revision.
It changes neither the original [FC theorem](../explicit-controller.md) nor
the [first controller optimization](cutoff_controller_optimization.md).

## G1. Smaller graph, with the actual required flow capacity

For every integer n at least two, six permutations of n vertices give an
undirected multigraph, retaining edge multiplicities and discarding loops, having
degree at most 12 and


```math
|\partial S|\ge\tfrac12\min(|S|,n-|S|).
                                                        \qquad\text{(G1)}
```


Choose six independent uniform permutations. For a fixed set of s at most
n/2 vertices put t=s/n. If fewer than s/4 directed edges leave it, more
than 23s/4 of the 6s images stay in it. Prescribing any k such images to
stay has probability at most t to the k: within each permutation the bound
is the usual falling-factorial ratio, and the permutations are independent.
Use k=ceil(23s/4), which is a weaker event when 23s/4 is integral.
The binomial entropy bound and t at most 1/2 bound the union over all sets by


```math
\sum_{s=1}^{\lfloor n/2\rfloor}r^s,
 \qquad r=\exp(1+6H(1/24))\,2^{-19/4}.
```


Rounding k upward only strengthens the power of t and decreases the entropy
bound, since k/(6s) is at least 23/24. Exactly


```math
r^4=\exp(4)\frac{24^{24}}{23^{23}2^{19}}
 <\left(\frac{11}{4}\right)^4
   \frac{24^{24}}{23^{23}2^{19}}<\frac1{16}.
                                                        \qquad\text{(G2)}
```


Here exp(1)<11/4 follows from j! at least 2 times 3 to the power j-2
for j at least two, with strictness for j at least four. The last comparison
is between explicit integers. Thus r<1/2 and the displayed geometric sum
is less than one, for every n including the small cases. Some tuple avoids
every bad set. Every permutation has equally many incoming and outgoing
crossing edges, so its undirected edge count is twice its outgoing count.
This proves (G1). A finite construction can enumerate permutation tuples
until every cut passes; the counting proof establishes termination.

The old expansion constant 8 is unnecessary for FC's stated transfer box.
Let C=floor(KX/g) and suppose each integral demand coordinate has absolute
value at most KX/(2g). Then


```math
|b_v|\le\lfloor KX/(2g)\rfloor
       =\lfloor C/2\rfloor\le C/2.
```


For every cut the sum of demands is bounded by C/2 times its smaller side,
which is at most C times its edge boundary by (G1). The same integral-flow
argument as FC therefore realizes the entire required zero-sum box with
edge capacity C. The floor identity is essential when C is odd; no real
capacity is silently substituted for an integer capacity.

## G2. A finite controller variant

Replace FC's two graphs by the G1 graphs. Each has at most 6n edges, so
the two ordinary networks together have at most 12n reservoirs. The exact
reservation cap becomes


```math
B_{12}=(24n+8)(P+7K)+4(n+1)(g/2-1).                \qquad\text{(G3)}
```


The two independent diagonal reservoirs and all residue repairs are unchanged.
Actual seed demand is at most (12n+4)s, so the old larger seed assumption
(64n+4)s remains sufficient. Reserve only the actual needed seeds.

There is a direct variant of FC with B replaced by B12 in the raw-supply
and occupancy hypotheses, and all other displayed FC hypotheses unchanged.
To justify it, follow FC's proof with the smaller actual reservoir count:

- Each later prime selection retains M or H after charging the entire B12.
  Prefix coverage, wide extension, and double-pair selection are unchanged.
- The graph replacement only reduces every ordinary placement degree and
  midpoint-rounding contribution. The original L, J, and centering bounds
  remain valid upper bounds. All rectangles are still placed jointly and
  all ordinary pairs avoid both diagonals.
- The old cut argument is replaced by the integer half-capacity argument
  above, which proves exactly the same target box. It does not assert the
  larger unused 8C demand box.
- Diagonal transfer capacity, reference orientations, residue paths, and
  completion using every remaining entry are unchanged.

This is a new conventional finite implication proved by the specified changes
to FC, not a claim that the literal original FC statement uses B12.

## G3. Coupled cubic target specialization

Take the index/mean assumptions of the earlier optimization,
E at least 32768, n at least E to the power 32, and the original seed and
raw global supplies. Set


```math
\delta=1/64000,\quad K=\lfloor n/E^3\rfloor,
 \quad H=\lfloor X/(4096000E^2)\rfloor,
 \quad D=y/e^3.                                    \qquad\text{(G4)}
```


Each macro interval/class requires raw supply X/(2048000E squared).
M and P remain as in the earlier optimization. With its notation Q(E),
the scaled reservation envelope now is


```math
\frac{E^2B_{12}}X<\frac{U_{12}(E)}{Q(E)},\qquad
 U_{12}(E)=\left(24+\frac8{E^{32}}\right)
 \left(\frac{5120}{E^{27}}+\frac7E\right)
 +\frac{32}{E^{29}}\left(1+\frac1{E^{32}}\right).
```


At E=32768 this is below 0.000000225796975481976573, while the
allowed value is 1/4096000, approximately 0.00000024414. Every nonconstant
term decreases with E; Q is positive and increasing. A separate B12/n
squared check leaves at least half the exact pool. The original conservative
placement and centering bounds also pass, with main centering term .09375.

The larger target window uses a coupling which the old independent envelopes
discarded. From X at most n cubed, log base 2 of X greater than E-1,
and y greater than (2/5)nX, one obtains


```math
e>\frac43E-\frac{10}{3}\ge\frac54E\quad(E\ge40).
                                                        \qquad\text{(G5)}
```


Since n/E cubed is at least five, the floor K retains four fifths of
n/E cubed. Consequently


```math
\frac D{KX}<\frac{3/5}{4/5}\left(\frac45\right)^3
 =\frac{48}{125}=0.384.
```


Adding FC's strict baseline radius 0.1 KX still gives less than 0.5 KX.
The K parameter is therefore unchanged even though the target radius changed
from fourth to third power. Target prime supply and exact-total construction
remain separate inputs. The optimized target size requirements follow from
n at least E to the power 32 and e at most 2E; they are checked explicitly.

The standalone program
[cutoff_graph_experiment.py](../PROVENANCE.md#optimized-bound) passes 33
exact finite comparisons, 8166 all-cut checks in deterministic constructed
multigraph controls at orders 2 through 12, 4419 rational floor-identity
controls, and five intended negative controls. Repeating a single cycle six
times fails the required cut condition at n=64, and is retained as a negative
control; bounded degree alone does not imply the routing result.

The first integer E satisfying this depletion invoice is 31514. This is a
sufficient-estimate threshold, not a mathematical obstruction below it.
Every ceiling and floor is handled pointwise as in the earlier optimization,
so evaluating the decreasing envelopes covers the whole integer E tail.

## Net role

The graph change reduces the leading ordinary reservation coefficient from
128 to 24 and supports the full row/column transfer box, while preserving
diagonal independence and the exact permutation of entries. It can lower a
cutoff only when controller depletion is active.

[Manuscript index](../README.md) · [Optimized theorem](../optimized-bound.md) · [Source and review record](../PROVENANCE.md#optimized-bound)
