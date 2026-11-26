# The exact number of six-vertex paths in $P_8$-free graphs

*Mira Cult*

Write $P_j$ for the path on $j$ **vertices**. A copy is an injective
edge-preserving path sequence up to reversal, and need not be induced.
Likewise $P_8$ is forbidden as a subgraph, not merely as an induced subgraph.
For every integer $n\ge1$,

```math
\mathrm{ex}(n,P_6,P_8)=
\begin{cases}
0 & n<6,\\
360 & n=6,\\
2520 & 7\le n\le10,\\
12(n-3)(n-4)(n-5) & n\ge11.
\end{cases}
```

For $n<6$ every graph attains the bound. For $n=6,7$ the unique maximizer
is the complete graph. For $n=8,9$ the extremal graphs are exactly the
disjoint union of $K_7$ and an arbitrary graph on the remaining vertices.
At $n=10$ the only maximizers are that family and the join $K_3\vee \overline K_7$. For $n\ge11$ the unique extremal graph, up to isomorphism, is
$K_3\vee \overline K_{n-3}$: the three clique vertices are adjacent to
every independent-set vertex.

[Gerbner and Palmer, §6, p. 47](https://www.combinatorics.org/ojs/index.php/eljc/article/download/ds27/pdf/)
identify this pair as the first open exact case for paths in their survey.
The earlier general estimates and path-join constructions are due to
[Győri, Salia, Tompkins and Zamora](https://arxiv.org/abs/1803.03240v5);
their path indices count **edges**, so this pair is $P_5,P_7$ in that paper.
Their asymptotic equivalence in §2 takes the forbidden length to infinity
after the order of the graph, and does not give the fixed-$P_8$ coefficient.
The proof here is combinatorial at every order; the included graph census is
an independent finite check, not a premise.

It suffices first to prove for connected n≥8 the upper envelope:
strictly less than 2520 at n=8,9, and at most F(n) for n≥10,
with equality for n≥10 only at the join. We do this by circumference. Set $F(n)=12(n-3)(n-4)(n-5)$, and write $(a)_j=a(a-1)\cdots(a-j+1)$ for a falling factorial.

## A literal six-cycle

If connected n≥8, there is no C₇ (append an outside neighbor
to a traversed C₇) or longer cycle. Fix a C₆. The outside vertices
are independent and all have a cycle neighbor: a two-vertex
arm y–x–a into the cycle extends over all six cycle sites to P₈.
In particular anything at distance≥2 is impossible, as is any
outside edge.

The UNION U of all outsider neighborhoods in the cycle contains
no cyclically adjacent pair a,b. If hit by the same outsider,
replace ab by its length-two route to produce a C₇; if hit by
different outsiders, even the cycle path obtained by deleting
ab extends at both ends to P₈. So |U|≤3. If |U|=3 call the
alternating sites a1,a2,a3, the others b1,b2,b3, where b1 links
a1,a2, b2 links a2,a3, b3 links a3,a1. Any edge b1b2 is
impossible: take distinct outsiders x,y attached respectively
to a2 and one of a1,a3. They exist because |U|=3 and there are
at least two outsiders (if a single x supplies both kinds, use
the other outsider's neighbor and take x for the opposite kind).
If y touches a1 use x–a2–b1–b2–a3–b3–a1–y; the other case is
its symmetric orientation. Rotating labels excludes every edge
inside B. Thus the entire graph is a subgraph of K₃ joined to
an independent set. That join has longest path 7 and exactly
F(n) P₆: choose three hubs and three nonhubs, four admissible
nonadjacent placements of the latter, 3! orders and (n−3)_3
orders, divided by two.

If |U|≤2, dominate by K₆ with r=n−6 independent outsiders, all
adjacent to the same two core hubs. No P₆ can use three outsiders:
with three outsiders and three core sites every core site in the
path is adjacent along that path to an outsider, requiring three
distinct hubs. Counts for at most two outsiders are
    360 + 336r + 72 binom(r,2).
Zero outsiders: 360. One fixed outsider: as endpoint 2(5)_4=240;
internal it uses both hubs, then four possible internal positions
give 4·2·(4)_3/2=96. Two fixed outsiders: both endpoint gives
2(4)_2=24 counting each path in the direction of one chosen
outsider. If one is internal and one an endpoint, they must share
the first hub, so the internal outsider is at position three
from the chosen endpoint, giving 2·2·(4)_2=48. Both internal
are impossible: the two required hub pairs cannot use only
two distinct core sites in a simple path. The displayed count
is below 2520 at n8,9, and below F(n) for all n≥10 (at $r=4$ the bound is 2136, and the gap $12r^3+36r^2-168r-288$ is increasing for $r\ge4$).

## Circumference five

Fix a literal C₅ and put r=n−5. No three outside vertices may be
an arm into the cycle, because traversing all five cycle vertices
would then make P₈. In any outside connected component choose
an attaching vertex u. No length-two outside path starts at u.
Therefore all other vertices are its neighbors and there are no
edges among them: the component is a star. For a star of order
at least three, its center is the only vertex allowed to attach
to the cycle (otherwise a leaf-center-other-leaf route extends).
In a two-site component with both sites attaching, they must
both attach only to the same core site: different core sites
give a length-three ear whose union with the longer C₅ arc is
a C₆ or C₇. Each outside vertex attaches to at most two core
sites, since consecutive neighbors create a C₆ and an independent
set of C₅ has size two.

Every P₆ hits the cycle (outside components are stars). Its
maximal outside runs have length one or two in vertices. A doubled
run cannot be internal: that would require its two ends attach
to two different core vertices. Every outside endpoint uniquely
determines at most one oriented doubled arm going toward the core:
its successor must be the unique attachable center, or the other
site of its two-site component. In particular at most r such arms.
Count using at most three outside runs as follows (all core adjacency
restrictions may be dropped except those to outside vertices).

* One singleton run: all five core sites used; endpoint ≤2·4!=48
  for a given outside site, and internal ≤4·2·3!/2=24. One doubled
  run (necessarily endpoint): choose at most 2 first core sites
  and then (4)_3 remaining sites, hence ≤48 per rooted arm. Combined
  these cost ≤120r.
* Two singleton runs: for each unordered pair, if both are endpoints,
  ≤4·(3)_2=24. If one is an endpoint, normalize direction to start
  there, and choose which outsider (2 ways). The other outsider
  at position 3,4,5 gives respectively ≤12,8,8 choices: at pos3
  its ordered pair of hubs (≤2) fixes the first core site and
  allows ≤(3)_2 remaining choices; at pos4 or5 the endpoint's
  neighbor has ≤2 choices and the remaining core site ≤2.
  Hence ≤56. If both are internal, possible position pairs are
  (2,4),(2,5),(3,5). Shared middle-neighbor cases (2,4),(3,5)
  each give ≤2 for a fixed placement of the outsider labels:
  their two actual neighbor sets must meet in exactly one site,
  or else the other two core sites would repeat or not exist;
  there are ≤2 choices for the one remaining core site. Case
  (2,5) uses both ordered neighbor pairs (≤4). The two label
  placements cancel reversal, giving ≤8. Thus ≤88 binom(r,2).
* One double plus one singleton: normalize direction to start with
  the doubled arm. The singleton can be in positions 4,5,6.
  At pos4 its ordered neighbor pair (≤2) fixes the first two
  chosen core sites and leaves ≤3 choices; at pos5 the ordered
  pair (≤2) leaves ≤2 choices at the arm's core attachment;
  at pos6 the two end attachment choices are ≤2 each and the
  middle core site ≤3. Total ≤6+4+12=22 for a specified arm and
  singleton. There are ≤r(r−2) such choices, since the singleton
  is different from BOTH outside arm sites.
* Two doubled arms: both endpoints, with two core sites in between
  chosen in at most 4 ways for a specified direction. Unordered
  distinct arm choices give ≤2r².
* Three singleton runs: three core sites remain. Of the four
  directed no-adjacency patterns, the two alternating patterns
  allow ≤2 core choices per ordered outsider triple (middle
  outsider fixes its ordered two distinct neighbors, the last
  degree-two outsider then has ≤1 fresh neighbor). The other
  two patterns allow ≤4 each (the middle outsider fixes two
  ordered neighbors, a remaining neighbor choice is at most two).
  Divide reversal: ≤6(r)_3. One double and two singles:
  normalize the double first; the middle singleton specifies
  the two ordered distinct core neighbors (≤2 choices). Choose
  the distal endpoint of the arm and the two singleton sites
  in order, ≤(r)_3 possibilities, since that endpoint uniquely
  determines its other arm site. Cost ≤2(r)_3. Any other
  three-run split is too long.

Totals give
   8(r)_3 +44r(r−1)+22r(r−2)+2r²+120r
   =8r³+44r²+48r.
This is <2520 for r=3,4 (n8,9). For r≥5 subtract from
F(r+5)=12r(r+1)(r+2); the difference is 4r(r²−2r−6)>0.

## Circumference at most four

A *big block* means a 2-connected block on at least five sites.
Every big block is K_{2,t} (t≥3) possibly with the edge between
its hubs. Here is a justification not relying on a classification
theorem. Such a block has a C₄: if it had only triangles, a
triangle with extra sites has an outside connected component
attaching to at least two triangle vertices by 2-connectivity;
an ear between them of length≥2 closes against the longer triangle
arc to make a cycle of length≥4. Now fix C₄. No outside component
of order ≥2 is possible inside the block. Its attachment edges
to the C₄ cannot form a single star: if centered at a C₄ vertex
that vertex separates the component; if centered at an outside
vertex it separates all other sites of that component. Thus
two attachment edges have distinct endpoints on both shores,
and their outside endpoints can be joined inside the component
to produce an ear with ≥2 outside sites. With the longer C₄ arc
this creates a cycle of length≥5. Consequently each outside
site is independent off the C₄ and attaches to an opposite
pair there (at least two neighbors by 2-connectivity; an
adjacent pair makes C₅). Different opposite pairs from two
outsiders create a C₆. So all outsiders use the same opposite
hub pair. An edge between the two remaining original cycle
sites creates C₅ using any outsider. This proves the form.

For small-block graphs (all blocks have order ≤4), a simple
path between fixed endpoints traverses the unique block chain,
with fixed entry/exit sites in each block. In a block the ways
for lengths 1,2,3 are at most 1,2,2 respectively (K₄ bounds),
and larger lengths fail. For a fixed endpoint pair and total
length five, the largest coefficient $`[x^5](x+2x^2+2x^3)^b`$
over all possible chain lengths b is 18 (b=3; b=1,2,4,5
give 0,8,8,1). Similarly length 2 gives at most 2 fixed
endpoint choices and length 3 at most 4. No big block
therefore gives ≤9n(n−1) P₆.

### Exactly one big block

Write it as hubs u,v and t leaves. Every component outside
the block attaches to one unique block site (block-cut tree).
Let e_x count all external sites in branches attached to x,
E_H=e_u+e_v, E_L the sum at leaf sites, and E=E_H+E_L.
For a fixed external endpoint, an arm of length 1,2,3
into its attachment site has ≤1,2,4 choices by the small
block estimate.

Fixed-endpoint paths which do not use a freely chosen inner
leaf in the big block obey the same ≤18 bound: inside that
block the remaining local fixed-endpoint possibilities are
at most 1,2,2 for lengths 1,2,3 and zero longer. A path
never leaves and reenters a block along a different site
because that would contradict the block-cut tree. We count
the remaining free-inner-leaf paths by their two distinct
entry sites in the big block (a path using one site of the
block is already counted).
- Hub/hub: interior length2 via one free leaf (≤t ways).
  Outer arm lengths sum3. Splits 1+2 and 2+1 cost ≤4t e_u e_v;
  splits 0+3 and 3+0 cost ≤4t E_H.
- Hub/leaf: interior length3 via one free leaf (≤t).
  Outer sum2, cases hub 2/leaf 0, both 1, hub 0/leaf 2 give
  respectively ≤2t² E_H, t E_H E_L, 4t E_L after summing
  over possible hubs and leaf sites.
- Leaf/leaf: interior length4 via one free leaf and either
  hub order (≤2t), outer sum1. The total ≤2t² E_L.

These counts orient only by the prescribed first attachment
when needed: for two distinct fixed entry sites, choose one to
define direction, then count the outer arm length splits.
Thus the free-leaf terms total at most
   t E_H E +2t² E +4t E
   ≤ tE(E+2t)+4tE ≤ n³/2+n².
The entire count is ≤n³/2+10n².

### At least two big blocks

Any two big blocks must share a common hub. If disjoint,
concatenate rooted three-edge arms inside them (always
possible from any attachment site) with the connecting
path, giving P₈. If sharing at a leaf in either, that
block has a rooted four-edge arm (t≥3) and the other has
a three-edge arm, again P₈. Pairwise intersection of the
big blocks must now be at one common cut site z, because
different intersections would create a cycle in the block-cut tree.
In the branch of one of these blocks, no other blocks may
attach at a non-z leaf: a rooted z arm of length3 can end
at any such leaf, and extension by one more site plus the
three-arm in another big block gives P₈. At its other
hub, any external arm of length≥2 similarly extends
a length2 rooted z arm and is forbidden. Hence each such
branch consists of K₂,ₜ with only possible pendant edges
at its other hub.

Let B be the total non-z sites in these big branches and
S=n−1−B the sites of the other (small-block) branches.
No rooted z arm can have length≥4, since it could be
combined with a three-arm in a different big branch.
Thus a P₆ through z uses rooted lengths two and three
into distinct branches. The number of two-arms is ≤2(n−1):
big branch with t leaves and L pendant sites has at
most 2t+L, and a small branch contributes at most two
per possible endpoint by the fixed-endpoint bound.
The number of three-arms is ≤B²+4S: a big branch
contributes t(t−1+L), bounded by the square of its
total sites, and a small branch ≤4 per endpoint.
A P₆ avoiding z cannot be in a big branch (there it
is a star), and costs ≤9S(S−1) elsewhere. Total
   ≤2(n−1)(B²+4S)+9S(S−1).
As a function of B with S=n−1−B this is convex.
At its endpoints B=n−1 and B=0 the values are
2(n−1)^3 and 8(n−1)^2+9(n−1)(n−2); for n≥10
the former dominates. At n8,9 both endpoint values
are below 2520.

The no-big and one-big bounds are also below 2520 at
n8,9. For n≥10 all three upper bounds are strictly less
than F(n): check n=10, then F(n)/n³ is increasing while
the first two bounds divided by n³ are decreasing, and
F(n)/(n−1)^3 is increasing for the multi-big bound.
This finishes the connected envelope.

## Finishing the exact maximum and equality

For $n\le 7$ the complete graph is allowed and maximizes every subgraph count. Its $P_6$ count is 0 below 6, 360 at 6 and 2520 at 7. At orders 6 and 7 every edge of the clique lies in a $P_6$, so omitting any edge strictly decreases the count. For n8,9,10 there cannot be two nonzero
components (each needs six sites); only order-seven
components, or the connected join at n=10, attain 2520.
An order-seven component attaining 2520 must be full
K₇, because every edge of that clique lies in a P₆.

For n≥11, put n_i for component orders. Each component
of size at most ten costs at most 360 n_i: the largest
ratio is 2520/7=360 (connected n8,9,10 obey our bounds
and at n10 F(10)=2520). Every larger component costs
≤F(n_i). The ratio F(m)/m is strictly increasing for
m≥11 and F(11)/11>360. Thus a proper component of
an n≥11 graph has strictly smaller per-site contribution
than F(n)/n; summing proves disconnected strictness.
A connected optimum must be the join itself: every
allowed join edge is used by some P₆, and any missing
edge strictly loses one. This proves the all-n formula
and the asserted equality cases.


## Finite checks

The proof above is independent of either checker. To replay the path-position
ceilings and the optional exact graph census, run from this directory:

```sh
python3 replay/check_p6_in_p8_free_exact_0233_counts.py
g++ -std=c++17 -O3 -Wall -Wextra replay/p6-p8-finite-enumeration.cpp -o /tmp/p6p8
/tmp/p6p8 14
```

The C++ checker starts with a single vertex. It builds connected graphs by
adding a vertex with at least one neighbor. This is exhaustive because
deleting a leaf of any spanning tree leaves a connected subgraph, and the
forbidden-path condition passes to that subgraph. It tests for a forbidden
eight-vertex path through the new vertex by combining disjoint rooted
path supports. Color refinement and exhaustive individualization give
canonical keys. A subset recurrence counts simple oriented paths and divides
by two for reversal; a partition recurrence handles disconnected graphs.
The census is optional corroboration only.

## Acknowledgment

Mira’s dots, using OpenAI’s GPT Astra models, assisted with the mathematical investigation, proof preparation, and checking under Mira’s direction.
