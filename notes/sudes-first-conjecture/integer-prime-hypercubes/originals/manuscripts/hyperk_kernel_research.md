# Pure selectors, local kernel projectors, and the distributed obstruction

Author: `/root/kernel_architecture`. This supplementary investigation is
separate from the first frozen all-dimension scientific source. It proves
the local constructions below and preserves explicit failures of attempted
global assembly. It does **not** claim the full signed-line physical
controller. Labels are manuscript-local; no permanent claim ID is allocated.

The setting and full integer map are those of
[the general incidence manuscript](hyperk_incidence.md). Write `K_d` for
the common kernel of all full signed-coordinate line contractions on
integer arrays on a sufficiently large centered odd alphabet. A physical
template has entries in `{-1,0,1}` and zero axis sums, so its positive and
negative cells can be paired along any chosen coordinate. A matching of
fresh equal-gap prime pairs then realizes its scalar multiple by actual
swaps. Support and load must still be paid across different templates.

## 1. A recursive pure signed-line selector

**Lemma PS(b).** For every integer `b>=2` there is a finite integer tensor
`Q_b`, supported on positive labels, with the following properties:

1. Every entry is `0,+1,-1`.
2. Its contraction on the full all-positive body is one.
3. Every proper signed-line contraction is identically zero, and every
   other full signed body has contraction zero.
4. Its support is a disjoint union of products of previously constructed
   selectors and two-point differences. In particular it can be paired
   along **each** coordinate, using half as many pairs as support cells.

Any injection of its finite positive alphabet into noncentral reflection
orbits preserves these statements. Reflecting whole coordinates gives a
pure selector for any normalized signed body.

### Construction and proof

Put `B=[b]`. Choose distinct positive labels `a,b_1,...,b_b` and set

`U_B = tensor_(i in B) (e_a-e_(b_i))`.

For each proper subset `C` of `B` with `|C|>=2`, take an inductively
constructed copy `Q_C` on the coordinates `C`. Its entire alphabet is
disjoint from that of `U_B` and from the entire alphabet of every other
`Q_D`. These are copies indexed by **subsets**, not independent copies
chosen anew in each term of the following formula.

Let `Pi_<B` be the collections of pairwise disjoint such proper subsets,
including the empty collection. Define

```
Q_B = sum_(pi in Pi_<B) (-1)^|pi|
       (tensor_(C in pi) Q_C)
       tensor (tensor_(i outside union(pi)) (e_a-e_(b_i))).       (PS1)
```

The coordinate factors are placed in their original positions. For `b=2`
the sum contains only its empty term, so this starts the induction.

Fix a proper all-positive varying block `D`, with `|D|>=2`.
For any term of (PS1), one of the following holds:

- `D` is disjoint from every block of `pi`. Its contraction is paired with
  the term indexed by `pi union {D}`. The original two-point factors have
  contraction one on `D`, and `Q_D` has contraction one, so the two results
  cancel with opposite signs.
- `D` equals a block in `pi`. This is the reverse member of that pair.
- `D` is properly contained in a block `C` of `pi`. Its contraction
  vanishes by the inductive purity of `Q_C`.
- `D` meets two different alphabet groups, including the original factors
  as one group. Those alphabets are disjoint, so a common parameter cannot
  occur and the contraction is zero.

These cases exhaust the possibilities. Axis sums vanish because every
factor has zero axis sums. A mixed-sign line cannot meet positive support:
its varying coordinates would have opposite signs, whereas all coordinates
in a support cell are positive. For the full all-positive body, every
nonempty `pi` crosses two alphabet groups, and therefore contributes zero;
only `U_B` remains, with body contraction one.

Different terms of (PS1) have disjoint supports. Indeed distinct collections
assign some coordinate to different alphabet groups. This remains true
when their unions agree but their block partitions differ. Every tensor
factor has entries `+1` or `-1`, so every nonzero entry of `Q_B` has that
property. For any coordinate, each fixed complementary fiber has equally
many positive and negative entries because its axis sum is zero. Pair
them in that fiber. These pairs are cell-disjoint and exhaust the support.
Assigning one equal-gap prime pair to each gives the claimed physical
switch. This proves PS(b) by induction.

### Finite dependence on dimension

Let `a_b` be the number of positive labels and `s_b` the support size in
this construction. Deliberately keeping all subset alphabets separate gives

```
a_b = b+1 + sum_(c=2)^(b-1) binom(b,c) a_c,
s_b = sum_(pi in Pi_<B) 2^(b-|union(pi)|) product_(C in pi) s_|C|. (PS2)
```

Both are finite recurrences in `b`; neither depends on the ambient order.
The first diagnostic values are:

| b | positive labels a_b | support cells s_b | equal-gap pairs |
|---:|---:|---:|---:|
| 2 | 3 | 4 | 2 |
| 3 | 13 | 32 | 16 |
| 4 | 75 | 416 | 208 |
| 5 | 541 | 7,552 | 3,776 |
| 6 | 4,683 | 176,128 | 88,064 |

These are construction costs, not optimized minima. The finite supply
constant in a physical theorem would have to include them. This lemma is
stronger locally than a generic cuboid: all proper signed families are
preserved exactly. It does not construct arbitrary target arrays.

## 2. An exact local projector with disjoint physical support

Let

`R = tensor_(i=1)^d (e_(u_i)-e_(v_i))`, with `u_i != v_i`.

The endpoints may include zero, opposite labels, or repeated labels in
different coordinates. For a signed block `H=(B,sigma)`, `|B|>=2`, a
**witness** is a parameter `t` for which

`epsilon_(H,t) = product_(i in B) (e_(u_i)-e_(v_i))(sigma_i t)`

is nonzero. There are at most two witnesses, each of sign `+1` or `-1`.
Their sum is the ordinary contraction scalar `beta_H(R)`, which can be
zero or have magnitude two; no false unit-coefficient assumption is made.

For each witness choose a reflected copy `Q_(H,t)` of PS(|B|), using its
own noncentral orbit alphabet. All these alphabets are disjoint from one
another and from every endpoint orbit of `R`. Put

`Qtilde_H = sum_t epsilon_(H,t) Q_(H,t)`.

Its native contraction is `beta_H(R)`, all other contractions within its
coordinate block are zero, and its copies have disjoint support. Use the
**same** `Qtilde_H` wherever `H` occurs below. For all collections `pi` of
pairwise disjoint signed blocks of size at least two, define

```
P_R R = sum_pi (-1)^|pi|
          (tensor_(H in pi) Qtilde_H)
          tensor (tensor_(i outside union(pi)) (e_(u_i)-e_(v_i))). (LP1)
```

**Lemma LP(d).** The tensor (LP1) belongs to `K_d`. After expanding the
signed witness sums, all its nonzero entries are `+1` or `-1`, its component
supports are disjoint, and it can be paired along every coordinate.
Its alphabet, support size, and number of pairs are bounded by constants
depending only on `d`.

**Proof.** The cancellation in PS(b) applies verbatim to any tested signed
block `D`. Terms whose block collection is disjoint from `D` contract on
the original factors by `beta_D(R)`, and pair with terms containing `D`,
whose selector has the same contraction. Terms with `D` properly inside
a selector vanish by purity; terms crossing alphabet groups vanish by
orbit disjointness. Every nonempty tested block is allowed in (LP1), so
there is no surviving full-body exception. Axes vanish as before.

After expanding each `Qtilde_H`, distinct decorated collections use
different alphabet groups in some coordinate, including different witnesses
of the same block. Therefore their supports are disjoint. Their signs are
products of signs, so no entry has magnitude two. Zero axis sums give the
physical pairing exactly as in PS(b). The number of signed blocks, witnesses,
collections, and pure-selector cells is finite for fixed `d`. QED.

Merely duplicating a coefficient-two selector separately in each partition
term would not justify the cancellation. The shared signed witness sum is
the exact compatibility needed here.

## 3. Bounded point load for independently projected graph products

LP(d) can be applied to every product of edge differences in a graph of
maximum degree `Delta`. It is possible to choose its local marker alphabets
so that the resulting collection of projected templates has bounded point
incidence, with a bound depending only on `d,Delta`. This useful fact does
not assert that the projected templates reconstruct a given input tensor.

Here is an explicit finite-palette argument. Let `m=(n-1)/2`. Write the
abstract positive labels in each pure selector as `j=1,...,a_|B|`, and let
`a_*` be the largest such alphabet size. A witness `t!=0` has base
`rho(t)=|t|-1`; use `rho(0)=0` for the exceptional center witness.
For palette `h`, embed abstract label `j` at the positive orbit

`1 + ((rho(t)+h a_*+j-1) mod m)`.                       (PL1)

Here are explicit finite constants. Put

```
h_d=(3^d-1)/2,  w_d=2(h_d-d),  a_*=a_d,
H_d=2d+w_d a_*+1.                                      (PL2)
```

The alphabet recurrence (PS2) is increasing for `d>=2`, so `a_d` is a
valid maximum. There are at most `w_d` witnesses in one bundle, and at
most `2d+(w_d-1)a_*` forbidden orbits when its last witness is assigned.
Take `m>H_d a_*`.
For one witness, the orbit labels across its possible palette blocks are
distinct. Hence a forbidden orbit eliminates at most one palette. Greedy
selection produces every required disjoint alphabet. This argument treats
zero as a separate possible witness; it does not pretend that the center
has a two-element reflection orbit.

Fix an output cell `y` and a decorated partition term that could contain it.
For each of its blocks, any one coordinate of `y` identifies the witness
absolute value through (PL1), up to at most `H_d a_*` possibilities; the
sign of the witness gives a further factor two, and zero gives one extra
possibility. The deliberately larger bound `3H_d a_*` covers all of them.
There are therefore only a dimension-dependent number of
witness tuples. An original edge in a covered coordinate must be incident
to the corresponding signed witness value; an edge in an uncovered
coordinate must be incident to the corresponding coordinate of `y`.
Each has at most `Delta` choices. To make the pattern count explicit, define

```
p_0=1,
p_d=p_(d-1)+sum_(s=2)^d binom(d-1,s-1) 2^(s-1) p_(d-s).
B_(d,Delta)=p_d Delta^d (3H_d a_*)^floor(d/2).           (PL3)
```

The recurrence counts collections of disjoint signed blocks, with the
least coordinate either unused or in its unique block. Such a collection
has at most `floor(d/2)` blocks. Once its witness values and original edges
are fixed, the entire raw tensor and its actual selected palettes are fixed;
there is no additional growing choice of support words. Thus (PL3) bounds
the number of projected templates containing the specified cell, including
the empty-partition term. Constants can be enlarged without affecting the
argument, but no unspecified growing factor is hidden in this interface.

In particular every fixed signed equality stratum of codimension `c`
has at most `B_(d,Delta)` times its number of cells in support incidences,
which is `O_(d,Delta)(n^(d-c))`. This pays support, including support with
zero net contraction. It is not inferred merely from a vanishing trace.

## 4. Why the local projector does not close the global decomposition

Suppose a zero-margin tensor has the bounded tensor-expander expansion

`M = sum_e x_e R_e`.

Applying LP(d) separately gives exact kernel templates, but in general

`sum_e x_e P_(R_e) R_e != M`.                            (G1)

The residual is a sum of marker terms. If `M` already belongs to `K_d`,
that residual also belongs to `K_d`. Neither fact bounds the cost of
decomposing it into a globally bounded-load family. Choosing all marker
alphabets equal would restore a common linear projector in an appropriate
construction, but would destroy the point-load proof above.

There is a particularly clean identity for **coherent** marker assignments.
Choose `Q_(H,t)` depending only on `H,t`, without adapting it to the other
endpoints of `R_e`. For any fixed disjoint signed partition `pi`, summing
the corresponding marker term over the graph-product expansion gives exactly

```
sum_(t_H : H in pi) (tensor_(H in pi) Q_(H,t_H))
     tensor M((sigma_i t_H)_(i in H), free coordinates).         (G2)
```

Indeed, after expanding each edge product, the coefficient of the selector
product is precisely the value of `M` with those coordinates prescribed.
If `M in K_d`, every free-coordinate slice in (G2) is in the **full**
kernel on its free coordinates, because every contraction there vanishes
pointwise in the fixed coordinates. Summing over any one marker parameter
also gives zero, by the corresponding contraction of `M`. Thus (G2) has
both a kernel-valued slice interface and zero marker marginals.

This is stronger than knowing only zero axis margins. It explains why
module-valued flows are attractive. But coherent markers cannot in general
avoid every complementary endpoint. Adaptive palette selection in Section 3
solves avoidance while destroying the exact slice identity (G2). Closing
this discrepancy, or routing while maintaining endpoint avoidance, is a
remaining mathematical obligation.

## 5. A concrete obstruction to unrestricted marker routing

Choose distinct positive labels `a,b,c,z`. Set

`Q=(e_a-e_b) tensor (e_a-e_c)`, `F=e_a-e_z`.

The matrix `Q` is a pure all-positive pair selector and `F in K_1` is a
zero-total vector. Nevertheless `Q tensor F` has full all-positive body
contraction **one**. Its mixed `(1,3)` pair-family image is `e_a-e_c`.
Thus a complementary kernel factor by itself does not suppress mixed
contractions when selector and complementary alphabets overlap.

Let `Q'=(e_d-e_e) tensor (e_d-e_f)` on another three positive labels,
disjoint from `a,b,c,z`. Then `Q-Q' in K_2`, but

`(Q-Q') tensor F`

still has full-body contraction one and the same nonzero mixed pair image.
It therefore does **not** belong to `K_3`. This is an exact counterexample
to the unrestricted implication `K_b tensor K_t subset K_(b+t)` under
arbitrary common label supports. The implication holds under disjoint
reflection-orbit supports; that proviso cannot be dropped in a module-flow
construction. The companion code independently enumerates every signed
line touching these supports and verifies the offending images.

## 6. Finite colors and rational averaging: exact remaining obligations

Partitioning reflection orbits into finitely many colors can supply an
unused marker color for a compact template. It does not automatically
preserve the tensor kernel after restriction. Already the zero-total
vector `e_a-e_b` ceases to have zero total when `a,b` have different colors.
At the signed-trace level, take two pure pair selectors `Q_red,Q_blue`
on disjoint monochromatic alphabets. Their difference lies in `K_2`,
while its red-box restriction has trace one and its blue-box restriction
has trace minus one. Global trace cancellation is not colorwise trace
cancellation.

A valid colored architecture must therefore control **color-resolved**
contractions and their exact aggregate compatibilities. If every such
contraction vanishes, then each color box has the relevant internal
kernel properties directly; this follows by restricting the remaining
coordinates in the defining zero contraction. The additional vanishing
conditions are stronger than membership in `K_d` and cannot be assumed
without a proved correction stage. A finite number of colors makes the
structural list finite, but does not by itself construct that stage or
bound its physical load.

Likewise averaging fixed-marker projections is an exact rational identity
on `K_d`, but it scales coefficients without providing a bound on how many
nonzero reservoirs touch a fixed marker cell. Even a unit residual
coefficient requires a disjoint physical stage. The issue already occurs
for the simpler zero-axis anchored basis

`R_u=tensor_(i=1)^d(e_(u_i)-e_0)`, `u_i!=0`:

all `(n-1)^d` distinct basis supports contain the center cell. This is an
exact support-incidence count, independent of their coefficient magnitudes.
Embedding every one as a separate native correction reservoir would require
that many stages through the same native line. It is not a lower bound on
all possible decompositions, nor a claim that this anchored basis is a
full-signed-kernel basis. It demonstrates why a numerical rounding bound
alone cannot establish a physical reservation bound. The available
fixed-marker KG bounds likewise do not rule out concentrated support.
A bounded integer relation frame could repair an averaging architecture,
but it remains an additional generator and packing theorem.

## 7. Evidence, scope, and next obligation

[hyperk_kernel_research.py](../code/hyperk_kernel_research.py) independently
checks pure-selector support, every signed-line image, coordinate pairing,
the recursive invoices, local projected templates with repeated/opposite/
central endpoints, and the marker-collision and color-restriction failures.
Its algebra is finite and exact. These are physical-template and incidence
controls, not complete prime-hypercube arrangements or proof of asymptotic
packing. The coordinator records the executed revision and commands.

The useful proved output is PS(b), LP(d), the bounded local marker-palette
allocation, and the coherent-slice identity (G2). The open step is an exact
globally bounded-load reconstruction combining local physical purity with
endpoint-safe kernel-valued routing. It is the same explicit BK(d)
obligation consumed by [the controller manuscript](hyperk_controller.md),
now with several of its local requirements discharged and its forbidden-
endpoint issue demonstrated by an exact counterexample.

No inherited theorem or scientific source is modified. These claims require
independent review of their own frozen source before being treated as
reviewed components.
