# Full signed-line incidence in four dimensions

Author: `/root/hyper_incidence`. The labels below are manuscript-local;
no permanent claim IDs are allocated. This new source extends, without
modifying, [the axis-image theorem](incidence.md#axis-image-theorem) and
the three-dimensional [signed-image proof](signed_incidence.md) at PR79
scientific revision `a2445962ec6e06b2a893980fb7a183057eb9bcee`, delivered
at `cdb7879e358f93afa54b685027a27692d22635a9`.

Theorems here concern signed integer arrays and numeric coefficients.
Their lifts need not be positive or permutations of any prescribed pool.
Physical equal-gap swaps, prime supply, disjoint placement, centering and
capacity are separate composition obligations. Independent review of this
new source is pending.

## 1. The line map and every eventual compatibility equation

Let $n=2m+1\ge3$, $I=\{-m,\ldots,m\}$, and $J=\{1,2,3,4\}$.
For a nonempty set $S\subseteq J$, a sign pattern $\epsilon\in\{\pm1\}^S$
is normalized by $\epsilon_{\min S}=1$. Define

$$
 L_S^\epsilon a(x_{J\setminus S})
   =\sum_{t\in I}a(x),\qquad x_i=\epsilon_i t\quad(i\in S).
 \tag{1}
$$

The fixed coordinates are the arguments on the left. These are distinct
cell sets at $n\ge3$: a line determines its varying coordinate set, and
then its relative signs; different fixed coordinates give different sets.
The number of required lines is

$$
 M_4(n)=\sum_{s=1}^4 {4\choose s}2^{s-1}n^{4-s}
       =4n^3+12n^2+16n+8.                    \tag{2}
$$

Write $A_i=L_{\{i\}}a$ for the four axis tensors,
$F_{ij}^\sigma=L_{\{i,j\}}^{(1,\sigma)}a$ for the twelve pair-family
matrices, $G_S^\epsilon=L_S^\epsilon a$ for the sixteen triple-family
vectors, and $b^\epsilon=L_J^\epsilon a$ for the eight body scalars.
Here and below ordered coordinate lists are increasing.

All the following equalities are necessary:

1. **Axis marginals.** For $i\ne j$,
   $$S_jA_i=S_iA_j,                                      \tag{A}$$
   as arrays on the two remaining coordinates.
2. **Pair marginals.** For $S=\{i,j\}$, $k\notin S$, and the other
   coordinate $l\notin S\cup\{k\}$,
   $$
   \sum_{x_k}F_{ij}^\sigma(x_k,x_l)
      =\sum_t A_k(x_i=t,x_j=\sigma t,x_l).
                                                               \tag{P}
   $$
   The arguments of $F$ are placed in their coordinate order. There
   are two marginal equations for each pair-family matrix.
3. **Triple totals.** For $|S|=3$ and $l=J\setminus S$,
   $$
      \sum_{x_l}G_S^\epsilon(x_l)
        =\sum_t A_l((\epsilon_i t)_{i\in S}).           \tag{T}
   $$
4. **Complementary-pair traces.** For each of the three unordered
   partitions $\{i,j\}\mid\{k,l\}$ of $J$ and signs $\sigma,\tau$,
   $$
      \sum_t F_{ij}^\sigma(t,\tau t)
          =\sum_t F_{kl}^\tau(t,\sigma t).              \tag{C}
   $$
   There are twelve equations (C).

Each equality partitions the same coordinate or diagonal section into
parallel lines. Equation (C) is the $2+2$ partition identity; it is not
implied by attaching a free coordinate to the three-dimensional equations.
None of these sections is required to have prime sum. If the entry total
is prescribed as $T$, add

$$
                 \sum_{x_{J\setminus\{1\}}}A_1=T.     \tag{F}
$$

Equations (A) make the other directional totals equal to the same $T$.
There is no eventual extra identity involving the eight $b^\epsilon$;
the sufficiency proof establishes this rather than assuming it.

<a id="si4"></a>
## 2. The full integer image on the odd tail

**Theorem SI4.** For every odd $n\ge17$, an integer vector of targets
for all the lines (1) has an integer-array lift if and only if it
satisfies (A), (P), (T) and (C). The image lattice is saturated. The
rational rank, dependency rank, and integer-kernel rank are

$$
\begin{aligned}
 \operatorname{rank}L_4&=4n^3+6n^2-4n-9,\\
 \operatorname{rank}\ker L_4^T&=6n^2+20n+17,\\
 \operatorname{rank}\ker_{\mathbb Z}L_4
     &=n^4-4n^3-6n^2+4n+9.                         \tag{3}
\end{aligned}
$$

Fixing (F) reduces the attainable affine dimension by one. For integers
$r$ and $q\ge1$, such a target has a lift with every entry congruent
to $r\pmod q$ exactly when each line target is congruent to $nr\pmod q$.
In particular, compatible odd targets have an odd integer lift. Neither
positivity nor a prescribed entry pool is part of this theorem.

### 2.1. The integral axis kernel

Put $V=\{v\in\mathbb Z^I:\sum_tv(t)=0\}$. The integral splitting
$\mathbb Z^I=\mathbb Ze_0\oplus V$ and the axis-image theorem give
an integer lift of (A), with common axis kernel

$$
 V^{\otimes4},\qquad
 B_{u,v,w,z}=(e_u-e_0)\otimes(e_v-e_0)
             \otimes(e_w-e_0)\otimes(e_z-e_0),
 \quad u,v,w,z\ne0.                                  \tag{4}
$$

These $B$ form an integral basis; the axis rank is
$n^4-(n-1)^4=4n^3-6n^2+4n-1$. One direct axis lift fixes directions
in order: insert the current residual of direction $i$ on the slice
$x_i=0$. Its previously fixed marginals are zero by (A), so they
remain fixed. This specifies a linear integer right inverse, with
no positivity or size guarantee.

Subtracting this lift, the remaining targets consist of twelve integer
zero-row/column matrices $F$, sixteen zero-total vectors $G$, and
eight arbitrary scalars $b$, subject to (C). We now lift exactly that
residual system within (4).

An elementary hypercuboid is

$$
 C=(e_{a_0}-e_{a_1})\otimes(e_{b_0}-e_{b_1})
     \otimes(e_{c_0}-e_{c_1})\otimes(e_{d_0}-e_{d_1}).  \tag{5}
$$

It has sixteen signed vertices and zero axis sums. For a varying set
$S$, its line image is the contraction

$$
 \left[\sum_t\prod_{i\in S}(e_{x_{i,0}}-e_{x_{i,1}})
                              (\epsilon_i t)\right]
       \bigotimes_{j\notin S}(e_{x_{j,0}}-e_{x_{j,1}}).
                                                               \tag{6}
$$

Equation (6) computes every image claimed below. Noncentral reflection
orbits are the pairs $\{a,-a\}$ with $1\le a\le m$. Requiring
different orbits, rather than different coordinate values alone, is
essential when negative signs and central intersections are present.

### 2.2. Body controls, then triple transfers

Choose five different positive orbit representatives $a,b_1,b_2,b_3,b_4$.
The cuboid

$$
                    \bigotimes_{i=1}^4(e_a-e_{b_i})     \tag{7}
$$

has body image one on the all-positive body and zero on the other
seven. Its only triple images are the four all-positive vectors
$e_a-e_{b_l}$, and its only pair images are the six all-positive
matrices $(e_a-e_{b_k})\otimes(e_a-e_{b_l})$. Reflecting whole
coordinates provides the other seven body controls. Thus all body
errors can be corrected first, while retaining compatible lower-family
residuals. We do not assert that these lower residuals remain unchanged.

For a triple family $S$, and distinct remaining levels $u,v$, select
four positive orbit representatives $a,b_1,b_2,b_3$ avoiding the at
most two noncentral orbits of $u,v$. Put

$$
 C_{S;u,v}=\bigotimes_{i\in S}(e_a-e_{b_i})
                        \otimes(e_u-e_v),              \tag{8}
$$

with the factors in their coordinate positions. This has native triple
image $e_u-e_v$, no other triple or body image, and exactly three
possible pair images, for pairs contained in $S$. Each spill is a
tensor product of one factor $e_a-e_{b_i}$ with $e_u-e_v$. Their
reflection-orbit supports are disjoint, so both signed traces of
each spill vanish. Reflect the coordinates in $S$ to obtain every
signed triple family.

Since every zero-total vector is an integer combination of $e_u-e_0$,
(8) corrects all sixteen vectors while preserving the bodies. At
$m\ge8$ there are more than enough free orbits for (7) and (8).

### 2.3. Coupled complementary-pair trace controls

For a zero-margin matrix $M$, put

$$
                  \beta_\sigma(M)=\sum_tM(t,\sigma t).
                                                               \tag{9}
$$

For three different positive orbit representatives $a,b,c$ the rectangle

$$
 Q_+=(e_a-e_b)\otimes(e_a-e_c)                           \tag{10}
$$

has $(\beta_+,\beta_-)=(1,0)$. Reflect its second coordinate to
obtain $Q_-$ with trace vector $(0,1)$. We call either a generic
unit-trace rectangle. Both have zero row and column sums.

Take generic $A_\sigma$ and $B_\tau$ in complementary coordinate
pairs, using disjoint sets of three noncentral orbits. The single
hypercuboid

$$
                              A_\sigma\otimes B_\tau   \tag{11}
$$

has exactly two nonzero pair-family images: $B_\tau$ in the first
pair family of sign $\sigma$, and $A_\sigma$ in the complementary
family of sign $\tau$. Its other pair, triple and body images vanish.
Indeed, a mixed pair contraction would require a shared reflection
orbit across the two groups. Its two surviving traces both equal one.
Consequently (11) corrects one of the twelve common integers (C),
without changing the other eleven. These cuboids require only six
noncentral orbits.

After this step each remaining pair matrix has both traces zero.

### 2.4. Every pure pair kernel is integrally reachable

Fix a native pair family and write $M$ for its residual matrix on
the complementary coordinates. Thus $M$ has zero margins and
$\beta_+(M)=\beta_-(M)=0$. In the integral anchored rectangle basis,

$$
 M=\sum_{u,v\ne0}M(u,v)R_{uv},\qquad
 R_{uv}=(e_u-e_0)\otimes(e_v-e_0).                      \tag{12}
$$

Choose once and for all the two markers $Q_+,Q_-$ from (10), using
the same three positive orbits. For each anchored rectangle define

$$
 K_{uv}=R_{uv}-\beta_+(R_{uv})Q_+
                  -\beta_-(R_{uv})Q_-.                \tag{13}
$$

Here
$\beta_+(R_{uv})=1+\mathbf1_{u=v}$ and
$\beta_-(R_{uv})=1+\mathbf1_{u=-v}$.
These coefficients are integers, and their sum is at most three.
Equation (12) and the two zero traces of $M$ give

$$
                         M=\sum_{u,v\ne0}M(u,v)K_{uv}. \tag{14}
$$

The support of $K_{uv}$ uses at most five noncentral reflection orbits:
at most two from $u,v$, and three from the fixed markers. Since $m\ge8$,
choose a native generic unit-trace rectangle $A_\sigma$ using three
orbits outside all five. Then

$$
                              A_\sigma\otimes K_{uv}   \tag{15}
$$

has native pair image $K_{uv}$ and no other pair, triple or body image.
The complementary pair contractions vanish because both traces of
$K_{uv}$ are zero. Mixed contractions vanish by orbit separation.
Expression (15) is an integer sum of at most four cuboids, counting
multiplicity, so it belongs to (4). Possible overlaps in this numeric
sum are harmless here; they are not licensed as physical swaps.
Equations (14)--(15) independently correct all twelve pair matrices.
This completes the integer sufficiency proof for every odd $n\ge17$.

### 2.5. Rank, kernel, and congruences

The two trace maps on a zero-margin matrix are integrally independent
by (10). The twelve matrices have $12(n-1)^2$ free integer coordinates;
the twelve equations (C) have independent rank twelve. Indeed, for
each of the three complementary-pair partitions, its four matrices
have eight independently selectable trace coordinates; (C) merely
equates four disjoint pairs of those coordinates. There is no mixing
between the three partitions. The sixteen zero-total vectors add
$16(n-1)$ coordinates and the bodies add eight. Adding the axis rank
gives (3).

The proof provides an integral section $J$ of the extra image: fix
all orbit choices, use the anchored triple expansion, then (11) and
(13)--(15) in the displayed order. Each step depends linearly and
integrally on the residual data. In particular the full integer kernel
is explicitly

$$
 \left\{\sum_{\mathbf u\in(I\setminus\{0\})^4}
       c_{\mathbf u}B_{\mathbf u}:Q_n c=0\right\},       \tag{16}
$$

where the exact reduced integer matrix $Q_n$ is specified in section 4.
An explicit finite integral generating set is
$B_{\mathbf u}-J(L_4B_{\mathbf u})$ for all $\mathbf u$.
It generates the whole kernel because $\mathrm{id}-JL_4$ is the
identity on that kernel, not merely a rational projection. A basis can
be extracted by integer elementary operations. No assertion that this
redundant generating set is a basis is intended.

The image equals the integer solutions of homogeneous equations
(A), (P), (T), (C), hence is saturated. For the congruence refinement,
subtract the constant array $r$ at the target level (subtract $nr$
from every line target) and divide by $q$. The result is an integer
compatible vector because a constant array itself satisfies every
displayed identity. Apply SI4, multiply the lift by $q$, and add $r$
entrywise. This proves sufficiency; summing a line proves necessity.

## 3. A bounded numeric solver for the extra families

The anchored construction proves saturation, but its common marker
supports are unsuitable for sparse disjoint physical reservoirs. This
section supplies a different bounded decomposition. Its geometric
marker requirements are explicit and proved below; physical placement
in four dimensions remains separate.

Use a loopless multigraph $G$ on $I$, of maximum degree
$\Delta=64$ and edge expansion at least eight, as in the preserved
[tensor-expander theorem](incidence.md#tensor-expander-coefficient-theorem).
Edges are individually labeled, including parallel edges. With
oriented incidence matrix $B$, every integer zero-margin matrix $D$
can be written

$$
 D=BXB^T=\sum_{e,f}x_{ef}R_{ef},\qquad
 \|X\|_\infty\le L_n^2\|D\|_\infty+\tfrac12+512n^2,
 \quad L_n=5\log n+5.                                 \tag{17}
$$

The precise imported rounding term is retained; it is not replaced
by a bounded real solution. For correction units $g$, applying (17)
to $D/g$ gives physical scalar bound
$L_n^2\|D\|_\infty+g/2+512gn^2$.

### 3.1. Sparse marker projection

**Lemma MP4.** For all sufficiently large odd $n$, the graph-product
rectangles in (17) admit the following fixed collection of templates.
Each template has zero margins and both signed traces zero; it is a
sum of at most five pairwise cell-disjoint signed rectangles, with
coefficients $\pm1$. There are $O_\Delta(n^2)$ templates. Every
target cell belongs to only $O_\Delta(1)$ templates. For every
integer $D$ with zero margins and both traces zero, $D$ is an integer
combination of these templates, each coefficient having magnitude
at most the right side of (17). The auxiliary marker-flow coefficients
can in fact be bounded by the ceiling of one eighth of that bound.

**Proof.** A graph-product rectangle $R_{ef}$ has four distinct cells.
The quantity $|\beta_+(R_{ef})|+|\beta_-(R_{ef})|$ is at most four.
If it is nonzero, its support meets one of the $2n-1$ signed-diagonal
cells. Each such cell belongs to at most $\Delta^2$ labeled graph
rectangles. There are therefore at most $2\Delta^2n$ active
rectangles, and at most $8\Delta^2n$ unit trace contributions.

For each contribution allocate its own generic marker $M$ of the
required trace sign, with coefficient $s_M\in\{1,-1\}$ equal to
the sign of that contribution. Markers attached to one rectangle
use disjoint noncentral reflection orbits, and avoid every orbit of
that rectangle. Write

$$
                 C_{ef}=R_{ef}-\sum_{M\text{ attached to }(e,f)}s_M M.
                                                               \tag{18}
$$

It has both traces zero and is a sum of at most five cell-disjoint
rectangles. Inactive rectangles need no marker.

Here is a uniform bounded-load allocation. For each marker choose
its three positive orbit labels greedily. Maintain an orbit-use cap
$L=256\Delta^2$. There are at most $24\Delta^2n$ total uses, so
fewer than $n/8$ labels can be saturated at any time. Excluding the
at most four original rectangle orbits, at most nine previous marker
orbits in this bundle, and already chosen labels removes only a
constant number. Since $m=(n-1)/2$, three eligible labels remain
for all sufficiently large $n$. Every coordinate cell of the marker
plane then belongs to at most $L$ markers: a marker containing that
cell uses each nonzero coordinate orbit of the cell. All markers
avoid the center. Thus marker cell load is bounded independently
of $n$.

Substitute (18) in (17). The remaining marker coefficient is
$\mu_M=s_Mx_{ef}$, with $|\mu_M|\le F:=\|X\|_\infty$.
For each trace sign, $\sum_M\mu_M=0$, since the corresponding
trace of $D$ is zero. We express this sum by differences of
cell-disjoint markers of the same sign.

There are $p_\pm\ge |E(G)|\ge4n$ markers of each sign. For plus,
each $R_{ee}$ has nonzero plus trace. For minus, fix an edge
column $b_e$. The reflected vector $Rb_e$ is a nonzero member of
$V$, and the edge columns span $V$ since expansion makes $G$
connected. Hence $b_e^TRb_f\ne0$ for some $f$. This gives at least
one minus marker for each $e$; labeled contributions are distinct.

Start with a degree-64, expansion-eight graph on the $p_\pm$ markers.
If the endpoint supports of an edge intersect, replace that labeled
edge by a length-two path through a marker disjoint from both.
Each marker meets at most $4L$ others in a cell, so at most $8L+2$
possible middle vertices are forbidden for one replacement. Cap
middle-vertex use at 128. There are at most $32p_\pm$ replacements,
so at most $p_\pm/4$ middle vertices are saturated. Once
$p_\pm>16L+8$, an allowed unsaturated choice exists. The resulting
labeled multigraph has maximum degree at most 320. Its expansion
is at least eight: each original crossing edge has at least one
crossing edge on its replacement path, with distinct edge labels.

The integer max-flow argument of
[the signed-cube coefficient theorem](signed_incidence.md#bounded-coefficient-solvers)
now gives an integer flow of magnitude at most $\lceil F/8\rceil$
whose divergence is $\mu$. Replacing an oriented graph edge by
$M_u-M_v$ recovers the marker residual. Its two rectangles have
disjoint supports and equal trace vectors; consequently their
difference has both traces zero.

Each target cell belongs to at most $\Delta^2$ original graph
rectangles, at most $L$ markers in (18), and at most $320L$
marker-graph edges. Thus all template cell loads are bounded by
$\Delta^2+321L$. The number of templates is $O_\Delta(n^2)$,
and each of their coefficients has the asserted bound. This proves
the lemma. $\square$

There is a useful stronger invoice for exceptional target cells.
At most $2\Delta^2n$ original templates meet either signed diagonal.
Every marker-flow template is counted among at most
$160(p_++p_-)\le1280\Delta^2n$ labeled graph edges. Thus at most
$1282\Delta^2n$ templates meet the union of the two signed
diagonals. A generic marker has exactly one signed-diagonal cell;
a marker difference has exactly two, since its supports are disjoint.
All templates outside the displayed $O_\Delta(n)$ exceptional set
avoid both signed diagonals completely. The total template count is
at most $(\Delta n/2)^2+1280\Delta^2n$.

For each template $C$, choose a generic native selector $A_\sigma$
whose orbits avoid every coordinate orbit used by $C$. There are
at most sixteen such noncentral orbits for (18), and at most six
for a marker difference. Equation (15) therefore applies eventually.
The numeric tensor $A_\sigma\otimes C$ affects exactly the intended
pair family. It comprises at most five disjoint cuboids, with at
most forty parallel equal-gap pairs required by a later physical
implementation. Choosing these orbits separately does not establish
disjointness between different physical stages or reservoirs.

### 3.2. Descending correction and trace sharing

Bodies are corrected by (7). Triple vectors are then corrected by
(8) on the degree-64 graph: a zero-total vector bounded by $E$ has
an integer edge flow bounded by $\lceil E/8\rceil$. The triple
control spills only into pair matrices with both traces zero.
Its target-cell load must be bounded across the chosen family of
triple templates; that is a geometric placement invoice, not a
consequence of a single cuboid formula.

For each of the twelve common complementary-pair traces, a residual
pair matrix bounded by $E$ has trace magnitude at most $nE$.
Split that integer into $n$ integers, each of magnitude at most
$E+1$, and use $n$ generic coupled controls (11). Their six orbit
slots can be balanced greedily just as above, so each target cell
belongs to a bounded number of these controls. This reduces all
pair traces to zero with at most a constant-factor increase in
the maximum pair error. Apply MP4 to each of the twelve residual
matrices. It changes only its native family and preserves all
previously corrected bodies, triples and other pair families.

The exact coefficient bound for the pure pair pass is therefore
$O(L_n^2E)+O(gn^2)$ in scalar units. Neither a lost factor $n$
in the trace pass nor an uncharged common marker is hidden in
this statement: the former is divided among $n$ controls, and
the latter is routed on the bounded-degree marker graph.

### 3.3. Residues and the physical boundary

**Lemma MR4 (no-division residue solver).** Keep the fixed graph-product
and marker allocation of MP4. For any modulus $h\ge1$, a residue
matrix with zero margins and both traces zero in $\mathbb Z/h\mathbb Z$
is a combination of the templates (18) and a second fixed collection
of $O_\Delta(n)$ disjoint-marker differences. All coefficients may
be chosen in $\{0,\ldots,h-1\}$. No integer involving $n$ needs
to be inverted modulo $h$.

**Proof.** Choose a spanning tree of $G$. Its oriented edge columns
are an integral basis of $V$: deleting one row gives a square
matrix of determinant $\pm1$, as follows by successively deleting
leaves. Tensor that basis twice. It spans every zero-margin residue
matrix over $\mathbb Z/h\mathbb Z$ for every $h$, without a field
hypothesis. Equivalently, lift the noncentral entries arbitrarily
and recover central entries by negative row/column sums, expand
that integer zero-margin matrix in the tree-product basis, and
reduce coefficients modulo $h$. Thus $D=\sum x_{ef}R_{ef}$ modulo
$h$, with each $x_{ef}$ in the stated range. Apply (18). For each
sign the remaining marker coefficients $\mu$ have total zero modulo
$h$, because the corresponding trace of $D$ is zero modulo $h$.

Order each marker set arbitrarily. The coefficient on its $j$th
path edge is the prefix sum $\sum_{i\le j}\mu_i$, reduced modulo
$h$. These edge divergences recover $\mu$ modulo $h$, including
the final vertex. If two consecutive marker supports intersect,
replace that labeled path edge by a two-edge path through a marker
disjoint from both, using the same coefficient on both edges.
Choose middle vertices with use cap four. There are fewer than $p$
replacements, hence fewer than $p/4$ saturated choices; the same
$8L+2$ forbidden-support bound used above supplies a choice for
$p>16L+8$. The middle vertex has cancelling contributions. This
fixed routed path has maximum degree at most ten and at most
$2(p-1)$ edge copies. Every edge is a difference of cell-disjoint
markers, so the templates have the required form. $\square$

The residue template cell load is at most $\Delta^2+11L$; at most
$2\Delta^2n+2(p_++p_-)\le18\Delta^2n$ templates meet either
signed diagonal. The count and degree concern the entire fixed
routed path, not one replacement in isolation.

The body and triple steps similarly use integral cuboids and
ordinary tree flows before coefficient reduction. Coupled pair
traces can be corrected modulo $h$ with one preallocated generic
coupled control for each trace; dividing a trace by $n$ is not
required. These stages leave pure pair residue matrices to which
MR4 applies. For even physical gaps $g=2h$, an odd-to-odd target
difference is divided by two, solved modulo $h$, and restored by
physical scalar steps congruent to two modulo $g$. Every use requires
a separately proved compatible residue vector; arbitrary independent
pair or body residues cannot be presumed compatible.

This section does not assert that reducing all coefficients modulo
$h$ has the same small drift as solving the bounded integer problem.
Residue stages and their actual integer spill must be charged in the
physical proof. In particular an abstract hypercuboid needs eight
mutually disjoint pairs of the same actual difference; a compound
template needs up to forty. All entries, cells, both correction
signs, total depletion and whole-reservoir line intersections must
be controlled separately.

## 4. Exact finite diagnostics and reproducibility

In the axis kernel (4), a basis vector indexed by nonzero coordinates
$\mathbf u$ has the following contraction on a varying set $S$:

$$
 \sum_t\prod_{i\in S}(e_{u_i}-e_0)(\epsilon_i t)
       =(-1)^{|S|}+
           \mathbf1_{u_i=\epsilon_i u_{\min S}\ (i\in S)}. \tag{19}
$$

At nonzero fixed coordinates its remaining factors are Kronecker
deltas. Retain the noncentral $(n-1)^2$ entries of each pair matrix,
the noncentral $n-1$ entries of each triple vector, and all bodies.
Zero margins and zero totals recover the omitted central entries
integrally. Thus the reduced matrix $Q_n$ has

$$
       [12(n-1)^2+16(n-1)+8]\times(n-1)^4              \tag{20}
$$

integer entries prescribed by (19). It retains the exact image
lattice on the integral axis kernel; it is not merely a rational
rank reduction. The full rank is $n^4-(n-1)^4+\operatorname{rank}Q_n$.

The producer [hyper4_incidence.py](../code/hyper4_incidence.py) exports
integer lattice certificates for $Q_3$ and $Q_5$. At order three it
uses an elementary-operation Smith log. At order five it first uses
the unchanged PR79 unit-pivot preconditioner; a producer-only pinned
`python-flint==0.8.0` calculation then returns two smaller integer
unimodular transformations, their integer inverses, and a nonsingular
block. A small elementary-operation Smith log finishes that block.
The checker verifies the inverse identities and the full transformed
matrix, so no opaque HNF or Smith assertion is trusted. The independent checker
[verify_hyper4_incidence.py](../code/verify_hyper4_incidence.py)
regenerates the geometric subsets from fixed/forward/reversed words,
checks (19) by direct summation on anchored basis arrays, and replays
the logs. Verification needs only the Python standard library. It
also checks every displayed gadget image and the full
constructive lift, including negative controls. Exact outcomes and
source revisions belong in the coordinator's recovery handoff after
these commands have run; finite checks do not prove SI4's odd tail.
The deterministic marker fixture uses the cycle graph at $n=65$
and checks MR4 for $h=1,5,6,13,65$, including moduli sharing a
factor with $n$. It is a no-division residue fixture, not an
expansion-eight graph certificate or a physical reservoir certificate.
Its checker rejects hidden template support overlaps, colliding
marker-path endpoints, invalid residue margins, omitted or duplicated
lines, wrong integral bases, nonunimodular transforms, changed total
data, invalid congruences, and the central-body and repeated-endpoint
regressions.

The exact retained invariants are:

| Order | Full line count | $Q_n$ dimensions | Rank of $Q_n$ | Full rank | Array-kernel rank | Nonunit invariant factors |
|---|---:|---:|---:|---:|---:|---|
| 3 | 272 | $88\times16$ | 16 | 81 | 0 | $3$ four times; $6$ once |
| 5 | 888 | $264\times256$ | 203 | 572 | 53 | $5$ eighteen times; $10$ seven times; $30$ eight times; $60$ twice |

Thus the finite images have saturation indices $486$ and
$2^{19}3^{10}5^{35}$ respectively, in addition to their finite
rational dependencies. There are 191 and 316 full rational
dependencies. In particular the eventual rank formula must not be
substituted at order five. The inputs explicitly export a complete
integer kernel basis in the anchored coordinates, a complete reduced
dependency basis, and every nonunit image-divisibility functional.
The anchored embedding (4) converts the exported kernel basis into
a basis of the full array kernel. For an arbitrary full target, first
check (A), lift its axes by section 2.1, subtract that lift and check
the zero-margin and zero-total conditions (P), (T); then apply the
exported reduced dependency and divisibility rows. This is an exact
small-order image-membership criterion. Equation (C) is included
among the reduced dependencies rather than assumed sufficient there.

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyper4_incidence.py --smith 3 --output /tmp/hyper4_incidence_n3.json
python3 -m pip install --target /tmp/hyper4-incidence-deps python-flint==0.8.0
PYTHONPATH=/tmp/hyper4-incidence-deps python3 -B problems/prime-arrays-beyond-square/code/hyper4_incidence.py --smith 5 --output /tmp/hyper4_incidence_n5.json
python3 -B problems/prime-arrays-beyond-square/code/verify_hyper4_incidence.py
```

The retained inputs are incidence certificates, not prime-target
vectors and not arrangements of the first $n^4$ odd primes. At small
orders there can be extra relations or torsion; SI4 deliberately
starts at 17 and makes no lattice assertion at 3 or 5 without the
corresponding finite certificate.
