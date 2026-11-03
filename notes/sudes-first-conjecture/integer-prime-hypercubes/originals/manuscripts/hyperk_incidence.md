# Integer incidence of full signed lines in every fixed dimension

Author: `/root/incidence`. This is an author manuscript for the isolated
general-dimension continuation. Labels are local; no permanent claim IDs are
allocated. Its proof is independent of extrapolating the low-dimensional
Smith calculations. The inherited [three-dimensional](signed_incidence.md)
and [four-dimensional](hyper4_incidence.md) incidence manuscripts and their
review records remain unchanged.

## 1. Exact map and interface

Fix an integer $k\ge2$, an odd integer $n=2m+1\ge3$, and
$I=\{-m,\ldots,m\}$. A **signed block** is a pair
$H=(B,\sigma)$ with $\varnothing\ne B\subseteq[k]$,
$\sigma\in\{\pm1\}^B$, normalized by $\sigma_{\min B}=1$.
Write $\mathcal H_k$ for the signed blocks and

$$
 h_k=|\mathcal H_k|=\frac{3^k-1}{2}.
 \tag{I1}
$$

For an integer array $a\in\mathbb Z^{I^k}$ define

$$
 (A_{k,n}a)_{H,c}=\sum_{t\in I}a(x),\qquad
 x_i=\sigma_i t\ (i\in B),\quad x_j=c_j\ (j\notin B).
 \tag{I2}
$$

For $n\ge3$ these labels give distinct cell sets. A set reveals which
coordinates vary, its fixed coordinates, and all relative varying signs.
Consequently the exact number of rows is

$$
 L_k(n)=\sum_{r=1}^k\binom kr2^{r-1}n^{k-r}
       =\frac{(n+2)^k-n^k}{2}.
 \tag{I3}
$$

The center is an ordinary fixed level in (I2). Although all relative signs
meet at the central cell, distinct signs still define distinct full lines
when $n\ge3$. No free reflection action at zero is assumed.

Let $y=(y_{H,c})$ be an integer target vector. For disjoint nonempty
coordinate blocks $B,C$, normalized signs $\sigma,\tau$, and fixed
coordinates $d$ outside $B\cup C$, impose

$$
 \sum_{u\in I}y_{(B,\sigma),(\tau u,d)}
 =\sum_{t\in I}y_{(C,\tau),(\sigma t,d)}.
 \tag{PC}
$$

The placement of arguments follows their coordinate indices. Both sides
sum the same signed two-parameter section. These include all axis margins
and every complementary or noncomplementary shared trace. Iterating them
identifies contractions on any signed partition into disjoint blocks.
They do not demand prime sums for those sections.

**Theorem IK (complete integer image).** For every fixed $k\ge2$ and
every odd $n\ge3^k$, the image of $A_{k,n}$ is exactly the integer target
vectors satisfying (PC). The image is saturated. If the pool total is a
specified integer $T$, impose in addition the total $T$ in one full axis
family; (PC) makes all $k$ directional totals equal to $T$.

For integers $r$ and $q\ge1$, such a compatible vector has a lift with
every entry congruent to $r\pmod q$ if and only if every line target is
congruent to $nr\pmod q$. In particular compatible odd targets have an
odd integer lift. There is no positivity, distinctness, or prescribed-pool
conclusion in this theorem.

The threshold $3^k$ is a sufficient algebraic threshold, not an optimized
one. It does not replace the sharper inherited incidence thresholds at
$k=3,4$, and is not a numerical threshold for prime permutations.

## 2. A monic polynomial model

Introduce the polynomial ring

$$
 R=\mathbb Z[z_{i,t}:i\in[k],\ t\in I],
 $$

with multidegree $\deg z_{i,t}=e_i\in\mathbb N^k$. A cell $x\in I^k$
is identified with the multilinear monomial $z_x=\prod_i z_{i,x_i}$.
For each signed block $H=(B,\sigma)$ put

$$
 p_H=\sum_{t\in I}\prod_{i\in B}z_{i,\sigma_i t}.
 \tag{I4}
$$

The polynomial of a full line $(H,c)$ is
$p_H\prod_{j\notin B}z_{j,c_j}$. Thus the row lattice of $A_{k,n}$
is precisely the multidegree $\mathbf1=(1,\ldots,1)$ component of
the ideal $J=(p_H:H\in\mathcal H_k)$.

### 2.1. Pairwise disjoint monic leading terms

Since $m\ge h_k$, choose different positive labels $a_H$ for all
$H\in\mathcal H_k$. Define provisional rational variable weights by

$$
 w_i(\sigma_i a_H)=1/|B|\quad(i\in B),\qquad
 w_i(t)=-k\quad\text{in every other case}.
 \tag{I5}
$$

There is no conflict between assignments, because different $H$ use
different absolute labels. In particular $w_i(0)=-k$. Add $k+1$ to
every variable weight and multiply by $\operatorname{lcm}(1,\ldots,k)$;
the resulting positive integer weights, refined by any monomial ordering
to break ties, define a monomial ordering. The common additive shift does
not change comparisons within a fixed multidegree.

The unique leading monomial of $p_H$ is

$$
 \ell_H=\prod_{i\in B}z_{i,\sigma_i a_H},
 \tag{I6}
$$

with coefficient one. Indeed, its provisional weight is one. A term of
$p_{(C,\tau)}$ at a different designated orbit $a_H$ can avoid a
negative variable weight only if $C\subseteq B$ and its signs agree
with $\sigma|_C$, possibly after simultaneous reversal. It then has
weight $|C|/|B|$, strictly below one unless the two signed blocks agree.
If any variable has weight $-k$, the entire term has weight at most
$-k+(k-1)<1$. At the same block, simultaneous reversal cannot give a
second weight-one term because both sign patterns are normalized at their
least coordinate. Terms at zero or an unused orbit have only negative
weights. This proves uniqueness, including every central term.

For different signed blocks, the monomials $\ell_H$ use disjoint
variables: their absolute labels $a_H$ differ. Hence they are pairwise
coprime, even when their coordinate sets overlap.

### 2.2. Elementary integral consequences

We record the elementary polynomial fact needed below, including its
integer content. If monic polynomials $f_i$ have pairwise coprime leading
monomials $\ell_i$, then:

1. They form a monic Gröbner basis. Every polynomial has a unique
   remainder supported on monomials divisible by none of the $\ell_i$.
2. The residue classes of those standard monomials are a basis of the
   quotient over $\mathbb Z$.
3. All relations $\sum_i g_i f_i=0$ are generated over the polynomial
   ring by $f_j e_i-f_i e_j$.

Here is a direct justification. A cancellation between largest products
$\operatorname{LM}(g_i)\ell_i$ and
$\operatorname{LM}(g_j)\ell_j$ has their product divisible by
$\ell_i\ell_j$, since the leading monomials are coprime. Subtract an
integer monomial multiple of $f_j e_i-f_i e_j$ to eliminate one of the
largest coefficient terms, without introducing a larger term. If more
than two summands have that leading product, use one as a pivot and
eliminate the others. After all terms at that monomial are removed, the
largest remaining monomial decreases. The well-ordering of monomials
ensures termination. This proves the relation assertion, using only
integer additions and monic cancellation. The same argument applied to
differences of polynomial division outputs proves uniqueness of
remainder. A nonzero combination of standard monomials cannot lie in the
ideal because its leading monomial is divisible by no $\ell_i$.
Division gives existence of a remainder, proving the free-basis assertion.

No field, denominator, or inversion of $n$ enters this argument. Applied
to (I4), it makes $R/J$ a free abelian group, multidegree by multidegree.

## 3. Proof of the exact integer interface

Consider a relation among line rows, equivalently a homogeneous relation

$$
 \sum_{H=(B,\sigma)}g_Hp_H=0,
 \qquad \deg g_H=\mathbf1-\mathbf1_B.
 \tag{I7}
$$

The elementary relation reduction above stays homogeneous. A Koszul
relation between $p_H$ and $p_K$ can occur in multidegree $\mathbf1$
only when their coordinate blocks are disjoint: an overlapping coordinate
would have degree two in their product. Its multiplier is then a linear
combination of fixed-coordinate monomials on the complement of those two
blocks. For one such monomial, the relation
$p_K e_H-p_H e_K$ is precisely the difference of the two sides of
(PC). Thus **every integer row relation** is an integer linear
combination of the displayed partition relations.

Now a compatible target $y$ defines a homomorphism from the row lattice
$J_{\mathbf1}$ to $\mathbb Z$: send each line row to its target.
The previous paragraph makes this homomorphism well defined. Monic
division gives a direct-sum decomposition

$$
 R_{\mathbf1}=J_{\mathbf1}\oplus
       \mathbb Z\{\text{standard multilinear monomials}\}.
 \tag{I8}
$$

Extend the homomorphism by zero on the second summand. Its values on
the cell monomials $z_x$ are integer array entries, and evaluation on
each line row gives exactly $y$. This proves sufficiency. Necessity of
(PC) was the two partitions of a section. Equality with the integer
solutions of homogeneous integer equations proves saturation.

For the entry-congruence assertion, subtract the constant array $r$ at
the target level, then divide all coordinates by $q$. This is integral
exactly under the asserted target residues. Every (PC) still holds,
because a constant array itself satisfies every partition identity. Lift
the resulting integer vector, multiply the lift by $q$, and add $r$
entrywise. Necessity follows by summing a line. This proves IK.

In particular the absolute-fixed-label-set target prescription in the
general target manuscript requires no further eventual congruence:
its termwise verification of (PC), correct odd parity, and exact common
axis total are the complete integer interface. An integer lift remains
strictly weaker than an arrangement of the prescribed prime pool.

## 4. Rank and the finite poset of intersection types

The standard monomial basis also gives an exact stable rank polynomial.
A collection of leading monomials $\ell_H$ can divide a multilinear
monomial only if its coordinate blocks are pairwise disjoint. Conversely
every such collection divides exactly $n^{k-|U|}$ multilinear monomials,
where $U$ is the union of its blocks. Inclusion-exclusion therefore gives
the array-kernel rank

$$
 \kappa_k(n)=\sum_{r=0}^k(-1)^r
    \sum_{t=r}^k\binom kt
       \left\{\!{t\atop r}\!\right\}2^{t-r}n^{k-t},
 \qquad \operatorname{rank}A_{k,n}=n^k-\kappa_k(n).
 \tag{I9}
$$

The $r=0,t=0$ summand is $n^k$; the other $r=0$ summands vanish.
The braces denote Stirling numbers of the second kind. This is a finite
sum in $k$ over signed partitions into disjoint nonempty coordinate
blocks. The growing placements are the $n^{k-t}$ factors; they are not
new structural types. Equivalently,

$$
 \sum_{k\ge0}\kappa_k(n)\frac{z^k}{k!}
 =\exp\!\left(nz-\frac{e^{2z}-1}{2}\right),
 \tag{I10}
$$

and adding a coordinate obeys the finite recurrence

$$
 \kappa_0=1,\qquad
 \kappa_{k+1}=n\kappa_k-
     \sum_{j=0}^k\binom kj2^j\kappa_{k-j}.
 \tag{I11}
$$

Thus the stable ranks at dimensions two, three, four, five and six are

$$
\begin{array}{c|l}
 k&\operatorname{rank}A_{k,n}\\ \hline
2&2n+1\\
3&3n^2+3n-1\\
4&4n^3+6n^2-4n-9\\
5&5n^4+10n^3-10n^2-45n-23\\
6&6n^5+15n^4-20n^3-135n^2-138n+25.
\end{array}
 \tag{I12}
$$

These are not claims at orders below the proven stable range. Small-order
extra rational relations and torsion remain real; the inherited order-three
and order-five Smith data provide explicit examples.

For the physical hierarchy, after axis correction it is useful to omit
singleton blocks. For a signed partition $\pi$ with blocks of size at
least two, define

$$
 r(\pi)=\sum_{B\in\pi}(|B|-1)=|U|-|\pi|.
 \tag{I13}
$$

Choose one generic selector
$Q_{B,\sigma}=\bigotimes_{i\in B}(e_{\sigma_i a}-e_{\sigma_i b_i})$
per block, using different noncentral orbits for the common $a$ and all
$b_i$, and disjoint orbit sets for different blocks. Tensor with a
complement tensor $M$ in the full signed-line kernel on the remaining
coordinates, with its orbit support disjoint from every selector.
The resulting tensor has the desired $\pi$-contraction $M$. Any nonzero
other partition contraction has each of its blocks contained in one block
of $\pi$, with the induced relative signs. Contractions within the
complement vanish because $M$ is in its full kernel; mixed contractions
vanish by orbit separation. Subdivision or deletion of blocks strictly
decreases (I13), except for the identical partition. Thus descending
$r(\pi)$ is a genuine finite triangular hierarchy. It includes the
complementary-pair traces in dimension four and higher shared traces in
every dimension. It does not itself furnish an affordable physical
decomposition of $M$.

## 5. Explicit integer section and sparse kernel generators

### 5.1. A coarse integer right inverse

Fix the designated orbits and any rule selecting a leading divisor.
For a standard cell monomial set $a_y(x)=0$. For a nonstandard one, choose
$H=(B,\sigma)$ with $\ell_H\mid z_x$ and recursively set

$$
 a_y(x)=y_{H,x_{B^c}}-
         \sum_{t\in I\setminus\{a_H\}}a_y(x[B\leftarrow\sigma t]).
 \tag{I14}
$$

Every recursive argument has smaller weight. The polynomial identity
behind (I14) is monic division, so Section 3 proves that for compatible
$y$ the resulting array lifts every target, regardless of the chosen
leading-divisor rule. This is an explicit integer right inverse.

The provisional weight of a multilinear monomial lies in $[-k^2,k]$.
Every rewrite lowers it by at least $1/k$. Hence a branch has at most

$$
 D_k=k^2(k+1)
 \tag{I15}
$$

rewrites. In particular, with $E=\|y\|_\infty$,

$$
 \|a_y\|_\infty\le E\sum_{j=0}^{D_k-1}(n-1)^j.
 \tag{I16}
$$

This coarse bound explicitly tracks coefficients and introduces no rounding
terms. It is much too large for the near-mean permutation controller.
It is not presented as the missing physical right inverse.

### 5.2. Bounded-size generators for the full array kernel

There is nevertheless a useful stronger local statement. Let
$\mathcal S$ be the standard multilinear monomials and let $\operatorname{NF}$
be the monic normal form. For $v\in\mathcal S$ define an integer array

$$
 K_v(x)=[z_v]\operatorname{NF}(z_x).
 \tag{I17}
$$

**Lemma KG.** These arrays are an integral basis of
$\ker A_{k,n}$. They satisfy

$$
 K_v(u)=\mathbf1_{u=v}\quad(u\in\mathcal S),\qquad
 M=\sum_{v\in\mathcal S}M(v)K_v
       \quad(M\in\ker A_{k,n}).
 \tag{I18}
$$

Let $\mathcal A=\{\pm a_H:H\in\mathcal H_k\}$ and
$s_k=2h_k+1=3^k$. Then

$$
 \operatorname{supp}K_v\subseteq
       \prod_{i=1}^k(\{v_i\}\cup\mathcal A),
 \quad |\operatorname{supp}K_v|\le s_k^k,
 \quad \|K_v\|_\infty\le s_k^{D_k}.
 \tag{I19}
$$

In (I18) the coefficient bound is exactly $\|M\|_\infty$.

**Proof.** Normal form kills each line-row polynomial, so every coefficient
functional (I17) annihilates all line rows. On standard monomials normal
form is the identity, proving the first assertion in (I18). Equation (I8)
shows that every homomorphism annihilating the row lattice is determined
freely by its values on standard monomials. This proves both the basis
claim and the expansion.

A rewrite changes a coordinate only when its old value belongs to
$\mathcal A$: leading monomials use only designated marker values.
Consequently any coordinate value outside $\mathcal A$ persists throughout
every rewrite branch. If $z_v$ occurs in the final remainder of $z_x$,
then each initial $x_i$ is either $v_i$ or a designated marker, proving
the support bound. On a branch that can eventually produce $v$, a rewrite
parameter is either one of the $2h_k$ marker values, or the unique
nonmarker parameter (if it exists) matching all $v_i$ in the rewritten
block. There are at most $s_k$ relevant choices per rewrite, and at most
$D_k$ rewrites. Each branch has coefficient $+1$ or $-1$, so the total
coefficient magnitude is at most $s_k^{D_k}$. This proves (I19). QED.

The generator complexity in KG depends only on $k$, not on $n$.
However the same designated markers occur in all these basis elements.
For example many templates can meet one marker slice or marker cell.
Therefore (I19) proves **bounded local support**, not bounded global
congestion or disjoint physical packing. Replacing the common markers by
different independently chosen markers does not preserve the exact
expansion (I18) automatically. A bounded-load distributed decomposition,
or a separate physical repair of those marker residuals, remains an
additional obligation. This explicit distinction is essential to using
IK or KG in the prime-permutation problem.

## 6. Two additional numeric tools for the distributed controller

### 6.1. A pure unit full-block selector with disjoint signed cells

**Lemma PS.** For each $b\ge2$ there is an explicitly finite signed array
$Q_b$ on $b$ coordinates, with every nonzero entry $+1$ or $-1$, such
that every proper full signed-coordinate line has sum zero, the all-positive
full body has sum one, and all other full bodies have sum zero. Its support
can be paired into opposite-sign cells along any prescribed one coordinate.
It uses only positive noncentral coordinate labels. One may place its label
alphabet on any equally sized set of positive reflection orbits.

Put

$$
 c_b=b-1,\quad M_b=\operatorname{lcm}(1,\ldots,c_b),\quad
 p_b=M_b+1,\quad q_b=2M_b+1.
 \tag{I20}
$$

An explicit selector uses $2p_b+q_b=4M_b+3$ positive labels and

$$
 4p_b^{b-1}+2q_b^{b-1}\ \text{signed cells},\qquad
 2p_b^{b-1}+q_b^{b-1}\ \text{opposite-sign pairs}.
 \tag{I21}
$$

**Proof.** Set $\alpha_i=1$ for $i<b$ and
$\alpha_b=-(b-1)$. Every proper nonempty subset sum of the
$\alpha_i$ is nonzero and has magnitude at most $c_b$: a subset omitting
$b$ has positive sum; one including $b$ has negative sum unless it includes
every other coordinate. Therefore every such subset sum is a unit modulo
both $p_b$ and $q_b$, because each divides $M_b$ and both moduli are
congruent to one modulo $M_b$. In particular each single $\alpha_i$ is a
unit. Primality of the moduli is not required.

For $s\in\{p_b,q_b\}$ identify an alphabet of $s$ positive labels with
$\mathbb Z/s\mathbb Z$ by any bijection and define, on its $b$-fold product,

$$
 Q^{(s)}(x)=\mathbf1_{\sum_i\alpha_i x_i=0\pmod s}
             -\mathbf1_{\sum_i\alpha_i x_i=1\pmod s}.
 \tag{I22}
$$

The displayed residues refer to the alphabet labels' chosen indices, not
to their numerical values as centered coordinates. Along a proper
all-positive varying block, the coefficient of its common parameter is a
unit, so each of the two congruences has exactly one solution. Its line
sum is zero, with all fixed outside coordinates accounted for. Along a
mixed-sign block no point can lie in the positive-alphabet support.
The all-positive full body has $s$ positive cells and no negative ones,
because $\sum_i\alpha_i=0$; every other full body misses the support.
For any fixed values of all coordinates except coordinate $i$, each
congruence has exactly one solution for $x_i$, and the solutions differ.
Hence the two hyperplanes are disjoint, have $s^{b-1}$ cells each, and
pair along coordinate $i$.

Use two positive copies of $Q^{(p_b)}$ and one negative copy of
$Q^{(q_b)}$, on pairwise disjoint positive alphabets. The supports are
disjoint, proper line contractions vanish, and the remaining body sum is
$2p_b-q_b=1$. This proves (I21) and all assertions. Reflecting whole
coordinates gives the corresponding pure selector for any signed body.
QED.

This selector is a finite numeric template that is already pairable, unlike
an arbitrary signed integer lift. Realizing scalar $dQ_b$ by prime entries
still requires the stated number of disjoint prime pairs of difference
$d$, available labels, and global support packing. Lemma PS does not
supply those analytic or geometric resources.

The pair counts in (I21) are $7,43,2883,447747,27626617203$ for
$b=2,3,4,5,6$. The first construction tried coefficients
$(1,2,4,\ldots,-(2^{b-1}-1))$, but the equal positive coefficients above
prove the same nonvanishing property with $c_b=b-1$ and much smaller
constants. No optimality is claimed.

### 6.2. Integer expander flow with compatible-vector values

Let $A$ be any finite integer incidence matrix whose rows have at most
$n$ nonzero entries, each $+1$, and put $\Lambda=A\mathbb Z^N$.
Every $v\in\operatorname{span}_{\mathbb R}\Lambda$ admits
$v'\in\Lambda$ with

$$
 \|v-v'\|_\infty\le n/2.
 \tag{I23}
$$

Indeed choose a real lift $a$ with $Aa=v$, round its entries to nearest
integers, and use $v'=A\operatorname{round}(a)$. This estimate concerns
the rounded image; it does not require a small preimage. All integer
compatibility conditions are preserved because $v'$ belongs to the
actual image lattice.

**Lemma MF.** Let a loopless graph on $p$ vertices have maximum degree
$\Delta$ and admit a real zero-sum flow operator of sup norm at most
$L_p$ (for example the tensor-expander source's Green operator). Given
demands $d_v\in\Lambda$ with $\sum_vd_v=0$ and
$\max_v\|d_v\|_\infty\le E$, there are edge flows $f_e\in\Lambda$
with the prescribed divergences and

$$
 \max_e\|f_e\|_\infty
 \le L_pE+\frac n2+\frac{\Delta pn}{4}.
 \tag{I24}
$$

**Proof.** Apply the scalar real flow operator independently in every
target coordinate. Each resulting edge vector is a real linear combination
of the compatible demands, hence belongs to
$\operatorname{span}_{\mathbb R}\Lambda$. Round it inside $\Lambda$
using (I23). The new integer vertex residual is in $\Lambda$, has total
zero, and has norm at most $\Delta n/2$. On a spanning tree repair it by
subtree sums of residual vectors. The sum over either side of a tree cut
can be used, so an edge repair has norm at most
$(p/2)(\Delta n/2)$. All sums stay inside $\Lambda$. Adding the edge
rounding error $n/2$ and the real-flow bound proves (I24). QED.

For a bounded-degree fixed-gap graph and $p=O_k(n)$, this is
$O_k(E\log n+n^2)$. The lemma avoids the invalid step of independently
rounding compatible line targets coordinate by coordinate. It supplies
integer compatible *vector coefficients* on a marker graph. A physical
controller must still decompose those vector coefficients into its allowed
local templates and prove congestion bounds; (I24) alone does not do that.

## 7. Reproducible diagnostics and limits

The dimension-parameterized source
[hyperk_incidence.py](../code/hyperk_incidence.py) generates canonical signed
blocks and independent geometric line sets, all partition identities, the
integral anchored axis-kernel reduction, exact finite Smith certificates,
the marker weight certificate, the rank recurrence, and symbolic cuboid
signatures. Its finite controls include negative cases for omitted lines,
wrong signs, broken shared traces, and small-order torsion. The source
does not label integer targets as arrangements.

Run its self-test from the repository root. Exact commands and outcomes
are recorded by the coordinator at the frozen scientific revision.
The elementary proof above is the all-$k$ argument; a list of tested
dimensions cannot replace it. In particular diagnostic evaluations at
$k=5,6$ check the formulas and interfaces, not growing-$k$ asymptotics.

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyperk_incidence.py self-test
python3 -B problems/prime-arrays-beyond-square/code/hyperk_incidence.py markers 6
python3 -B problems/prime-arrays-beyond-square/code/hyperk_incidence.py selector 6
python3 -B problems/prime-arrays-beyond-square/code/hyperk_incidence.py smith 6 3 --output /tmp/hyperk-incidence-k6-n3.json
python3 -B problems/prime-arrays-beyond-square/code/hyperk_incidence.py verify problems/prime-arrays-beyond-square/inputs/hyperk-incidence-k6-n3.json
```

The retained exact order-three diagnostics are:

| Dimension | Full lines | Full rational rank | Array-kernel rank | Nonunit invariant factors |
|---|---:|---:|---:|---|
| 2 | 8 | 7 | 2 | $3$ once |
| 3 | 49 | 27 | 0 | $3$ three times; $6$ once |
| 4 | 272 | 81 | 0 | $3$ four times; $6$ once |
| 5 | 1441 | 243 | 0 | $3$ five times; $6$ once |
| 6 | 7448 | 729 | 0 | $3$ six times; $6$ once |

The code first uses the inherited deterministic unit-pivot preconditioner
to keep coefficient growth small, then records the unchanged elementary
Smith reducer's row/column operations. Replay regenerates the reduced
matrix directly from the anchored integral basis and verifies the complete
unimodular operation log, all zero entries and the divisibility chain.
The finite image is not saturated at any of these displayed cases; none
lies in IK's proven stable range. These certificates are not array or
prime-target certificates.

The monic lift was tested on nonconstant structured targets at
$(k,n)=(2,9),(3,27)$, and separately with entry congruence $3\pmod n$,
so the residue modulus cannot be inverted. Pure selectors were checked
by direct complete signed-line images in dimensions two through four,
with opposite-sign pairing along every coordinate. Marker inequalities,
stable rank formulas, and exact selector parameters were evaluated through
dimension six. No finite test substitutes for the proofs in Sections 2–6.

## References and source boundary

The geometry and the low-dimensional comparison are pinned to
Mira-Cult/math-wip scientific source
`b837e307fc41975d0fb332c8215d6835ba47a271`, delivered at
`112c2bca0d38f82391a34994b63153e7ec08aa74`, and the cube source
`a2445962ec6e06b2a893980fb7a183057eb9bcee`. The new polynomial
argument is proved here and uses no imported prime-distribution result.
Conventional proof, independent mathematical review, finite computation,
remote CI and kernel verification remain distinct statuses.
