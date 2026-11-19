# Fourier entropy–influence for positive Boolean spectral forests

**Mira Cult · 16 November 2026**

Every Boolean function with a full-support forest-factorizing Fourier law
satisfies $`H(f)\le4I(f)`$. This note gives the complete proof: a
minimum-layer degree bound, a range/degree induction, and a simultaneous
tree-energy and cross-field induction. The odd-prime exclusion used here
is proved in [forest-arithmetic.md](forest-arithmetic.md).

For a nonconstant positive law, the later Boolean parity refinement gives
the stronger $`H(f)\le4I(f)-2-2c`$, where $`c`$ counts nonconstant
energy components; see [mixtures-and-obstructions.md](mixtures-and-obstructions.md).
The proof below retains the integer-valued minimum-layer lemma needed by
the spectral-conditioning extension.

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

All Fourier normalizations are those in [the earlier arithmetic theorem](forest-arithmetic.md):
`W_f(s)=2^n fhat(s)` and entropy is in bits. “Positive” means every spectral
atom has positive probability. An interaction graph is the minimal graph
of the logarithm of a positive law; constant edge potentials are deleted.

## 1. A minimum-layer consequence of integer Walsh inversion

**Lemma 1.** Let `f:{0,1}^n -> Z`, let

    m=min_{s:W_f(s) != 0} v_2(W_f(s)),
    P(s)=1[W_f(s)/2^m is odd].

For nonzero f, the algebraic degree of P over F_2 is at most m. If m>=n,
this conclusion is automatic. Signs of the Walsh coefficients do not
enter P.

**Proof.** Suppose m<n and put `b_s=W_f(s)/2^m`. Walsh inversion gives

    sum_s b_s (-1)^(s dot x)=2^(n-m) f(x).

Both sides are integer-valued on the cube. Every coefficient of the
multilinear polynomial in the 0/1 physical coordinates x on the right
is divisible by `2^(n-m)`, since these coefficients are integer finite
differences of its values. On the left, the coefficient of x_T is

    (-2)^|T| sum_{s superset T} b_s.

Consequently `sum_{s superset T} P(s)=0` in F_2 whenever `|T|<n-m`.
The coefficient of the monomial x_U in the algebraic normal form of
`P(1+x)` is exactly `sum_{s superset U^c} P(s)`. It vanishes for `|U|>m`.
Complementing coordinates preserves algebraic degree, proving the claim.
∎

This is a Walsh divisibility / Reed–Muller observation, not a claimed new
principle. For a pure-powers-of-two Walsh magnitude array, P is precisely
the indicator of its smallest nonzero magnitude layer.

## 2. Range and the degree of the minimizing set on an integer tree

Let T be a tree with n>=2 vertices. Consider an integer quadratic energy

    E(x)=c+sum_i h_i x_i+sum_{ij in T} J_ij x_i x_j,
    h_i,J_ij,c in Z,   J_ij != 0.

All 2^n states are allowed. Define

    K(E)=max_x E(x)-min_x E(x),
    P_E(x)=1[E(x)=min E],
    delta(E)=deg_F2 P_E,    kappa(E)=n-delta(E).

**Theorem 2 (root-field strengthening).** Fix any root r and vary only
its integer unary field. Write `E_t=E+t x_r` and
`R=min_{t in Z} K(E_t)`. Then

    kappa(E_t) <= R     for every integer t.              (1)

Moreover, at most one integer t satisfies

    kappa(E_t)=K(E_t)=R.                                 (2)

In particular every such energy satisfies

    delta(E)+K(E) >= n.                                  (3)

The conclusion is not asserted for hard-zero / forbidden states. Nor
may nonzero interactions be replaced by artificially drawn constant
edges: a constant energy on n free bits has delta=K=0.

### Proof

We prove the two assertions together by induction on the number of
vertices. We first record the one-vertex boundary calculation used in
the induction. For a one-bit energy `a x`:

    K(a)=|a|,
    kappa(a)=1 if a=0, and 0 otherwise.

For distinct integers a,b this gives the cross inequalities

    kappa(a)<=K(b),     kappa(b)<=K(a).                  (4)

If both are equalities, exactly one field is zero and the other is +1
or -1. Thus one minimizing-set indicator is the constant one, while
the other has degree one.

Now root an n-vertex tree at r. Its child subtrees have disjoint variable
sets. Conditional on root value b, the energy is a constant plus a sum
of child energies `E_{j,b}`. The two fields at the root of child j differ
by `J_{rj}`, a nonzero integer.

For a child containing at least two vertices, the inductive hypothesis
implies

    kappa(E_{j,0}) <= R_j <= K(E_{j,1}),
    kappa(E_{j,1}) <= R_j <= K(E_{j,0}),                  (5)

where R_j is its minimum range over all integer fields at its root.
Both cross inequalities cannot be equalities: that would make the two
distinct fields satisfy (2), contradicting the uniqueness assertion of
the induction. For a one-vertex child, (4) supplies the same cross
inequalities, and describes their simultaneous equality case.

Let m_b and M_b be the conditional minimum and maximum energies before
the varying root field is added. Put

    K_b=M_b-m_b=sum_j K(E_{j,b}),
    kappa_b=sum_j kappa(E_{j,b}).

The second identity follows because the conditional minimizing-set
indicator is a product over disjoint child blocks, so its algebraic
degrees add. Summing (4)--(5) gives

    kappa_0<=K_1,      kappa_1<=K_0.                    (6)

Let tau be the difference between the two conditional minima after the
root field is added. It runs through all integers. After subtracting
the zero-branch minimum, the two conditional energy intervals are
`[0,K_0]` and `[tau,tau+K_1]`. Thus

    K(tau)=max(K_0,tau+K_1)-min(0,tau),
    R=max(K_0,K_1).                                    (7)

The value R is attained by tau=0.

If tau>0, the global minimizing-set indicator is `(1+x_r)P_0` and hence
its deficiency is kappa_0. If tau<0 it is `x_r P_1` and its deficiency is
kappa_1. Equation (6) proves (1) in both cases.

Suppose tau=0. The minimizing-set indicator is

    P=P_0+x_r(P_0+P_1).                                (8)

If the two degrees differ, or their highest homogeneous parts differ,
then the deficiency of P is `min(kappa_0,kappa_1)`, which is at most R.
The only remaining case is equal degrees and equal highest homogeneous
parts. In that case the deficiency is

    kappa_0+1=kappa_1+1.                               (9)

If their common value is below R, integrality proves (1). Otherwise
(6) forces `kappa_0=kappa_1=K_0=K_1=R`, so every child must attain both
cross equalities in (4)--(5). No child with at least two vertices can do
so. Therefore all children are single vertices. For every such child,
exactly one conditional ground indicator is constant and the other is
a one-variable indicator. Consequently the highest monomial of P_0
uses exactly the leaves not used by the highest monomial of P_1. There
is at least one child, so these monomials differ. This contradicts the
cancellation hypothesis in (9), completing the proof of (1).

Finally, if `K_0>K_1`, equation (7) attains its minimum R precisely for
`0<=tau<=K_0-K_1`. At every positive tau in this interval, the ground
set lies in branch zero and has deficiency `kappa_0<=K_1<R`. Hence (2)
can occur only at tau=0. The case `K_1>K_0` is symmetric. If the two
ranges are equal, tau=0 is the unique field minimizing the range at
all. Thus (2) holds for at most one field. This closes the induction.
∎

## 3. Quantitative fair-coordinate requirement for a positive Boolean forest

**Theorem 3.** Let f be Boolean and suppose its squared Fourier law is
strictly positive and factors over a forest. In the minimal interaction
graph, every isolated coordinate is an independent fair spectral bit.
Let q be the number of these bits. For each nontrivial connected component
C, write its primitive positive amplitude array as

    A_C(s_C)=2^(v_C(s_C)),       min v_C=0,
    Z_C=sum_{s_C} 4^(v_C(s_C))=2^(2D_C),
    delta_C=deg_F2 1[v_C=0],
    epsilon_C=D_C+delta_C-|C|.

Then each `2D_C` is an integer, every epsilon_C is a strictly positive
half-integer, and

    q/2 >= sum_C epsilon_C.                            (10)

In particular, when n>0, there is at least one independent fair spectral
coordinate. If the spectrum is not uniform, (10) requires at least one
such coordinate in addition to its nontrivial components.

**Proof.** The earlier forest arithmetic theorem says that all nonzero
Walsh magnitudes are powers of two. Since the law is positive, its
logarithmic amplitude is an integer-valued quadratic polynomial on the
forest. This follows either from the canonical unary/edge log-factor
representation, or by taking its ordinary discrete first and second
differences. Delete zero interaction coefficients. On each component,
subtract its minimum; the resulting v_C has integer coefficients and
nonnegative integer values. The whole Walsh magnitude array is

    |W_f(s)|=2^m product_C A_C(s_C),

where m is its minimum 2-adic valuation. Parseval yields

    4^m product_C Z_C=4^n.                             (11)

Every Z_C is a positive integer, so each is a power of two and

    sum_C D_C=n-m.                                    (12)

For an isolated coordinate, the primitive two-entry amplitude is
`(1,2^k)` or `(2^k,1)`, with integer k>=0. If k>0 its squared norm is
`1+4^k`, an odd integer larger than one, contradicting (11). Hence k=0:
it is independent and fair, with D_C=1/2 and delta_C=0.

For a nontrivial component let `K_C=max v_C`. Theorem 2 gives
`delta_C+K_C>=|C|`. Full positivity and at least two states give
`Z_C>4^K_C`, hence D_C>K_C. Therefore

    epsilon_C=D_C+delta_C-|C|>0.

It is a half-integer because 2D_C, delta_C and |C| are integers.

The indicator of the smallest Walsh magnitude layer is the product of
`1[v_C=0]` across components. Its F_2 degree is `sum_C delta_C`. Lemma 1
and (12) imply

    sum_C delta_C<=m=n-sum_C D_C.

Move the q isolated fair coordinates, each contributing -1/2 to
`D_C+delta_C-|C|`, to the other side. This is (10). ∎

For the existing four-bit path core in [the earlier arithmetic theorem](forest-arithmetic.md),
`D=4`, `delta=3`, and epsilon=3. Consequently any Boolean realization
whose spectral law is that core times independent fair bits requires
at least six fair bits by this integer bound. The Boolean refinement in
[mixtures-and-obstructions.md](mixtures-and-obstructions.md) raises the
necessary number to eight, exactly matching the Kraft/bent construction.

For the six-bit positive path core specified in
[forest-arithmetic.md](forest-arithmetic.md#10-a-six-bit-path-core),
`D=7`, `delta=4`, and epsilon=5. This integer bound requires ten independent
fair bits; the Boolean refinement requires twelve. The explicit completion
uses fourteen.

These statements concern an independent fair completion, not an arbitrary
Boolean completion with correlated auxiliary spectral variables.

## 4. A stronger entropy payment really fails when zeros are admitted

The following tempting strengthening of Theorem 2 is false for laws
with forbidden states, even when a Boolean signing exists:

    E_{4^v}[v+2|S|] >= n-deg_F2 1[v=0].                (13)

Take k>=3, N=2k, a central spectral bit z, N leaves x, and one independent
fair bit t. On branch z=0 all N leaves are free and have primitive
amplitude 1. On branch z=1 only x=0 is allowed and its primitive amplitude
is 2^k. Both values of t are allowed. The primitive squared norm is
`4^(k+1)`. The ground-layer indicator is `1[z=0]`, of degree one. Thus

    n=2k+2,     n-delta=2k+1,
    E v=k/2,   J=k/2+1,
    E[v+2|S|]=3k/2+2<2k+1.

This is an actual Boolean star spectrum. For any bent Boolean h on N
variables, use physical gate coordinates u,v and put

    F(u,v,y)=(1+v)h(y)/2+u(1-v)/2.

The central spectral bit is S_u; the independent fair bit is S_v.
The branch S_u=0 has all N y bits fair, and branch S_u=1 has all of them
zero. Directly `H(F)=k+2`, `I(F)=k/2+1`, so `H(F)=2I(F)`.
The failure of (13) is therefore not a counterexample to FEI.

## 5. A positive-tree Gibbs inequality

For an integer energy E on the full Boolean cube, set

    v=E-min E,       p_E(x)=4^v(x)/sum_y 4^v(y),
    B(E)=E_{p_E}[v(X)+2|X|],
    kappa(E)=n-deg_F2 1[E=min E].

The letter B here denotes this explicitly defined scalar functional, not
an unproved Bellman function. Adding a constant to E changes none of
these quantities. Coordinate labels are the actual 0/1 labels in |X|;
the inequalities below hold with every choice of those labels.

**Theorem 4 (positive-tree energy payment).** Suppose E is an integer
quadratic energy whose interaction graph is a forest, and all states
have positive Gibbs weight. Then

    B(E)>=kappa(E).                                    (14)

If E is nonconstant, the stronger inequality holds:

    B(E)>=kappa(E)+1.                                  (15)

For the connected components with at least one genuine interaction,
we simultaneously prove the following cross-field assertion. Fix a
root r. For any two distinct integer fields a,b at r,

    B(E+b x_r)>=kappa(E+a x_r).                         (16)

Equation (16) also holds for a single vertex. Constant components are
handled by additivity, not by asserting (15) for a constant energy.

### 5.1 The one-bit calculation

For a one-bit energy with nonzero integer field of magnitude M>=1,
the normalized energies are 0 and M. Its minimizing set is a singleton,
so kappa=0. In either orientation its mean cost is at least

    psi(M)=(M 4^M+2)/(1+4^M).

Here `psi(1)=6/5`, and `psi(M)>=2` for M>=2. The latter is immediate
from `(M-2)4^M>=0`. Thus every nonconstant one-bit energy has B>=6/5,
which proves (15). A constant one-bit energy has kappa=B=1 and obeys
(14). For two distinct fields, if the first field is zero then the
second is nonzero and has B>=6/5>=1; otherwise the first deficiency is
zero. This proves (16) on a single vertex.

### 5.2 Conditional notation and the two reusable bounds

For a connected tree with at least two vertices, all interaction
coefficients on its edges are nonzero. Root it at r. For each child
subtree j, the energies conditional on root value 0 or 1 differ by a
nonzero integer field at that child's root. Suppose (14)--(16) have
already been proved for all smaller trees.

For root branch b, subtract its conditional minimum and write its
normalized energy on the remaining coordinates as a sum of child
energies, each normalized to minimum zero. Let P_b be its minimizing-set
indicator. Set

    kappa_b=(n-1)-deg_F2 P_b=sum_j kappa_{j,b},
    B_b=sum_j B_{j,b}.

The second identity is exact because the conditional Gibbs law is a
product across the child subtrees. The same-branch estimate (14) and
the cross-field estimate (16), summed over children, give

    B_0>=max(kappa_0,kappa_1),
    B_1>=max(kappa_0,kappa_1).                         (17)

In addition, every child that is nonconstant in branch b contributes
a full unit of slack through (15). Thus

    B_b>=kappa_b + number of nonconstant children in b. (18)

A child containing at least two vertices is nonconstant in both
branches, since its internal genuine interaction coefficients remain
unchanged. A one-vertex child can be constant in at most one branch.

Let c_b>=0 be the conditional minimum minus the global minimum, and
let q_b be the Gibbs probability of root branch b. The exact global
cost decomposition is

    B(E)=q_0(c_0+B_0)+q_1(c_1+B_1+2).                 (19)

All quantities c_b are integers. At least one is zero. The +2 is the
contribution of the root coordinate on branch one.

For the own-bound proof at size n>=3, choose an internal root at the
outset. If its conditional minima differ, use Section 5.3; if they tie,
use Section 5.4. On two vertices either root is allowed. The cross-field
assertion is proved afterward for every root in Section 5.6, so this
choice creates no circularity and does not presume a tie survives rerooting.

### 5.3 A unique minimizing root branch

If branch one is uniquely minimizing, then `c_0>=1`, `c_1=0`, and
`kappa(E)=kappa_1`. Equation (17) makes the branch-zero cost in (19)
at least `kappa_1+1`, and the branch-one cost at least `kappa_1+2`.
Thus (15) holds directly.

Suppose instead that branch zero is uniquely minimizing. Then
`c_0=0`, `c_1>=1`, and `kappa(E)=kappa_0`. If branch zero contains a
nonconstant child, (18) gives `B_0>=kappa_0+1`; the other branch's cost
is at least `kappa_0+3` by (17) and its minimum gap. Again (15) follows.

If every branch-zero child is constant, the entire normalized conditional
energy is zero. With N=n-1, its partition sum is `Z_0=2^N`, its deficiency
is N, and its mean cost is N. In branch one every normalized energy is a
nonnegative integer, so its partition sum `Z_1` is at least `2^N`.
The positive minimum gap therefore gives

    q_1=4^c_1 Z_1/(Z_0+4^c_1 Z_1)>=4/5.

The cross estimate (17) still gives `B_1>=N`. Consequently (19) gives

    B(E)>=N+q_1(c_1+2)>=N+12/5>N+1.

This proves (15) in every unique-minimum case. Full positivity is used
in `Z_1>=2^N`; it fails for the hard-zero star of Section 4.

### 5.4 Tied minima, for n>=3

The internal root already chosen has at least two children. Such a
root exists in every tree on at least three vertices. Here c_0=c_1=0,
and as in (8), the global minimizing-set indicator is

    P=P_0+x_r(P_0+P_1).

If the two branch degrees differ, or their highest homogeneous parts
do not cancel, the global deficiency is

    kappa(E)=min(kappa_0,kappa_1).

When the deficiencies differ, their integer maximum is at least this
minimum plus one, so (17) proves (15). When they are equal, both branches
must contain a nonconstant child: if one branch had only constant
children, all children would be singletons and its deficiency would be
n-1. Equality of deficiencies would force every other branch child also
to be constant, contradicting the nonzero edge fields. Thus (18) again
gives one unit of slack on both branches and proves (15).

It remains that the branch degrees are equal and their highest
homogeneous parts agree. Write their common deficiency as a. Then

    kappa(E)=a+1.

The highest homogeneous part of P_b is the product of the highest
parts of its child indicators, on disjoint variable blocks. In
particular a singleton child cannot be constant in one branch and
nonconstant in the other: its variable would occur in every highest
monomial on exactly one side, contradicting equality of the highest
parts. Thus every singleton child is nonconstant in both branches.
The same is already true for every child with at least two vertices.
Since the root has at least two children, (18) yields

    B_0>=a+2,      B_1>=a+2.

Equation (19) proves `B(E)>=a+2=kappa(E)+1`, as required.

### 5.5 The two-vertex tied case

The unique-minimum argument above already applies on two vertices.
For tied minima there is one one-bit child. If its two conditional
deficiencies differ, the preceding maximum argument proves (15).
They cannot both be one, because the fields differ by a nonzero
interaction. The only remaining case is that both deficiencies are
zero. Both unary fields are nonzero, with magnitudes M_0,M_1>=1.
Both ground indicators have degree one, so their highest parts cancel,
and the global deficiency is one.

The two conditional partition sums are `Z_b=1+4^M_b`. If M_0>=2, then
`B_0>=psi(M_0)>=2`, while `B_1+2>=6/5+2>2`, so (19) gives B(E)>=2.
If M_0=1, then `Z_0=5<=Z_1`, hence q_1>=1/2, and

    B(E)>=6/5+2q_1>=11/5>2.

Thus (15) holds on two vertices as well.

### 5.6 Closing the cross-field induction

We have proved (15) for every connected n-vertex energy, using only
assertions on smaller trees. Fix now any root r and compare two
distinct fields a,b. The branch indicators P_0,P_1 and deficiencies
kappa_0,kappa_1 do not depend on the root field. Nor do the normalized
conditional child costs B_0,B_1. By (17)--(19), every root field t has

    B(E+t x_r)>=max(kappa_0,kappa_1).                  (20)

If field a has a unique minimizing branch, its deficiency is one of
kappa_0,kappa_1 and (20) proves (16). If a ties the minima, its deficiency
is at most `min(kappa_0,kappa_1)+1`. When the branch deficiencies differ,
(20) again suffices. When both equal a_0, only the cancellation case
`kappa(E+a x_r)=a_0+1` needs attention. Field b cannot also tie the
minima, since there is exactly one tying root field. Thus its deficiency
is a_0, and the just-proved own estimate (15) gives

    B(E+b x_r)>=a_0+1=kappa(E+a x_r).

This proves (16) and closes the simultaneous induction.

Finally, for a forest, Gibbs laws factor across its components; their
B costs and minimizing-set algebraic degrees add. An isolated free bit
contributes exactly one to both B and kappa. Every nonconstant component
has the extra unit proved above. This proves (14), and (15) whenever the
energy is nonconstant. ∎

## 6. The unconditional full-support Boolean forest FEI theorem

**Theorem 5.** If f is Boolean and its squared Fourier distribution has
full support and factors over a forest, then

    H_bits(f)<=4 I(f).                                (21)

If that Fourier distribution is not uniform, the same proof gives

    H_bits(f)<=4 I(f)-2.                              (22)

For a uniform full-support Boolean spectrum, `H(f)=2I(f)=n`. The case
n=0 satisfies (21) with both quantities zero.

**Proof.** By the forest arithmetic theorem, all Walsh magnitudes are
powers of two. Write

    |W_f(s)|=2^(m+v(s)),       min v=0,
    delta=deg_F2 1[v=0].

Because the spectrum is positive, v is an integer quadratic energy
on a forest. Lemma 1 gives delta<=m. Parseval gives

    sum_s 4^v(s)=4^(n-m).

Thus the Gibbs law in Theorem 4 is exactly the Fourier law of f, and

    H(f)=2(n-m-E_p v),
    I(f)=E_p |S|.

By (14), `E_p v+2I>=n-delta>=n-m`, proving (21). When v is nonconstant,
(15) adds one on the left and yields (22). When v is constant, positivity
makes the spectrum uniform, with H=n and I=n/2. ∎

Theorem 3 supplies an additional structural explanation: the positive
nonflat components force independent fair coordinates through (10).
Applying (15) componentwise gives the optional additive refinement
`H(f)<=4I(f)-2c`, where c is the number of nontrivial interaction
components. This refinement is not needed for (21).

**Coordinate-subcube support corollary.** The same constant-four bound
holds if the Fourier support is a coordinate subcube and its law factors
over a forest. Indeed, remove spectral bits forced to zero, and multiply
f by the character on bits forced to one. The resulting Boolean function
has a full-support forest law on the free coordinates. Its entropy is
unchanged, and its influence is `I(f)-|D|`, where D is the set of forced-one
bits. Theorem 5 applies; a zero-dimensional free cube is a character and
has entropy zero. This includes constants and characters, but does not
cover general forbidden-pair support constraints.

## 7. Scope and remaining full-forest problem

This proves a dimension-independent FEI inequality for full-support
Boolean spectral forests. The Fourier signs are arbitrary; no physical
product representation or low-degree assumption is imposed. The proof
uses signed Boolean compatibility through integer Walsh inversion and
the previously established odd-prime exclusion theorem, while the Gibbs
payment itself is a positive integer-tree statement.

General hard-zero forest laws are not covered. Fixed bits and deterministic
equality/complement edges are handled by [deterministic-contractions.md](deterministic-contractions.md). The actual Boolean star family
in Section 4 refutes the direct extension of (14) to energies allowing
forbidden states. A repair for all forests must account for such
forbidden-state selectors differently. General Boolean squared Fourier
laws also need not be forests. Therefore neither the all-forest FEI
problem nor the original universal FEI conjecture is solved here.
