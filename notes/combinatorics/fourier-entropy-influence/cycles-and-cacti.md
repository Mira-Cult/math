# Boolean spectral arithmetic, cycles, and cacti

**Mira Cult · 16 November 2026**

Positive Boolean Fourier laws that factor into unary and pairwise potentials on
a cactus satisfy $`H(f)\le4I(f)`$, with no bound on the number of cycles. The
same constant holds when deleting one spectral vertex leaves a forest.
The common arithmetic theorem is broader: it forces powers-of-two Walsh
magnitudes whenever the suspended graph has no $`K_5`$ minor, in particular
for every pairwise graph of treewidth at most two. The latter arithmetic
conclusion by itself does **not** establish FEI for all treewidth-two laws.
A separate [bounded-treewidth entropy proof](bounded-treewidth.md) now
covers every positive width-two law with constant below fourteen, including
genuine triangle potentials. The constant-four scope proved here is unchanged.

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

Throughout f:{0,1}^n -> {-1,1} is Boolean,

    W_f(s)=sum_x f(x)(-1)^(s dot x),
    fhat(s)=2^(-n)W_f(s),     p_f(s)=fhat(s)^2.

A positive spectral law has W_f(s)!=0 at every index. Factorization over G
means a product of unary and pairwise nonnegative potentials on G; positivity
makes the occurring potentials strictly positive. Entropy is in bits.

## 1. Main statements

For a graph G let G^+ denote its suspension: add a new vertex 0 adjacent to
every vertex of G.

**Theorem 1 (arithmetic rigidity).** If p_f is positive, factors over G,
and G^+ has no K_5 minor, every |W_f(s)| is a power of two. In particular the
conclusion holds whenever G has treewidth at most two.

The earlier forest theorem used min-sum localization to one- or two-coordinate
cylinders. A cycle permits a different obstruction to localization. The proof
here identifies that obstruction with a cut-polytope cycle face and proves
that the corresponding modular Fourier support is rigid for Boolean functions.

**Corollary 2 (FEI beyond forests).** Suppose p_f is positive and factors
over a graph G such that G-r is a forest for some vertex r. Then

    H(f)<=4 sum_{i!=r} Inf_i(f)<=4I(f).             (1)

No restriction on Fourier magnitudes, degree, cycle lengths, interaction
strengths, or dimension is assumed. If G itself is a forest, the original
positive-forest theorem also applies. A graph G-r may contain many connected
components, and G may have arbitrarily many cycles through r.

**Proof from Theorem 1.** Adding r to every edge/vertex bag of a forest
decomposition gives a tree decomposition of G of width at most two. Theorem 1
therefore supplies the power-of-two magnitudes. Condition on the spectral
bit S_r. Each remaining law is a positive forest law. Apply Theorem 3 of
[Spectral conditioning beyond forests](spectral-conditioning.md), with
k=1. That theorem uses the integer-valued sections

    (f(x_r=0,y)+(-1)^a f(x_r=1,y))/2 in {0,-1,1}

and exactly cancels the label entropy; the sections are not incorrectly
declared Boolean. ∎

The same statement holds after removing fixed spectral coordinates and
contracting deterministic equality/inequality spectral edges if the resulting
positive quotient graph satisfies the stated graph hypothesis. The previously
proved parity quotient preserves Booleanity and entropy and cannot increase
influence. Genuine three-state edge supports remain outside this corollary.

**Theorem 2a (positive cactus FEI).** If p_f is positive and factors over a
cactus graph, then H(f)<=4I(f). Here a cactus is a graph each of whose edges
belongs to at most one simple cycle. Neither the number nor the lengths of
the cycles are bounded. If the minimal interaction graph has a cycle, the
proof constructs a spectral cutset K and gives the stronger bound

    H(f)<=4 sum_{i notin K} Inf_i(f)-2.             (1a)

The proof, including the cost of conditioning on all of K, is in Section 6.

## 2. A modular support-rigidity lemma

Let p be an odd prime. Fourier coefficients can be reduced modulo p because
2 is invertible in F_p. On the d-variable sign cube, the functions
chi_A(x)=product_{i in A}x_i form a basis over F_p: the Walsh matrix has
inverse 2^(-d) times its transpose in this field.

**Lemma 3.** Let

    L(x)=c_0+sum_{i=1}^d c_i x_i

over F_p. If L(x)^2=1 on the sign cube, exactly one of c_0,c_1,...,c_d is
nonzero, and that coefficient is 1 or -1.

**Proof.** Reduce x_i^2=1 and compare the unique Walsh coefficients in
L^2=1. The coefficient of x_i is 2c_0c_i, and the coefficient of x_ix_j
for i!=j is 2c_ic_j. Since p is odd, these equalities make the products
of every two distinct c_i, including c_0, zero. At most one coefficient
is nonzero. The constant equation sum_i c_i^2=1 then makes it a sign.
∎

Let

    A_d={0,e_1,...,e_d} subset F_2^d.

**Lemma 4 (lifting modular support).** Suppose a Boolean function F on
variables (x,z,y), where x has d sign coordinates and z has one sign
coordinate, has all Fourier coefficients outside

    A_d x F_2 x F_2^(dim y)

equal to zero modulo p. Then all those coefficients are exactly zero over
the rationals.

**Proof.** After reducing its Fourier expansion modulo p, for each fixed
(z,y) the function of x is affine linear. Since actual F takes only signs,
its reduction squares to one. Lemma 3 says the reduction is exactly a sign
or a signed single coordinate. The two integers 1 and -1 are distinct
modulo p. Therefore the actual Boolean function of x is precisely that
same real sign or signed coordinate. For every fixed (z,y) its exact real
Fourier coefficients of x-degree at least two vanish. Transforming also
in (z,y) proves the asserted global vanishing. ∎

The lemma allows arbitrary dependence on the outside variables y. Treating
them as scalar coefficients before fixing y would lose the Boolean lifting
step. It also allows some coefficients inside the displayed support to vanish.

## 3. Cycle equality sets have the required affine normal form

Let C=(v_1,...,v_l,v_1), l>=3, be a simple cycle on spectral coordinates.
For a spectral bit vector s put

    x_i(s)=s_(v_i) xor s_(v_(i+1)),

with v_(l+1)=v_1. The cut vector x(s) has even parity around C. Fix an odd
subset F of its l edges and put

    u_i(s)=x_i(s) xor 1[i in F].

The vector u has odd parity. Define the cycle equality set

    T(C,F)={s_C : sum_i u_i(s)=1}.                  (2)

This is the set where the valid cycle inequality

    sum_{i in F} x_i - sum_{i notin F} x_i <= |F|-1

is tight. Its slack is sum_i u_i-1, a nonnegative even integer.

**Lemma 5.** The map

    s_C -> (u_1,...,u_(l-1), s_(v_1))

is an invertible affine map over F_2, and it sends T(C,F) to

    A_(l-1) x F_2.                                (3)

**Proof.** Starting from s_(v_1) and the first l-1 edge differences, one
recovers the successive vertex bits uniquely. Thus the map is affine
invertible. Odd parity fixes u_l=1 xor u_1 xor ... xor u_(l-1).
There is exactly one 1 among all l coordinates precisely when the first
l-1 coordinates are either all zero or a unit vector. ∎

An invertible linear change of spectral coordinates permutes the physical
cube by the inverse transpose; a spectral translation multiplies the physical
function by a character. Both preserve Booleanity and permute the integer
Walsh coefficients up to signs. Applying Lemmas 4 and 5 gives:

**Corollary 6.** If p divides W_f(s) for every s with s_C outside T(C,F),
then W_f(s)=0 for every such s.

This assertion holds for every odd prime, not only three, and with arbitrary
extra variables outside C. The set T(C,F) is proper when l>=3, because
2l<2^l.

## 4. The precise cut-polytope input

For a finite graph H, CUT(H) is the convex hull of its 0/1 cut vectors.
We use the following established description, not a new polyhedral theorem:

**Barahona–Mahjoub [BM86, Corollary 3.10, pp. 169–170].** If H has no
K_5 minor, CUT(H) is defined by

    0<=x_e<=1

for edges e not contained in a triangle, and

    x(F)-x(C\F)<=|F|-1                             (4)

for each chordless cycle C and each odd subset F of its edges. Their
Theorems 3.3 and 3.4 identify these as the facet inequalities. The paper
uses “not contractible to K_5”; the no-minor hypothesis used here is
sufficient. Its cut polytope is full dimensional.

Primary source: F. Barahona and A. R. Mahjoub, *On the cut polytope*,
Mathematical Programming 36 (1986), 157–173,
DOI 10.1007/BF02592023. Author-hosted PDF:
https://www.lamsade.dauphine.fr/~mahjoub/Papers/BM86.pdf.
The source text of Corollary 3.10 and the preceding facet statements was
inspected for this proof; this is an external mathematical dependency,
not a locally re-proved classification of all cut-polytope facets.

We only use the following immediate consequence: a proper face of CUT(H)
is contained in the equality set of at least one inequality from this
description. For example, the average of all vertices of that face lies
on the boundary, so at least one defining inequality is tight there;
nonnegative slacks then make it tight at every vertex of the face.

## 5. Proof of arithmetic rigidity

Put A(s)=|W_f(s)|. Positive pairwise factorization gives the canonical
rational factorization

    A(s)=A(0) product_i r_i^(s_i)
                   product_{ij in E(G)} r_ij^(s_i s_j),

where r_i=A(e_i)/A(0) and
r_ij=A(e_i+e_j)A(0)/(A(e_i)A(e_j)). The formulas follow by taking logarithms
and their ordinary multilinear coefficients; interactions of order at least
three vanish, and nonedges have r_ij=1. All factors are positive rationals.

Suppose an odd prime p divides at least one A(s). Taking valuations gives
an integer quadratic energy

    V(s)=v_p(A(s))=c+sum_i h_i s_i+sum_ij J_ij s_i s_j.  (5)

All its values are nonnegative. Its minimum is zero: if p divided every
W_f(s), integer Walsh inversion would force p to divide 2^n f(x), which
is impossible. Thus its minimizing set

    D={s:V(s)=0}

is nonempty and proper.

Every pattern on one or two spectral coordinates occurs in D. Otherwise
p divides every W_f(s) in that pattern's cylinder. The Boolean cylinder
divisibility lemma in
[forest-arithmetic.md, Lemma 1](forest-arithmetic.md#1-a-boolean-cylinder-divisibility-lemma)
then makes that cylinder identically zero, since p>2 for two coordinates
and p>1 for one coordinate. This contradicts the assumed full spectral
support. For clarity, the lemma follows by taking the partial Walsh sum
on the one or two physical coordinates. It is even, has magnitude at most
2 or 4, and is divisible by p after inverting the remaining Walsh transform
modulo p. The only such even multiple is zero.

Now form H=G^+, set the hub spectral bit s_0=0, and let X(s) be the cut
vector of s on H. Thus

    X_(0i)=s_i,       X_(ij)=s_i+s_j-2s_i s_j.

Substituting s_i s_j=(X_(0i)+X_(0j)-X_(ij))/2 turns V into a real affine
linear functional of X. Consequently the convex hull of X(D) is the
proper minimizing face of CUT(H) for that functional.

Let q be the average of X(s) over s in D. A bound inequality for an edge
not in a triangle is strict at q. Indeed every edge of G belongs to a
triangle with the hub; the only remaining edges of H are hub edges for
isolated vertices, and both states of every such coordinate occur in D.

Every chordless cycle of H containing the hub is a triangle (0,i,j).
For its four odd-set inequalities, the slack at X(s) is twice the indicator
of one of the four patterns of (s_i,s_j). Each pattern occurs in D, so all
four slacks are strictly positive at q. Thus none of these inequalities
can contain the minimizing face.

By the exact polytope description in Section 4, some remaining defining
cycle inequality is tight at q. Its chordless cycle C lies entirely in G.
Since its slack is nonnegative at every cut, it is tight at every s in D.
Hence

    D subset {s : s_C in T(C,F)}

for the odd edge subset F in that inequality. Equivalently, p divides
every W_f(s) with s_C outside T(C,F). Corollary 6 then makes every one of
those coefficients exactly zero. The set is nonempty by l>=3, contradicting
positivity. No odd prime can divide a nonzero A(s), proving Theorem 1 under
the suspension hypothesis.

Finally, if G has a tree decomposition with bags of size at most three,
adding the hub to every bag gives a decomposition of G^+ with bags of size
at most four. Treewidth is minor-monotone: deletion preserves a decomposition,
and contracting an edge is implemented by replacing its two endpoint names
by one. Any tree decomposition of K_5 has a bag containing all five
vertices, because its five vertex-subtrees intersect pairwise and connected
subtrees of a tree have the Helly property. Thus K_5 has treewidth four,
whereas G^+ has treewidth at most three. It has no K_5 minor. ∎

## 6. Paying for unboundedly many cactus cycles

For a positive law the minimal interaction graph is defined by the nonzero
pairwise coefficients in the multilinear expansion of log p_f. If the law
factors over a cactus, this minimal graph is also a cactus. We use only this
minimal graph, so an edge used below is a genuine nonzero interaction.

**Lemma 7 (cactus cutset with witnesses).** Let G be a finite cactus having
at least one cycle. There is a nonempty vertex set K, of size k, such that
G-K is a forest and has at least k connected components containing an edge.

**Proof.** In any connected cactus having a cycle, choose a cycle C that is
a leaf among the cyclic blocks in its block-cut tree: branches from C may
contain trees, but all the other cyclic blocks, if any, are reached through
one vertex v of C. Such a C exists by taking an end of the minimal subtree
joining the cyclic block nodes. If C is the only cyclic block, choose any
vertex v of C instead.

Delete v and put it in K. The component containing C minus v is now a forest:
the remaining cycle edges form a path, and all branches attached to this
path are trees. The path has at least one edge because |C|>=3. Freeze this
component and never select a vertex from it. Repeat the construction in
each remaining component that still contains a cycle. At each step the
number of cyclic blocks decreases, so the process ends with a forest.
Each selected vertex has produced a distinct frozen edge-containing
component, and later deletions occur outside it. These k components remain
distinct components of G-K. ∎

Every cactus has treewidth at most two. For a cycle v_1,...,v_l, its bags
{v_1,v_j,v_(j+1)}, 2<=j<=l-1, form a width-two decomposition. Edge blocks
use their two endpoints, and the decompositions of different blocks can
be joined at bags containing their common articulation vertex along the
block-cut tree. Disconnected components can be joined arbitrarily without
changing bag sizes.

**Proof of Theorem 2a.** If the minimal graph is a forest, use the original
positive-forest theorem. Otherwise take K from Lemma 7. Theorem 1 supplies
power-of-two Fourier magnitudes, because the cactus has treewidth two.
For each spectral assignment a to K, conditioning leaves a positive forest
law on G-K. All its internal pairwise coefficients remain unchanged;
only unary fields can change. Thus each of the k frozen edge-containing
components is nonconstant under every assignment a.

Use the refined integer-packet estimate of Theorem 1 in
[the spectral-conditioning proof](spectral-conditioning.md). For the
integer section h_a=2^(k-1)g_a its raw entropy is at most

    4I(h_a)-2k w(h_a).

Scaling back and summing over the disjoint spectral rows gives exactly

    H(f)<=4I_(outside K)(f)+(2k-2)-2k
         =4I_(outside K)(f)-2.

This proves (1a) and hence constant four. The denominator cost grows with
the number of cuts, but the nonconstant-component slack pays for it with
the same coefficient. No cycle count or dimension remains in the final
constant. ∎

More generally the same proof gives a useful structural estimate. If G
has treewidth at most two and a feedback vertex set K of size k>=1 such
that G-K has b components containing genuine interaction edges, then

    H(f)<=4I_(outside K)(f)+2(k-1-b).               (5a)

In particular constant four follows whenever b>=k-1. The common-vertex
case has k=1 and needs no witness component; cactus graphs have b>=k.
This criterion is false as a graph-only assertion for all graphs of treewidth
two. Here is a small exact obstruction to that proposed extension. Let G
be the square of the 11-vertex path: vertices 1,...,11 are joined when their
distance along the path is one or two. The consecutive triple bags give
a width-two decomposition. For any feedback vertex set K of size k,
write b for the number of edge-containing components of G-K. Then

    b<k-1.                                         (5b)

To prove this, observe first that G-K is a forest exactly when no three
consecutive vertices survive. The necessity comes from its consecutive
triangles. For sufficiency, scan surviving vertices from left to right:
the addition of one new vertex can have two earlier neighbors only when
the preceding two consecutive vertices also survive, making such a
triangle. Without that case, each addition creates no cycle.

Separate components of G-K require at least two consecutive deleted
vertices between their surviving vertices. Hence b<=floor(k/2)+1. If
b>=k-1, this forces k<=4. Two or fewer deletions cannot break every
consecutive triple on 11 vertices. With k=3, eight vertices survive; all
four runs between deletions must have length exactly two, so all three
deletions are isolated and G-K is connected, giving b=1<2. With k=4,
b>=3 would require two separators using all four deletions in two pairs.
The seven survivors would then occupy three runs, each of length at most
two, which is impossible. This proves (5b).

The accompanying checker exhausts all 2047 nonempty K and obtains
min(k-1-b)=1. This graph obstruction refutes only the proposed component
payment for every width-two graph. It neither constructs a Boolean spectral
law on G nor refutes FEI for such a law. A sharper energy payment within
the remaining connected forest could still handle it.

## 7. Scope, examples and next obstruction

The explicit 12-variable genuine four-cycle Boolean spectrum and the
infinite families in
[the spectral-conditioning note](spectral-conditioning.md#5-explicit-genuine-cycle-witness-and-scope-of-the-example)
show that Corollary 2 covers spectra that admit no forest factorization in
their given coordinates. The four-cycle logarithmic interaction is certified
exactly. As documented there, the displayed construction itself has an
earlier entropy proof; the theorem's statement covers every compatible
Boolean signing and does not assume that construction.

Theorem 1 applies to all positive pairwise Boolean spectral laws of treewidth
two. Theorem
2a handles the full cactus subclass, with unboundedly many separated or
articulation-sharing cycles. For the remaining treewidth-two graphs the
unpaid term in (5a) is explicit. A dimension-independent energy payment
for the remaining connected forest pieces, or a better paid decomposition
into the integer packets, is the next unresolved estimate.

The first obstruction beyond this arithmetic proof is exact: for suspensions
with a K_5 minor the edge/cycle inequalities need not describe the whole cut
polytope. An odd-prime valuation may minimize on another facet. One must
either prove an appropriate replacement for modular Boolean support rigidity
on the additional equality sets or find a different argument. The literal
extension of that rigidity is already false, as the following exact small
counterexample shows.

The K_5 clique max-cut facet has, with the hub fixed, equality set

    D={s in {0,1}^4 : |s| is 2 or 3}.

Let f on four physical 0/1 variables be +1 exactly when the physical
Hamming weight is at least three, and -1 otherwise. Its unnormalized Walsh
coefficients in little-endian order are

    (-6,-6,-6,2,-6,2,2,2,-6,2,2,2,2,2,2,-6).

Modulo three its Fourier support is exactly D, although every coefficient
outside D is the nonzero integer -6. Thus the modular lifting statement for
this noncycle facet fails for an actual Boolean function. This function's
positive magnitude law does not factor pairwise: the logarithmic magnitude
indicator has a nonzero three-way difference. Consequently the example
refutes the attempted facet-by-facet lifting extension, not the assertion
that all positive pairwise Boolean spectra might still be dyadic. Treating
that latter assertion as proved would nevertheless be unjustified.

The proof uses Booleanity twice: the partial-Walsh cylinder bound and the
unique lifting of field-valued signs in Lemma 4. Positivity is used to
turn every modular support exclusion into a contradiction and to make the
canonical rational factorization valid. Forest factorization is no longer
used in the arithmetic theorem; it is still used after spectral conditioning
in the entropy corollary. The existing minimum-layer and tree-energy
induction enter exactly through the integer forest-packet theorem.

## 8. Exact finite verification

Run from this note directory:

    python code/check_cycle_facet_arithmetic.py
    python code/check_dyadic_feedback_forest.py

The first program checks every odd-edge cycle normal form in lengths 3--8,
the modular lifting implication for every three- and four-variable Boolean
function at primes three and five, the exact K_5-facet counterexample,
200 explicitly constructed cactus graphs (fixed seed 20261116), and every
cutset of the displayed 11-vertex graph. The second checks the exact
12-variable Boolean cycle construction, 65,814 Boolean functions and their
eligible one-/two-bit spectral cuts, and 6,654 integer-valued ternary
functions with their eligible forest spectra. The tests use exact integer
or rational arithmetic; the only logarithm comparisons in the counterexamples
are certified by explicit integer inequalities. These finite checks do not
replace the general proofs, the external cut-polytope theorem, independent
review, or a literature-priority assessment.
