# Spectral conditioning and integer dyadic forest packets

**Mira Cult · 16 November 2026**

A partial Fourier transform of a Boolean function produces an integer-valued
section after an explicit power-of-two rescaling. This note proves the
constant-four raw entropy bound for integer forest sections with
powers-of-two magnitudes, then keeps the full rescaling cost under fixed
and adaptive spectral conditioning. The [cycle-facet theorem](cycles-and-cacti.md)
supplies the magnitude hypothesis for positive pairwise treewidth-two laws.

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

We use normalized Walsh coefficients on the uniform cube, with entropy in
bits. For an arbitrary real-valued function h define the **raw** quantities

    H_*(h)=sum_s hhat(s)^2 log_2(1/hhat(s)^2),
    I(h)=sum_s |s| hhat(s)^2,
    w(h)=E h^2.

Zero coefficients contribute zero; the zero function has all three quantities
zero. H_* need not be nonnegative. For h!=0 the normalized spectral law
q_h(s)=hhat(s)^2/w(h) satisfies

    H(q_h)=H_*(h)/w(h)+log_2 w(h).                 (1)

For Boolean f, H_*(f)=H(f) and w(f)=1. We call a nonzero magnitude
**dyadic** here only when it is exactly an integer power of two, not merely
a rational with a power-of-two denominator. Every Boolean Walsh coefficient
is dyadic rational; the hypothesis used here is strictly stronger.

## 1. The forest estimates used in the proof

The [complete positive-forest proof](positive-forests.md), Lemma 1 and Theorem 4,
supplies the following two statements.

* If h on N variables is integer-valued, m is the least 2-adic valuation
  of a nonzero unnormalized Walsh coefficient, and P is the indicator of
  the coefficients attaining that valuation, then deg_F2 P<=m.
* If v is a nonnegative integer quadratic energy on a forest, with minimum
  zero and with every state allowed, put q(s)=4^v(s)/sum_t4^v(t) and
  delta=deg_F2 1[v=0]. Then

      E_q[v+2|S|]>=N-delta+c(v),                   (2)

  where c(v) counts the connected components on which v is nonconstant.
  A one-vertex component with a nonzero unary field counts. Free coordinates
  do not count. Equation (2) follows by summing the source's componentwise
  own bounds; its simultaneous cross-field induction is essential.

Neither statement says that an arbitrary positive forest probability law is
Boolean-realizable. The first statement is precisely the extra arithmetic
input retained below. We do not need to extend the Boolean odd-prime
exclusion theorem to integer functions; that extension is false.

## 2. Integer forest packets with unrestricted amplitude spread

**Theorem 1.** Let h:{0,1}^N -> Z be nonzero. Suppose its Fourier spectrum
has full support, every Fourier magnitude is an integer power of two, and
its normalized squared Fourier law factors over a forest. Then

    H_*(h)<=4 I(h)-2 c(v) w(h)<=4 I(h).            (3)

There is no upper bound on the spread of the Fourier magnitudes.

**Proof.** Write its positive unnormalized Walsh magnitudes as

    |W_h(s)|=2^(m+v(s)),   min_s v(s)=0.

Because h is integer-valued, m is a nonnegative integer. Positive forest
factorization makes v an integer quadratic polynomial on that forest:
the ordinary first and second differences of the integer-valued logarithm
give integer coefficients, while all other interactions vanish. The
minimum-layer lemma gives delta<=m. Parseval gives

    Z=sum_s4^v(s)=4^(N-m) w(h).

Consequently the normalized spectral law is exactly the Gibbs law in (2),
and

    H_*(h)/w(h)=2(N-m-E_q v)
              <=4 E_q|S|-2c(v).

Multiplication by w(h) proves (3). This proof also covers N=0: a nonzero
integer h with power-of-two magnitude has H_*(h)<=0=I(h). ∎

The same conclusion without the c(v) refinement applies to the following
zero cases. First remove globally fixed spectral coordinates. Then contract
deterministic equality/inequality spectral edges. If the resulting law has
full support and factors over a forest, Theorem 1 applies to the quotient.
The power-of-two magnitude hypothesis is still required.

Here is the complete integer-valued justification for this reduction. A fixed
spectral bit can be removed by character multiplication and deletion of its
physical coordinate; integer values and the L2 norm are preserved. For a
deterministic block C of r coordinates the spectral indices have the form
s_i=a_i xor z_C. Orient z_C so that at least one a_i is zero. Fourier inversion
then gives

    h(x)=chi_a(x) g(y),   y_C=product_{i in C} x_i

in sign coordinates. The map x->y is surjective and takes the uniform law to
the uniform law. Hence g is integer-valued, w(g)=w(h), and the nonzero Fourier
coefficients are unchanged up to their indices. Writing a=|a_C| and
q=P(z_C=1) under the normalized spectral law, the block's original expected
weight is

    a(1-q)+(r-a)q >= q.

Indeed if a=0 it equals rq, and otherwise 1<=a<=r-1 makes it at least 1.
Therefore I(g)<=I(h), and raw entropy is unchanged. Apply Theorem 1 to g.
No claim is made here for a genuinely three-state edge constraint.

**Corollary 2 (integer packets).** Suppose Boolean f is a sum of
integer-valued h_j with pairwise disjoint Fourier supports. If each h_j
satisfies Theorem 1 or its stated zero-case extension, then H(f)<=4I(f).

**Proof.** Both raw entropy and influence add over disjoint Fourier supports.
Sum (3). ∎

This extends the [integer flat-packet theorem](integer-flat-packets.md): the
packet magnitudes here can vary without a bounded spread. As in that earlier
theorem, such integer packets necessarily form a signed partition in physical
space. Orthogonality gives E sum_j h_j^2=1, while integrality and sum_j h_j=f
give sum_j h_j(x)^2>=1 at every point. Thus equality holds pointwise, and
exactly one packet is nonzero, with value f(x). This is a proved property of
these packets; it is not an identification of arbitrary fractional or
probability-mixture components with an integer partition.

## 3. A spectral cutset theorem

Let K be k>=1 coordinates and R its complement. For a in {0,1}^K define the
partial Fourier section on the remaining physical variables by

    g_a(y)=2^(-k) sum_{x in {0,1}^K} f(x,y)(-1)^(a dot x).

Its Fourier coefficients are ghat_a(t)=fhat(a,t). This is spectral
conditioning, not a physical restriction. If p_K(a)=w(g_a)>0, the normalized
squared Fourier law of g_a is p_f(t | S_K=a).

**Theorem 3.** Suppose f is Boolean, every nonzero Fourier magnitude of f is
an integer power of two, and each nonzero g_a has a normalized Fourier law
covered by Theorem 1 or its stated zero-case extension. Then

    H(f)<=4 sum_{i notin K} Inf_i(f)+2k-2.         (4)

In particular, if k=1,

    H(f)<=4 sum_{i notin K} Inf_i(f)<=4I(f).       (5)

**Proof.** A sum of 2^k signs is even. Therefore

    h_a=2^(k-1)g_a

is integer-valued for every a. Its nonzero Fourier magnitudes are still
integer powers of two, and multiplication by this scalar does not change
its normalized spectral law. Theorem 1 applies to h_a. For a zero section
the desired inequality is 0<=0. The exact scaling identities are

    H_*(h_a)=4^(k-1)[H_*(g_a)-(2k-2)w(g_a)],
    I(h_a)=4^(k-1) I(g_a).

Thus H_*(g_a)<=4I(g_a)+(2k-2)w(g_a). Now use the exact coefficient
partition identities

    sum_a H_*(g_a)=H(f),
    sum_a I(g_a)=sum_{i notin K} Inf_i(f),
    sum_a w(g_a)=1.

Their sum proves (4). There is no missing entropy of the label a: in
normalized language, (1) contributes sum_a p_K(a)log_2 p_K(a), which exactly
cancels the H(S_K) term in the Shannon chain rule. ∎

**Corollary 4 (cyclic interaction graphs).** Let f have full Fourier support
and power-of-two Fourier magnitudes. Suppose its squared Fourier law factors
over a graph G with a feedback vertex set K of size k, meaning that G-K is
a forest. If k>=1, (4) holds. For k=0 the original forest theorem applies.
For fixed k>=1 the dimension-independent FEI constant

    C_k=4+(8/3)(k-1)                               (6)

is valid. In particular all such graphs whose cycles share a common vertex
satisfy FEI with constant four, regardless of the number or lengths of their
cycles, the number of vertices, the interaction strengths, or Fourier degree.

**Proof.** Conditioning on S_K=a leaves a strictly positive forest law on R;
incident edges become unary factors. This establishes Theorem 3's hypotheses.
For a nonconstant Boolean function with the stated magnitude restriction,
its constant coefficient is either zero or has absolute value at most 1/2.
Thus I(f)>=Var(f)>=3/4. Combining this with (4) gives (6). Constants have
H=I=0 and are handled separately. If a particular K is supplied, the sharper
bound (4), including the subtraction of its coordinate influences, is
preferable to (6). ∎

The class contains every strictly positive Boolean spectral forest, since
the earlier arithmetic theorem proves the power-of-two hypothesis there.
For arbitrary cyclic laws the hypothesis is not inferred from factorization.
The companion [arithmetic theorem](cycles-and-cacti.md)
proves it for all positive pairwise-factorizing Boolean spectra of treewidth
at most two. Since
a graph made into a forest by deleting one vertex has treewidth at most two,
(5) consequently holds for every positive Boolean spectrum on such a graph.
For cacti, the [component-payment argument](cycles-and-cacti.md#6-paying-for-unboundedly-many-cactus-cycles)
removes dependence on the number of cuts. Constant four for the entire
unbounded-feedback-set class of positive pairwise treewidth two remains
unresolved. A separate [bounded-treewidth entropy proof](bounded-treewidth.md)
now gives constant below fourteen for every positive width-two law,
including arbitrary triangle potentials.

If every conditional forest contains a nonconstant component, summing the
refinement in (3) improves (4) by 2. In particular a genuine simple cycle
of length at least three, with any independent fair coordinates appended,
has this improvement after deleting a cycle vertex: its remaining path is
nonconstant. For k=1 the refined assertion is H(f)<=4I_R(f)-2. Some such
graphs admit no nonflat Boolean realization; no existence assertion is
implicit in this conditional refinement.

## 4. Actual denominator costs and adaptive sections

Retain the power-of-two magnitude and conditional-forest hypotheses of
Theorem 3 throughout this section.

The uniform denominator 2^(k-1) is only a worst-case payment. Let d_a be any
nonnegative integer such that 2^d_a g_a is integer-valued. Applying Theorem 1
at this actual scale gives the stronger exact conclusion

    H(f)<=4I_R(f)+2 sum_a p_K(a)d_a,               (7)

with a further subtraction 2 sum_a p_K(a)c_a when all sections have positive
forest quotient energies with c_a nonconstant components. Setting d_a=k-1
recovers (4). A zero section can be assigned d_a=0.

There is also an adaptive version. Partition the spectral cube by the leaves
of a coordinate decision tree, stopping when the nonzero residual section
has a law covered by Theorem 1. For a leaf L let K_L be its queried
coordinates, a_L their values, g_L its partial Fourier section, p_L=w(g_L),
and d_L a nonnegative integer making 2^d_L g_L integer-valued. Then

    H(f)<=4 E[|S outside K_L|]+2 E[d_L],           (8)

where S~p_f determines its leaf L. The proof is the same disjoint coefficient
partition and exact scaling calculation. If the root is not terminal then
each leaf has positive depth and d_L<=|K_L|-1, so a sufficient cost bound
is 2 E[depth(L)-1]. A terminal root uses d=0. Empty-probability leaves do not
affect the identities. Equation (8) proves a conversion with its full cost;
it does not assert that an efficient decision tree exists.

At the extreme of singleton spectral leaves, d_L=log_2(1/|fhat(S)|)
and 2E[d_L]=H(f). That version is circular. A viable route to general FEI
must produce large forest packets with a separately paid denominator cost.

## 5. Explicit genuine-cycle witness and scope of the example

On four spectral bits in little-endian order put

    v(s)=1-s_0+s_2-s_3+s_0s_1-s_1s_2+2s_2s_3+s_3s_0.

Its values are

    (1,0,1,1,2,1,1,1,0,0,0,1,3,3,2,3),

and sum_s4^v(s)=256. Thus p(s)=4^(v(s)-4) is positive, nonuniform,
and its minimal interaction graph is the four-cycle: all four displayed
mixed differences are nonzero, and the two diagonal mixed differences
vanish. Uniqueness of the multilinear logarithmic expansion means that
no forest factorization in these coordinates is possible.

Apply the existing [Kraft-prefix/bent completion](forest-arithmetic.md#6-every-powers-of-four-law-has-a-boolean-completion-with-independent-fair-spectral-bits)
with lengths d_s=4-v(s). It gives a 12-variable Boolean F with exact law

    p_F(s,t)=p(s)2^(-8).

The checker reconstructs all 4096 Boolean values and their integer Walsh
transform. Its four core marginals are

    (73/128, 101/256, 59/64, 215/256),

its core entropy is 89/32, and therefore

    H(F)=345/32,       I(F)=861/128.

Complementing core bits 0,2,3 reduces influence to 81/16 while preserving
the genuine four-cycle and entropy. Independent multiplication by an
arbitrary even-dimensional bent function gives an infinite family with the
same genuine dependency cycle and unbounded dimension and degree.

This construction is **not** claimed as a previously unknown FEI family.
Every Kraft-prefix completion already has H<=4I by its explicit fair-coordinate
budget. Moreover this particular core is affine-equivalent to the reviewed
four-bit path core: if the four binary linear forms have masks (4,12,5,3),
then the path valuation at that image xor 9 equals the displayed v. The
example proves strict containment beyond original-coordinate forest
factorization; it does not itself establish literature novelty. The new
theorem applies to every Boolean signing with the specified cyclic law,
without assuming a Kraft realization, independent fair-coordinate budget,
bounded arity, a read-once representation, or a bound on amplitude spread.

## 6. Why the dyadic and integer hypotheses cannot silently be dropped

Take h=1-1_{(0,0)} on two physical bits. It is integer-valued, and its Walsh
magnitudes are (3,1,1,1), so its positive squared Fourier law is a forest
law on one edge. Yet

    H_*(h)=(9/16)log_2(16/9)+3/4 > 1=4I(h).

The strict inequality is certified without numerical logarithms: 16/9>sqrt2
implies the left side exceeds 33/32. Thus the constant-four integer theorem
really needs an additional arithmetic hypothesis. This failure does not
contradict the Boolean positive-forest theorem.

Its Boolean completion is the three-variable AND/OR phase, with Fourier
magnitudes (3,1,1,1,1,1,1,1)/4. Conditioning on any one spectral coordinate
leaves two positive two-bit forest laws, but

    H(f)=4-(9/16)log_2 9 > 2=4I_R(f).

Indeed log_2 9<7/2 because 81<128, so H(f)>65/32. Therefore deleting the
power-of-two hypothesis from Theorem 3 is false. The original three-bit
law has a genuine three-way logarithmic interaction; this counterexample
does not disprove a larger-constant theorem for pairwise cyclic laws.

## 7. Literature comparison and the remaining obstacle

Potapov [Pot26], as described in [REFERENCES.md](REFERENCES.md), proves
the sharp constant four for plateaued Boolean functions; the existing
integer-flat-packet theorem extends its integer support argument. Theorem 1
here permits arbitrarily many distinct magnitudes and obtains the payment
from the positive-tree Gibbs theorem instead of a bounded-spread comparison.

O'Donnell–Tan [OT13, Theorem 1] is a biased-spectrum composition theorem
for functions on disjoint variable blocks and yields bounded-arity read-once
FEI. The partial Fourier sections here are usually {0,±1}-valued at k=1
and are not Boolean composition gates; no disjoint physical-block
representation is assumed. Consequently that theorem is not being invoked
as a conversion from spectral conditional independence to a read-once
formula. Conversely we have not proved that this entire class is disjoint
from every class already covered in the literature, and the displayed
example has the prior construction guarantee explicitly noted above.

The established extension is a uniform constant-four theorem after one
spectral cut, and a dimension-independent constant for every fixed number
of cuts, under the exact arithmetic and conditional-forest hypotheses.
Uncontrolled cutset size would reintroduce dimension dependence. For more
general conditional-forest laws, the [integer-forest theorem](integer-forests.md) removes the arithmetic
hypothesis with a larger constant and supplies a bound for every fixed
conditioning depth; the counterexample above shows why the original constant-four
integer statement cannot supply it. The companion cut-polytope argument
supplies exactly that arithmetic repair for positive pairwise treewidth-two
parent laws.
Allowing three-state constraints requires a different repair because the
earlier hard-zero star already refutes the positive-tree Gibbs inequality
in that setting. The hard-zero gap is not resolved by either integer-forest argument.

The accompanying checker is
[code/check_dyadic_feedback_forest.py](code/check_dyadic_feedback_forest.py). It verifies the exact cycle
construction, the scaling and section identities, exhaustive small Boolean
cases, and the integer-forest boundary cases. Finite checks are evidence
against transcription errors, not a proof of the universal class theorem.
