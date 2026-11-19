# Boolean arithmetic, mixtures, and the remaining cost

**Mira Cult · 16 November 2026**

Boolean Walsh inversion gives an additional parity saving in the minimum
spectral layer. This strengthens the forest deficit and determines a sharp
independent fair-completion cost for one explicit core. Separate exact
obstructions show why arbitrary forest mixtures, tree projections, and
coarsened selector labels cannot be used without an additional payment.
These results clarify what remains between the proved class theorems and
general FEI.

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

All Fourier transforms are uniform and normalized, with
`W_f(s)=2^n fhat(s)`. Entropy is in bits and influence is
`I(f)=sum_s |s| fhat(s)^2`. Zero coefficients contribute zero.

## 1. Boolean parity strengthens the minimum-layer bound

**Lemma 1.** Let nonzero Boolean `f` have
`m=min_{W_f(s)!=0} v_2(W_f(s)) < n`. Put

    P(s)=1[W_f(s)/2^m is odd].

Then `deg_F2 P <= m-1`.

**Proof.** Write `b_s=W_f(s)/2^m`. Walsh inversion in physical zero-one
coordinates is

    sum_s b_s product_{i in s}(1-2x_i)=2^(n-m) f(x).

For nonempty `T`, the coefficient of `x_T` in the multilinear polynomial
representing `f` is an alternating sum of `2^|T|` odd integers and is even.
The coefficient on the left is
`(-2)^|T| sum_{s superset T} b_s`. Thus this upper-face sum is even whenever
`1<=|T|<=n-m`. For `T=emptyset` it is also even, by the displayed inversion
at zero and `m<n`.

The coefficient of `x_U` in the algebraic normal form of `P(1+x)` is
`sum_{s superset U^c} P(s)`. It therefore vanishes whenever `|U|>=m`.
Complementing coordinates preserves algebraic degree. ∎

The hypothesis `m<n` matters: a character has `m=n` and a singleton
minimum-layer support of degree `n`. Every noncharacter Boolean function
has at least two nonzero Walsh coefficients, so Parseval implies `m<n`.
This is a strengthened use of the existing Walsh/Reed--Muller observation;
no historical priority for that general divisibility principle is claimed.

**Corollary 2.** For a nonconstant positive Boolean forest, let `c` be the
number of nonconstant energy components, after deleting constant edge
potentials. Then

    H(f) <= 4I(f)-2-2c.

In particular, a nonuniform positive forest has slack at least four.

**Proof.** In the notation of the reviewed energy theorem,
`B=E[v+2|S|]>=n-delta+c`. Lemma 1 gives `delta<=m-1`, whereas
`H=2(n-m-Ev)`. Hence
`4I-H=2(B-(n-m))>=2+2c`. Positivity and `n>0` exclude a character.
∎

For deterministic quotients the same conclusion applies to a nonconstant
positive quotient; any additional original-coordinate influence only
increases the slack. A zero-dimensional quotient is a character and is
handled directly. All nonconstant admissible forest functions, including
characters, retain the weaker uniform slack at least two used by the
interpolation theorem.

**Corollary 3 (a sharp independent fair-completion cost).** In the notation
of Theorem 3 of [positive-forests.md](positive-forests.md), a positive Boolean forest
with `q` isolated fair spectral bits and nontrivial components `C` satisfies

    q/2 >= 1 + sum_C (D_C+delta_C-|C|),

provided the total number of coordinates is positive. Indeed the proof of
that theorem now uses `sum_C delta_C<=m-1` instead of `<=m`.
The reviewed four-bit nonuniform path core has `D=4, delta=3`, so any
independent fair completion needs at least eight extra bits. The existing
Kraft/bent construction uses exactly eight and is therefore minimal in this
specific independent-fair completion model. The six-bit path core needs
at least twelve; its construction uses fourteen. No assertion about
arbitrary correlated completions follows.

## 2. A Boolean law for which every forest mixture is a point-mass mixture

**Proposition 4.** For three-bit majority, every representation

    p_Maj3 = sum_j lambda_j p_j

with positive weights and Boolean forest-factorizing Fourier laws `p_j`
uses only point masses. This remains true even if all hard-zero forest
laws are permitted as components. Consequently every such label has
`I(S;J)=H(S)=2`.

**Proof.** The Fourier expansion is

    Maj3(x)=(x_1+x_2+x_3-x_1x_2x_3)/2.

Its law is uniform on
`D={100,010,001,111}`, an affine two-dimensional plane. Positivity of the
mixture weights implies `support(p_j) subset D` for every component.
Multiplication by `x_3` and the surjective parity substitution
`y_1=x_1x_3, y_2=x_2x_3` show that every Boolean function with Fourier
support inside D is `x_3 g(y_1,y_2)` for a two-bit Boolean `g`. Such a `g`
is either a character, or has four Fourier coefficients all of magnitude
one half. This follows directly by counting the number of negative truth
values: even counts give characters and odd counts give four magnitudes
one half. Thus a non-point component would have to be uniform on D.

That law cannot factor over any forest. Every singleton and every pair
marginal of the uniform law on D is full and uniform. In a unary/edge
factorization, a zero factor would forbid a positive singleton or pair
marginal, so every factor would be positive. The joint law would then be
positive on all eight states, contrary to its support. Therefore every
component is a point mass. The value of S is determined by J, proving
`I(S;J)=H(S)=2`. ∎

This is an obstruction to a universal decomposition having even one
nontrivial forest component. It does not refute the proposed `O(I)` cost:
here `I(Maj3)=3/2`. Enlarging the component class to arbitrary plateaued
Boolean laws makes this example a single component, as expected from
Potapov's plateaued theorem. The new integer-packet approach is a different
repair: its raw entropy pays component mass entropy inside the inequality.

For any decomposition into components satisfying `H(p_j)<=4I(p_j)`, the
exact chain rule always gives the necessary lower bound

    I(S;J) >= H(f)-4I(f).

Hod's explicit families with ratio greater than 6.454784 therefore require
a genuine additional information cost exceeding `2.454784 I(f)` in the
limit. A universal zero-cost interpolation with constant four is impossible.

## 3. Why integer spectral packets pay a label that ordinary mixtures do not

Suppose Boolean f is a sum of integer-valued functions `h_j` with pairwise
disjoint Fourier supports. Orthogonality gives `sum_j E h_j^2=E f^2=1`.
Pointwise,

    sum_j h_j(x)^2 >= sum_j |h_j(x)| >= |f(x)|=1.

Equality of the expectations forces equality at every input. Thus exactly
one packet is nonzero at each point, its value is a sign, and it equals f.
This proves, rather than assumes, that these particular integer packets
form a signed unambiguous physical partition. A fractional certificate has
not been converted into such a partition by this observation.

Write `w_j=||h_j||_2^2` and let `p_j=hat h_j^2/w_j` when `w_j>0`.
The label is also determined by the Fourier index, but

    H_raw(h_j)=w_j H(p_j)+w_j log_2(1/w_j).

Consequently a raw bound `H_raw(h_j)<=C I(h_j)` pays both the conditional
entropy and its full label cost. Summing gives `H(f)<=CI(f)` without an
unpaid mixture term. This explains why the integer-forest theorem and the
dyadic integer-forest theorem address the interpolation obstacle directly.
The requirement that the inverse packets be integer-valued is substantial;
arbitrary equal-magnitude grouping does not satisfy it.

## 4. Tree approximation: the correct identity and an exact nonrealizable tree

Let p be any law on spectral bits and T a forest. Root each tree and define
q_T by the root marginal and transition probabilities from p's edge
marginals. A transition out of a zero-probability parent state can be
chosen arbitrarily: that state is never reached. Then q_T matches all
selected pair and singleton marginals, and `support(p) subset support(q_T)`.
Taking expectations of

    log q_T(s)=sum_roots log p_r(s_r)
                +sum_(i parent j) log p(s_j | s_i)

under p and q_T gives the same value. Zero-mass terms are omitted. Hence

    H(q_T)-H(p)=D_2(p || q_T),
    E_qT |S|=E_p |S|.

These are standard tree-projection entropy identities, not new FEI
inequalities. For three-bit majority every such q_T is the uniform law on
eight points. It has `H(q_T)=3`, while `H(p)=2` and the divergence is one.
It is not Boolean-realizable: its Fourier magnitudes would be `1/sqrt(8)`,
whereas Boolean Walsh coefficients are integers divided by eight.
Thus matching the correct influences and tree marginals does not allow the
Boolean forest theorem to be used on q_T.

The potentially useful general estimate retains the correction:

    H(q_T) <= C I(f)+D_2(p_f || q_T).

For a fixed choice of T this is algebraically equivalent to FEI. It becomes
an attack only with an additional structural argument controlling the
Boolean-realizability defect and divergence together. No such estimate for
arbitrary Boolean f is proved here.

## 5. Coarsening a physical selector label can lose its spectral cost

The physical interpolation theorem has label cost
`H(L)=E depth`, because a uniform restriction-tree leaf at depth d has
probability `2^(-d)`. It gives the exact paid bound

    H(f) <= E H(g_L)+4[I(f)-E I(g_L)]+H(L)/2.

The full leaf label cannot in general be replaced by the identity of the
selected function. The explicit balanced four-bit gate in
[interpolation.md](interpolation.md) has `H=3`, `I=3/2`, and a threefold
balanced disjoint self-composition b has `H(b)=57/4`, `I(b)=27/8`.
Set `F(z,y)=b(z)y`. Its two distinct payloads are the forest functions
`+y` and `-y`; their coarsened label J is balanced, so `H(J)=1`.
Yet `H(F)=57/4`, `I(F)=35/8`, and the proposed replacement bound would be

    H(F) <= 4[(35/8)-1]+1/2 = 14 < 57/4.

Thus even two payload labels can conceal unpaid selector Fourier entropy.
This does not refute a low-information mixture of squared Fourier laws;
it refutes this particular function-level shortcut. The same gate's
fourfold composition, multiplied by y, has `H-4I=1/8>0`, showing why an
unrestricted iteration of constant-four forest selection is impossible.
These are exact algebraic counterexamples, not numerical extrapolations.

## 6. What remains after the repaired approaches

The cycle theorem gives all positive spectral graphs that become forests
after deleting one vertex, and all positive cactus spectral graphs with
arbitrarily many cycles, with constant four. A cactus has edge-disjoint
cycles meeting in at most articulation vertices. Its proof chooses a
feedback set whose surviving nonconstant forest components pay the full
conditioning denominator cost; no bound on the number of cycles is used.
The general integer method
gives dimension-free constants for every fixed bound on the number of
spectral conditioning bits, even without dyadic magnitudes. The physical
interpolation theorem preserves constant four for unrestricted-length
first-hit lists with nonconstant admissible forest payloads. The preserved
constant four is the advance described here for that class; older selector inequalities already
give a coarser dimension-free bound.

The bounded-treewidth arithmetic theorem alone does not supply FEI for
all width-two laws. The independent [paid integer-bag theorem](bounded-treewidth.md)
now gives constant below fourteen, and covers all positive fixed widths. The square of an eleven-vertex
path defeats the tested component-count payment, as proved and checked in
the cycle manuscript; it is a graph obstruction, not a Boolean FEI
counterexample. Hard-zero
three-state constraints remain outside the positive forest energy proof,
with the separate [forbidden-pair extension](zero-edges.md) now available. Arbitrary
integer packet denominators, conditioning depth and cyclic factorization
defects still have no universal influence budget. The new arguments do not
convert AA fractional certificates into those objects, and the final AA
large-influence bound alone does not pay these costs.

The precise next routes are to pay the integer local-factor defect on
cyclic laws, to extend modular support rigidity to the additional cut
facets, or to construct a global integer-packet decomposition with a paid
denominator. The cycle manuscript gives an explicit Boolean obstruction to
the naive modular lift at a K_5 facet. These are narrower, testable gaps;
none is claimed solved by a forest approximation or by small computations.

## References and reproducibility

- V. N. Potapov, arXiv:2609.21563v1, Proposition 4 and Theorem 2: the
  support-degree method and the plateaued FEI class. See [REFERENCES.md](REFERENCES.md).
- R. O'Donnell and L.-Y. Tan, arXiv:1304.1347v1, Theorem 1 and the definition
  of biased FEI+: disjoint-input composition needs the biased corrected
  entropy hypothesis, not just uniform FEI for its factors.
- R. Hod, arXiv:1711.00762v1, abstract and the three constructions:
  explicit lower bounds on the universal constant, including 6.454784.
- F. Barahona and A. R. Mahjoub, *On the cut polytope*, Mathematical
  Programming 36 (1986), 157--173, Corollary 3.10: the external polyhedral
  input to the new arithmetic theorem.
- [code/check_beyond_forest_bridge.py](code/check_beyond_forest_bridge.py) exhausts Boolean functions through
  four variables for Lemma 1, checks the majority mixture obstruction and
  projection exactly, and checks the sharpened fair-completion parameters.
  These finite checks supplement, rather than prove, the displayed results.
