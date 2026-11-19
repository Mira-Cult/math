# Integer spectral forests and bounded conditioning

**Mira Cult · 16 November 2026**

Integer-valued functions whose positive squared Fourier magnitudes factor
over a forest satisfy a raw entropy bound with the dimension-independent
constant $`C_F=6/\log_2(16/9)<8`$. The proof combines integer local
factorization with the classical cube logarithmic Sobolev inequality.
It allows arbitrary odd factors in Walsh coefficients. It also gives an
explicit paid defect for cyclic factorization and a Boolean FEI bound for
every fixed bound on spectral conditioning depth.

All spectral entropies and relative entropies use base-two logarithms;
`ln` denotes the natural logarithm.

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

## 1. Results and normalization

For a real function h on the n-dimensional sign cube set

    H_raw(h) = sum_s hhat(s)^2 log_2(1/hhat(s)^2),
    I(h) = sum_s |s| hhat(s)^2,
    W(h) = E h^2.

Raw entropy need not be positive or be an entropy of a probability law.
Zero coefficients contribute zero. The half-difference derivative is
D_i h(x)=(h(x)-h(x^i))/2, so I(h)=sum_i E(D_i h)^2.

Write

    d = log_2(16/9),
    C_F = 6/d = 7.2282625189... < 8.                 (1)

**Theorem 1 (integer forest).** If h is integer-valued and its squared
Fourier magnitudes are strictly positive and factor over a forest, then

    H_raw(h) <= C_F I(h).                            (2)

There is no bound on the integer values of h and no restriction on odd
prime factors in its Walsh coefficients. The same assertion holds after
removing fixed spectral coordinates and contracting deterministic
equality/inequality components, provided the quotient Fourier law is
strictly positive and forest-factorizing. The zero function is included
separately. Genuine three-state edge supports are not included.

**Theorem 2 (one spectral conditioning coordinate).** Suppose f is Boolean
and, for a fixed spectral coordinate r, both positive-mass conditional
Fourier laws given s_r=0 and s_r=1 satisfy the support conditions of
Theorem 1. Then

    H(f) <= C_F sum_{i != r} Inf_i(f) <= C_F I(f).    (3)

The condition is on Fourier sections, not on physical restrictions.
In particular, every full-support Boolean Fourier distribution
factorizing over a graph with a feedback vertex set of size at most one
satisfies (3). This includes an arbitrary number of dependency cycles
meeting at one vertex, and cycles with trees attached. Neither powers-of-two
magnitudes nor bounded cycle length are assumed.

For a bounded number of conditioning coordinates there is a larger
constant, still independent of ambient dimension.

**Theorem 3 (bounded spectral conditioning).** Suppose a Boolean Fourier
law has a partition into spectral subcubes of codimension at most k such
that every positive-mass conditional law is strictly positive and
forest-factorizing on its free coordinates. Constants are included.
For k>=2,

    H(f) <= [32 + 1/ln 2 + (2+8 ln 2)(k-1)] I(f).    (4)

For k=1 use (3), and for k=0 the reviewed positive-forest constant four
is stronger. A fixed conditioning set of size k is a special case.
Thus (4) applies to all full-support Boolean spectral graphical models
with feedback vertex number at most k. Its constant depends on k;
no bound on that parameter in terms of influence is asserted.

The full-support hypothesis in Theorem 3 can be replaced cellwise by
the deterministic-quotient extension in Theorem 1, as explained below.

## 2. Positive integer factorization on a forest

**Lemma 1.** Let A(s)>0 be integers indexed by {0,1}^n, and suppose A
factorizes over unary and pairwise potentials on a forest. There are
positive integer factors u_alpha, each involving at most two coordinates,
and an integer c>=1, such that

    A(s) = c product_alpha u_alpha(s_alpha).          (5)

The graph of these factors can be taken to be the same forest.

**Proof.** For each prime p occurring in some A(s), the valuation
E_p(s)=v_p(A(s)) is an integer-valued quadratic energy on the forest.
One way to see this without assuming rational initial potentials is to
write the unique multilinear expansion of log A. Forest factorization
sets all terms of order at least three, and every nonedge pair term, to
zero. Exponentiating these identities gives multiplicative identities
among integer entries A(s); taking v_p gives the same vanishing identities
for E_p. Thus its constant, unary and edge coefficients are integers.

On each rooted tree, eliminate leaves by integer min-sum messages.
Subtract from the contribution at an edge child-parent its minimum over
the child, and add that integer minimum to the parent's unary contribution.
Every resulting edge residual is nonnegative and integer. After the last
elimination subtract the minimum of the root unary contribution. The
remaining root residual is also nonnegative and integer. Consequently

    E_p(s) = min E_p + sum_alpha R_(p,alpha)(s_alpha),

where every R is a nonnegative integer unary or edge function. Different
components and isolated vertices are handled independently. Exponentiating
prime by prime proves (5), with c=product_p p^(min E_p). Only finitely
many primes occur. ∎

Positivity is used twice: log A is defined, and all messages concern all
binary states. No claim of this integer reparameterization is made for an
arbitrary cyclic graph: frustrated prime-valuation energies can obstruct it.

## 3. A logarithmic Sobolev estimate for integer local factors

The next lemma is the main estimate. It holds for a product of positive
integer factors on *any* graph; acyclicity is only needed in Lemma 1 to
produce such a representation.

**Lemma 2 (integer factor estimate).** Let A satisfy (5), with every
factor of arity at most two, and let p(s)=A(s)^2/Z, Z=sum_s A(s)^2.
Put J=E_p|s| and L=E_p log_2 A(s). Then

    D_2(p || Uniform) <= c_0 L,
    c_0 = 9/(16 ln 2) = 0.8115159605... .            (6)

Consequently

    n-L <= (3/d) J,  d=log_2(16/9).                  (7)

**Proof.** First establish the scalar inequality

    (1-1/U)^2 <= kappa ln U  (integer U>=1),
    kappa = 9/(32 ln 2).                            (8)

For U=1 it is immediate. The real function
(1-1/u)^2/ln u is decreasing for u>=4: the sign of its derivative is
that of 2 ln u-(u-1), which is negative at four and decreases thereafter.
For U=2 and U=4 the comparison is direct. For U=3, (8) is equivalent to
2^128<=3^81, an integer inequality. Thus the maximum on positive integers
is attained at U=4.

For a spectral cube edge (s,s^i), let a=A(s)>=b=A(s^i), orienting that
edge towards its larger entry. Let U be the product of the factors
incident to i, evaluated at s, and V the corresponding product at s^i.
The common factors cancel, so b/a=V/U. Both U and V are positive integers;
in particular b/a>=1/U. By (8),

    (a-b)^2 <= kappa a^2 ln U.

Let L_i(s)=sum_(alpha containing i) ln u_alpha(s_alpha). Removing the
orientation by allowing the nonnegative term at both endpoints gives

    (A(s)-A(s^i))^2
      <= kappa [A(s)^2 L_i(s)+A(s^i)^2 L_i(s^i)].

Uniformly averaging and dividing by four yields

    E(D_i A)^2 <= (kappa/2) E[A^2 L_i].

Every factor is charged at most twice. Since c>=1,

    sum_i E(D_i A)^2 <= kappa E[A^2 ln A].           (9)

Use the cube logarithmic Sobolev inequality, with natural entropy,

    Ent_uniform(A^2) <= 2 sum_i E(D_i A)^2.          (10)

Dividing by E A^2 and then by ln 2 proves (6). Equation (10) uses the
half-difference derivative fixed above. It is the standard Gross cube
inequality; its exact normalization is stated in O'Donnell--Wright--Zhou,
*The Fourier Entropy--Influence Conjecture for certain classes of Boolean
functions*, introduction, p. 2, and follows from the two-point inequality
and entropy tensorization.

For the remaining step compare p with the product distribution
r(s)=(8/9)^n 2^(-3|s|). Nonnegativity of D_2(p||r) gives

    H(p) <= 3J+n log_2(9/8).

Together with n-H(p)<=c_0 L, this yields

    n d <= c_0 L+3J, d=1-log_2(9/8)=log_2(16/9).

Here c_0<d. For an exact check, multiplying by ln2 reduces this to
9/16<ln(16/9). If t=7/25, the first two positive terms in
ln((1+t)/(1-t))=2 sum_(j>=0) t^(2j+1)/(2j+1) already exceed 9/16.
Since L>=0, division by d proves (7). Also d>3/4, because
(16/9)^4>8, so C_F<8. ∎

The estimate does not infer a property of a probability law from unsigned
factorization alone: its integer amplitude hypothesis is essential.
For example, arbitrarily small product-coordinate marginals would
invalidate (7) if arbitrary positive real factors were admitted.

### 3.1 A limitation at factor arity three

The limitation below concerns the pure amplitude-logarithm estimate. The
later [bounded-treewidth proof](bounded-treewidth.md) adds an influence
term to the local entropy bound and resolves the positive fixed-width
case, including arity three. It leaves the sharper forest constant intact.


The same proof with factors of arity at most r gives
D_2(p||Uniform)<=r kappa E_p log_2 A. For r=3, the resulting coefficient
3 kappa exceeds one, whereas d<1 for every finite entropy tangent slope.
The absorption in (7) then fails. Merely replacing a tree by a junction
tree with triple factors does not prove a bounded-treewidth theorem by
this argument. This is a limitation of this estimate, not a counterexample
to FEI or to a stronger use of Boolean identities.

### 3.2 A paid local-integrality defect on arbitrary graphs

**Corollary 1 (local-integrality defect).** Let f be Boolean with a strictly
positive Fourier law. Put A(s)=2^n|fhat(s)|, a positive integer tensor.
If K>=1 is an integer for which

    K A(s)=c product_alpha u_alpha(s_alpha),

with c and all u_alpha positive integers and every factor of arity at
most two, then

    H(f) <= C_F I(f)+2log_2 K.                        (18)

The graph of the factors may have arbitrary treewidth and arbitrarily
many cycles. In particular, K=1 gives a dimension-independent FEI theorem
on this integer-factor class, without any forest hypothesis.

**Proof.** Apply (7) to K A. Its normalized square law is still p_f,
whereas E_p log_2(KA)=log_2 K+E_p log_2 A. Boolean Parseval gives
H(f)=2n-2E_p log_2 A and I(f)=E_p|s|. These identities prove (18).
No assertion that an arbitrary probability tensor is Boolean-realizable
is used. ∎

If A has any positive pairwise graphical factorization, such a finite
integer K exists. Indeed the multilinear expansion of log A has only
constant, unary and edge terms. Exponentiating its coefficients expresses
A as a rational constant times finitely many positive rational unary and
pairwise factors: every coefficient is a logarithm of a ratio of products
of the integer entries A(s). Clear the denominators in each factor and
in the remaining rational constant. This produces a finite integer K
and an integer representation of K A. It need not produce a small K.

One may therefore define the local-integrality defect to be

    Gamma(A)=min {log_2 K : K is a positive integer admitting this
                  unary/pairwise integer representation of K A}.

The set is nonempty for every positive integer pairwise tensor, so this
minimum exists. Corollary 1 reads H(f)<=C_F I(f)+2Gamma(A).
Lemma 1 proves Gamma(A)=0 for forests. On a cyclic graph, globally
nonnegative prime-valuation energies need not admit nonnegative local
integer residuals without a compensating constant; Gamma records a
sufficient cost for that obstruction. No universal bound Gamma(A)=O(I(f))
is proved. Nor is the defect claimed to be necessary for FEI: spectral
conditioning and the stronger cyclic arguments can succeed even when
this particular representation incurs a cost. The corollary supplies
an explicit quantitative remainder instead of discarding Boolean
realizability or assuming a free approximation by tree laws.

## 4. Raw entropy, lattice scaling and deterministic support

For integer h on n variables, A(s)=2^n |hhat(s)| is integer. Under the
positive-forest hypothesis, Lemmas 1--2 apply. If W=E h^2, then

    H_raw(h)/W = 2n-2E_p log_2 A,
    I(h)/W = E_p |s|.

Equation (7) proves Theorem 1. If h=0 there is nothing to prove. For a
nonzero integer constant (n=0), raw entropy is nonpositive.

For any g with Lg integer, L>=1, scaling gives

    H_raw(g) <= C_F I(g)+2(log_2 L) E g^2.           (11)

In particular the cost in (11) is an exact lattice penalty, not an
unpaid approximation or mixture-label entropy.

To allow deterministic edges, use the already reviewed contraction in
[deterministic-contractions.md](deterministic-contractions.md). It applies
to integer functions as well: spectral support contained in the resulting
affine duplication subspace means

    h(x)=chi_a(x) h_0(y),  y_C=product_(i in C) x_i.

The map x -> y is surjective, so h_0 is integer-valued. Fourier coefficients
are relabeled bijectively, preserving raw entropy and W. Orient each
component as in the cited contraction proof so its contribution to
I(h) is at least that of its latent coordinate in I(h_0). Fixed spectral
ones only increase influence. Thus I(h_0)<=I(h), proving the extension
in Theorem 1. No three-state edge is eliminated by this argument.

## 5. Exact conditioning and the first cyclic theorem

For a Boolean f(x,z) with one sign coordinate z, write

    g_0(x)=[f(x,1)+f(x,-1)]/2,
    g_1(x)=[f(x,1)-f(x,-1)]/2.

Both functions take values in {-1,0,1}. Their Fourier coefficients are
the two rows of f's Fourier table. Therefore

    H(f)=H_raw(g_0)+H_raw(g_1),
    sum_(i != z) Inf_i(f)=I(g_0)+I(g_1).

Apply Theorem 1 to the nonzero rows. This proves (3) without ever claiming
that a normalized conditional Fourier law is itself Boolean-realizable.
The actual integer-valued sections are the object to which the theorem
applies. If deleting one spectral vertex leaves a forest, conditioning
that vertex leaves positive forest rows, so the graphical corollary follows.

More generally, for k conditioned coordinates,

    g_t(x)=2^(-k) sum_z f(x,z) chi_t(z)

satisfies |g_t|<=1 and 2^(k-1)g_t integer when k>=1. Summing (11) gives

    H(f) <= C_F I_outside(f)+2(k-1).                 (12)

For balanced f, I(f)>=1, so (12) already gives
H(f)<=[C_F+2(k-1)]I(f). The unbalanced case requires the next argument;
the additive term in (12) is not silently charged to influence.

## 6. Concentrated integer forest sections

**Lemma 3.** Let h be integer-valued, |h|<=L with L>=1, and suppose its
squared Fourier law is positive and forest-factorizing on m active
coordinates. Write mu=E h, v=Var(h), and ell=log_2 L. If v<mu^2/2, then

    m <= 16+4(ln 2)ell.                             (13)

**Proof.** We may assume m>=1. Put A_s=2^m |hhat(s)|. Then A_0>0 and
A_0<=L2^m. Choose an independent set U in the forest of size a>=m/2.
On the spectral subcube with all coordinates outside U fixed to zero,
A factorizes as a product tensor of positive integers. Primitive integer
rank-one factorization, with coprime positive u_i,v_i, gives

    A_0=c product_(i in U) u_i,  c>=1,
    A_{e_i}/A_0=v_i/u_i=:r_i.

The factorization follows by reducing each rational coordinate ratio;
the resulting integer product tensor has gcd one, forcing its scalar
to be an integer. The variance hypothesis gives

    sum_(i in U) r_i^2 <= v/mu^2 <1/2.

Since u_i>=1/r_i, the arithmetic-geometric mean inequality implies

    A_0 >= product_i (1/r_i) > (2a)^(a/2) >= m^(m/4).

Combining this with A_0<=L2^m yields

    (m/4) log_2(m/16) <= ell.

If m<=16, (13) is automatic. Otherwise ln x>=1-1/x gives
(m/4)log_2(m/16)>=(m-16)/(4 ln2), proving (13). ∎

With deterministic-quotient support, apply this lemma after contraction.
Because mu!=0, the spectral zero vector belongs to the support; therefore
no fixed-one offset is present, and the quotient preserves the mean,
variance and coefficient magnitudes. The dimension bound is on the
quotient, which is sufficient for coefficient granularity below. It is
not a bound on the number of original variables after parity duplication.

## 7. Proof of the general conditioning theorem

Consider a spectral subcube partition as in Theorem 3. For cell C_j let
B_j be its fixed coordinates, t_j the subset fixed to one, d_j=|B_j|<=k,
and g_j its Fourier section after deleting t_j. Then

    H(f)=sum_j H_raw(g_j),
    I(f)=sum_j I(g_j)+sum_j |t_j| W_j,
    W_j=E g_j^2.

There is exactly one cell C_0 containing the spectral zero vector; all
other cells have |t_j|>=1. Set L=2^(k-1), ell=k-1. Every Lg_j is integer
and |g_j|<=1. Using (11) on the nonzero cells gives

    sum_(j != 0) H_raw(g_j)
      <= C_F sum_(j != 0) I(g_j)+2ell sum_j |t_j|W_j. (14)

It remains to treat g_0. Let mu=E g_0=E f and v=Var(g_0).
If v>=mu^2/2, then W_0<=3v<=3I(g_0), and (11) yields

    H_raw(g_0)<=(C_F+6ell)I(g_0).                    (15)

If v<mu^2/2, apply Lemma 3 to h=Lg_0. Its active quotient dimension is
at most 16+4(ln2)ell. Every nonzero Fourier coefficient of g_0 has
magnitude at least 2^(-m)/L. Therefore its nonconstant raw entropy is
at most

    [32+(2+8ln2)ell] v
      <=[32+(2+8ln2)ell] I(g_0).                    (16)

The constant Fourier coefficient contributes at most

    mu^2 log_2(1/mu^2)
      <=(1-mu^2)/ln2=Var(f)/ln2<=I(f)/ln2.          (17)

Combining (14)--(17), using C_F<8 and ell>=1, proves (4). Empty or
zero-mass cells contribute zero. If f is constant, H=I=0 is checked
directly. If a cell has deterministic-quotient support, use its quotient
in Lemma 3 and in the coefficient-granularity statement, as described
above. This completes the proof of Theorem 3.

## 8. Failed constant four and verification controls

The integer theorem cannot use the previous Boolean forest constant four.
Take h=1 minus the indicator of one point on two variables. With suitable
sign conventions,

    hhat=(3,1,1,-1)/4,
    I(h)=1/4,
    H_raw(h)=9/16 log_2(16/9)+3/4.

Thus H_raw(h)/I(h)=3+(9/4)log_2(16/9)
=4.8676687467...>4. This is an actual integer-valued function with a
positive one-edge spectrum, not an arbitrary unsigned probability law.
It has norm squared 3/4. Disjoint products preserve this raw ratio and
give an infinite family. The failure is exactly why the odd-factor
integer estimate is needed for general Fourier sections.

An exact integer scan of all ternary functions on four variables examines
3^16=43,046,721 truth tables. There are 43,776 with all Walsh coefficients
nonzero and a forest magnitude factorization. The largest observed raw
ratio is the preceding value, attained by a product of two two-variable
examples; the largest odd part of a Walsh magnitude is nine. The scan
proves only these finite classification/count statements. Printed entropy
ratios are floating-point diagnostics, not universal proofs.

## 9. Relation to prior results and the remaining gap

The reviewed positive Boolean forest theorem in
[positive-forests.md](positive-forests.md) gives the stronger constant four on its
own class. Its Boolean prime exclusion and minimum-layer induction are
not invoked in the new integer theorem. We reuse only the forest
min-sum integer reparameterization, prove it explicitly, and then use
Gross's logarithmic Sobolev inequality in the spectral index variables.
Booleanity enters the cyclic theorem through the exact ternary Fourier
sections, and the bounded-conditioning theorem through their lattice,
pointwise bound and the global constant-coefficient/variance payment.

The conditional leaves here can be arbitrarily large, nonuniform forest
models with arbitrary Fourier signs. Product leaves are a subclass;
no bounded vertex cover is required inside a leaf. The displayed constant
is a sufficient bound and is not asserted optimal, even for product leaves.

O'Donnell--Tan, *A composition theorem for the Fourier Entropy-Influence
conjecture*, arXiv:1304.1347, concerns disjoint physical input blocks and
the outer Fourier transform under the product bias induced by the inner
functions. The present hypotheses concern conditional squared Fourier
laws and actual integer Fourier sections. No conversion between these
hypotheses is assumed. Their composition theorem can apply to particular
examples in our class; cyclic dependence alone does not establish novelty
relative to all older classes.

The literature comparison is bounded; no exhaustive historical priority
claim is made. The standard logarithmic Sobolev input is
explicitly normalized in O'Donnell--Wright--Zhou, introduction p.2:
https://www.cs.cmu.edu/~odonnell/papers/fei.pdf.
The O'Donnell--Tan primary paper is
https://www.cs.cmu.edu/~odonnell/papers/fei-composition.pdf.

General FEI remains open here. Theorem 3 pays linearly in the largest
spectral conditioning depth. It supplies no universal O(I) forest
partition or low-information mixture. The direct extension of the
integer-factor Sobolev estimate to triple factors fails at its absorption
step; the paid local entropy argument in [bounded treewidth](bounded-treewidth.md)
repairs that step with a larger constant. Arbitrary hard-zero forest edges
remain open, with a new forbidden-pair special case and explicit barriers
in [zero edges](zero-edges.md).
