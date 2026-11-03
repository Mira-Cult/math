# Fixed quartic prime inputs and centered antipodal reservoirs

Author: /root/analytic. Manuscript-local results; no permanent claim IDs.
This manuscript proves analytic and actual-pair interfaces, not the physical
array theorem. Its canonical-pool dependency is the balanced normalization
proved in normalization_local.md: one representative of every unramified
prime-element associate class, in the symmetric logarithmic and first-angle
fundamental domain. No other prime classes are discarded.

## 1. Exact sources and conventions

The primary sources inspected for this argument are:

- **KM:** Wataru Kai, *Notes on Mitsui's Prime Number Theorem with Siegel
  zeros*, [arXiv:2209.11816v3](https://arxiv.org/html/2209.11816v3),
  8 September 2026, Theorems 2.3.1, 2.3.2, 3.1.1; Appendices A.4--A.6.
- **KL:** Wataru Kai, *Linear patterns of prime elements in number fields*,
  [arXiv:2306.16983v5](https://arxiv.org/html/2306.16983v5),
  Theorem 6.1, Theorem 12.1, Remarks 12.2--12.4 and Appendix D.

Fix one of \(K=K_5,K_8,K_{12}\), with its fixed power integral basis.
The degree, called \(r\) here, is four; \(D=2,3\) is array dimension.
Let \(\sigma=(\sigma_1,\sigma_2):K\to\mathbb C^2\cong\mathbb R^4\)
be the fixed pair of nonconjugate embeddings. Coefficient sup norm and
Minkowski Euclidean norm are equivalent with fixed field-dependent constants.
Lebesgue volume in \(\mathbb C^2\) is ordinary four-dimensional volume;
the covolume of \(\sigma(O)\) is \(\sqrt{|D_K|}/4\).

Write \(w=|\mu(K)|\), \(L=\log|\sigma_1(\epsilon)|>0\), where
\(O^\times=\mu(K)\langle\epsilon\rangle\) is the **full** unit group.
The standard regulator is \(\mathcal R_K=2L\). Set

\[
 \mathcal D=\{(z_1,z_2):z_1z_2\ne0,\
     -L/2\le\tfrac12\log(|z_1|/|z_2|)<L/2,\
     -\pi/w\le\arg z_1<\pi/w\}.
\]

Let \(\mathcal D_1=\mathcal D\cap\{|z_1|^2|z_2|^2\le1\}\).
Endpoints have the exact conventions in the normalization manuscript.
Boundary choices affect finite enumeration, but not volume calculations.
A prime element means its principal ideal is a nonzero prime ideal;
rational-prime norm is not the definition.

## 2. A prime-box estimate which permits zero mean embeddings

For a convex open set \(C\subset\{|z_1|,|z_2|<Y\}\) and a unit class
\(a\bmod\mathfrak q\), KM Theorem 3.1.1 specializes to

\[
 \sum_{\substack{\pi\in O\cap C\ {\rm prime\ element}\\
                   \pi\equiv a\ (\mathfrak q)}}\log N(\pi)
 =\frac{c_K}{\varphi_K(\mathfrak q)}
   \int_C\{1-\chi(z;a)N(z)^{\beta-1}\}\,dz
   +O_K\bigl(Y^4e^{-c\sqrt{\log Y}}\bigr),                 \tag{2.1}
\]

where \(c_K=w/(\pi^2h_K\mathcal R_K)\). The possible exceptional
term is retained and is absent if no exceptional character exists.
The allowed modulus norm is at most \(\exp(c'\sqrt{\log Y})\),
for a sufficiently small field-dependent constant. This is an
**enclosing-radius** error, not one proportional to \(\operatorname{vol}C\).
No constant has been numerically evaluated.

The real exceptional character has trivial archimedean component because
\((\mathbb C^\times)^2\) is connected. Thus its sign is constant in \(z\)
for fixed residue \(a\). KL Theorem 6.1 supplies the Siegel estimate
\(1-\beta\gg_{K,e}N(\mathfrak f_\chi)^{-e}\) for every fixed \(e>0\).
The constant in that estimate is ineffective.

**Lemma W4 (uniform boxes, including near embedding zero).** Fix
\(A,B,C_0>0\). Put \(H=Y/(\log Y)^A\). Every coefficient-coordinate
box \(C\) of side between \(H/C_0\) and \(C_0H\), contained in an
enclosing coefficient box of radius \(C_0Y\), contains

\[
 \gg_{K,A,B,C_0}\frac{H^4}{\varphi_K(\mathfrak q)\log Y}       \tag{2.2}
\]

prime elements in every unit class modulo every ideal of norm at most
\((\log Y)^B\), once \(Y\) exceeds a uniform ineffective threshold.
No nonzero-coordinate assumption on the center is required. The statement
also holds for fixed-shape parallelepipeds, after fixed changes of constants.

**Proof.** Inside \(C\), choose a smaller open box of side \(cH\)
on which both \( |\sigma_j(z)|\ge cH\). The constant depends only
on the fixed coordinate change and shape bounds. To justify the choice,
normalize \(H=1\). Each \(\sigma_j\) is a surjective real linear map
to a plane; the portion of the box where \( |\sigma_j(z)|<\delta\)
has volume \(O_K(\delta^2)\), uniformly under translations. For small
fixed \(\delta\), the two excluded portions and a thin boundary strip
occupy less than the box. Choose a remaining point and shrink about it.

On this subbox \(N(z)\ge(cH)^4\), hence \(\log N(z)\gg\log Y\).
For \(N\mathfrak q\le(\log Y)^B\), choose
\(e=1/(2\max(B,1))\). Uniformly, the Siegel estimate implies
\((1-\beta)\log N(z)\gg\sqrt{\log Y}\); eventually the integrand
in (2.1) is at least \(1/2\), in either sign case. The main term is
\(\gg Y^4/(\log Y)^{4A+B}\), which dominates the enclosing error.
Each prime weight is \(O_K(\log Y)\). This proves (2.2).
There is no division by a tiny embedding at the original center. QED.

In particular, a box near \((cY,0)\) has useful four-dimensional prime
supply at radius \(H=Y/(\log Y)^A\). Its second embedding coordinates
can have size \(H\); its norms can then have size \(Y^2H^2\), rather
than \(Y^4\). Both scales have logarithm comparable to \(\log Y\).
It would be incorrect to infer the same conclusion in a box of radius
\(O(R)\) about a center of size \(Y=nR\) from (2.1): its relative
four-volume is \(O(n^{-4})\), beyond this error estimate.

The primes in W4 are arbitrary prime elements. When the box lies strictly
in \(\mathcal D\), they are automatically frozen canonical representatives
with multiplicity one. Otherwise they can be **target sums**, but cannot
be substituted for input entries.

## 3. Initial-segment scale, distribution, and centroid

**Lemma P4 (pool law).** Let \(M\) be the number of prescribed entries,
\(B_M\) their largest norm, \(R=B_M^{1/4}\), and \(m_M\) their exact
average in \(K\otimes\mathbb R\). Then

\[
 M\sim\frac{B_M}{\log B_M},\qquad
 B_M\sim M\log M,\qquad R\sim(M\log M)^{1/4}.               \tag{3.1}
\]

Moreover

\[
 \frac{m_M}{R}\longrightarrow(c,0),\qquad
 c=\frac45\frac{\sinh(L/2)}{L/2}
                \frac{\sin(\pi/w)}{\pi/w}.                \tag{3.2}
\]

**Proof.** Class number one and the normalization bijection identify the
pool with all prime ideals, minus finitely many ramified classes. The
prime-ideal theorem gives the first count. Each norm tie contains at most
four prime ideals: its norm is a rational prime power with unique rational
prime and exponent, and a degree-four field has at most four prime ideals
above it. Cutting the final tie changes the count by at most three.
This proves (3.1).

For the moment calculation write
\(z_1=\rho e^s e^{i\theta_1}\),
\(z_2=\rho e^{-s}e^{i\theta_2}\). On \(\mathcal D_1\),
\(0<\rho\le1\), \(-L/2\le s<L/2\),
\(-\pi/w\le\theta_1<\pi/w\), and \(\theta_2\) runs around the
full circle. The volume form and volume are

\[
 dz=2\rho^3\,d\rho\,ds\,d\theta_1\,d\theta_2,\qquad
 \operatorname{vol}\mathcal D_1=\frac{2\pi^2L}{w}.          \tag{3.3}
\]

Thus \(c_K\operatorname{vol}\mathcal D_1=1\), because \(h_K=1\)
and \(\mathcal R_K=2L\). On each fixed compact radial annulus, (2.1)
with trivial modulus, box approximation, and partial summation give
uniform ordinary-volume distribution to leading order. Small radial
pieces have volume \(O(\delta^4)\) and first moment \(O(\delta^5)\);
boundary pieces admit outer box covers of arbitrarily small total volume.
Consequently the prime mean converges to the volume mean of \(\mathcal D_1\).

The independent averages of \(\rho,e^s,e^{i\theta_1}\) are \(4/5\),
\(\sinh(L/2)/(L/2)\), and \(\sin(\pi/w)/(\pi/w)\), respectively.
The second angular average is zero. Final-tie and finite omitted-prime
effects are \(O(R/M)\) in the mean. This proves (3.2). QED.

Prime ideals of residue degree at least two contribute
\(O_K(B_M^{1/2}/\log B_M)\) classes and total coefficient size
\(O_K(RB_M^{1/2}/\log B_M)\). They are lower-order in these asymptotics,
but stay in the exact input pool and exact total. Inert rational prime
elements have norm \(p^4\) when present; residue-degree-two prime elements
have norm \(p^2\).

For \(M=n^D\),

\[
 R\asymp n^{D/4}(\log n)^{1/4},\quad
 \mu=nm_M,\quad Y\asymp nR,\quad H=\frac{nR}{(\log n)^A}.   \tag{3.4}
\]

The second embedding of \(\mu/Y\) tends to zero. This is a proved
feature of the pool, not a reason to replace it by a preferred cone.

## 4. Exact totals by three prime targets

**Lemma T4 (uniform ternary completion).** Fix \(A,B,C_0>0\).
Let \(T\in O\), \(\|T\|_\infty\le C_0Y\),
\(H=Y/(\log Y)^A\), and let \(\mathfrak q\) have norm at most
\((\log Y)^B\). Include every norm-two prime ideal in \(\mathfrak q\).
Prescribe unit classes \(b_1,b_2,b_3\bmod\mathfrak q\), summing
to \(T\bmod\mathfrak q\). For all sufficiently large \(Y\), there are
prime elements \(p_j\) in those classes with

\[
 p_1+p_2+p_3=T,\qquad \|p_j-T/3\|_\infty\le H.             \tag{4.1}
\]

The threshold is uniform in the data and ineffective. No nonzero limit
for every embedding of \(T/Y\) is required. The targets need not be
canonical representatives.

**Proof.** Choose a generator \(\kappa\) of \(\mathfrak q\), normalized
by the full unit fundamental domain. Multiplication by \(\kappa\)
has all singular values comparable to \(N(\mathfrak q)^{1/4}\).
Choose \(b_1,b_2\) in a bounded fundamental parallelepiped of \(\kappa O\),
so their coefficient sizes are \(O_K(N(\mathfrak q)^{1/4})\). Define

\[
 \psi_1=b_1+\kappa x,\quad
 \psi_2=b_2+\kappa y,\quad
 \psi_3=T-b_1-b_2-\kappa(x+y),\qquad x,y\in O.             \tag{4.2}
\]

Restrict \(\psi_1,\psi_2\) to coefficient boxes of radius \(H/4\)
about \(T/3\). The third value is within \(H/2\) of \(T/3\).
The preimage is convex in eight integer coordinates and satisfies

\[
 \Omega\subset[-N,N]^8,\quad N\asymp_K Y/N(\mathfrak q)^{1/4},
 \quad\operatorname{vol}\Omega\asymp_K H^8/N(\mathfrak q)^2. \tag{4.3}
\]

KL Theorem 12.1 applies with **fixed** \(t=3,d=8\), target ideal \(O\),
and the fixed integral basis (Remark 12.2). Coefficients and constants
divided by \(N\) have polynomial-logarithmic size. For every \(i\ne j\),
the restriction of \(\dot\psi_i\) to the integer kernel of
\(\dot\psi_j\) has image \(\kappa O\), of finite index \(N(\mathfrak q)\).
This is the theorem's actual finite-cokernel hypothesis.

At a prime ideal not dividing \(\mathfrak q\), with residue-field size
\(Q\), change variables to \(u=\psi_1,v=\psi_2\). The number of pairs
with \(u,v,T-u-v\) all nonzero is

\[
 \begin{cases}
 (Q-1)(Q-2),&T=0\pmod{\mathfrak p},\\
 Q^2-3Q+3,&T\ne0\pmod{\mathfrak p}.
 \end{cases}                                             \tag{4.4}
\]

The corresponding normalized factor is \(1-(Q-1)^{-2}\) or
\(1+(Q-1)^{-3}\). Norm-two primes have been included in the modulus.
At its prime divisors all fixed residues are units, giving factor
\((1-Q^{-1})^{-3}\ge1\). The product has a positive lower bound
depending only on the field since \(\sum_{\mathfrak p}N(\mathfrak p)^{-2}\)
converges. KL Remark 12.3 permits this factorization for the \(O\)-linear
forms, including ramified rational primes through their separate prime ideals.

Choose KL's error exponent \(A'>8A+B+20\), increasing it also for the
coefficient bound. The error/main-volume ratio is
\(O((\log Y)^{8A-A'})=o(1)\). Thus the weighted count is bounded below
by a positive multiple of (4.3).

To remove proper prime-ideal powers, note that only
\(O_K(Y^2(\log Y)^2)\) elements \(\alpha\) of coefficient size \(O(Y)\)
have \((\alpha)=\mathfrak p^k\), \(k\ge2\). Summing over exponents,
there are \(O_K(Y^2\log Y)\) such ideals of norm \(O(Y^4)\).
Each has \(O_K(\log Y)\) associates in the enclosing box: both
embedding-size bounds restrict the full unit exponent to an interval
of that length. For a fixed bad value of one form, its remaining
four-dimensional fiber has \(O_K(Y^4\operatorname{polylog}Y)\) points.
With all three weights, bad tuples contribute
\(O_K(Y^6\operatorname{polylog}Y)=o(\operatorname{vol}\Omega)\).
Zero and units have zero von Mangoldt weight. A surviving tuple gives
(4.1). Prime ideals of higher residue degree are not prime-ideal powers
and are not removed. QED.

The two forms \(x,T-x\) fail finite cokernel, so this proof imports no
binary Goldbach assertion. Nor is a growing number of forms used.

## 5. Compatible target lists and symmetric tensors

**Lemma S4.** Fix \(k\ge1\), \(A,B>0\), and a symmetric \(k\)-tensor
of unit residue classes indexed by \([n]^k\), \(n\ge3\), with labeled
position sum \(S\bmod\mathfrak q\). Suppose
\(\|S/n^k\|_\infty\le C_0Y\), and the modulus satisfies T4.
There is a symmetric tensor of prime elements with those classes,
exact labeled sum \(S\), and every entry within \(Y/(\log Y)^A\)
of \(S/n^k\). The threshold is uniform in \(n,S\) and the residue pattern,
with \(k,A,B,C_0\) fixed.

**Proof.** An orbit of the symmetric group has weight at most \(w_0=k!\).
There are \(n\ge3\) weight-one constant-coordinate positions; reserve three.
Put \(d=Y/(100w_0(\log Y)^A)\). Process the other orbits. In each
coefficient coordinate choose the corner sign opposite the discrepancy.
W4 supplies one prime vector in the required class whose four coordinate
displacements have these signs and magnitudes in \([d/2,d]\).
Adding an orbit of weight at most \(w_0\) keeps each discrepancy in
\([-w_0d,w_0d]\): it decreases in magnitude or crosses zero by at
most the increment. This chooses one element with four coordinates,
not four independently chosen elements.

The remaining total is \(T=3S/n^k-E\in O\), with bounded discrepancy
\(E\), and the last three residues sum to it. Apply T4 at \(T/3\)
with radius \(d\), using fixed-factor changes of constants. All three
primes remain within the asserted radius of \(S/n^k\).
Repeated target values are permitted. QED.

Such a unit-residue pattern exists whenever
\(S\equiv n^k\pmod{\mathfrak p}\) at every norm-two prime ideal.
Set all but three weight-one positions to the unit one and solve the
remaining three-unit equation. Formula (4.4) solves it over every field
of size at least three, for every total. Over the field of two elements
the total must be one. Lift to prime-ideal powers and apply CRT.

For squares, use a common length-\(n\) prime list of total equal to
the exact pool total \(T_{\rm pool}\) as both row and column targets,
and choose two diagonal primes independently by W4. For cubes, use a
symmetric \(n\times n\) prime tensor \(P\) of total \(T_{\rm pool}\)
as all three directional axis-target families. Its marginals agree.
For each of the six slice-diagonal families apply S4 with exact total
equal to the relevant diagonal sum of \(P\); choose the four body
targets independently. These are the compatible-target equations of
the pinned ordinary architecture. Its integer-image and physical
realization statements remain separate geometric obligations.

At \(m=8\), pool entries are one in the norm-two residue field, and
these conditions hold at every odd \(n\). At \(m=5,12\), no norm-two
prime ideal occurs, so this target method introduces no order restriction.
This is a sufficiency statement for the target method, not by itself a
classification of all local array obstructions.

## 6. Centered endpoints despite a missing central support point

The second mean coordinate vanishes. Thus \(m_M/R\) approaches a point
outside the canonical support, and sufficiently small balls there
contain no canonical entries. The repair does **not** change the pool:
use antipodal second-embedding endpoints with their midpoint at the mean.

**Lemma E4 (four conditioned interior chords).** In each field there
are constants \(\delta,\epsilon,c_0>0\) and four real vectors
\(v_1,\ldots,v_4\in\mathbb C^2\) such that
\((c,0)\pm v_j/2\) lie in the interior of \(\mathcal D_1\),
their norms are at most \(1-\epsilon\), and the real gap matrix
has inverse norm at most \(c_0\).

**Proof.** The normalization proof gives \(L<1\), \(w\ge8\). Hence

\[
 0<c\le\frac45\frac{\sinh(1/2)}{1/2}<\frac{21}{25}<1.
\]

The rational upper bound follows from the power series for \(\sinh\);
no floating-point inequality is a premise. The points \((c,\pm c)\)
and \((c,\pm ic)\) have log ratio zero, first phase zero, and norm
\(c^4<1\), so are strict interior points. For small fixed \(\delta>0\)
take

\[
 v_1=(\delta,2c),\quad v_2=(-\delta,2c),\quad
 v_3=(i\delta,2ic),\quad v_4=(-i\delta,2ic).                \tag{6.1}
\]

Their endpoints stay in small interior neighborhoods of those four
points. The real determinant has absolute value \(16\delta^2c^2>0\).
Compactness gives the margin and inverse bound. These continuum vectors
are not asserted to be ring elements or literal prime gaps. QED.

By (3.2), the boxes of radius \(\eta R\) centered at
\(m_M\pm Rv_j/2\), where \(\eta=(\log R)^{-a}\), remain in
the same interior region for large \(M\). Every prime in them occurs
strictly before the last norm tie. Endpoints are far from the mean;
their **midpoints** are close to it.

## 7. Actual same-gap pairs, congruences, and depletion

**Lemma M4 (actual centered macro gaps).** Fix \(a,B>0\), let
\(\eta=(\log R)^{-a}\), and \(N\mathfrak q\le(\log R)^B\).
After deletion of any

\[
 Q=o\bigl(\eta^4M/(\log R)^B\bigr)                         \tag{7.1}
\]

pool entries, each chord \(v_j\) supplies a gap \(\Delta_j\in\mathfrak q\)
with

\[
 \|\Delta_j-Rv_j\|_\infty=O_K(\eta R)                      \tag{7.2}
\]

and at least

\[
 \gg_K\frac{\eta^4M\,N(\mathfrak q)}
                  {\varphi_K(\mathfrak q)^2\log R}
 \ \ge\ \frac{c'\eta^4M}{(\log R)^{B+1}}                  \tag{7.3}
\]

disjoint actual pairs \((p,p+\Delta_j)\) from the remaining pool.
Every midpoint is \(m_M+O_K(\eta R)\). The four gaps are real-linearly
independent and their matrix inverse is \(O_K(1/R)\). Required submatchings
can be made mutually disjoint provided total consumption obeys (7.1).

**Proof.** Apply W4 to the two endpoint boxes in the same unit class
modulo \(\mathfrak q\). Each has at least
\(c\eta^4M/\varphi_K(\mathfrak q)\) eligible primes. Deletion (7.1)
leaves a fixed positive fraction. Differences belong to \(\mathfrak q\)
and lie in a box of radius \(O_K(\eta R)\) about \(Rv_j\).

There are \(O_K(\eta^4R^4/N\mathfrak q)\) possible differences.
Choose a balanced ideal generator: its multiplication map has all
singular values comparable to \(N(\mathfrak q)^{1/4}\), so lattice-box
counting gives this bound, with boundary terms dominated because
\(\eta R/N(\mathfrak q)^{1/4}\to\infty\).
Pigeonhole over all pairs proves (7.3), using \(M\asymp R^4/\log R\).
For a fixed difference these pairs already form a matching, since the
boxes are disjoint and each endpoint has a unique possible partner.
The gap and midpoint bounds follow. Matrix inversion is stable under
the \(O(\eta)\) perturbation of (6.1). Reserve only the required
submatchings, then repeat after their deletion. QED.

**Lemma U4 (modular gap classes).** A class \(u\bmod\mathfrak q\)
is a difference of two unit classes exactly when it vanishes in each
norm-two residue field dividing \(\mathfrak q\). For each such class,
the endpoint boxes for any fixed chord supply the lower bound (7.3)
of actual equal-gap pairs with gap \(u\bmod\mathfrak q\) and
midpoint \(m_M+O_K(\eta R)\), after deletions (7.1).

**Proof.** In a residue field of size at least three, choose \(a\)
outside \(0,-u\). Then \(a,a+u\) are nonzero. Over the field of two
elements both units are one, so the difference must vanish.
Lift to prime-ideal powers and use CRT. Prescribe the two unit classes
in the endpoint boxes and repeat M4's argument in a coset of the ideal. QED.

Unlike the quadratic near-center formulation, the actual modular gap
can have magnitude \(O_K(R)\), not \(O(\eta R)\). Its midpoint remains
centered. Composition must charge the larger increment:
a polynomial-logarithmic number of operations costs
\(R\operatorname{polylog}n=o(nR/(\log n)^A)\).

An additive gap lattice \(\Gamma\) need not be an ideal. If a seed
basis has coefficient matrix \(G\) and determinant \(d\ne0\), the
adjugate identity gives \(dO\subset\Gamma\). M4 with \(\mathfrak q=dO\)
supplies **new actual pairs** whose gaps lie in that ideal. No endpoint
is multiplied by \(d\), by a unit, or by any other factor. Rank four
changes the number of arithmetic directions; a spatial rectangle still
needs two disjoint equal-gap pairs and a cuboid four.

## 8. One compatible quantitative interface

Write \(\ell=\log n\), \(M=n^D\), and take \(N\mathfrak q\le\ell^{20}\)
and \(\eta=\ell^{-200}\). Every endpoint box then contains
\(\gg M/\ell^{820}\) eligible primes; one gap has
\(\gg M/\ell^{821}\) disjoint pairs. These counts survive arbitrary
prior deletion \(O(M/\ell^{1000})\).

The target window \(H=nR/\ell^{1120}\) is justified by W4 and T4;
T4 can use any fixed error exponent greater than \(8\cdot1120+40\).
If maximum per-line reserve load is \(O(n/\ell^{950})\), midpoint
bias is at most \(O(nR/\ell^{1150})=o(H)\).
A prefix consuming \(\ell^{100}\) pairs for each of \(O(n^{D-1})\)
incidence types uses \(O(n^{D-1}\ell^{100})=o(M/\ell^{1000})\)
entries. Per-line load requires separate physical placement bounds.
Whole-bundle concentration at scale \(R\sqrt{n\log n}\), when its
bounded-difference hypotheses hold, is \(o(H)\).

These choices pay for the **analytic** supply/depletion demands.
They do not prove the incidence-type count, load bound, prefix coverage,
tensor rounding, or simultaneous spatial realization. Those are separate
controller/composition obligations. This manuscript supplies actual prime
pairs, not just vector span, and exact-total prime targets, not an
uncontrolled growing linear pattern.

## 9. General fixed-field boundary

KM and KL are fixed-number-field results. In general, principal prime
ideals have leading density \(1/h_K\), and only those give prime elements.
Nonprincipal ideals cannot be inserted as array entries. A full unit
fundamental domain and its bounded archimedean model must be proved anew.
One-point estimates and the ternary finite-cokernel argument then remain
available; for nonprincipal moduli use a norm-length-compatible ideal
basis rather than a generator. Norm-two residue fields remain the only
local obstruction to three-unit completion and to arbitrary unit difference.

The needed geometric hypothesis is stronger than density: the canonical
support reflected through its mean must intersect itself in an open set
generating the full arithmetic space, or a proved balanced multipair
mechanism must replace that property. E4 verifies the stronger condition
in the concrete quartic domains. No uniformity in conductor, degree,
regulator, class number, or growing number of forms is claimed.
