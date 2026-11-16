# Isomorphism classes of higher-defect Heisenberg loops

**Theorem with scoped independent reviews, continuing 0323:C0010 [context outside this selected packet: `../claims/C0010.md`].** This is scoped to the explicit lex-support family in [the higher-defect construction](odd-monolithic-defect-two.md), exact reviewed source `b40066d01085772606b1d1160d58c033b8ba3302`, not all simple odd loops or all folders on its envelope. Let E=F_{3^6}, F₀=F_{3^3}; M,M′ are good F₀-lines, U≤M and U′≤M′ are respective F₃-lines, and (b₁+U,b₂+U), (b₁′+U′,b₂′+U′) are ordered F₃-bases of the respective two-dimensional quotients.

Claim: the displayed loops are isomorphic exactly when there are h∈F₀× and j∈{0,2,4} such that

  M′=h M^{3^j}, U′=h U^{3^j},
  b_i′+U′=h b_i^{3^j}+U′ for i=1,2.                         (1)

Sufficiency: take c∈R the unique square root of 3^j in F₇×. The map Σv_u e_u↦hΣv_u^{3^j}e_{cu}, with uniform coordinate scaling c, intertwines x_i↦x_i^c, y_i↦y_i^c, z↦z^{c²}, a_i↦a_i. It commutes with σ, preserves the lexicographic residue support and sends W and the two graph classes as in (1). Thus it identifies canonical folders and loops.

Necessity: A loop isomorphism gives a canonical folder isomorphism commuting with τ, since K generates and τ inverts K. The monolith V is characteristic. Complements to V in G are V-conjugate: V^T=0 and the coprime normal subgroup T gives H¹(L,V)=0. If two complements are τ-stable, the unique conjugating vector is τ-fixed, because C_V(L)=0. Therefore τ-stable complements can be aligned without losing τ-commutation. We obtain an automorphism φ of L commuting with θ and an F₃-linear intertwiner F commuting with σ. The complement alignment may conjugate H by a vector of V; it does not change H∩V=W or the projection J of H. It adds an A-coboundary to the stabilizer graph, whose origin coordinate vanishes because A fixes e₀₀.

O₇(J)=X=<x₁,x₂>, so φ(X)=X; θ-commutation gives φ(Y)=Y, Y=<y₁,y₂>. On the two coordinate planes the automorphism is diag(P,P) for an invertible matrix P∈GL₂(F₇), and the common-center commutator makes PᵀP=c₀I. The subgroup J consists of X⋊A. Since φ commutes with θ and maps J to J, the possible X-translation in φ(a_i) vanishes by comparing θφ(a_i) with φ(a_i⁻¹); hence φ(A)=A. Normalizing the A-weight decomposition makes P monomial, with an underlying coordinate permutation. On the common center, F is semilinear with a Frobenius exponent j and c₀=3^j mod 7. Since 3 is a quadratic nonresidue and c₀ is a square of a monomial entry, j is even.

The E-span of W is exactly the coordinate support E^S: U is nonzero, and all other displayed support lines are full. Under F this span is carried to itself. The joint x-eigenlines are permuted by a monomial transformation with the same coordinate permutation as P, and y-shifts force a common E-scalar. Testing vectors on individual coordinate axes shows every nonzero scaling belongs to R. If the permutation reversed two indices i<k, a support vector with first nonzero i-coordinate in R and k-coordinate in −R would have its image first nonzero in −R, a contradiction. Hence the permutation is the identity. Each entry of P is the unique residue square root c of 3^j, so P=cI. The distinct A-weights then force φ(a_i)=a_i. The intertwiner is h times Frobenius 3^j and the uniform basis permutation e_u↦e_{cu}. Commutation with σ forces h=bar h, so h∈F₀×. The map on W yields the first two equations in (1). The origin-coordinate map of H¹(A,V) records the two classes b_i+U; conjugating a complement by V adds coboundaries which vanish at the origin, because A fixes e₀₀. Thus the last two equations are necessary.

Count under this criterion. There are 28 F₀-lines in E, seven forbidden, 13 F₃-lines U inside each good M, and |GL₂(3)|=48 ordered quotient bases. F₀× has order 26 and acts freely on this data: a nonidentity scalar cannot act as identity on the two-dimensional quotient M/U, because multiplication by its difference from 1 is invertible on M. Thus 21·13·48/26=504 scalar orbits. The remaining Frobenius² group has order 3 and acts freely on those scalar orbits. Indeed, any fixed orbit would give a semilinear map T on the 3-dimensional F₃-space M preserving U and inducing the identity on M/U. Its cube is scalar and the identity action on M/U forces that scalar to be 1. Writing T(x)=αx⁹ after choosing an F₃-linear identification M≅F₂₇, T³=1 gives α^{1+9+9²}=1. The cyclic group F₂₇× shows that every such α is β/β⁹, so T is conjugate by multiplication by β to Frobenius 9. That Frobenius has a one-dimensional fixed space and order 3, hence minimal polynomial (X−1)³ and rank(T−1)=2; but inducing the identity on M/U forces rank(T−1)≤1. Contradiction. Hence the exact count is 504/3=168.

The proof relies on the cited reviewed folder construction, the odd canonical uniqueness interface and the explicitly stated cohomology alignment. The exact-source independent reviews below include alignment and the automorphisms of L preserving θ and J. No computation is used to claim exhaustiveness.

## Extension to q=7 and r=3

The same normalizer and lex-order argument works for r=3: the central-product quotient has three distinct A-weight pairs, the induced symplectic matrix is monomial, every scalar must be a residue, and lex order rules out every nonidentity coordinate permutation. Here U=0, so the E-span of W has support S₃−{0}, rather than S₃. Its support together with the fixed origin recovers S₃, so the same necessity proof still applies. The criterion is (1), with i=1,2,3 and U=U′=0. There are 21·|GL₃(3)|=21·11232 ordered line/basis data. F₂₇× acts freely and Frobenius² acts freely on scalar orbits, because a semilinear map acting as the identity on a full basis is the identity, whereas its nontrivial field automorphism is not. This gives 21·11232/(26·3)=3024 loop-isomorphism classes within the q=7,r=3 family, under the same reviewed necessity proof. The r=1 case retains the reviewed nine-class result; one must not assume the Frobenius action is free there.

## Uniform orbit criterion under the reviewed construction hypotheses

Let q≡7 mod 12 be prime, d=ord_q(3), m=d/2, and 1≤r≤m; assume the Fourier minor hypothesis in the reviewed higher-defect construction. Set E=F_{3^d} and F₀=F_{3^m}. For a good F₀-line M choose an F₃-subspace U≤M of codimension r and an ordered basis (b_i+U) of M/U. The preceding proof gives the following full within-family isomorphism criterion: two such loops are isomorphic if and only if there are h∈F₀× and an even j modulo d with

    M′=hM^{3^j},  U′=hU^{3^j},  b_i′+U′=h b_i^{3^j}+U′  (1≤i≤r).  (2)

For necessity, O_q(J)=X and θ-commutation preserve X and Y and impose the same P on both; the central commutator gives PᵀP=3^jI. Normalizing A forces P to be monomial, including an a priori coordinate permutation. Since q≡7 mod 12, both −1 and 3 are quadratic nonresidues. The support test on each coordinate axis forces every nonzero monomial entry to be a residue; the lex-order test on two coordinates of opposite residue sign excludes every nonidentity permutation. Every diagonal entry is therefore the unique residue square root of 3^j; in particular j is even and all entries agree. Thus A is fixed coordinatewise. When U≠0 the E-span of W has support S_r; when U=0 it has support S_r−{0}, and adjoining the fixed origin recovers S_r. The coordinate and cocycle comparison is otherwise unchanged. The converse uses the same common scaling/Frobenius map as above.

This is an orbit criterion, not an asserted closed orbit count for general q and r. It includes the reviewed r=1 line criterion and the q=7 counts above. The independent exact-source mathematical reviews below do not assert a general all-odd classification or unbounded defect.

## Independent review

At exact source `1a8a1eddcdfaeb5fab6f3e7682a37c5597a3b522`, GPT-6.1 Terra reviewers [model reviewer identity omitted], [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the full within-family orbit criterion for all admitted q and r and the q=7 counts 168 and 3024, conditional on the reviewed higher-defect construction, its Fourier-minor hypothesis and canonical-folder/cohomology inputs. All checked the tau-compatible complement alignment, absence of hidden X/Y/A twists, monomial normalizer and lexicographic support restriction, common scalar and even Frobenius, ordered origin cohomology data, U=0 support recovery and freeness arguments. No new computation was used or claimed. This classifies the stated construction family, not arbitrary higher-defect loops or all stabilizers on these envelopes; no literature-priority or unbounded-defect assertion is made.

## Proposed closed count for the uniform family

**Deduction with the scoped independent reviews below, from the reviewed orbit criterion above.** Under its hypotheses, m is odd: q-1 has exactly one factor of two, and the reviewed nonresidue condition on 3 makes ord_q(3)=2m even. Consequently gcd(m,2k)=gcd(m,k). Put

    Q=3^m+1,   g_k=gcd(m,k),
    a_k=gcd(9^k−1,Q)−gcd(9^k−1,q)        (0≤k<m).

In particular a₀=Q−q. The number of isomorphism classes in the displayed q,r family is

\[
 \mathcal N_{q,r}=\frac1m\sum_{k=0}^{m-1}a_k\prod_{i=1}^{r-1}(3^{g_k}-3^i). \tag{3}
\]

where an empty product is 1. If r>g_k the product is zero. For r=1, (3) is exactly the reviewed one-factor line count. The count is conditional on the minor hypothesis and does not claim infinitely many admissible primes or classify loops outside this family.

To prove (3), apply Burnside to F₀×⋊<Frob₉> acting on (M,U,(b_i+U)). A line M is fixed by a scalar–Frobenius element exactly when it is fixed by its Frobenius component, since F₀× fixes each F₀-line. The [reviewed one-factor argument](odd-monolithic-heisenberg-prime-family.md) counts its fixed good lines as a_k. On any one of them, choosing an F₀-linear identification M≅F₀ identifies the different scalar twists with every semilinear operator T=α Frob₉^k, α∈F₀×.

The data U and its ordered quotient basis are equivalent to a surjective F₃-linear map π:F₀→F₃^r, with U=ker π and π(b_i)=e_i. They are fixed by T exactly when πT=π. Put g=g_k and e=m/g. Then T^e is multiplication by the relative norm n=α^{(3^m−1)/(3^g−1)}∈F_{3^g}×. If πT=π and n≠1, multiplication by n−1 is invertible, forcing π=0. Thus n=1. Conversely, the cyclic group F₀× shows that precisely (3^m−1)/(3^g−1) elements α have norm 1, and each is β/β^{9^k} for some β∈F₀×. Multiplication by β conjugates T to Frob₉^k.

The coinvariant space F₀/(Frob₉^k−1)F₀ has F₃-dimension g, since its dimension equals that of the fixed field F_{3^g}. The number of surjections from it to F₃^r is ∏_{i=0}^{r−1}(3^g−3^i). For each k the fixed-data count is therefore

    a_k · (3^m−1)/(3^g−1) · ∏_{i=0}^{r−1}(3^g−3^i).

Dividing the sum by m(3^m−1) cancels the i=0 factor and gives (3), including its zero convention. No assumption that a Frobenius-fixed line is pointwise fixed is used: its scalar factor is absorbed into α.

For q=7, m=3, (3) gives 168 and 3024 at r=2 and r=3. For q=19, m=9 and r=2, its nine summands before dividing by 9 are

    387007200, 0, 0, 648, 0, 0, 648, 0, 0,

so the count is 43000944. The integer arithmetic is a check of the displayed formula, not an independent review or a census of other constructions.

At exact source `cdfe466523a3358d1636f517f51664f3c7c51e22`, GPT-6.1 Terra reviewers [model reviewer identity omitted], [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the closed-count deduction, conditional on the earlier orbit criterion, one-factor fixed-good-line count and minor hypothesis. All checked odd m, setwise-fixed lines with arbitrary scalar twists, the relative norm condition and cyclic conjugacy, ordered quotient-basis/surjection correspondence, coinvariant dimension, cancellation and zero/empty-product cases. Each independently checked the q=19,r=2 arithmetic, obtaining the displayed summands and 43,000,944; the HS reviewer also checked the q=7 controls. This is a uniform within-family count, not an exhaustive census of other loops, an infinitude assertion or formal verification.
