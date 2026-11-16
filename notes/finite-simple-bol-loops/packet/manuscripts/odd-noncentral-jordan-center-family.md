# Simple odd Bol loops with noncentral derived centers of unbounded Jordan length

**Continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`], with the scoped independent reviews below.** The endpoint is an explicit simple proper odd Bol G-loop for every admissible parameter triple

    m≥1,   p>2m+1 an odd prime,   q an odd prime dividing p−1.

Writing s=ord_p(q), its order is p^{6m+3}q^{2(m+1)s+1}. Its canonical derived group D is nilpotent of class two, with exponent-p and exponent-q Sylow factors, but Z(D) is not central in G. The own-prime action on Z(P) has a single Jordan block of length 2m+1. This refutes a universal central-center reduction even within the class-two branch; it does not classify all noncentral centers or give an isomorphism census of this family. The [central class-two theorem](odd-central-class-two-classification.md), reviewed at `598fa119be327480c829af2a9beb709b02886bc4`, is the baseline and remains valid under its explicit centrality hypothesis.

There are admissible parameters for every m, without needing an arithmetic progression theorem. Put B=2m+1, M=3B! and choose any prime divisor p of M²+M+1. It exceeds B, since every prime at most B divides M. The order of M modulo p is three: M³≡1, and M≡1 would force p=3, impossible. Thus p≡1 mod 3 and q=3 is admissible. This observation supplies unbounded Jordan lengths, not pairwise loop-isomorphism parameters.

## Ring, groups and the noncentral stabilizer cocycle

Let n=2m+1, R=F_p[ε]/(εⁿ), and write bar for ε↦−ε. Put W=R² and β(x,y)=x₁y₂−x₂y₁. Let P be the class-two BCH group on W⊕W⊕R with product

    (x,y,z)(x′,y′,z′)
      =(x+x′,y+y′,z+z′+½[β(x,y′)+β(y,x′)]).         (1)

The R-valued alternating pairing has zero radical and its values span R. Hence P has exponent p, P′=Z(P)=R, and order p^{5n}. The map τ_P(x,y,z)=(bar y,bar x,bar z) is an involutory automorphism. Class two is less than p; the subgroup/ideal and automorphism interface is the [pinned Lazard source](../REFERENCES.md#lazard-bch-interface), arXiv:2310.17595v3, §2.3, Facts 2.13–2.14. All ring exponentials below are finite nilpotent series, separate from the notation exp for this Lie/group correspondence.

Let A_p be the additive group F_p^{m+1}, written t=(g,b), where

    g=Σ_{j=0}^{m−1} a_j ε^{2j+1},   b∈F_p.

It acts on the two W-halves by multiplication by exp(g/2) and on R by T_t=exp(g); b acts trivially on P. Let A_q=⟨c⟩≅C_q and choose λ∈F_p× of order q. Its action is (x,y,z)↦(λx,λ⁻¹y,z). These actions commute, preserve (1), and are inverted by τ_P, since bar g=−g.

Let F=F_{q^s} and η∈F× have order p. Take V=⊕_{j=0}^m F² with the nondegenerate F_q-alternating form γ given by the sum of the field traces of the determinants. Let Q be the exponent-q extraspecial group on V⊕V⊕F_q, with the same product (1) using γ. On the j-th plane of V, A_p acts by η^{a_j} for j<m and by η^b on the last plane; it acts inversely on the opposite half. A_q acts trivially on Q. Let τ_Q swap the halves and fix Z_Q=F_q. Set

    D=P×Q,   A=A_p×A_q,   G=D⋊A,

and let τ restrict to τ_P,τ_Q and invert A. Its first-half stabilizers are S_P=W⊕0⊕0 and S_Q=V⊕0⊕0.

The P-central graph is a cocycle, not a homomorphism into Z(G). Define

    f(g,b)=(exp(g)−1)/ε+b ε^{2m}.                     (2)

Here g is its specified polynomial representative, and the exponential in the numerator is computed through degree n **before** division by ε. The quotient is then reduced modulo εⁿ. This prescription retains its top coefficient and does not divide by a unit in R. All needed factorials are invertible because p>n. The exponential identity modulo ε^{n+1} gives

    f(t+u)=f(t)+T_t f(u),
    f(t)+T_t bar f(t)=2f(t).                         (3)

The second identity follows from bar((exp g−1)/ε)=(1−exp(−g))/ε; the bottom ε^{2m} is fixed by T_t and bar. If the first nonzero coefficient of g is a_j, f has leading term a_j ε^{2j}. If g=0 and b≠0, its leading term is b ε^{2m}. In particular f(t)=0 iff t=0.

Use f to lift A_p to the subgroup {z_P(f(t))t:t∈A_p}, and lift c to z_Q(1)c. The cocycle identity makes the first lift a subgroup isomorphic to A_p. The two lifted groups commute, since A_q fixes R and A_p fixes Z_Q. They normalize both first halves. Let H be their semidirect product with S_P×S_Q, and let K={g∈G:τ(g)=g⁻¹}.

The dimensions and orders are

    |G|=p^{11m+6}q^{4(m+1)s+2},
    |H|=|C_G(τ)|=p^{5m+3}q^{2(m+1)s+1},
    [G:H]=p^{6m+3}q^{2(m+1)s+1}.                    (4)

For the fixed count, τ_P has a 2n-dimensional fixed space on the swapped W-halves and m+1 even monomials in R. The Q count is its usual half plus center. No nonidentity odd A-label is τ-fixed. Although H∩τH=1, (4) gives |G|/|H|²=p^m, so the symmetric exact-factorization lemma does not apply here.

## Full marked transversality and the canonical group

Let Λ be the full outside-involution class in G⋊⟨τ̂⟩. Since G has odd order, Λ=τ̂K, |K|=|G:C_G(τ)| and Λ²=K² is G-conjugacy invariant. A product of two marked involutions is inverted by one factor. We exclude inversion of every nonidentity h∈H by any marked involution; this is the original-group collision test, not a projected quotient-loop claim.

Write its torus labels as t=(g,b) and c^k. Suppose g≠0 and j is its first nonzero index. Reduce the local P⋊A image modulo ε^{2j+1} in both vector halves and center. This is a valid group quotient, stable under τ and all actions, because the bracket preserves that ideal. The own-prime action of t becomes trivial, and f(t) becomes the nonzero fixed central element a_j ε^{2j}. If k=0, a nonzero reduced first-half vector cannot be negated by a marked involution: inner conjugation does not change the vector shadow, all torus actions preserve the halves, and τ swaps them. If that vector is zero, the fixed nonzero central element prevents inversion. The independent t-label does not affect this conclusion, since its action is trivial in the quotient and its label is inverted by τ.

If instead k≠0, the operator λ^k exp(g/2)−1 is a unit on S_P, since its constant coefficient is λ^k−1. Conjugation by S_P removes the P-vector of h without a central correction; S_P is abelian and the torus preserves it. The remaining local image is z_P(f(t))t c^k, with commuting p- and q-primary parts. In the quotient just used, the p-part has a nonzero τ-fixed central coordinate and a separately inverted t-label. It cannot be inverted. Conjugation by S_P preserves H and the marked collision question.

If g=0,b≠0, t acts trivially on P and f(t)=bε^{2m} is central in all G and fixed by τ. For k=0 the first-half shadow or this center excludes inversion. For k≠0, conjugate away the first-half vector using λ^k−1, and use the fixed nonzero central p-part. If t=0 but k≠0, inspect Q: its incoming A_p-label is zero, and its first-half shadow or the nonzero fixed q-central twist excludes inversion. If all labels vanish, a nonzero first-half P or Q component is excluded by the same swap argument. There is no nonidentity purely central element in H with zero labels.

Thus H∩Λ²=1. The count (4) and conjugacy invariance yield all conjugate transversals. Full inversion is inverse- and sandwich-closed, so the canonical folder interface gives a left Bol loop.

The pure A lies in K. The normal subgroup ⟨K⟩ of odd G contains its normal closure. A_q has no fixed vector on P/Φ(P)=P/Z(P); the m+1 independent A_p characters have no common fixed vector on Q/Φ(Q). Commutators therefore generate both Frattini quotients and hence P,Q. It follows that G′=D and ⟨K⟩=G.

An A-element inducing inner automorphisms on both factors must act trivially on both central quotients. The Q characters detect every A_p-label; with that label zero, the P scalar detects every A_q-label. Thus it is the identity, and C_G(D)=Z(D). A normal subgroup inside H intersects D trivially: a nontrivial normal Sylow intersection would meet its center, disjoint from H. It then centralizes D and lies in Z(D)⊂D, so is trivial. Therefore H is core-free and G is canonical. Here C_G(D)=Z(D) must not be confused with Z(G). In fact

    Z(D)=R×Z_Q,   Z(G)=F_p ε^{2m}×Z_Q.               (5)

The generator g=ε acts on R by exp ε, a single unipotent Jordan block of length n. Hence (5) is a strict inclusion for every m≥1.

## Strict defect for all invariant normal subgroups

Let N◁G be τ-stable, L_P=N∩P, L_Q=N∩Q and I=log L_P. Put C=I∩R. Invariance under the action exp ε is equivalent to invariance under multiplication by ε: exp ε−1=ε times a unit, and ε is its truncated logarithm. The invariant subspaces of this single Jordan block are precisely

    C=0 or ε^kR (0≤k≤2m).

For C=ε^kR define d(C)=m+1−⌈k/2⌉, the number of even monomials at least k; put d(0)=0. This is dim C^τ. Every nonzero L_P meets R and thus has d(C)>0. Coprime A_q averaging splits I into C and its vector shadow, since the two vector weights λ,λ⁻¹ are nontrivial. Projection to the τ-plus space injects S_P∩L_P modulo C, because the first half misses the negative eigenspace and the center. Therefore

    |C_{L_P}(τ)|/|S_P∩L_P| ≥ p^{d(C)}.               (6)

For Q the analogous ratio is at least q whenever L_Q≠1, since every nontrivial normal subgroup of Q contains its cyclic fixed center.

Let T_p×T_q be the image of N in A, and J_p×J_q the image of H∩N. To bound J_p, choose a p-element h∈H∩N above a prescribed t; its A_q-label is zero. Let its P-vector be s∈S_P. The commutator with the pure generator c∈A_q has P-vector (1−λ)s and no P-central correction, because S_P is abelian; its other coordinates are trivial. Normality and λ≠1 put s into log L_P. Remove this S_P component from h, retaining an element of H∩N. The P-coordinate of hτ(h) is now exactly f(t)+T_t bar f(t)=2f(t). This element is in N∩D, whose Sylow factors separate, so f(t)∈C.

For C=ε^kR, the leading terms in (2) imply that labels with f(t)∈C form a coordinate subspace of dimension d(C): a_j must vanish whenever 2j<k, and the independent b is allowed. For C=0 all labels vanish. Consequently

    |J_p|≤p^{d(C)}.                                  (7)

No splitting of N's torus lifts is used. If J_q≠1 but L_Q=1, choose a q-element lift in H∩N. It centralizes Q by normality, while its own A_q action on Q is trivial, so its S_Q vector must vanish. The Q-component of hτ(h) is then a nonzero twice-central graph label, contradicting L_Q=1. Thus J_q can cancel a factor q only if the corresponding local normal factor is present.

Fixed elements of N have trivial A-image. Hence the exact fixed/stabilizer ratio is the product of the two local ratios divided by |J_p||J_q|. If T_q≠1, the P-vector action of a lift with nonzero q-label has eigenvalues λ^{±k}exp(g/2), each differing from 1 by a unit. Commutators force L_P=P. Its exact local ratio is p^{m+1}, so if T_p<A_p it leaves a strict p-factor after division by |J_p|≤|T_p|. If T_p=A_p as well, the independent characters force L_Q=Q, and N=G. If T_q=1 and T_p≠1, at least one Q-plane is moved, so L_Q≠1 and its center leaves an uncancelled q-factor since J_q=1. If T_p=T_q=1 and N≠1, a nonzero local intersection contributes a positive fixed-center factor with J=1. Every nontrivial proper invariant normal has strict defect.

The reviewed [strict-defect criterion](odd-folder-radicals.md), source `65a3e58df517df59656ab948ac9d122208f62c4a`, therefore gives simplicity. Its maximal-simple-quotient argument is retained; inversion is not presumed to descend through every arbitrary quotient.

## Direct properness and all isotopes

For properness restrict to G₀=(F_p ε^{2m}×Q_last)⋊(⟨b⟩×A_q), where Q_last is the last Q-plane together with the common Q-center. The b action is trivial on P and scalar η on that plane. Its H-intersection is exactly the two central graph lifts and that Q first half. The explicit section from the [reviewed fixed-central construction](odd-unbounded-derived-class.md#a-direct-moufang-witness), source `722ba8c289c96dfd87c98f9a5ab3dcb8b2080998`, lies in G₀ and is also the unique ambient K-section. It gives the actual subloop product

    (u,t_p,t_q)·(v,s_p,s_q)
      =(u+η^{t_p}v,t_p+s_p,t_q+s_q−γ(u,v)).          (8)

Choose v,w with γ((η−1)v,w)≠0. For X=(0,1,0), Y=(v,0,0), Z=(w,0,0), the central coordinates of (XY)(ZX) and (X(YZ))X are −γ(ηv,w) and −γ(v,w). They differ, proving properness without CFSG. No generation or faithfulness assumption is imposed on the restricted subfolder.

The entire loop is a G-loop by explicit outer automorphisms. For each odd c∈R⁻, put α_c=1+εc, and let μ_c be its unique square root congruent to 1 modulo ε. Both are bar-fixed. Define φ_c on P by scaling the two vector halves by μ_c and the center by α_c; fix Q,A_q; and map each pure p-torus element t to

    z_P(δ_c(t))t,   δ_c(t)=−εc f(t)=−c(T_t−1).       (9)

The scaling preserves (1), δ_c is an A_p cocycle, and its values are central in P, so all semidirect relations hold. The maps preserve H because α_c f(t)+δ_c(t)=f(t). They compose by

    φ_c φ_d=φ_{c+d+εcd}.

The odd space is closed under this operation; the corresponding even units multiply. This gives a group of p^m automorphisms, with inverses and distinct parameters. On P they commute with τ. Using bar f=T_t⁻¹f, direct calculation on a torus generator gives

    φ_c τ φ_c⁻¹=Inn(z_P(2c)) τ,                     (10)

where Inn(g)(x)=gxg⁻¹. For example the central correction to t⁻¹ on both sides is 2c(1−T_t⁻¹). The formal extension sends τ̂ to z_P(2c)τ̂, an involution because bar c=−c; these extensions respect the same group law.

We have C_H(τ)=1: a fixed element has zero torus label and first-half vectors equal to their second-half images, forcing them to vanish. The p^m involutions z_P(2c)τ̂ occupy distinct H-orbits. Otherwise, applying an inverse φ first reduces to a nonzero such involution H-conjugate to τ̂. Torus comparison forces the conjugator into S_P×S_Q. Its τ-displacement being central forces both first-half vectors to vanish by the direct half decomposition; it is the identity and cannot produce a nonzero c. Each of these orbits has size |H| because φ_c preserves H. Finally (4) gives |Λ|/|H|=p^m, so these orbits exhaust Λ. The resulting stabilizer-preserving automorphisms send the full inverted section to every shifted section. The general principal-isotope interface reviewed at `ea836a5f328d6bc52913aac8fd1841a87072f5f8` proves the G-loop assertion.

At exact source `379317e583fa1e0c9171d526562c4f7e484d7d19`, GPT-6.1 Terra reviewers [model reviewer identity omitted], [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the full uniform construction. Each checked the elementary parameter availability, exponential precision and cocycle identities, all marked-collision cases, canonical generation and core, every invariant normal-subgroup defect including nonsplit lifts, the actual bottom-coordinate Moufang subloop, and all outer-automorphism and marked-orbit steps. Their acceptances retain the cited Lazard, canonical-folder, strict-defect and principal-isotope interfaces. No computation, fresh primary-source audit, formal verification or novelty claim is made. In particular the construction neither derives a normal form for arbitrary noncentral-center envelopes nor bounds their center/module complexity; it supplies unbounded surviving cases that such a normal form must accommodate.
