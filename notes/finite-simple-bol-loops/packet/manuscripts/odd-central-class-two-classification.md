# Odd Bol loops with central class-two derived Sylow factors

**Continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`], with scoped reviews of the exponent-p case and the exponent-free continuation below.** The precise endpoint is construction, exhaustion and an isomorphism criterion for every finite simple nonassociative odd left Bol loop Q whose canonical left multiplication group G has nilpotent derived subgroup D=G′, and whose nontrivial Sylow factors P_i have exponent p_i, class at most two and Z(P_i)≤Z(G). The primes p_i are distinct and odd. The baseline is the [extraspecial-derived classification](odd-extraspecial-classification.md), independently accepted at `dce010e03e56d50af4fbfbb4aba69806228ec518`; the new gap is arbitrary elementary center rank under the stated class and centrality hypotheses. No assertion is made about noncentral Sylow centers, higher class or exponent, nonnilpotent D, or even loops.

The proposed result below gives tensor and linear-operator parameters, a finite central-subspace closure test for simplicity, and an explicit linear equivalence. Unlike the rank-one case, it does not give a closed character/partition normal form for those tensor orbits. Its quantifiers and completion criterion concern this structural branch only.

## Inputs and notation

Use the canonical odd folder (G,H,K,τ) and the reviewed inputs from [the derived-envelope analysis](odd-folder-radicals.md#derived-envelope-constraints-on-the-fixed-stabilizer), source `e896039d004ff3882621aca115b1a39cc8fed207`: G=HD, τ induces inversion on A=G/D, C_G(τ)≤D, |H|=|C_G(τ)|, and K is the full τ-inverted set. In G⋊⟨τ̂⟩ all outside involutions form Λ=τ̂K; Λ²=K² is G-conjugacy invariant and meets every conjugate of H only in 1. The strict-defect/equality criterion is the version reviewed at `65a3e58df517df59656ab948ac9d122208f62c4a`, with its maximal-simple-quotient qualification. The isotope input is the principal-isotope interface reviewed at `ea836a5f328d6bc52913aac8fd1841a87072f5f8`. The earlier [necessity theorem](odd-extraspecial-classification.md#splitting-and-simultaneous-local-alignment) at `7941d518a3142819b44a75b089c1386b206e87f1` supplies an elementary complement lemma whose hypotheses do not require a rank-one center. Schur–Zassenhaus is the source version recorded in REFERENCES.md (Craven 2012, §2.1, Theorem 2.1).

Put Z_i=Z(P_i), U_i=P_i/Z_i, S_i=H∩P_i and W_i=S_iZ_i/Z_i. Each Z_i is elementary abelian. It is fixed pointwise by τ: otherwise a nonzero negative central line is a proper τ-stable normal subgroup N with |C_N(τ)|=|H∩N|=1, contradicting strict defect. Core-freeness gives H∩Z_i=1. The commutator induces a Z_i-valued alternating form Ω_i on U_i, with zero radical by definition of the center. Since [S_i,S_i]≤H∩Z_i, S_i is elementary abelian and W_i is isotropic. It is A-invariant because G=HD. Write B_i=A_{p_i′}.

## Necessary fixed spaces and elimination of central graph offsets

First U_i^{B_i}=0. From D=G′ and G=HD one has U_i=W_i+[U_i,A]: the H′ contribution lies in W_i, and commutators with D give the second term. Coprime averaging splits U_i=F_i⊕M_i with F_i=U_i^{B_i} and M_i=[U_i,B_i]. The two summands are Ω_i-orthogonal because B_i fixes Z_i, so Ω_i restricted to F_i has zero radical. Averaging the displayed equality gives F_i=(W_i∩F_i)+[F_i,A_{p_i}]. On F_i/(W_i∩F_i), the augmentation ideal of the finite p_i-group A_{p_i} is nilpotent; equality with its image forces this quotient to be zero. Thus F_i≤W_i is isotropic and orthogonal to M_i, contradicting zero radical unless F_i=0.

The scalar-center proof of shadow avoidance cannot simply be invoked here: a nonzero w may have Ω_i(w,U_i) properly contained in Z_i, so a central graph offset could evade the local K² test. The actual coprime action removes this offset. Fix i and work in G/D_{p_i′}, where P_i embeds. The inverse image of B_i⋊⟨τ̂⟩ is an extension by the normal Hall p_i-subgroup P_i. Schur–Zassenhaus gives a complement, chosen to contain the original τ̂ by P_i-conjugacy. Let B₀ be its B_i-part. The image of H over B_i has normal Hall kernel S_i and has a B-complement B_H, which is P_i-conjugate to B₀. Temporarily conjugate the original H by that P_i element while retaining τ.

The class-two exponent-p_i BCH model is a vector space U_i⊕Z_i with group law adding half the commutator. Averaging a linear section over the coprime group B₀⋊⟨τ̂⟩ makes it equivariant. The conjugated S_i is then the graph of a linear B₀-map W_i→Z_i. Because W_i^{B_i}=0 and Z_i is trivial, this map is zero. Any nonzero w∈W_i∩(U_i)₋ would therefore lift to an actual element of this conjugate of H that is inverted by τ. It would belong to H^g∩K, a contradiction. The collision is in the original P_i and folder, not an assumed quotient folder. Inner conjugation does not change W_i, so

    W_i∩(U_i)₋=0.                                      (1)

The space W_i∩τ(W_i) is A- and τ-stable. By (1) τ acts identically there; since τ inverts A, the odd-order A-action there is trivial. It is therefore zero because U_i^{B_i}=0.

For completeness, the central-character bound of the pinned necessity theorem works for arbitrary elementary Z_i. In G/(Z_iD_{p_i′}), its elementary complement lemma gives a τ-compatible A-complement, since U_i^{B_i}=0. Applying complement conjugacy to U_i/W_i aligns a temporary conjugate of H with W_i⋊A. A Sylow p_i-subgroup of that conjugate stabilizer maps injectively into W_i⋊A_{p_i}, since its kernel would lie in H∩Z_i. The inverse image of the pure A_{p_i} is a subgroup C≅A_{p_i}. In G/D_{p_i′}, the map χ(c)=τ(c)c lies in Z_i and is a homomorphism. If its kernel C₀ were nontrivial, C₀D_{p_i′} would be τ-stable. Conjugacy of its Hall complements supplies an outside element normalizing and inverting C₀; an odd power makes it an outside involution λ∈Λ. For c∈C₀, c⁻² is then in H^g∩Λ², impossible. Thus χ is injective and A_{p_i} is elementary with log_{p_i}|A_{p_i}|≤dim Z_i. This argument does not use the dimension-one center assumption or identify the temporarily conjugated folder with the original loop.

Set a_i=log_{p_i}|A_{p_i}|, z_i=dim Z_i, w_i=dim W_i and u_i^+=dim(U_i)₊. The fixed-element and stabilizer order comparison gives

    a_i+w_i=z_i+u_i^+.

Projection along (U_i)₋ in (1) gives w_i≤u_i^+, hence a_i≥z_i. Equality follows from χ-injectivity. The nontrivial B_i weights pair with their distinct inverses under τ, so u_i^+=dim U_i/2 even when the own-prime action is not semisimple. Consequently

    A_{p_i}≅Z_i,   U_i=W_i⊕τ(W_i),   w_i=dim U_i/2.      (2)

These statements hold for the original shadows. For the original H, an element of H∩C_G(τ) lies in H∩D; each shadow is in W_i∩τ(W_i)=0 and each remaining central coordinate is in H∩Z_i=1. Thus H∩C_G(τ)=1. The order equalities give |H|=|Q| and G=C_G(τ)H. As before H acts regularly on Λ, and the pinned principal-isotope interface gives the G-loop property. Every prime of A occurs in D, since |H|=|C_G(τ)| and C_G(τ)≤D.

## Simultaneous normal form and construction parameters

The elementary complement lemma applies componentwise to U_i and U_i/W_i. The fiber-product and actual-folder alignment proof in the reviewed [global splitting](odd-extraspecial-classification.md#global-splitting-and-preservation-of-the-original-loop) now applies without a rank-one condition: choose an inverted A-complement in G/Z(D), align H modulo Z(D), and replace the aligning conjugation by one in C_G(τ) using G=C_G(τ)H. Hence the original loop is preserved up to folder isomorphism. If E is the preimage of that A-complement, E∩H maps isomorphically onto A and splits the central extension. The map c↦τ(c)c is injective on E∩H and, by (2), has the same order as Z(D). Halving this central character gives an inverted complement identified with A=∏_iZ_i and

    H=(∏_iS_i)⋊{a z(a):a∈A},                            (3)

where z:A→Z(D) is the fixed coordinate identification.

Set β_i(x,y)=Ω_i(x,τy) on W_i. It is an alternating Z_i-valued bilinear map with zero radical. Coordinates based on the actual S_i and τ(S_i) have no central shear, since the complement normalizes both. Thus

    P_i=W_i⊕W_i⊕Z_i,
    Ω_i((x,y),(x′,y′))=β_i(x,y′)+β_i(y,x′),
    (v,z)(v′,z′)=(v+v′,z+z′+½Ω_i(v,v′)),
    τ(x,y,z)=(y,x,z),
    a(x,y,z)=(ρ_i(a)x,ρ_i(a)⁻¹y,z),
    β_i(ρ_i(a)x,y)=β_i(x,ρ_i(a)y).                       (4)

The commuting ρ_i form a representation of A, with W_i^{B_i}=0 and faithful combined action. The image of β_i spans Z_i. To justify this last condition, quotient the split group by ∏P_i′. Its D-image is abelian; in these coordinates A acts linearly on U_i, fixes Z_i/P_i′, and contributes no central shear. The derived subgroup of that quotient has no Z_i/P_i′ component. Since D=G′, that component must vanish. Thus P_i′=Z_i. In particular the hypotheses force the Sylow groups to be special, and an abelian central Sylow factor cannot survive.

Conversely the precise input data are: a finite set of at least two distinct odd primes; nonzero finite F_{p_i}-spaces Z_i,W_i; a zero-radical alternating β_i:W_i×W_i→Z_i with spanning image; A=∏_iZ_i; and representations ρ_i of A, self-adjoint for β_i as in (4), with W_i^{A_{p_i′}}=0 and faithful combined action. Define G,τ,H by (3)–(4). All these conditions are finite linear or matrix tests at fixed dimensions.

The full inverted set K above a∈A has coordinates (x,−ρ_i(a)⁻¹x,0). In a product of two such elements lying in H, the second coordinate forces x′=−ρ_i(b)x and the central coordinate becomes

    ½[β_i(x,ρ_i(a)⁻¹x)+β_i(x,ρ_i(b)x)]=0.

Self-adjointness and alternation imply both vector-valued terms vanish in odd characteristic. The central labels z(ab) in H then force ab=1, and the first coordinate vanishes too. Therefore H∩K²=1. The full outside-involution class makes K² conjugacy invariant, and |K|=[G:H]=|A|∏|W_i|; the inverse- and sandwich-closed set K gives a Bol folder.

Coprime averaging gives [U_i,B_i]=U_i. Since Φ(P_i)=P_i′=Z_i, commutators with A generate all P_i, so G′=D and K generates G by the full-inverted-set normal-generation argument. A normal subgroup contained in H has trivial intersection with D: any nontrivial normal subgroup of a finite p-group meets its center, disjoint from H. It then centralizes D; faithful A-action makes C_G(D)=Z(D), again disjoint from H. Thus the folder is faithful and G is its canonical group. Counts and the coordinate swap give H∩C_G(τ)=1 and H regular on Λ, hence a G-loop.

Right-H coset coordinates (u_i,t_i)∈W_i×Z_i have product

    (u,t)·(v,s)=(u_i+ρ_i(t)v_i, t_i+s_i−β_i(u_i,v_i))_i. (5)

The two half-commutator terms in the reviewed operator coordinate calculation cancel exactly as vectors in Z_i, so its derivation applies to (4). This can also be checked directly by multiplying the section (−ρ_i(−t)u_i,u_i,0) over −t and then removing the torus and first-vector coordinates on the right.

## All τ-stable normal subgroups

Let N◁G be τ-stable, with L=N∩D=∏L_i. Put C_i=L_i∩Z_i, V_i=L_iZ_i/Z_i≤U_i and T=π_A(N). Each V_i is A- and τ-stable and

    Ω_i(V_i,U_i)⊆C_i.                                  (6)

The subgroup L_i/C_i is the graph of a linear map V_i→Z_i/C_i: its commutator is zero modulo C_i by (6). This map is B_i-equivariant. Since V_i^{B_i}=0 and Z_i/C_i is trivial, the map is zero. Hence L_i consists exactly of all (v,c) with v∈V_i,c∈C_i.

For n=d a∈N, normality under the pure complement A makes the vector of d fixed modulo V_i under B_i. Exactness of coprime invariants gives (U_i/V_i)^{B_i}=0, so that vector lies in V_i. Multiplication by an element of L reduces n to a z. Its product with its τ-image is z²∈∏C_i; oddness gives z∈∏C_i, so a∈N. Therefore

    N=(∏_i(V_i×C_i))⋊T,
    (ρ_i(t)⊕ρ_i(t)⁻¹−1)U_i⊆V_i for all t∈T.            (7)

Conversely any A,τ-stable V_i, subspaces C_i≤Z_i and subgroup T≤A satisfying (6)–(7) give a τ-stable normal subgroup. In checking conjugates of a torus element by u∈U_i, the BCH central correction is a scalar multiple of Ω_i(u,(t−1)u). This lies in C_i because (t−1)u∈V_i and (6) holds; the vector condition alone is not being substituted for the group calculation.

Write T_i=T∩A_i≤Z_i, and d_i^+=dim(V_i)₊, w_i′=dim(V_i∩W_i). The actual H-intersection has torus image T∩∏C_i and kernel ∏(V_i∩W_i). Since fixed elements of N have zero odd A-coordinate,

    |C_N(τ)|/|H∩N|
      = ∏_i p_i^{dim C_i+d_i^+−w_i′−dim(T_i∩C_i)}.      (8)

Each exponent is nonnegative: V_i∩W_i injects into (V_i)₊ by projection, and dim(T_i∩C_i)≤dim C_i. Equality holds precisely when all exponents are zero. The pinned criterion gives simplicity iff every proper nontrivial tuple has strict defect.

## Simplicity by closure of central subspaces

The normal-subgroup test reduces further and does not require enumeration of V_i or T. For a tuple of subspaces C_i≤Z_i, identify C=∏C_i≤A and put

    X_i(C)=Σ_{c∈C}(ρ_i(c)−1)W_i,
    F(C)_i=C_i+span_Fpi{β_i(x,w):x∈X_i(C), w∈W_i}.       (9)

Call C closed if F(C)=C. The exact simplicity criterion is

    the only closed C are 0 and A.                      (10)

Indeed if C is a nonzero proper closed tuple, take V_i=X_i(C)⊕τ(X_i(C)) and T=C. Commutativity makes X_i(C) A-invariant; it is stable under inverse operators too. Closure is exactly the central condition (6) for these V_i, and (7) holds by definition. The corresponding N_C is nontrivial and proper because its A-image is C. The swap has fixed dimension dim X_i(C), its W_i-intersection has that same dimension, and T_i=C_i. Thus every exponent in (8) is zero, giving nonsimplicity.

Conversely equality in (8) for a proper nontrivial N forces C_i⊆T_i, since each exponent is a sum of the two nonnegative dimension differences. Therefore X_i(C)⊆V_i and (6) implies β_i(X_i(C),W_i)⊆C_i, so C is closed. If C=0, zero radical in (6) forces V_i=0 and (7) plus faithfulness forces T=0, contradicting N≠1. If C=A, then T=A, and (7) with [U_i,B_i]=U_i forces V_i=U_i, contradicting N<G. Thus a failure of simplicity produces a nonzero proper closed tuple. This proves (10).

The map F is monotone and extensive. Its stable iterate, not necessarily F in one step, is a closure operator on the finite lattice of central-subspace tuples. One may test (10) by checking that every nonzero one-dimensional central seed generates all A under iteration: any nonzero closed tuple contains such a seed, and closure is monotone. With dim Z_i=1 this reduces exactly to strong connectivity of the cross-action graph in the reviewed extraspecial theorem. Higher-dimensional centers require subspaces rather than just vertex subsets.

## Properness, isomorphisms and scope

For every i, W_i≠0 and W_i^{B_i}=0 guarantee a nontrivial cross-prime action ρ_i(a_j), j≠i. Choose u with (ρ_i(a_j)−1)u≠0, then v with β_i((ρ_i(a_j)−1)u,v)≠0, using zero radical. In (5), let x have only the central label a_j, and y,z only node-i vectors u,v. The Moufang sides (xy)(zx) and (x(yz))x differ in the node-i central coordinate by that nonzero vector. This proves properness for all input data, including those passing (10), without CFSG.

A loop isomorphism preserves D, its distinct-prime Sylow factors, centers, S_i, and the unique inversion automorphism. Faithfulness gives Z(G)=Z(D). As in the scalar-center proof, the complement in H is intrinsically {h∈H:τ(h)h∈Z(G)}: complementary W_i and τW_i components vanish precisely for a pure twisted torus element. The central character identifies its action on A with its action on Z(D). Thus two input data give isomorphic loops iff the prime sets agree and there are linear bijections T_i:W_i→W_i′ and E_i:Z_i→Z_i′, with E=∏E_i also acting on A, such that

    E_i β_i(x,y)=β_i′(T_i x,T_i y),
    T_i ρ_i(a)=ρ_i′(E(a)) T_i  for every a∈A.             (11)

Necessity follows from the intrinsic complement and commutators. Conversely (x,y,z)↦(T_i x,T_i y,E_i z), a↦E(a), defines a BCH group isomorphism preserving τ,H,K, so it gives a loop isomorphism. This is a finite explicit linear equivalence test at fixed dimensions. No classification of these tensor orbits by a short discrete list, efficiency bound, or universal bound on dimensions is asserted.

Together (2)–(11) supply the proposed construction, soundness, exhaustion, properness, simplicity and isomorphism parameterization for exactly the central class-two exponent-p derived-Sylow branch stated at the start. The exponent-p necessity, normal-subgroup and closure steps have the scoped reviews recorded below; those reviews do not cover the later arbitrary-exponent continuation. No new computation, literature-novelty assertion or formal verification is claimed. The complete finite-simple-Bol goal remains open.

## Explicit example with two-dimensional centers

Take E=F₂₇, ζ∈E× of order 13 and η=3∈F₁₃× of order 3. Set Z₃=A₃=F₃², Z₁₃=A₁₃=F₁₃², W₃=E²⊕E² and W₁₃=F₁₃²⊕F₁₃². Let β₃ output the alternating trace form on each plane into its corresponding central coordinate, and β₁₃ output the two alternating prime-field forms. These forms have zero radical and spanning image. An element (a₁,a₂)∈A₃ acts on the two W₁₃ planes by η^{a₁},η^{a₂}; an element (b₁,b₂)∈A₁₃ acts on the two W₃ planes by ζ^{b₂},ζ^{b₁}. Own-prime actions are trivial. The operators commute, are self-adjoint for the vector-valued forms, give faithful combined action and have no cross-prime fixed vectors. Thus they meet the construction hypotheses.

For any central subspaces C₃,C₁₃, a nonzero first coordinate in C₃ forces the first central axis of C₁₃ into F(C); a nonzero second coordinate forces its second axis. A nonzero first coordinate in C₁₃ forces the second central axis of C₃, and a nonzero second coordinate forces its first axis. A nontrivial scalar minus one is invertible on the targeted plane, whose pairing spans exactly that output axis. These four implications form the cycle

    3₁ → 13₁ → 3₂ → 13₂ → 3₁.

Any nonzero central-subspace tuple, including one with only diagonal lines, has a nonzero coordinate and therefore propagates all four axes. Thus the only closed tuples are 0 and A. Criterion (10) makes the resulting loop simple; the direct witness proves it proper. Its order is 3¹⁴·13⁶, and its derived Sylow centers each have rank two, so it lies outside the extraspecial-derived branch. These conclusions depend on the preceding exponent-p theorem, with the scoped reviews recorded below.

The standalone [central-subspace certificate](../code/verify_odd_vector_center_closure.py) enumerates the six subspaces of F₃² and sixteen subspaces of F₁₃² and applies these exact axis rules to all 96 pairs. Root read it before running bundled Python 3.12.14 with assertions enabled. Only zero/full were fixed, and every nonzero seed reached the full tuple in at most three iterations. The script implements neither finite fields nor loop multiplication, and does not prove the folder, normal-form or simplicity theorem. The certificate has the scoped independent proof/code review recorded below.

## Independent review of the exponent-p case

At exact source `15ecc63d113f7362e625c2b7d5c3d97a8d6ec6fd`, GPT-6.1 Terra reviewers [model reviewer identity omitted], [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the complete exponent-p parameterization. All three checked the coprime BCH alignment and original-folder collision, central-character equality, global splitting, normal-subgroup graphs and lifts, BCH central correction, both closure-criterion directions with C_i⊆T_i, properness, intrinsic-complement equivalence, and the rank-two-center cycle. Their acceptances retain the pinned folder, defect, complement and isotope interfaces. They explicitly distinguish this finite tensor/operator equivalence test from a closed list of tensor orbits. Reviewer [model reviewer identity omitted] also read and accepted the certificate and independently ran its pinned source with bundled Python 3.12 and assertions enabled, reproducing all 96 tuples, only zero/full fixed, and the three-iteration bound. The other two reviewers did not audit or run that optional certificate. No formal verification or novelty audit is asserted.

## Arbitrary odd exponent: extended endpoint

**Continuation with the scoped independent reviews below.** Remove only the exponent-p hypothesis from the endpoint above. Thus Q is any finite simple nonassociative odd left Bol loop with D=G′ nilpotent, every Sylow P_i of class at most two, and Z(P_i)≤Z(G). The proposed classification uses nonzero finite abelian p_i-groups W_i,Z_i, replacing the vector spaces in (3)–(11), and alternating **biadditive** maps β_i:W_i×W_i→Z_i with zero radical and additively generating image. Put A=∏Z_i, require faithful combined action by group automorphisms ρ_i, self-adjointness as in (4), and W_i^{A_{p_i′}}=0. All sums, spans and subspaces in (9) are replaced by sums, generated subgroups and subgroups of finite abelian groups. Equations (3)–(5) remain the construction; (10) remains the simplicity criterion for central subgroups; (11) uses abelian-group isomorphisms E_i,T_i. The following proof addresses the places where the elementary exponent mattered. It is not an assertion that all surviving P_i have exponent p_i.

### BCH additive groups and the coprime splitting

A finite odd class-two group P has a canonical abelian additive group L with addition

    x+y=xy[x,y]⁻¹ᐟ²,

using the convention [x,y]=x⁻¹y⁻¹xy. Unique square roots exist in the odd central commutator subgroup. The class-two commutator identities show this addition is commutative and associative, that the commutator is biadditive, and that the original product is x+y+½[x,y]. The underlying p-primary group L need not have exponent p. Automorphisms preserve these operations. Conversely a finite abelian p-group with an alternating biadditive central bracket and zero triple brackets gives the group by that product. Subgroups correspond to additive subgroups closed under the bracket: in one direction the commutator and its unique odd-order half lie in the subgroup, and in the other the displayed product stays in it. This supplies the BCH operations used here without assuming a vector-space structure.

Let Z=Z(P), U=L/Z, S=H∩P, W=SZ/Z and B=A_{p′}. The same strict-defect argument fixes Z pointwise under τ: a nonzero negative subgroup would contain a negative element of order p, giving the forbidden central normal line. The pairing Ω:U×U→Z is alternating biadditive with zero radical. The subgroup S is abelian and additive since [S,S]≤H∩Z=1; its image W is isotropic and A-invariant.

The proof U^B=0 still works. Coprime averaging is an idempotent endomorphism of every finite abelian p-group, using an integer inverse of |B| modulo its exponent. Thus U=F⊕[U,B] with F=U^B, and the two summands are orthogonal since B fixes Z. The identity U=W+[U,A] gives F=(W∩F)+[F,A_p]. For the finite abelian p-group M=F/(W∩F), the equality M=[M,A_p] descends modulo p. The augmentation ideal of F_p[A_p] is nilpotent, so M/pM=0; finiteness then implies M=0. As before isotropy and zero radical force F=0. This argument also covers nonsplit additive p-groups and does not use semisimplicity of A_p.

Choose the actual B⋊⟨τ̂⟩ complement in G/D_{p′} and temporarily align the image of H by P-conjugacy exactly as in the exponent-p proof. On its action on the BCH group L, coprime averaging gives the stronger statement

    L=C_L(B)⊕[L,B]=Z⊕[L,B].                            (12)

Indeed fixed points are exact for a coprime action on finite abelian p-groups; Z is fixed and U^B=0, so C_L(B)=Z. The additive complement [L,B] maps isomorphically onto U and is τ-stable because τ normalizes B. Thus the central additive extension splits equivariantly here; no general splitting theorem for abelian p-group extensions is assumed. The aligned S is the graph of a B-homomorphism W→Z. Since W^B=0, averaging gives W=[W,B], and such a homomorphism is zero. Therefore W∩U₋=0 by the same actual H^g∩K collision. The shadow is unchanged by inner conjugacy. The A,τ-stable subgroup W∩τW has no negative part, so τ is the identity there; τ inverts odd A, forcing its action trivial, and U^B=0 then gives W∩τW=0.

### The central character and arbitrary p-power orders

The elementary complement lemma in the pinned necessity theorem applies to a finite abelian p-group kernel U unchanged. In the preimage of normal B it uses Schur–Zassenhaus and C_U(B)=0 to obtain E=U N_E(B₀) with U∩N_E(B₀)=0. It does not use scalar multiplication by F_p. The same holds for U/W. Hence its τ-compatible quotient splitting and temporary stabilizer alignment produce a subgroup C≅A_p with a central homomorphism χ:C→Z in G/D_{p′}. The Sylow map is still injective: a p-element in its kernel inside ZD_{p′} belongs to H∩Z=1. The kernel collision using Hall-complement conjugacy and an outside inverting involution is identical. Thus χ is injective and |A_p|≤|Z|, without requiring either group elementary.

Fixed-point lifting and the stabilizer comparison now give the cardinality equation

    |A_p| |W|=|Z| |U₊|.

Projection W→U₊ is injective since W∩U₋=0. It follows that |A_p|=|Z| and |W|=|U₊|, and χ identifies A_p with Z as finite abelian groups. Furthermore |U₊|=|U₋|. Each p-adic layer p^rU/p^{r+1}U has no B-fixed vector, by exactness of coprime invariants. Over a splitting field its nontrivial B-weights are paired with their distinct inverses by τ, giving equal plus/minus dimensions. Since 2 is invertible, the τ-eigenspace idempotents commute with the p-adic filtration, so these layer counts multiply to equality of |U₊| and |U₋|. Together with W∩τW=0, this proves

    U=W⊕τW,    |W|²=|U|,    A_p≅Z(P).                 (13)

The original stabilizer again has H∩C_G(τ)=1: its shadow in each W∩U₊ is zero, and it avoids the center. Counts give |H|²=|G| and G=C_G(τ)H. The componentwise complement and actual-folder alignment argument therefore applies, and the central character splits G and identifies A with Z(D) exactly as before. Actual S and τS remove all central shears, producing (3)–(4) over finite abelian p-groups. In the split coordinates, quotienting by the subgroup generated by the values of β shows, as before, that D=G′ requires those values to generate all Z. This proves necessity of the stated exponent-free data.

### Construction, normal subgroups and closure without vector spaces

For the converse, the BCH product in (4) is meaningful because every center has odd order and division by 2 is unique. Self-adjointness still gives β(x,ρ(a)x)=−β(x,ρ(a)x), hence zero. The K² transversality calculation, the count |K|=[G:H], full marked-class argument, and coordinate product (5) are consequently unchanged. So are the direct Moufang witness and the regularity/G-loop argument.

Generation requires a slightly different formulation: Φ(P_i) need not equal Z_i at higher exponent. Instead [U_i,B_i]=U_i says the subgroup generated by torus commutators maps onto U_i. Its commutators then contain every value of Ω_i and hence all Z_i, because the β_i values generate Z_i. It therefore equals P_i. This proves G′=D and generation by K without using an incorrect Frattini equality. Core-freeness follows exactly as before from nontrivial normal p-subgroups meeting their center and from faithful A-action.

For a τ-stable N◁G, define the additive subgroups V_i,C_i and T as above. A subgroup of the BCH group is additive and bracket-closed, so L_i/C_i is a graph of a group homomorphism V_i→Z_i/C_i once Ω_i(V_i,U_i)⊆C_i. The graph is B_i-equivariant and vanishes since V_i=[V_i,B_i] while the target is trivial. Normality under the complement and (U_i/V_i)^{B_i}=0 remove the residual vector offsets in torus lifts. Finally τ-stability makes the residual central offset satisfy 2z∈C_i, which implies z∈C_i because the quotient has odd order. Thus (6)–(7) describe all τ-stable normal subgroups with subgroups in place of subspaces, including the same BCH central correction in their sufficiency proof.

The defect formula becomes

    |C_N(τ)|/|H∩N|
      = ∏_i (|C_i|/|T_i∩C_i|)
             (|(V_i)₊|/|V_i∩W_i|).                    (14)

Each factor is at least one, and in fact a power of p_i. The second assertion follows from the same injection V_i∩W_i→(V_i)₊; it needs no dimension. Equality therefore forces C_i≤T_i. Define X_i(C) and F(C) in (9) using additive subgroups and subgroup generation. A nonzero proper closed C produces N_C with V_i=X_i(C)⊕τX_i(C), T=C and equality in (14). Conversely equality for a proper nontrivial N gives C≤T, hence closed C by (6)–(7); C=0 forces N=1 using zero radical and faithfulness, while C=A forces N=G using [U_i,B_i]=U_i. The simplicity criterion (10) follows for arbitrary exponent. Its finite seed test now uses cyclic order-p_i subgroups in the individual centers: every nonzero central subgroup contains one, and monotonicity of F proves the same criterion.

Finally the intrinsic complement {h∈H:τ(h)h∈Z(G)} and its central-character identification remain valid for abelian p-groups. Necessity and sufficiency of (11) therefore hold with group isomorphisms T_i,E_i. One can list finite abelian p-group types at prescribed orders, all their biadditive maps and generator actions, and apply the explicit input, closure and equivalence tests. This is structural construction/isomorphism data with finite tests at fixed group types, not a closed normal form for all bimap orbits or an efficiency bound.

These arguments give an exponent-free parameterization of the central class-two derived-Sylow branch, with the scoped independent reviews below. They introduce no new computation. The reviewed exponent-p example and its finite certificate do not verify the new exponent-free claims. Noncentral Sylow centers, higher nilpotency class and nonnilpotent derived groups remain outside the result.

## Independent review of the arbitrary-exponent continuation

At exact source `598fa119be327480c829af2a9beb709b02886bc4`, GPT-6.1 Terra reviewers [model reviewer identity omitted], [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the complete arbitrary-exponent continuation. All checked odd BCH and subgroup correspondence, coprime additive splitting without a general abelian-extension splitting assumption, the central-character and p-adic weight arguments, original-folder alignment, generation without Φ(P)=Z, normal-subgroup graphs and lifts, the order defect formula, closure and order-p seeds, and the finite abelian-bimap equivalence. The acceptances retain the pinned earlier interfaces and concern only class-two derived Sylow factors with centers central in G. No new computation, formal verification or literature-novelty audit was performed; a closed normal form for all bimap orbits is not claimed.
