# Stabilizers and outer isotope automorphisms in the fixed class-four envelope

**Continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`], with the scoped independent reviews below.** Fix exactly the group G=(P×Q)⋊(A₁₁×A₅), inversion τ, Q-half S_Q and central graph z:A→Z(P)×Z(Q) in the [fixed-shadow construction](odd-fixed-shadow-simple-example.md), reviewed at `396d468577c78a43d2c4d1f4821b074ddfd477ea`. Let 𝔭=log P and σ=τ|𝔭. The endpoint here is to characterize which stabilizers of the form

    H(𝔰)=(exp 𝔰×S_Q)⋊{a z(a):a∈A},                  (1)

with 𝔰 an A₅-invariant F₁₁-Lie subalgebra, give a faithful generating simple Bol folder with the full inverted section K, and to decide the G-loop property for all of them. This fixes the entire envelope and graph, not just their orders. It does not classify other stabilizer graphs, other envelopes or all odd Bol loops. The previous reviewed [overlapping variant](odd-fixed-shadow-simple-example.md#an-overlapping-stabilizer-variant), source `f214f853346713f234786fdbf5566608a6aec26b`, supplies one baseline case; the gap is exhaustion of the remaining stabilizers in (1).

The precise answer is that (1) gives such a simple folder iff

    dim 𝔰=5,   𝔰∩Z(P)=0,
    (𝔰+Z(P))/Z(P) ∩ (𝔭/Z(P))₋ =0.                  (2)

Every resulting loop is proper and is a G-loop. Among the cases with H∩τ(H)≠1 there are exactly two loop isomorphism classes: the previous class-two stabilizer and a class-three stabilizer described below. No isomorphism census is asserted for the disjoint-stabilizer cases. The proof uses the pinned Lazard, canonical odd-folder, strict-defect, symmetric-factorization and general principal-isotope interfaces already recorded in the baseline manuscripts.

## Necessary conditions and weight decomposition

For a faithful simple folder (1), canonical odd-envelope equality |H|=|C_G(τ)| forces dim 𝔰=5, since the fixed count is 11⁶·5¹¹ and |H|=11^{dim 𝔰+1}5¹¹. Core-freeness forces 𝔰∩Z(P)=0 because Z(P) is central in G. For the last condition, suppose s∈𝔰 has nonzero σ-negative shadow. Write s=v+c z with σv=−v. The full A₁₁→Z(P) graph has a label a whose central value is −c z. Since A₁₁ acts trivially on P,

    exp(s) a z(a)=exp(v) a ∈H∩K,

and this is nonidentity. It has no Q-component or A₅ label, so τ indeed inverts the whole element. This contradicts the transversal. This use of central graph cancellation is specific to (1); negative-shadow avoidance is not inferred for arbitrary higher-class envelopes.

Let λ=3∈F₁₁ be the A₅ scalar. Its three distinct weight spaces on 𝔭 are

    V₊=⟨x,y′,v,w′⟩,   V₋=⟨x′,y,v′,w⟩,
    V₀=⟨u,u′,z⟩,

with weights λ,λ⁻¹,1, respectively. Subscripts here indicate A₅ weights, not σ eigenspaces. We have 𝔰=𝔰₊⊕𝔰₋⊕𝔰₀. Condition (2) gives 𝔰₊∩σ𝔰₋=0, so dim 𝔰₊+dim 𝔰₋≤4. Its projection on ⟨u,u′⟩ is injective and avoids the line u−u′, so dim 𝔰₀≤1. Equality of the total dimension forces equality in both bounds.

Write 𝔰₀=⟨a u+b u′+c z⟩, where a+b≠0. Either its shadow line differs from its σ-image and the full stabilizers are disjoint, or a=b and, after rescaling,

    𝔰₀=⟨f+e z⟩,   f=u+u′.                           (3)

To check that no central graph offset creates an extra intersection in the first case, compare h∈H∩τH. Its moving shadows lie in both 𝔰₊ and σ𝔰₋ (or vice versa) and vanish. Its remaining two zero-weight shadows are distinct lines unless (3) holds, so vanish too; the opposite graph labels then vanish in odd characteristic. In case (3), the common line is actually σ-fixed, and the same comparison gives H∩τH=exp⟨f+e z⟩ of order eleven.

In the disjoint case, |G|=|H|² and the symmetric envelope-factorization lemma at `7fbfbc5a56f4bb1ead9a4d6202c2d948a67950d8` gives the full Bol folder and G-loop property. It remains to handle (3).

## Exhausting the overlapping stabilizers

Set A=𝔰₊ and B=σ𝔰₋ inside V₊; in this paragraph A denotes a subspace, not the torus. They are complementary and invariant under N=ad f. On V₊, N has two Jordan blocks of size two. Hence V₊ is free of rank two over R=F₁₁[t]/(t²), with t acting by N, and A,B are complementary R-direct summands. A finite free module over this local ring has free direct summands: choose a basis modulo t and lift it; Nakayama gives generation and the complementary ranks give equality of dimensions. Thus the dimensions of A,B are (4,0), (2,2) or (0,4).

The extreme cases are ⟨f+e z,V₊⟩ and ⟨f+e z,V₋⟩. The automorphisms below remove e. The plus case is the reviewed overlapping stabilizer. Its mirror has the same full transversal and normalizer argument, with the two copies interchanged. The two are isomorphic within the fixed graph: apply σ on P, invert A₅, leave A₁₁ unchanged, and on Q use

    (r,s,t)↦(T r,T s,−t),   T(a,b)=(−a,b) on W=F_{5⁵}².

The map T multiplies β by −1 and commutes with the scalar A₁₁-action. This Q-map preserves S_Q and commutes with τ_Q. Its action on Z_Q matches inversion of A₅, so the full map preserves the central graph, commutes with τ and exchanges the extreme stabilizers.

For the mixed case choose free generators

    X=a x+b y′+α₀v+α₁w′,
    Y=c x′+d y+δ₀v′+δ₁w.

The leading vectors of X and σY are independent, so ad−bc≠0. Since [X,NY]=−(ad+bc)z is central and belongs to 𝔰, condition (2) forces ad+bc=0. Thus all a,b,c,d are nonzero. Rescale the generators to a=c=1 and then d=−b. Adding multiples of NX,NY removes the v,v′ coefficients. We obtain

    X=x+b y′+α w′,   Y=x′−b y+δ w,   b≠0.

Now [X,Y]=−b f+(δ−α)z, so Lie closure forces

    e=(α−δ)/b,   𝔰=⟨f+e z,X,NX,Y,NY⟩.              (4)

These calculations exclude the missing leading-coordinate charts as well as b=0; neither is silently assumed away.

Two σ-commuting derivations normalize the offsets. Define D₁ by

    D₁y=γw, D₁y′=γw′, D₁u=D₁u′=γz,

and zero on other basis elements. Define D₂ by D₂x=βw′, D₂x′=βw and zero elsewhere. The displayed u,u′ values in D₁ are required by [x,y]=u and its primed counterpart. Direct substitution in the remaining brackets, including mixed zero brackets, verifies both derivations. They square to zero, commute with σ and A₅, and fix z. Their images have zero mutual brackets, so 1+D_i are Lie automorphisms. Their actions on (α,δ,e) are, respectively,

    (α,δ,e)↦(α+bγ,δ−bγ,e+2γ),
    (α,δ,e)↦(α+β,δ+β,e).

Choose γ=(δ−α)/(2b) and then β to remove the common remaining offset. They extend by the identity on the torus and Q and preserve the fixed graph. The same D₁ removes e in either extreme case. Every mixed stabilizer is thus equivalent to

    𝔰(b)=⟨f,x+b y′,v+b w′,x′−b y,v′−b w⟩, b≠0.   (5)

Finally fix x,x′ and scale y,y′ by b⁻¹. This Lie automorphism scales u,u′,v,v′ by b⁻¹ and w,w′,z by b⁻², commutes with σ,A₅ and sends (5) to b=1. Extend it by the exponent map b⁻² on A₁₁. Since ⟨5⟩={1,3,4,5,9} is the square subgroup of F₁₁×, choose j with 5ʲ=b⁻² mod 11 and apply the 5ʲ-Frobenius to each field coordinate in both Q-halves. Frobenius preserves the trace alternating form, fixes Z_Q, commutes with its swap and intertwines R(a) with R(b⁻²a). It preserves S_Q. The A₁₁ exponent map matches the Z_P scaling, so this is an actual automorphism of the full envelope and graph commuting with τ. All mixed stabilizers reduce to 𝔰(1).

## The mixed folder and simplicity of every case

Put E=x+y′, D=y−x′, V=v+w′, W=w−v′, so 𝔰(1)=⟨f,E,D,V,W⟩. Its nonzero brackets are

    [E,D]=f,   [f,E]=−V,   [f,D]=−W.                 (6)

It has class three and no central z component. Its degree-one and degree-three shadows are complementary to their σ-images and remain so under every A₅ weight, while its degree-two shadow is the positive line f. Thus the lowest nonzero lower-central shadow of an S-element cannot be negated by a marked involution, just as in the reviewed overlapping example.

For the mixed torus case, use a group-theoretic replacement for the earlier abelian linear elimination. An element s bʲ in S⋊A₅ with j≠0 has commuting 11- and 5-primary parts. Its 5-part projects to bʲ and is S-conjugate to bʲ by Schur–Zassenhaus. Its 11-part then lies in C_S(bʲ)=exp⟨f⟩. This conjugation is in S≤H and leaves central graph labels fixed. Thus the P⋊A₅ image of any relevant h∈H reduces to exp(tf)z_P bʲ. Its 11-part cannot be inverted by a marked involution when t≠0 because its degree-two f shadow is fixed; when t=0 and the A₁₁ label is nonzero, the fixed nonzero z_P prevents inversion. If the A₅ label vanishes, use the lowest-grade obstruction or the nonzero center. When the A₁₁ label is zero but the A₅ label is nonzero, the unchanged Q-half or central-label obstruction applies. With both labels zero use whichever stabilizer component is nontrivial. This exhausts the marked collisions. The unchanged size count and conjugacy-invariance give every conjugate transversal, hence the Bol folder.

For any 𝔰 satisfying (2), generation and faithfulness follow from the previously reviewed fixed G argument: A⊂K normally generates both derived Sylows by their Frattini actions, and a normal subgroup inside H meets neither central Sylow subgroup and must centralize D. The coprime outer-action check gives C_G(D)=Z(D), disjoint from H.

The all-normal simplicity proof also only needs (2). For any nonzero invariant normal L≤P, its cyclic center Z_P lies in L. The plus projection injects 𝔰∩log L into (log L/Z_P)₊, so |C_L(τ)|/|S∩L|≥11. The Q factor analog is at least five. If a nontrivial torus label occurs in H∩N but the corresponding local N∩P_i is trivial, normality forces that stabilizer component to be central; center avoidance and hτ(h) then contradict the nonzero central graph label. This is exactly the J_i⇒L_i step of the reviewed construction. The same four torus-image cases force strict defect for every proper nonzero τ-stable normal N, with no assumption that N splits. The criterion at `65a3e58df517df59656ab948ac9d122208f62c4a` gives simplicity. The subgroup G₀=(Z_P×Q)⋊A and its section are unchanged because S∩Z_P=1, so the reviewed coordinate Moufang witness proves properness in every case. This establishes the asserted equivalence (2) under the cited interfaces.

## Outer automorphisms prove the remaining G-loop case

For the mixed stabilizer, the previous inner normalizer element exp(u−u′) fails to normalize S. Define r=u−u′ and the degree-two derivation

    Δx=−2v,   Δy=−2w+2v′,   Δx′=0,   Δy′=2v,

with zero values on all other basis elements. The bracket identities verify it, including Δ[x,y]=2z−2z=0 and Δ[y,y′]=−2z+2z=0. It commutes with A₅, fixes the center and preserves 𝔰(1): ΔE=0, ΔD=−2W and Δf=ΔV=ΔW=0. Its image is abelian and Δ²=0, so φ=1+Δ is a Lie automorphism. Extend φ to G by the identity on Q and A. It preserves the actual H and satisfies

    Δ−σΔσ=2 ad(r),   [Δ,σΔσ]=0,
    φʲσφ⁻ʲ=exp(2j ad r)σ.                            (7)

The first identities follow on each displayed basis vector; the degree-two operators annihilate each other's images. Thus φ extends to G⋊⟨τ̂⟩ by sending τ̂ to exp(2r)τ̂; this element is an involution since σr=−r and induces (7) on G. As φ fixes r, its j-th power sends τ̂ to exp(2jr)τ̂.

These eleven images belong to distinct H-orbits on the marked class Λ. Otherwise, after applying a power of φ⁻¹, a nonzero exp(2jr)τ̂ would be H-conjugate to τ̂. The torus comparison forces a conjugating h to have zero A-label, and the unchanged Q-half comparison forces its Q-coordinate to be zero. Write h∈S. In degree one, the shadow of h is in ⟨E,D⟩, disjoint from its σ-image, so a τ-commutator with zero degree-one term forces that shadow to vanish. Its remaining degree-two term is then a multiple of the fixed f, and the τ-commutator has zero degree-two component. It cannot equal exp(2jr). This contradiction proves distinctness.

We have |C_H(τ)|=11. Because φ preserves H, the centralizer in H of each of these eleven marked involutions also has order eleven. Each H-orbit therefore has size |H|/11, and the eleven orbits exhaust |Λ|=|H|. Automorphisms generated by φ and H-conjugation preserve H and carry τ̂ to every marked involution. They carry the full inverted section to every shifted section. The general principal-isotope interface at `ea836a5f328d6bc52913aac8fd1841a87072f5f8` proves that the mixed loop is a G-loop. Together with the symmetric and extreme cases, this proves the G-loop assertion for every stabilizer in the stated fixed-envelope class.

Finally, the two overlapping normal forms are nonisomorphic: a loop isomorphism preserves the canonical G,D, its 11-Sylow P, and H∩P. The extreme S has nilpotency class two and the mixed S has class three. Both were constructed and normalized above, so there are precisely two isomorphism classes among the overlapping cases in (1). This does not enumerate the disjoint cases or establish a universal G-loop theorem.

At exact source `d64289bb37659dc6fc95963f1e9b3323c3b22dfa`, GPT-6.1 Terra reviewers [model reviewer identity omitted], [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the full fixed-envelope theorem. Each checked the central-graph necessity, weight and dual-number exhaustion including all charts, the corrected derivations and full graph/Frobenius normalizations, extreme mirror equivalence, mixed primary-part transversality, applicability of every normal-subgroup defect and properness argument, the outer automorphism and eleven marked orbits, and the two overlapping isomorphism classes. Their acceptances retain the stated Lazard, canonical-folder, strict-defect, symmetric-factorization and principal-isotope inputs. No computation, fresh primary-source audit, formal verification or literature-novelty claim is made. The next larger gap is to control other central graphs, nonsplit fixed-subgroup extensions and other ambient envelopes, not to exclude the two explicit kinds of overlap already exhibited.
