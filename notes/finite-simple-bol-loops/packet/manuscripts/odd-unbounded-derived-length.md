# Odd simple Bol loops with unbounded derived length

**Continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`], with two independent exact-source acceptances below.** For every integer n≥4, the construction below gives a finite simple proper odd left Bol G-loop whose canonical left multiplication group G has derived length exactly 1+⌈log₂n⌉. It adapts the independently reviewed [unbounded nilpotency-class construction](odd-unbounded-derived-class.md), source `722ba8c289c96dfd87c98f9a5ab3dcb8b2080998`, replacing its filiform Lie algebra with strictly upper triangular matrices. The G-loop step uses the [symmetric factorization lemma](exact-factorization-criterion.md#symmetric-exact-factorizations-and-full-inverted-folders), reviewed at `7fbfbc5a56f4bb1ead9a4d6202c2d948a67950d8`. The related [central Lazard construction](odd-lazard-central-classification.md), source `9819182787d94bd1502a03130e2500dbba936937`, gives context but is not assumed to certify this new example. The new construction has the separate exact-source reviews below; it is not a classification of odd Bol loops.

## Parameters and construction

Fix n≥4 and distinct odd primes p>n−1 and q>n−2. Put r=ord_q(p), s=ord_p(q), E=F_{p^r}, F=F_{q^s}, and choose λ∈E× of order q and η∈F× of order p. Let N=n(n−1)/2.

Let L⁺ be the E-Lie algebra of strictly upper triangular n×n matrices, with basis e_ij for i<j. Its class is n−1 and its center is Ez, z=e_{1n}. Take a second copy L⁻, identify the two centers, and set all mixed brackets zero. The resulting algebra L has dimension 2N−1, center Ez and class n−1. Let σ_P swap the copies and fix z. The first-copy roots

    A={e_ij:1≤i<j<n}

form a copy of the strictly upper triangular (n−1)×(n−1) algebra, while the second-copy roots

    B={e_{i n}′:2≤i<n}

span an abelian subalgebra. Neither produces z internally. Their union is a subalgebra s_P of dimension N−1, and

    L=s_P ⊕ σ_P(s_P) ⊕ Ez.                                   (1)

Let A_q=C_q act on the first copy by diagonal weights (0,1,2,…,n−2,0) modulo q, and on the second by inverse weights. These weights are distinct except at the first and last coordinates, so every noncentral root has nontrivial weight under every nonidentity element of A_q. The action fixes z, preserves s_P and is inverted by σ_P. The root gap j−i gives the lower-central grading; the shadows of s_P and σ_P(s_P) are disjoint in each degree below the center.

Because n−1<p, the [Lazard/BCH interface](../REFERENCES.md#lazard-bch-interface), arXiv:2310.17595v3 §2.3, Facts 2.13–2.14, gives the exponent-p group P=exp L and subgroup S_P=exp s_P; it also identifies ideals with normal subgroups and preserves automorphisms. Restriction of scalars from E to F_p is understood.

Put A_p=(E,+), identified with Z(P). Choose an F_p-basis and write a∈A_p as (a₁,…,a_r). Let W=⊕_{j=1}^r F² with β the sum of the field traces of the standard alternating forms. Let R(a) multiply the j-th plane by η^{a_j}. The combined A_p action is faithful and has no common nonzero fixed vector; an individual nonzero a may fix some planes. Form the exponent-q extraspecial group Q with coordinates W⊕W⊕F_q and product

    (u,v,t)(u′,v′,t′)
       =(u+u′,v+v′,t+t′+½[β(u,v′)+β(v,u′)]).

Let σ_Q swap the two W halves, and let a∈A_p act by (R(a),R(a)⁻¹,1). The group A_q acts trivially on Q, while A_p acts trivially on P. Put S_Q={(u,0,0):u∈W}. Set

    A=A_p×A_q,          G=(P×Q)⋊A,
    τ=(σ_P,σ_Q) with inversion on A,
    H=(S_P×S_Q)⋊{a z(a):a∈A},

where z identifies A_p with Z(P)=E and A_q with Z(Q)=F_q. The central graph is a subgroup and normalizes both stabilizer factors. Set K={g∈G:τ(g)=g⁻¹}.

## Generation, transversality and canonical group

The fixed-free A_q action on P/Z(P), together with Z(P)≤P′=Φ(P), makes the commutators with A_q generate P. The A_p action has no common fixed vector on Q/Z(Q), so its commutators generate Q. Therefore G′=P×Q. Also A⊆K. In an odd group, ⟨K⟩ is normal, since every τ-commutator belongs to K; its normal closure of A contains P and Q, so ⟨K⟩=G.

A normal subgroup of G contained in H cannot meet P or Q nontrivially: a nontrivial normal subgroup of a finite p-group meets its center, and H avoids Z(P)×Z(Q). It therefore centralizes P×Q. If a torus element acts by an inner automorphism on P, its A_q component is trivial because an inner automorphism has p-power order while the A_q action has q-power order; similarly the A_p component must be trivial by its action on Q. Faithfulness of the cross actions then gives C_G(P×Q)=Z(P)×Z(Q), which H also avoids. Hence H is core-free, and the folder action is faithful.

The two central labels change sign under τ while the S_P and S_Q shadows occupy halves disjoint from their τ-images. Thus H∩τ(H)=1. The swaps and centers give

    |H|=|C_G(τ)|=p^{Nr} q^{2rs+1},     |G|=|H|².             (2)

The symmetric factorization lemma therefore supplies transversality of the full inverted set K to every H-conjugate, the Bol identity and the G-loop property.

## Strict defect and simplicity

Let 1≠N₀◁G be τ-stable. Put L_P=N₀∩P, L_Q=N₀∩Q, C_P=L_P∩Z(P), C_Q=L_Q∩Z(Q), and let T_p×T_q and J_p×J_q be the images in A of N₀ and H∩N₀ respectively. The prime factors split because p≠q. The normal subgroup intersections give τ- and A-invariant Lazard ideals.

A_q averaging projects L onto Ez, because the center is its only trivial weight; it preserves each A_q-invariant ideal and commutes with τ. Projection to the positive part of the noncentral shadow is injective on s_P, by (1). Thus

    |C_{L_P}(τ)| / |S_P∩L_P| ≥ |C_P|,
    |C_{L_Q}(τ)| / |S_Q∩L_Q| ≥ |C_Q|.                       (3)

Any nontrivial L_P or L_Q meets the corresponding center. These estimates do not require S_P abelian.

The central-label inclusions J_p≤C_P and J_q≤C_Q follow by the original-group normality argument of the reviewed 722 construction. For example, a p-element h∈H∩N₀ has zero A_q label and P-component s_P z_P, since A_p acts trivially on P. Normality forces s_P to centralize P modulo L_P, so [log s_P,L]⊆log L_P by the Lazard automorphism correspondence. The nonlinear terms in log(hτ(h)) therefore lie in log L_P. Averaging under A_q kills the noncentral linear terms and retains twice z_P, proving the p-label lies in C_P. The q-label proof is analogous, using the pure q-label and averaging under A_p. Thus

    |C_{N₀}(τ)| / |H∩N₀| ≥ (|C_P|/|J_p|)(|C_Q|/|J_q|).   (4)

Each factor is at least one. If T_p=T_q=1 and N₀≠1, a nontrivial derived-factor intersection contributes a strict center factor. If T_p≠1 but T_q=1, some T_p element moves a Q-plane, so L_Q≠1 and C_Q=Z(Q), while J_q=1. If T_q≠1 but T_p<A_p, then T_q=A_q and its fixed-free action forces L_P=P; the center P factor strictly exceeds J_p. If T_p=A_p and T_q=A_q, commutators force P,Q≤N₀ and N₀=G. Thus (4) is strict for every nontrivial proper τ-stable normal subgroup. The reviewed odd [strict-defect simplicity criterion](odd-folder-radicals.md#candidate-simplicity-criterion-using-τ-stable-normal-subgroups) at `65a3e58df517df59656ab948ac9d122208f62c4a` makes the loop simple; no split form of N₀ is assumed.

## Properness and derived length

The subfolder on (Z(P)×Q)⋊A and the Q-only Moufang witness in the reviewed 722 construction are unchanged. In its coordinates the product is

    (u,t_p,t_q)·(v,s_p,s_q)
      =(u+R(t_p)v, t_p+s_p, t_q+s_q−β(u,v)).               (5)

Choose a with R(a)≠1, v with (R(a)−1)v≠0, and w with β((R(a)−1)v,w)≠0. For X=(0,a,0), Y=(v,0,0), Z=(w,0,0), the two Moufang expressions (XY)(ZX) and (X(YZ))X differ in their F_q central coordinates. The proof that (5) is the restriction of the ambient loop multiplication is the explicit section calculation in the cited 722 construction; it does not depend on the internal brackets of s_P. Hence the loop is proper.

At the j-th derived stage of UT_n, the Lie algebra is spanned by e_ik with k−i≥2^j. Brackets add root gaps, and every root of gap at least 2^j is a bracket of two roots of gaps at least 2^{j−1}; induction gives equality. Its derived length is therefore ⌈log₂n⌉. Both copies embed in their central product, since their common center is identified rather than killed, and they commute; hence P has the same derived length. As G′=P×Q and Q has derived length 2,

    derived length(G)=1+⌈log₂n⌉.

Distinct primes satisfying the displayed bounds exist for every n. The construction therefore gives simple proper odd G-loops with unbounded canonical left-multiplication derived length. This does not assert an exhaustive odd-loop classification, a parameter isomorphism criterion or a literature-novelty claim. No computation or formal verification is claimed.

At exact source `7530ae6eeeb0614d7c94ed6ab1f6761f3493ab88`, GPT-6.1 Terra reviewers [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the entire uniform theorem under its cited Lazard, symmetric-factorization, canonical-folder and strict-defect inputs. Each checked the paired unitriangular algebra and complementary stabilizer, all-parameter weights and orders, canonical generation and core-freeness, symmetric transversality without abelian stabilizers, original-group central-label inclusions for every invariant normal subgroup without split-lift assumptions, the exhaustive strict-defect cases, actual subloop properness and root-gap derived-series length. No computation or fresh primary-source audit was used.
