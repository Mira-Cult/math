# Odd Lazard envelopes with no fixed quotient off the centers

**Continuation of 0323:C0010 [context outside this selected packet: `../claims/C0010.md`], with the scoped independent reviews below.** The precise endpoint is construction, exhaustion and isomorphism data for every finite simple nonassociative odd left Bol loop whose canonical group G has nilpotent D=G′ and, for each nontrivial Sylow P_i at odd prime p_i:

1. P_i has exponent p_i and nilpotency class less than p_i;
2. Z_i=Z(P_i) is central in G;
3. in G/(Z_i∏_{j≠i}P_j), a complement to P_i/Z_i over B_i=(G/D)_{p_i′} has no nonidentity fixed element on P_i/Z_i.

Condition 3 concerns common fixed points of the full coprime complement, not fixed points of each of its individual elements. Such complements exist and are conjugate by P_i/Z_i, so the condition is independent of the choice. The quotient may be nonabelian. Condition 3 is an **additional hypothesis**, not a consequence asserted here. The reviewed [unbounded-class construction](odd-unbounded-derived-class.md), source `722ba8c289c96dfd87c98f9a5ab3dcb8b2080998`, satisfies it; the class-two exponent-p case also satisfies it by the necessity theorem already proved there. This theorem does not subsume the arbitrary-exponent class-two result.

The baseline consists of those constructions and the [symmetric envelope-factorization lemma](exact-factorization-criterion.md#symmetric-exact-factorizations-and-full-inverted-folders), independently accepted at `7fbfbc5a56f4bb1ead9a4d6202c2d948a67950d8`. The new gap is exhaustion of all higher-class extensions, stabilizers and actions under conditions 1–3, with an explicit simplicity and isomorphism test. Removing condition 3, noncentral centers, arbitrary non-Lazard p-groups and nonnilpotent D remain separate obligations. Proper/non-Moufang members can be selected by the explicit finite identity test below; the endpoint here is all nonassociative simple members of the stated odd branch.

## Necessary simultaneous splitting

Use the reviewed odd-envelope inputs G=HD, |H|=|C_G(τ)|, C_G(τ)≤D, and K the full τ-inverted set, with the pins recorded in [the preceding class-two theorem](odd-central-class-two-classification.md#inputs-and-notation). Strict defect forces τ to fix each central Z_i pointwise: a negative central order-p_i line would have equality of fixed and stabilizer intersections. Core-freeness gives H∩Z_i=1. Put A=G/D and U_i=P_i/Z_i.

We need a nonabelian version of the Hall-normalizer argument. Suppose an extension E of Γ=A⋊⟨τ̂⟩ has normal p-kernel U, and the normal coprime subgroup B=A_{p′} has a complement B₀ with C_U(B₀)=1. All B-complements in its normal inverse image are U-conjugate, so E=U N_E(B₀). The kernel U∩N_E(B₀)=C_U(B₀)=1, since its commutators with B₀ lie in U∩B₀. Hence the normalizer maps isomorphically onto Γ. To make it contain the actual τ̂, first choose a complement over B⋊⟨τ̂⟩ and conjugate its involution to τ̂ inside the preimage of ⟨τ̂⟩. Its B-part then has the required normalizer. Only Schur–Zassenhaus and the specified fixed-point hypothesis are used; U need not be abelian.

Apply this locally to G/(Z_i∏_{j≠i}P_j), with τ̂ adjoined. The global quotient (G/Z(D))⋊⟨τ̂⟩ is the fiber product of these local quotients over Γ: its natural map is injective, and the orders are |Γ|∏|U_i| on both sides. The local normalizer complements therefore give a global Γ-complement containing τ̂. Let A₀ be its A-part, inverted by τ.

Let S_i=H∩P_i. In each local image of H, the kernel over A is the image of S_i, and a B_i-complement can be U_i-conjugated to the chosen one. The same normalizer argument inside that local stabilizer, whose kernel has trivial B_i-centralizer, forces it to contain the pure local A₀. Local conjugators lift to the commuting P_i factors and may be applied simultaneously. The global stabilizer image has kernel ∏S_iZ_i/Z_i. For an element above any a∈A, its local non-torus coordinates lie in these kernel factors and can be removed simultaneously. Thus a temporary conjugate H′ of the original stabilizer satisfies

    G/Z(D)=(∏U_i)⋊A₀,
    H′Z(D)/Z(D)=(∏S_iZ_i/Z_i)⋊A₀.                    (1)

Here S_i denotes the conjugated intersection. This temporary change retains the original τ,K and their full-conjugate transversal property. No quotient by a nonnormal S_i, and no assertion that a projected section is a quotient loop, is made.

Let E₀ be the preimage of A₀ in G. Then C=E₀∩H′ maps isomorphically onto A, because it is onto by (1) and its kernel lies in H′∩Z(D)=1. Since Z(D) is central, E₀=Z(D)×C and G=D⋊C. The central character

    χ(c)=τ(c)c∈Z(D)

is a homomorphism and is injective: χ(c)=1 implies c∈H′∩K=1. In particular |A_{p_i}|≤|Z_i| and A_{p_i} is elementary abelian.

## Disjoint Lie subalgebras and order equality

For any subgroup transversal to the full inverted K, H′∩τ(H′)=H′∩C_G(τ). Indeed if h and τ(h) lie in H′, then h⁻¹τ(h) belongs both to H′ and to K, so τ(h)=h. Therefore T_i=S_i∩τ(S_i) is fixed pointwise by τ. The subgroup C normalizes S_i and τ(S_i), since τ(c)=c⁻¹χ(c) with central χ(c). On T_i, conjugation by c equals conjugation by c⁻¹; oddness makes it trivial. The image of T_i in U_i is consequently B_i-fixed and must be zero by condition 3. Thus T_i≤H′∩Z_i=1.

Use Lazard logs over F_{p_i}; the exact interface is [arXiv:2310.17595v3, §2.3, Facts 2.13–2.14](../REFERENCES.md#lazard-bch-interface). Write 𝔭_i=log P_i, 𝔰_i=log S_i. Coprime averaging gives a τ-stable additive decomposition

    𝔭_i=Z_i⊕M_i,   M_i=[𝔭_i,B_i],                    (2)

because condition 3 identifies the fixed subspace with Z_i. Both 𝔰_i and τ𝔰_i are B_i-stable subalgebras avoiding Z_i. Their central graph maps vanish: their shadows have no B_i-fixed vectors, whereas Z_i is trivial. Hence both lie in M_i. Actual disjointness S_i∩τS_i=1 now implies disjoint shadows in 𝔭_i/Z_i. Projection of 𝔰_i to the plus eigenspace of that quotient is injective.

Primewise comparison of |H′|=|C_G(τ)| gives

    |A_{p_i}| |S_i|=|Z_i| |(𝔭_i/Z_i)₊|.

The central-character injection bounds the first factor on the left by |Z_i|, and the plus projection bounds the second by |(𝔭_i/Z_i)₊|. Thus both bounds are equalities. The nontrivial B_i-weights pair with their distinct inverse weights under τ, so the quotient's plus and minus dimensions are equal. We obtain

    𝔭_i=𝔰_i⊕τ𝔰_i⊕Z_i,
    A_{p_i}≅Z_i,   |S_i|²=|P_i/Z_i|.                   (3)

The first two summands are Lie subalgebras; they are not assumed abelian or ideals. The character χ identifies C with Z(D). Halving it gives a τ-inverted complement A identified with ∏Z_i, and the stabilizer is its central graph times ∏S_i.

There is no circular preservation-of-loop assumption. For the aligned H′, (3) gives H′∩C_G(τ)=1 and |G|=|H′|². Hence G=C_G(τ)H′. If H′=dHd⁻¹, write d⁻¹=c h′ with c∈C_G(τ), h′∈H′; then H=cH′c⁻¹. Conjugation by c preserves τ and full K, proving that the normalized folder represents the original loop up to isomorphism.

One further necessary condition is

    Z_i⊆[𝔭_i,𝔭_i].                                    (4)

In the abelianization 𝔭_i/[𝔭_i,𝔭_i], coprime averaging identifies the B_i-fixed part with the image of Z_i, which A fixes pointwise. Since the complement A is abelian and D=G′, this abelianization is generated by A-displacements. Its fixed central part therefore vanishes. This proves (4) and excludes an abelian central direct factor. The combined A-action is faithful, or a nonzero kernel element would give a central twisted torus element inside core-free H.

## Exact construction data and automatic transversality

Conversely take a finite set of distinct odd primes p_i and nonzero finite nilpotent F_{p_i}-Lie algebras 𝔭_i of class less than p_i, with centers Z_i satisfying (4). Supply involutions σ_i fixing Z_i, and Lie subalgebras 𝔰_i with

    𝔭_i=𝔰_i⊕σ_i𝔰_i⊕Z_i.                              (5)

Put A=∏(Z_i,+). Supply a faithful combined action ρ_i:A→Aut(𝔭_i) fixing every center pointwise and preserving 𝔰_i, such that σ_iρ_i(a)σ_i=ρ_i(a)⁻¹ and B_i=A_{p_i′} has no nonzero fixed vector on 𝔭_i/Z_i. These are explicit finite Lie-algebra and matrix conditions, and include all data obtained above. They force at least two primes: otherwise B_i=1 and 𝔭_i=Z_i, contradicting (4).

Let P_i be the Lazard group, S_i=exp 𝔰_i, D=∏P_i and G=D⋊A. Let τ restrict to σ_i and invert A. Identify z:A→Z(D) by the supplied coordinate groups and set

    H=(∏S_i)⋊{a z(a):a∈A},    K={g:τ(g)=g⁻¹}.          (6)

The action preserves both 𝔰_i and σ_i𝔰_i. The central graph is a subgroup. Equations (5) and (6) imply H∩τ(H)=1: equal torus labels in H and τH have opposite central labels, while their local components lie in the two complementary subalgebras. Taking logs of an equality s=σ(t)z reduces it to the direct sum (5), so the local shadows and twice the central labels vanish. Cardinalities give |G|=|H|². The symmetric envelope-factorization lemma at `7fbfbc5a56f4bb1ead9a4d6202c2d948a67950d8` therefore supplies the full Bol transversal and G-loop property automatically. There is no residual test through higher BCH products.

The common fixed-free action gives [P_i/Z_i,B_i]=P_i/Z_i, by coprime fixed-point lifting on its commutator quotient. The normal subgroup generated by the torus commutators therefore projects onto P_i/Z_i. Since Z_i≤P_i′ by (4), a subgroup projecting onto that quotient contains P_i′ and hence Z_i: if P_i=T Z_i with Z_i central, then P_i′=T′≤T. Thus it is all P_i. Consequently G′=D and, because A⊂K and ⟨K⟩ is normal, K generates G. There is no hidden inner-action kernel. If ρ_i(a) is conjugation by exp(v) in P_i, commutativity of A implies ρ_i(b)v−v∈Z_i for every b∈B_i; thus v modulo Z_i is B_i-fixed and must vanish. Hence any inner ρ_i(a) is the identity. An element d a centralizing D would make every ρ_i(a) inner, so combined faithfulness forces a=1 and d∈Z(D). Thus C_G(D)=Z(D). A normal subgroup contained in H has trivial intersection with D, since a nontrivial normal p-subgroup meets the center. It then centralizes D and lies in Z(D), disjoint from H. This proves core-freeness and makes G canonical.

## Complete ideal test for simplicity

Let N◁G be τ-stable. Write N∩P_i=exp I_i, where I_i is an A,σ_i-invariant ideal of 𝔭_i, and put C_i=I_i∩Z_i. Let T=π_A(N)≤A. Necessarily

    (ρ_i(t)−1)𝔭_i⊆I_i for every t∈T.                   (7)

Every such N has the exact form

    N=(∏exp I_i)⋊T.                                    (8)

To prove it, a lift n=d t∈N has its P_i-coordinate fixed modulo exp(I_i)Z_i by B_i, because N is normal and the torus is abelian. This quotient has no nonidentity B_i-fixed element, by coprime fixed-point lifting from P_i/Z_i. Hence the coordinate belongs to exp(I_i)Z_i. Remove the ideal components and write n=t z with z∈Z(D). Since τ inverts t and fixes z, nτ(n)=z²∈∏C_i; oddness gives z∈∏C_i, so t∈N. Conversely A,σ_i-invariant ideals and a subgroup T satisfying (7) yield a normal τ-stable subgroup (8): T acts trivially on each P_i/exp I_i by the Lazard automorphism correspondence, which is exactly the needed group normality condition. No central lift cocycle remains.

Let T_i=T∩A_i, with A_i identified with Z_i, and V_i=I_i/C_i. The fixed count is |C_i||(V_i)₊|. The H-intersection has kernel ∏(S_i∩exp I_i) and torus image T∩∏C_i. For the latter assertion, B_i averaging splits I_i into C_i and I_i∩M_i in (2), and 𝔰_i lies in M_i. Thus S_i∩exp(I_i)Z_i=S_i∩exp I_i; no stabilizer component can cancel a central offset outside C_i. It follows that

    |C_N(τ)|/|H∩N|
      =∏_i |C_i| |(V_i)₊| /
             (|S_i∩exp I_i| |T_i∩C_i|).                (9)

Each local factor is a power of p_i at least one, since the central intersection has size at most |C_i| and the stabilizer shadow injects into (V_i)₊ along its negative eigenspace. The exact finite simplicity test is strict inequality in (9) for every nonzero proper tuple (I_i,T) satisfying (7). The pinned strict-defect theorem at `65a3e58df517df59656ab948ac9d122208f62c4a` gives both directions, retaining its maximal-simple-quotient proof rather than assuming inversion descends to an arbitrary quotient.

These ideal and subgroup sets are finite at fixed Lie data and are specified independently of loop multiplication tables. No reduction of this higher-class test to the class-two central-subspace closure, efficiency estimate, or bound on class or dimension is asserted. Any selected simple loop is nonassociative: H contains the nontrivial central graph, while an associative loop has regular canonical left multiplication group and trivial stabilizer.

## Exact equivalence and remaining frontier

Two data give isomorphic selected loops iff they have the same prime set and there are F_{p_i}-Lie algebra isomorphisms φ_i:𝔭_i→𝔭_i′ preserving 𝔰_i and σ_i, whose restrictions E_i:Z_i→Z_i′ jointly define E:A→A′ and satisfy

    φ_i ρ_i(a)=ρ_i′(E(a)) φ_i   for every a∈A.           (10)

For necessity, a loop isomorphism preserves its canonical G,D,P_i,τ and S_i. Lazard turns the restrictions into the required Lie isomorphisms. Faithful action gives Z(G)=Z(D), and the complement in H has the intrinsic description

    {h∈H:τ(h)h∈Z(G)}={a z(a):a∈A}.

If h=s a z(a), centrality of τ(h)h puts a τS-component and an S-component equal modulo Z. Equation (5), using logs for the central equality, forces s=1. The central character τ(h)h=2z(a) then identifies the induced A-map with the center-map E. This gives (10). Conversely these Lie isomorphisms and E define a group isomorphism carrying τ,H,K to their primed versions, hence a loop isomorphism. This proves the complete equivalence criterion within the stated branch.

If only proper/non-Moufang members are wanted, evaluate a fixed Moufang identity in the finite constructed section and retain precisely those for which it fails. This is an explicit optional subclass filter, not an unproved assertion that every normal-form datum is proper. No simple Moufang classification is needed to establish the stated nonassociative odd endpoint. The broader all-simple program handles associative groups separately.

At exact source `9819182787d94bd1502a03130e2500dbba936937`, GPT-6.1 Terra reviewers [model reviewer identity omitted], [model reviewer identity omitted] and [model reviewer identity omitted] independently accepted the complete restricted parameterization. Each checked the nonabelian Hall normalizer, fiber product and actual stabilizer alignment, central-character and Lie-space equalities, preservation of the original loop, the derived-center condition, converse generation and exclusion of hidden inner actions, all normal ideals and torus lifts, exact defect test and both directions of the equivalence. Their acceptance retains the cited Lazard, symmetric-factorization, canonical odd-envelope and strict-defect interfaces. In the normal-subgroup argument, (7) follows after the lift reduction (8), rather than from an unnormalized lift alone. No computation, fresh primary-source audit, literature-novelty claim or formal verification is asserted.

The crucial remaining question is how to handle failure of condition 3; the [fixed-shadow construction](odd-fixed-shadow-simple-example.md), accepted by three independent reviewers at `396d468577c78a43d2c4d1f4821b074ddfd477ea`, gives an actual simple counterexample to its universal derivability. The theorem also does not cover noncentral centers, classes reaching the characteristic, non-prime exponents outside the separate class-two result, or nonnilpotent derived groups.
